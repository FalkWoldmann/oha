use bytes::Bytes;
#[cfg(unix)]
use compio::net::UnixStream;
use compio::{
    BufResult,
    buf::{IoBuf, IoBufMut},
    io::{AsyncRead, AsyncWrite, util::Splittable},
    net::TcpStream,
    tls::{TlsConnector, TlsStream},
};
use cyper_core::HyperStream;
use futures_util::future::{Either, select};
use hickory_resolver::config::{ResolverConfig, ResolverOpts};
use http_body_util::{BodyExt, Full};
use hyper::{Method, Request, http};
use rand::{prelude::*, rng};
use std::{
    borrow::Cow,
    cell::RefCell,
    future::poll_fn,
    io::Write,
    pin::{Pin, pin},
    rc::Rc,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering::Relaxed},
    },
    task::{Poll, ready},
    time::Instant,
};
use thiserror::Error;
use url::{ParseError, Url};

use crate::{
    ConnectToEntry,
    pcg64si::Pcg64Si,
    request_generator::{RequestGenerationError, RequestGenerator},
    runtime::{CancellationToken, LocalExecutor, spawn_workers},
    url_generator::UrlGeneratorError,
};

#[cfg(feature = "http3")]
use crate::client_h3::send_debug_request_http3;

type SendRequestHttp1 = hyper::client::conn::http1::SendRequest<Full<Bytes>>;
type SendRequestHttp2 = hyper::client::conn::http2::SendRequest<Full<Bytes>>;

fn format_host_port(host: &str, port: u16) -> String {
    if host.contains(':') && !(host.starts_with('[') && host.ends_with(']')) {
        format!("[{host}]:{port}")
    } else {
        format!("{host}:{port}")
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ConnectionTime {
    pub dns_lookup: std::time::Duration,
    pub dialup: std::time::Duration,
}

#[derive(Debug, Clone)]
/// a result for a request
pub struct RequestResult {
    pub rng: Pcg64Si,
    // When the query should started
    pub start_latency_correction: Option<std::time::Instant>,
    /// When the query started
    pub start: std::time::Instant,
    /// DNS + dialup
    /// None when reuse connection
    pub connection_time: Option<ConnectionTime>,
    /// First body byte received
    pub first_byte: Option<std::time::Instant>,
    /// When the query ends
    pub end: std::time::Instant,
    /// HTTP status
    pub status: http::StatusCode,
    /// Length of body
    pub len_bytes: usize,
}

impl RequestResult {
    /// Duration the request takes.
    pub fn duration(&self) -> std::time::Duration {
        self.end - self.start_latency_correction.unwrap_or(self.start)
    }
}

// encapsulates the HTTP generation of the work type. Used internally only for conditional logic.
#[derive(Debug, Clone, Copy, PartialEq)]
enum HttpWorkType {
    H1,
    H2,
    #[cfg(feature = "http3")]
    H3,
}

type LookupResult = Result<Vec<std::net::IpAddr>, Box<hickory_resolver::net::NetError>>;

struct LookupRequest {
    host: String,
    reply: futures_channel::oneshot::Sender<LookupResult>,
}

pub struct Dns {
    pub connect_to: Vec<ConnectToEntry>,
    lookup_tx: kanal::Sender<LookupRequest>,
}

impl Dns {
    /// Start the resolver on its own thread.
    ///
    /// A resolver is bound to the runtime of the thread it was created on, so worker threads
    /// can't share one directly and send their lookups here instead.
    pub fn new(
        config: ResolverConfig,
        opts: ResolverOpts,
        connect_to: Vec<ConnectToEntry>,
    ) -> anyhow::Result<Self> {
        let (lookup_tx, lookup_rx) = kanal::unbounded::<LookupRequest>();
        let (ready_tx, ready_rx) = std::sync::mpsc::channel::<anyhow::Result<()>>();

        std::thread::spawn(move || {
            let runtime = match crate::runtime::build_runtime() {
                Ok(runtime) => runtime,
                Err(err) => {
                    let _ = ready_tx.send(Err(err.into()));
                    return;
                }
            };
            runtime.block_on(async move {
                let resolver = match hickory_resolver::Resolver::builder_with_config(
                    config,
                    cyper_hickory::CompioConnectionProvider::new_current(),
                )
                .with_options(opts)
                .build()
                {
                    Ok(resolver) => std::rc::Rc::new(resolver),
                    Err(err) => {
                        let _ = ready_tx.send(Err(err.into()));
                        return;
                    }
                };
                let _ = ready_tx.send(Ok(()));

                let lookup_rx = lookup_rx.to_async();
                while let Ok(request) = lookup_rx.recv().await {
                    let resolver = resolver.clone();
                    compio::runtime::spawn(async move {
                        // It automatically caches the result
                        let addrs = resolver
                            .lookup_ip(request.host.as_str())
                            .await
                            .map(|lookup| lookup.iter().collect())
                            .map_err(Box::new);
                        let _ = request.reply.send(addrs);
                    })
                    .detach();
                }
            });
        });

        ready_rx.recv()??;

        Ok(Self {
            connect_to,
            lookup_tx,
        })
    }

    fn select_connect_to<'a, R: Rng>(
        &'a self,
        host: &str,
        port: u16,
        rng: &mut R,
    ) -> Option<&'a ConnectToEntry> {
        self.connect_to
            .iter()
            .filter(|entry| entry.requested_port == port && entry.requested_host == host)
            .collect::<Vec<_>>()
            .choose(rng)
            .copied()
    }

    /// Perform a DNS lookup for a given url and returns (ip_addr, port)
    pub(crate) async fn lookup<R: Rng>(
        &self,
        url: &Url,
        rng: &mut R,
    ) -> Result<(std::net::IpAddr, u16), ClientError> {
        let host = url.host_str().ok_or(ClientError::HostNotFound)?;
        let port = url
            .port_or_known_default()
            .ok_or(ClientError::PortNotFound)?;

        // Try to find an override (passed via `--connect-to`) that applies to this (host, port),
        // choosing one randomly if several match.
        let (host, port) = if let Some(entry) = self.select_connect_to(host, port, rng) {
            (entry.target_host.as_str(), entry.target_port)
        } else {
            (host, port)
        };

        let host = if host.starts_with('[') && host.ends_with(']') {
            // host is [ipv6] format
            // remove first [ and last ]
            &host[1..host.len() - 1]
        } else {
            host
        };

        // Perform actual DNS lookup, either on the original (host, port), or
        // on the (host, port) specified with `--connect-to`.
        let resolver_gone = || std::io::Error::other("DNS resolver has stopped");
        let (reply, addrs) = futures_channel::oneshot::channel();
        self.lookup_tx
            .send(LookupRequest {
                host: host.to_string(),
                reply,
            })
            .map_err(|_| resolver_gone())?;
        let addrs = addrs.await.map_err(|_| resolver_gone())??;

        let addr = *addrs.choose(rng).ok_or(ClientError::DNSNoRecord)?;

        Ok((addr, port))
    }
}

#[derive(Error, Debug)]
pub enum ClientError {
    #[error("failed to get port from URL")]
    PortNotFound,
    #[error("failed to get host from URL")]
    HostNotFound,
    #[error("No record returned from DNS")]
    DNSNoRecord,
    #[error("Redirection limit has reached")]
    TooManyRedirect,
    #[error(transparent)]
    // Use Box here because NetError is big.
    Resolve(#[from] Box<hickory_resolver::net::NetError>),

    #[cfg(feature = "native-tls")]
    #[error(transparent)]
    NativeTls(#[from] native_tls::Error),

    #[cfg(feature = "rustls")]
    #[error(transparent)]
    Rustls(#[from] rustls::Error),

    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Http(#[from] http::Error),
    #[error(transparent)]
    Hyper(#[from] hyper::Error),
    #[error(transparent)]
    InvalidUriParts(#[from] http::uri::InvalidUriParts),
    #[error(transparent)]
    InvalidHeaderValue(#[from] http::header::InvalidHeaderValue),
    #[error("Failed to get header from builder")]
    GetHeaderFromBuilder,
    #[error(transparent)]
    HeaderToStr(#[from] http::header::ToStrError),
    #[error(transparent)]
    InvalidUri(#[from] http::uri::InvalidUri),
    #[error("timeout")]
    Timeout,
    #[error("aborted due to deadline")]
    Deadline,
    #[error(transparent)]
    UrlGenerator(#[from] UrlGeneratorError),
    #[error(transparent)]
    UrlParse(#[from] ParseError),
    #[error("Request generation error: {0}")]
    RequestGeneration(#[from] RequestGenerationError),
    #[cfg(feature = "http3")]
    #[error(transparent)]
    Http3(#[from] crate::client_h3::Http3Error),
}

pub struct Client {
    pub request_generator: RequestGenerator,
    pub proxy_http_version: http::Version,
    pub proxy_headers: http::header::HeaderMap,
    pub dns: Dns,
    pub timeout: Option<std::time::Duration>,
    pub connect_timeout: std::time::Duration,
    pub redirect_limit: usize,
    pub disable_keepalive: bool,
    pub proxy_url: Option<Url>,
    #[cfg(unix)]
    pub unix_socket: Option<std::path::PathBuf>,
    #[cfg(feature = "vsock")]
    pub vsock_addr: Option<vsock::VsockAddr>,
    #[cfg(feature = "rustls")]
    pub rustls_configs: crate::tls_config::RuslsConfigs,
    #[cfg(all(feature = "native-tls", not(feature = "rustls")))]
    pub native_tls_connectors: crate::tls_config::NativeTlsConnectors,
}

#[cfg(test)]
impl Default for Client {
    fn default() -> Self {
        use crate::request_generator::BodyGenerator;

        let (resolver_config, resolver_opts) = crate::system_resolv_conf()
            .unwrap_or_else(|_| (ResolverConfig::default(), ResolverOpts::default()));
        Self {
            request_generator: RequestGenerator {
                url_generator: crate::url_generator::UrlGenerator::new_static(
                    "http://example.com".parse().unwrap(),
                ),
                https: false,
                http_proxy: None,
                method: http::Method::GET,
                version: http::Version::HTTP_11,
                headers: http::header::HeaderMap::new(),
                body_generator: BodyGenerator::Static(Bytes::new()),
                aws_config: None,
            },
            proxy_http_version: http::Version::HTTP_11,
            proxy_headers: http::header::HeaderMap::new(),
            dns: Dns::new(resolver_config, resolver_opts, Vec::new()).unwrap(),
            timeout: None,
            connect_timeout: std::time::Duration::from_secs(5),
            redirect_limit: 0,
            disable_keepalive: false,
            proxy_url: None,
            #[cfg(unix)]
            unix_socket: None,
            #[cfg(feature = "vsock")]
            vsock_addr: None,
            #[cfg(feature = "rustls")]
            rustls_configs: crate::tls_config::RuslsConfigs::new(false, None, None),
            #[cfg(all(feature = "native-tls", not(feature = "rustls")))]
            native_tls_connectors: crate::tls_config::NativeTlsConnectors::new(false, None, None),
        }
    }
}

struct ClientStateHttp1 {
    rng: Pcg64Si,
    send_request: Option<SendRequestHttp1>,
}

impl Default for ClientStateHttp1 {
    fn default() -> Self {
        Self {
            rng: SeedableRng::from_rng(&mut rand::rng()),
            send_request: None,
        }
    }
}

struct ClientStateHttp2 {
    rng: Pcg64Si,
    send_request: SendRequestHttp2,
}

pub enum QueryLimit {
    Qps(f64),
    Burst(std::time::Duration, usize),
}

// To avoid dynamic dispatch
// I'm not sure how much this is effective
pub(crate) enum Stream {
    Tcp(TcpStream),
    // Box for large variant
    Tls(Box<TlsStream<TcpStream>>),
    #[cfg(unix)]
    Unix(UnixStream),
    #[cfg(feature = "vsock")]
    Vsock(UnixStream),
    #[cfg(feature = "http3")]
    Quic(compio::quic::Connection),
}

async fn handshake_http1<S>(
    stream: HyperStream<S>,
    with_upgrade: bool,
) -> Result<SendRequestHttp1, ClientError>
where
    S: Splittable + 'static,
    S::ReadHalf: AsyncRead + Unpin,
    S::WriteHalf: AsyncWrite + Unpin,
{
    let (send_request, conn) = hyper::client::conn::http1::handshake(stream).await?;
    if with_upgrade {
        compio::runtime::spawn(conn.with_upgrades()).detach();
    } else {
        compio::runtime::spawn(conn).detach();
    }
    Ok(send_request)
}

async fn handshake_http2<S>(stream: HyperStream<S>) -> Result<SendRequestHttp2, ClientError>
where
    S: Splittable + 'static,
    S::ReadHalf: AsyncRead + Unpin,
    S::WriteHalf: AsyncWrite + Unpin,
{
    let (send_request, conn) = hyper::client::conn::http2::Builder::new(LocalExecutor)
        // from nghttp2's default
        .initial_stream_window_size((1 << 30) - 1)
        .initial_connection_window_size((1 << 30) - 1)
        .handshake(stream)
        .await?;
    compio::runtime::spawn(conn).detach();
    Ok(send_request)
}

impl Stream {
    async fn handshake_http1(self, with_upgrade: bool) -> Result<SendRequestHttp1, ClientError> {
        match self {
            Stream::Tcp(stream) => {
                handshake_http1(HyperStream::new_plain(stream), with_upgrade).await
            }
            Stream::Tls(stream) => {
                handshake_http1(HyperStream::new_tls(*stream), with_upgrade).await
            }
            #[cfg(unix)]
            Stream::Unix(stream) => {
                handshake_http1(HyperStream::new_plain(stream), with_upgrade).await
            }
            #[cfg(feature = "vsock")]
            Stream::Vsock(stream) => {
                handshake_http1(HyperStream::new_plain(stream), with_upgrade).await
            }
            #[cfg(feature = "http3")]
            Stream::Quic(_) => {
                panic!("quic is not supported in http1")
            }
        }
    }
    async fn handshake_http2(self) -> Result<SendRequestHttp2, ClientError> {
        match self {
            Stream::Tcp(stream) => handshake_http2(HyperStream::new_plain(stream)).await,
            Stream::Tls(stream) => handshake_http2(HyperStream::new_tls(*stream)).await,
            #[cfg(unix)]
            Stream::Unix(stream) => handshake_http2(HyperStream::new_plain(stream)).await,
            #[cfg(feature = "vsock")]
            Stream::Vsock(stream) => handshake_http2(HyperStream::new_plain(stream)).await,
            #[cfg(feature = "http3")]
            Stream::Quic(_) => {
                panic!("quic is not supported in http2")
            }
        }
    }
}

/// A connection upgraded by a proxy, to run TLS through the tunnel.
///
/// Both halves share the connection and only borrow it while polling. A pending read must not
/// block writes, which rules out `compio::io::util::split`.
#[derive(Clone)]
struct Tunnel(Rc<RefCell<hyper::upgrade::Upgraded>>);

impl Tunnel {
    fn new(upgraded: hyper::upgrade::Upgraded) -> Self {
        Self(Rc::new(RefCell::new(upgraded)))
    }

    async fn flush_upgraded(&self) -> std::io::Result<()> {
        poll_fn(|cx| hyper::rt::Write::poll_flush(Pin::new(&mut *self.0.borrow_mut()), cx)).await
    }
}

impl Splittable for Tunnel {
    type ReadHalf = Self;
    type WriteHalf = Self;

    fn split(self) -> (Self::ReadHalf, Self::WriteHalf) {
        (self.clone(), self)
    }
}

impl AsyncRead for Tunnel {
    async fn read<B: IoBufMut>(&mut self, mut buf: B) -> BufResult<usize, B> {
        let res = poll_fn(|cx| {
            let mut read_buf = hyper::rt::ReadBuf::uninit(buf.as_uninit());
            ready!(hyper::rt::Read::poll_read(
                Pin::new(&mut *self.0.borrow_mut()),
                cx,
                read_buf.unfilled()
            ))?;
            Poll::Ready(Ok(read_buf.filled().len()))
        })
        .await;
        if let Ok(len) = res {
            // SAFETY: `poll_read` has filled the first `len` bytes
            unsafe { buf.advance_to(len) };
        }
        BufResult(res, buf)
    }
}

impl AsyncWrite for Tunnel {
    async fn write<B: IoBuf>(&mut self, buf: B) -> BufResult<usize, B> {
        let res = poll_fn(|cx| {
            hyper::rt::Write::poll_write(Pin::new(&mut *self.0.borrow_mut()), cx, buf.as_init())
        })
        .await;
        // Flush as part of the write. compio's poll adapters report a flush as done once the
        // one already in flight completes, which loses data buffered while `flush` is pending.
        let res = match res {
            Ok(len) => self.flush_upgraded().await.map(|()| len),
            Err(err) => Err(err),
        };
        BufResult(res, buf)
    }

    async fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }

    async fn shutdown(&mut self) -> std::io::Result<()> {
        poll_fn(|cx| hyper::rt::Write::poll_shutdown(Pin::new(&mut *self.0.borrow_mut()), cx)).await
    }
}

/// compio has no vsock support. Sending and receiving works on any stream socket though, so
/// connect on the thread pool and hand the socket over.
#[cfg(feature = "vsock")]
async fn connect_vsock(addr: vsock::VsockAddr) -> std::io::Result<UnixStream> {
    let stream = compio::runtime::spawn_blocking(move || vsock::VsockStream::connect(&addr))
        .await
        .map_err(std::io::Error::from)??;
    UnixStream::from_std(std::os::fd::OwnedFd::from(stream).into())
}

impl Client {
    #[inline]
    fn is_http2(&self) -> bool {
        self.request_generator.version == http::Version::HTTP_2
    }

    #[inline]
    fn is_proxy_http2(&self) -> bool {
        self.proxy_http_version == http::Version::HTTP_2
    }

    fn is_work_http2(&self) -> bool {
        if self.proxy_url.is_some() {
            if self.request_generator.https {
                self.is_http2()
            } else {
                self.is_proxy_http2()
            }
        } else {
            self.is_http2()
        }
    }

    fn work_type(&self) -> HttpWorkType {
        #[cfg(feature = "http3")]
        if self.request_generator.version == http::Version::HTTP_3 {
            return HttpWorkType::H3;
        }
        if self.is_work_http2() {
            HttpWorkType::H2
        } else {
            HttpWorkType::H1
        }
    }

    /// Perform a DNS lookup to cache it
    /// This is useful to avoid DNS lookup latency at the first concurrent requests
    pub async fn pre_lookup(&self) -> Result<(), ClientError> {
        // If the client is using a unix socket, we don't need to do a DNS lookup
        #[cfg(unix)]
        if self.unix_socket.is_some() {
            return Ok(());
        }
        // If the client is using a vsock address, we don't need to do a DNS lookup
        #[cfg(feature = "vsock")]
        if self.vsock_addr.is_some() {
            return Ok(());
        }

        let mut rng = rand::rng();
        let url = self.request_generator.url_generator.generate(&mut rng)?;
        // It automatically caches the result
        self.dns.lookup(&url, &mut rng).await?;
        Ok(())
    }

    #[allow(clippy::type_complexity)]
    pub fn generate_request<R: Rng + Copy>(
        &self,
        rng: &mut R,
    ) -> Result<(Cow<'_, Url>, Request<Full<Bytes>>, R), ClientError> {
        let snapshot = *rng;
        let (url, mut req) = self.request_generator.generate(rng)?;
        if self.proxy_url.is_some()
            && req.uri().scheme_str() == Some("http")
            && let Some(authority) = req.uri().authority()
        {
            let requested_host = authority.host();
            let requested_port = authority.port_u16().unwrap_or(80);
            if let Some(entry) = self
                .dns
                .select_connect_to(requested_host, requested_port, rng)
            {
                let new_authority: http::uri::Authority =
                    format_host_port(entry.target_host.as_str(), entry.target_port).parse()?;
                let mut parts = req.uri().clone().into_parts();
                parts.authority = Some(new_authority);
                let new_uri = http::Uri::from_parts(parts)?;
                *req.uri_mut() = new_uri;
            }
        }
        Ok((url, req, snapshot))
    }

    /**
     * Returns a stream of the underlying transport. NOT a HTTP client
     */
    pub(crate) async fn client<R: Rng>(
        &self,
        url: &Url,
        rng: &mut R,
        http_version: http::Version,
    ) -> Result<(Instant, Stream), ClientError> {
        let timeout_duration = self.connect_timeout;

        if url.scheme() == "https" {
            let addr = self.dns.lookup(url, rng).await?;
            let dns_lookup = Instant::now();
            // If we do not put a timeout here then the connections attempts will
            // linger long past the configured timeout
            let stream =
                compio::time::timeout(timeout_duration, self.tls_client(addr, url, http_version))
                    .await;
            return match stream {
                Ok(Ok(stream)) => Ok((dns_lookup, stream)),
                Ok(Err(err)) => Err(err),
                Err(_) => Err(ClientError::Timeout),
            };
        }
        #[cfg(unix)]
        if let Some(socket_path) = &self.unix_socket {
            let dns_lookup = Instant::now();
            let stream =
                compio::time::timeout(timeout_duration, UnixStream::connect(socket_path)).await;
            return match stream {
                Ok(Ok(stream)) => Ok((dns_lookup, Stream::Unix(stream))),
                Ok(Err(err)) => Err(ClientError::Io(err)),
                Err(_) => Err(ClientError::Timeout),
            };
        }
        #[cfg(feature = "vsock")]
        if let Some(addr) = self.vsock_addr {
            let dns_lookup = Instant::now();
            let stream = compio::time::timeout(timeout_duration, connect_vsock(addr)).await;
            return match stream {
                Ok(Ok(stream)) => Ok((dns_lookup, Stream::Vsock(stream))),
                Ok(Err(err)) => Err(ClientError::Io(err)),
                Err(_) => Err(ClientError::Timeout),
            };
        }
        // HTTP
        let addr = self.dns.lookup(url, rng).await?;
        let dns_lookup = Instant::now();
        let stream = compio::time::timeout(
            timeout_duration,
            TcpStream::connect(std::net::SocketAddr::from(addr)),
        )
        .await;
        match stream {
            Ok(Ok(stream)) => {
                stream.set_nodelay(true)?;
                Ok((dns_lookup, Stream::Tcp(stream)))
            }
            Ok(Err(err)) => Err(ClientError::Io(err)),
            Err(_) => Err(ClientError::Timeout),
        }
    }

    async fn tls_client(
        &self,
        addr: (std::net::IpAddr, u16),
        url: &Url,
        http_version: http::Version,
    ) -> Result<Stream, ClientError> {
        let stream = TcpStream::connect(std::net::SocketAddr::from(addr)).await?;
        stream.set_nodelay(true)?;

        let stream = self.connect_tls(stream, url, http_version).await?;

        Ok(Stream::Tls(Box::new(stream)))
    }

    #[cfg(all(feature = "native-tls", not(feature = "rustls")))]
    fn tls_connector(&self, http_version: http::Version) -> TlsConnector {
        self.native_tls_connectors
            .connector(http_version >= http::Version::HTTP_2)
            .clone()
    }

    #[cfg(feature = "rustls")]
    fn tls_connector(&self, http_version: http::Version) -> TlsConnector {
        TlsConnector::from(self.rustls_configs.config(http_version).clone())
    }

    async fn connect_tls<S>(
        &self,
        stream: S,
        url: &Url,
        http_version: http::Version,
    ) -> Result<TlsStream<S>, ClientError>
    where
        S: Splittable + 'static,
        S::ReadHalf: AsyncRead + Unpin,
        S::WriteHalf: AsyncWrite + Unpin,
    {
        let stream = self
            .tls_connector(http_version)
            .connect(url.host_str().ok_or(ClientError::HostNotFound)?, stream)
            .await?;

        Ok(stream)
    }

    async fn client_http1<R: Rng>(
        &self,
        url: &Url,
        rng: &mut R,
    ) -> Result<(Instant, SendRequestHttp1), ClientError> {
        if let Some(proxy_url) = &self.proxy_url {
            let http_proxy_version = if self.is_proxy_http2() {
                http::Version::HTTP_2
            } else {
                http::Version::HTTP_11
            };
            let (dns_lookup, stream) = self.client(proxy_url, rng, http_proxy_version).await?;
            if url.scheme() == "https" {
                let requested_host = url.host_str().ok_or(ClientError::HostNotFound)?;
                let requested_port = url
                    .port_or_known_default()
                    .ok_or(ClientError::PortNotFound)?;
                let (connect_host, connect_port) = if let Some(entry) =
                    self.dns
                        .select_connect_to(requested_host, requested_port, rng)
                {
                    (entry.target_host.as_str(), entry.target_port)
                } else {
                    (requested_host, requested_port)
                };
                let connect_authority = format_host_port(connect_host, connect_port);
                // Do CONNECT request to proxy
                let req = {
                    let mut builder = http::Request::builder()
                        .method(Method::CONNECT)
                        .uri(connect_authority);
                    *builder
                        .headers_mut()
                        .ok_or(ClientError::GetHeaderFromBuilder)? = self.proxy_headers.clone();
                    builder.body(http_body_util::Full::default())?
                };
                let res = if self.proxy_http_version == http::Version::HTTP_2 {
                    let mut send_request = stream.handshake_http2().await?;
                    send_request.send_request(req).await?
                } else {
                    let mut send_request = stream.handshake_http1(true).await?;
                    send_request.send_request(req).await?
                };
                let stream = hyper::upgrade::on(res).await?;
                let stream = self
                    .connect_tls(Tunnel::new(stream), url, self.request_generator.version)
                    .await?;
                let send_request = handshake_http1(HyperStream::new_tls(stream), false).await?;
                Ok((dns_lookup, send_request))
            } else {
                // Send full URL in request() for HTTP proxy
                Ok((dns_lookup, stream.handshake_http1(false).await?))
            }
        } else {
            let (dns_lookup, stream) = self.client(url, rng, http::Version::HTTP_11).await?;
            Ok((dns_lookup, stream.handshake_http1(false).await?))
        }
    }

    async fn work_http1(
        &self,
        client_state: &mut ClientStateHttp1,
    ) -> Result<RequestResult, ClientError> {
        let do_req = async {
            let (url, request, rng) = self.generate_request(&mut client_state.rng)?;
            let mut start = std::time::Instant::now();
            let mut first_byte: Option<std::time::Instant> = None;
            let mut connection_time: Option<ConnectionTime> = None;

            let mut send_request = if let Some(send_request) = client_state.send_request.take() {
                send_request
            } else {
                let (dns_lookup, send_request) =
                    self.client_http1(&url, &mut client_state.rng).await?;
                let dialup = std::time::Instant::now();

                connection_time = Some(ConnectionTime {
                    dns_lookup: dns_lookup - start,
                    dialup: dialup - start,
                });
                send_request
            };
            while send_request.ready().await.is_err() {
                // This gets hit when the connection for HTTP/1.1 faults
                // This re-connects
                start = std::time::Instant::now();
                let (dns_lookup, send_request_) =
                    self.client_http1(&url, &mut client_state.rng).await?;
                send_request = send_request_;
                let dialup = std::time::Instant::now();
                connection_time = Some(ConnectionTime {
                    dns_lookup: dns_lookup - start,
                    dialup: dialup - start,
                });
            }
            match send_request.send_request(request).await {
                Ok(res) => {
                    let (parts, mut stream) = res.into_parts();
                    let mut status = parts.status;

                    let mut len_bytes = 0;
                    while let Some(chunk) = stream.frame().await {
                        if first_byte.is_none() {
                            first_byte = Some(std::time::Instant::now())
                        }
                        len_bytes += chunk?.data_ref().map(|d| d.len()).unwrap_or_default();
                    }

                    if self.redirect_limit != 0
                        && let Some(location) = parts.headers.get("Location")
                    {
                        let (send_request_redirect, new_status, len) = self
                            .redirect(
                                url,
                                rng,
                                send_request,
                                location,
                                self.redirect_limit,
                                &mut client_state.rng,
                            )
                            .await?;

                        send_request = send_request_redirect;
                        status = new_status;
                        len_bytes = len;
                    }

                    let end = std::time::Instant::now();

                    let result = RequestResult {
                        rng,
                        start_latency_correction: None,
                        start,
                        first_byte,
                        end,
                        status,
                        len_bytes,
                        connection_time,
                    };

                    if !self.disable_keepalive {
                        client_state.send_request = Some(send_request);
                    }

                    Ok::<_, ClientError>(result)
                }
                Err(e) => {
                    client_state.send_request = Some(send_request);
                    Err(e.into())
                }
            }
        };

        if let Some(timeout) = self.timeout {
            match compio::time::timeout(timeout, do_req).await {
                Ok(res) => res,
                Err(_) => Err(ClientError::Timeout),
            }
        } else {
            do_req.await
        }
    }

    async fn connect_http2<R: Rng>(
        &self,
        url: &Url,
        rng: &mut R,
    ) -> Result<(ConnectionTime, SendRequestHttp2), ClientError> {
        let start = std::time::Instant::now();
        if let Some(proxy_url) = &self.proxy_url {
            let http_proxy_version = if self.is_proxy_http2() {
                http::Version::HTTP_2
            } else {
                http::Version::HTTP_11
            };
            let (dns_lookup, stream) = self.client(proxy_url, rng, http_proxy_version).await?;
            if url.scheme() == "https" {
                let requested_host = url.host_str().ok_or(ClientError::HostNotFound)?;
                let requested_port = url
                    .port_or_known_default()
                    .ok_or(ClientError::PortNotFound)?;
                let (connect_host, connect_port) = if let Some(entry) =
                    self.dns
                        .select_connect_to(requested_host, requested_port, rng)
                {
                    (entry.target_host.as_str(), entry.target_port)
                } else {
                    (requested_host, requested_port)
                };
                let connect_authority = format_host_port(connect_host, connect_port);
                let req = {
                    let mut builder = http::Request::builder()
                        .method(Method::CONNECT)
                        .uri(connect_authority);
                    *builder
                        .headers_mut()
                        .ok_or(ClientError::GetHeaderFromBuilder)? = self.proxy_headers.clone();
                    builder.body(http_body_util::Full::default())?
                };
                let res = if self.proxy_http_version == http::Version::HTTP_2 {
                    let mut send_request = stream.handshake_http2().await?;
                    send_request.send_request(req).await?
                } else {
                    let mut send_request = stream.handshake_http1(true).await?;
                    send_request.send_request(req).await?
                };
                let stream = hyper::upgrade::on(res).await?;
                let stream = self
                    .connect_tls(Tunnel::new(stream), url, http::Version::HTTP_2)
                    .await?;
                let send_request = handshake_http2(HyperStream::new_tls(stream)).await?;
                let dialup = std::time::Instant::now();

                Ok((
                    ConnectionTime {
                        dns_lookup: dns_lookup - start,
                        dialup: dialup - start,
                    },
                    send_request,
                ))
            } else {
                let send_request = stream.handshake_http2().await?;
                let dialup = std::time::Instant::now();
                Ok((
                    ConnectionTime {
                        dns_lookup: dns_lookup - start,
                        dialup: dialup - start,
                    },
                    send_request,
                ))
            }
        } else {
            let (dns_lookup, stream) = self
                .client(url, rng, self.request_generator.version)
                .await?;
            let send_request = stream.handshake_http2().await?;
            let dialup = std::time::Instant::now();
            Ok((
                ConnectionTime {
                    dns_lookup: dns_lookup - start,
                    dialup: dialup - start,
                },
                send_request,
            ))
        }
    }

    async fn work_http2(
        &self,
        client_state: &mut ClientStateHttp2,
    ) -> Result<RequestResult, ClientError> {
        let do_req = async {
            let (_url, request, rng) = self.generate_request(&mut client_state.rng)?;
            let start = std::time::Instant::now();
            let mut first_byte: Option<std::time::Instant> = None;
            let connection_time: Option<ConnectionTime> = None;

            match client_state.send_request.send_request(request).await {
                Ok(res) => {
                    let (parts, mut stream) = res.into_parts();
                    let status = parts.status;

                    let mut len_bytes = 0;
                    while let Some(chunk) = stream.frame().await {
                        if first_byte.is_none() {
                            first_byte = Some(std::time::Instant::now())
                        }
                        len_bytes += chunk?.data_ref().map(|d| d.len()).unwrap_or_default();
                    }

                    let end = std::time::Instant::now();

                    let result = RequestResult {
                        rng,
                        start_latency_correction: None,
                        start,
                        first_byte,
                        end,
                        status,
                        len_bytes,
                        connection_time,
                    };

                    Ok::<_, ClientError>(result)
                }
                Err(e) => Err(e.into()),
            }
        };

        if let Some(timeout) = self.timeout {
            match compio::time::timeout(timeout, do_req).await {
                Ok(res) => res,
                Err(_) => Err(ClientError::Timeout),
            }
        } else {
            do_req.await
        }
    }

    #[allow(clippy::type_complexity)]
    async fn redirect<R: Rng + Send + Copy>(
        &self,
        base_url: Cow<'_, Url>,
        seed: R,
        send_request: SendRequestHttp1,
        location: &http::header::HeaderValue,
        limit: usize,
        rng: &mut R,
    ) -> Result<(SendRequestHttp1, http::StatusCode, usize), ClientError> {
        if limit == 0 {
            return Err(ClientError::TooManyRedirect);
        }
        let url = match Url::parse(location.to_str()?) {
            Ok(url) => url,
            Err(ParseError::RelativeUrlWithoutBase) => Url::options()
                .base_url(Some(&base_url))
                .parse(location.to_str()?)?,
            Err(err) => Err(err)?,
        };

        let (mut send_request, send_request_base) =
            if base_url.authority() == url.authority() && !self.disable_keepalive {
                // reuse connection
                (send_request, None)
            } else {
                let (_dns_lookup, stream) = self.client_http1(&url, rng).await?;
                (stream, Some(send_request))
            };

        while send_request.ready().await.is_err() {
            let (_dns_lookup, stream) = self.client_http1(&url, rng).await?;
            send_request = stream;
        }

        let mut request = self.generate_request(&mut seed.clone())?.1;
        if url.authority() != base_url.authority() {
            request.headers_mut().insert(
                http::header::HOST,
                http::HeaderValue::from_str(url.authority())?,
            );
        }
        *request.uri_mut() = if self.proxy_url.is_some() && url.scheme() == "http" {
            // Full URL in request() for HTTP proxy
            url.as_str().parse()?
        } else {
            url[url::Position::BeforePath..].parse()?
        };
        if self.proxy_url.is_some()
            && request.uri().scheme_str() == Some("http")
            && let Some(authority) = request.uri().authority()
        {
            let requested_host = authority.host();
            let requested_port = authority.port_u16().unwrap_or(80);
            if let Some(entry) = self
                .dns
                .select_connect_to(requested_host, requested_port, rng)
            {
                let new_authority: http::uri::Authority =
                    format_host_port(entry.target_host.as_str(), entry.target_port).parse()?;
                let mut parts = request.uri().clone().into_parts();
                parts.authority = Some(new_authority);
                let new_uri = http::Uri::from_parts(parts)?;
                *request.uri_mut() = new_uri;
            }
        }
        let res = send_request.send_request(request).await?;
        let (parts, mut stream) = res.into_parts();
        let mut status = parts.status;

        let mut len_bytes = 0;
        while let Some(chunk) = stream.frame().await {
            len_bytes += chunk?.data_ref().map(|d| d.len()).unwrap_or_default();
        }

        if let Some(location) = parts.headers.get("Location") {
            let (send_request_redirect, new_status, len) =
                Box::pin(self.redirect(base_url, seed, send_request, location, limit - 1, rng))
                    .await?;
            send_request = send_request_redirect;
            status = new_status;
            len_bytes = len;
        }

        if let Some(send_request_base) = send_request_base {
            Ok((send_request_base, status, len_bytes))
        } else {
            Ok((send_request, status, len_bytes))
        }
    }
}

/// Check error and decide whether to cancel the connection
pub(crate) fn is_cancel_error(res: &Result<RequestResult, ClientError>) -> bool {
    matches!(res, Err(ClientError::Deadline)) || is_too_many_open_files(res)
}

/// Check error was "Too many open file"
fn is_too_many_open_files(res: &Result<RequestResult, ClientError>) -> bool {
    res.as_ref()
        .err()
        .map(|err| match err {
            ClientError::Io(io_error) => io_error.raw_os_error() == Some(libc::EMFILE),
            _ => false,
        })
        .unwrap_or(false)
}

/// Check error was any Hyper error (primarily for HTTP2 connection errors)
fn is_hyper_error(res: &Result<RequestResult, ClientError>) -> bool {
    res.as_ref()
        .err()
        .map(|err| match err {
            // REVIEW: IoErrors, if indicating the underlying connection has failed,
            // should also cause a stop of HTTP2 requests
            ClientError::Io(_) => true,
            ClientError::Hyper(_) => true,
            _ => false,
        })
        .unwrap_or(false)
}

async fn setup_http2<R: Rng>(
    client: &Client,
    rng: &mut R,
) -> Result<(ConnectionTime, SendRequestHttp2), ClientError> {
    let url = client.request_generator.url_generator.generate(rng)?;
    let (connection_time, send_request) = client.connect_http2(&url, rng).await?;

    Ok((connection_time, send_request))
}

async fn work_http2_once(
    client: &Client,
    client_state: &mut ClientStateHttp2,
    report_tx: &kanal::Sender<Result<RequestResult, ClientError>>,
    connection_time: ConnectionTime,
    start_latency_correction: Option<Instant>,
) -> (bool, bool) {
    let mut res = client.work_http2(client_state).await;
    let is_cancel = is_cancel_error(&res);
    let is_reconnect = is_hyper_error(&res);
    set_connection_time(&mut res, connection_time);
    if let Some(start_latency_correction) = start_latency_correction {
        set_start_latency_correction(&mut res, start_latency_correction);
    }
    report_tx.send(res).unwrap();
    (is_cancel, is_reconnect)
}

pub(crate) fn set_connection_time<E>(
    res: &mut Result<RequestResult, E>,
    connection_time: ConnectionTime,
) {
    if let Ok(res) = res {
        res.connection_time = Some(connection_time);
    }
}

pub(crate) fn set_start_latency_correction<E>(
    res: &mut Result<RequestResult, E>,
    start_latency_correction: std::time::Instant,
) {
    if let Ok(res) = res {
        res.start_latency_correction = Some(start_latency_correction);
    }
}

pub async fn work_debug<W: Write>(w: &mut W, client: Arc<Client>) -> Result<(), ClientError> {
    let mut rng = Pcg64Si::from_rng(&mut rng());
    let (url, request, _) = client.generate_request(&mut rng)?;

    writeln!(w, "{request:#?}")?;

    let response = match client.work_type() {
        #[cfg(feature = "http3")]
        HttpWorkType::H3 => {
            let (_, (h3_connection, client_state)) = client.connect_http3(&url, &mut rng).await?;

            send_debug_request_http3(h3_connection, client_state, request).await?
        }
        HttpWorkType::H2 => {
            let (_, mut client_state) = client.connect_http2(&url, &mut rng).await?;
            let response = client_state.send_request(request).await?;
            let (parts, body) = response.into_parts();
            let body = body.collect().await.unwrap().to_bytes();

            http::Response::from_parts(parts, body)
        }
        HttpWorkType::H1 => {
            let (_dns_lookup, mut send_request) = client.client_http1(&url, &mut rng).await?;

            let response = send_request.send_request(request).await?;
            let (parts, body) = response.into_parts();
            let body = body.collect().await.unwrap().to_bytes();

            http::Response::from_parts(parts, body)
        }
    };

    writeln!(w, "{response:#?}")?;

    Ok(())
}

/// Run n tasks by m workers
pub async fn work(
    client: Arc<Client>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    n_tasks: usize,
    n_connections: usize,
    n_http2_parallel: usize,
    worker_threads: std::num::NonZeroUsize,
) {
    #[cfg(feature = "http3")]
    if matches!(client.work_type(), HttpWorkType::H3) {
        crate::client_h3::work(
            client,
            report_tx,
            n_tasks,
            n_connections,
            n_http2_parallel,
            worker_threads,
        )
        .await;
        return;
    }

    use std::sync::atomic::{AtomicUsize, Ordering};
    let counter = Arc::new(AtomicUsize::new(0));

    match client.work_type() {
        #[cfg(feature = "http3")]
        HttpWorkType::H3 => unreachable!(),
        HttpWorkType::H2 => {
            let workers = spawn_workers(worker_threads.get(), n_connections, move || {
                let report_tx = report_tx.clone();
                let counter = counter.clone();
                let client = client.clone();
                async move {
                    let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
                    loop {
                        match setup_http2(&client, &mut rng).await {
                            Ok((connection_time, send_request)) => {
                                let futures = (0..n_http2_parallel)
                                    .map(|_| {
                                        let report_tx = report_tx.clone();
                                        let counter = counter.clone();
                                        let client = client.clone();

                                        let mut client_state = ClientStateHttp2 {
                                            rng: SeedableRng::from_rng(&mut rand::rng()),
                                            send_request: send_request.clone(),
                                        };
                                        compio::runtime::spawn(async move {
                                            while counter.fetch_add(1, Ordering::Relaxed) < n_tasks
                                            {
                                                let (is_cancel, is_reconnect) = work_http2_once(
                                                    &client,
                                                    &mut client_state,
                                                    &report_tx,
                                                    connection_time,
                                                    None,
                                                )
                                                .await;

                                                if is_cancel || is_reconnect {
                                                    return is_cancel;
                                                }
                                            }

                                            true
                                        })
                                    })
                                    .collect::<Vec<_>>();

                                let mut connection_gone = false;
                                for f in futures {
                                    match f.await {
                                        Ok(true) => {
                                            // All works done
                                            connection_gone = true;
                                        }
                                        Err(_) => {
                                            // Unexpected
                                            connection_gone = true;
                                        }
                                        _ => {}
                                    }
                                }

                                if connection_gone {
                                    return;
                                }
                            }
                            Err(err) => {
                                if counter.fetch_add(1, Ordering::Relaxed) < n_tasks {
                                    report_tx.send(Err(err)).unwrap();
                                } else {
                                    return;
                                }
                            }
                        }
                    }
                }
            });
            workers.join().await;
        }
        HttpWorkType::H1 => {
            let workers = spawn_workers(worker_threads.get(), n_connections, move || {
                let report_tx = report_tx.clone();
                let counter = counter.clone();
                let client = client.clone();
                async move {
                    let mut client_state = ClientStateHttp1::default();
                    while counter.fetch_add(1, Ordering::Relaxed) < n_tasks {
                        let res = client.work_http1(&mut client_state).await;
                        let is_cancel = is_cancel_error(&res);
                        report_tx.send(res).unwrap();
                        if is_cancel {
                            break;
                        }
                    }
                }
            });
            workers.join().await;
        }
    };
}

/// n tasks by m workers limit to qps works in a second
pub async fn work_with_qps(
    client: Arc<Client>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    query_limit: QueryLimit,
    n_tasks: usize,
    n_connections: usize,
    n_http_parallel: usize,
    worker_threads: std::num::NonZeroUsize,
) {
    #[cfg(feature = "http3")]
    if matches!(client.work_type(), HttpWorkType::H3) {
        crate::client_h3::work_with_qps(
            client,
            report_tx,
            query_limit,
            n_tasks,
            n_connections,
            n_http_parallel,
            worker_threads,
        )
        .await;
        return;
    }

    let (tx, rx) = kanal::unbounded::<()>();

    let work_queue = async move {
        match query_limit {
            QueryLimit::Qps(qps) => {
                let start = std::time::Instant::now();
                for i in 0..n_tasks {
                    compio::time::sleep_until(
                        start + std::time::Duration::from_secs_f64(i as f64 * 1f64 / qps),
                    )
                    .await;
                    tx.send(())?;
                }
            }
            QueryLimit::Burst(duration, rate) => {
                let mut n = 0;
                // Handle via rate till n_tasks out of bound
                while n + rate < n_tasks {
                    compio::time::sleep(duration).await;
                    for _ in 0..rate {
                        tx.send(())?;
                    }
                    n += rate;
                }
                // Handle the remaining tasks
                if n_tasks > n {
                    compio::time::sleep(duration).await;
                    for _ in 0..n_tasks - n {
                        tx.send(())?;
                    }
                }
            }
        }
        // tx gone
        drop(tx);
        Ok::<(), kanal::SendError>(())
    };

    let rx = rx.to_async();
    match client.work_type() {
        #[cfg(feature = "http3")]
        HttpWorkType::H3 => unreachable!(),
        HttpWorkType::H2 => {
            let workers = spawn_workers(worker_threads.get(), n_connections, move || {
                let report_tx = report_tx.clone();
                let rx = rx.clone();
                let client = client.clone();
                async move {
                    let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
                    loop {
                        match setup_http2(&client, &mut rng).await {
                            Ok((connection_time, send_request)) => {
                                let futures = (0..n_http_parallel)
                                    .map(|_| {
                                        let report_tx = report_tx.clone();
                                        let rx = rx.clone();
                                        let client = client.clone();
                                        let mut client_state = ClientStateHttp2 {
                                            rng: SeedableRng::from_rng(&mut rand::rng()),
                                            send_request: send_request.clone(),
                                        };
                                        compio::runtime::spawn(async move {
                                            while let Ok(()) = rx.recv().await {
                                                let (is_cancel, is_reconnect) = work_http2_once(
                                                    &client,
                                                    &mut client_state,
                                                    &report_tx,
                                                    connection_time,
                                                    None,
                                                )
                                                .await;

                                                if is_cancel || is_reconnect {
                                                    return is_cancel;
                                                }
                                            }
                                            true
                                        })
                                    })
                                    .collect::<Vec<_>>();
                                let mut connection_gone = false;
                                for f in futures {
                                    match f.await {
                                        Ok(true) => {
                                            // All works done
                                            connection_gone = true;
                                        }
                                        Err(_) => {
                                            // Unexpected
                                            connection_gone = true;
                                        }
                                        _ => {}
                                    }
                                }
                                if connection_gone {
                                    return;
                                }
                            }
                            Err(err) => {
                                // Consume a task
                                if let Ok(()) = rx.recv().await {
                                    report_tx.send(Err(err)).unwrap();
                                } else {
                                    return;
                                }
                            }
                        }
                    }
                }
            });

            work_queue.await.unwrap();
            workers.join().await;
        }
        HttpWorkType::H1 => {
            let workers = spawn_workers(worker_threads.get(), n_connections, move || {
                let report_tx = report_tx.clone();
                let rx = rx.clone();
                let client = client.clone();
                async move {
                    let mut client_state = ClientStateHttp1::default();
                    while let Ok(()) = rx.recv().await {
                        let res = client.work_http1(&mut client_state).await;
                        let is_cancel = is_cancel_error(&res);
                        report_tx.send(res).unwrap();
                        if is_cancel {
                            break;
                        }
                    }
                }
            });

            work_queue.await.unwrap();
            workers.join().await;
        }
    };
}

/// n tasks by m workers limit to qps works in a second with latency correction
pub async fn work_with_qps_latency_correction(
    client: Arc<Client>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    query_limit: QueryLimit,
    n_tasks: usize,
    n_connections: usize,
    n_http2_parallel: usize,
    worker_threads: std::num::NonZeroUsize,
) {
    #[cfg(feature = "http3")]
    if matches!(client.work_type(), HttpWorkType::H3) {
        crate::client_h3::work_with_qps_latency_correction(
            client,
            report_tx,
            query_limit,
            n_tasks,
            n_connections,
            n_http2_parallel,
            worker_threads,
        )
        .await;
        return;
    }

    let (tx, rx) = kanal::unbounded();

    let work_queue = async move {
        match query_limit {
            QueryLimit::Qps(qps) => {
                let start = std::time::Instant::now();
                for i in 0..n_tasks {
                    compio::time::sleep_until(
                        start + std::time::Duration::from_secs_f64(i as f64 * 1f64 / qps),
                    )
                    .await;
                    let now = std::time::Instant::now();
                    tx.send(now)?;
                }
            }
            QueryLimit::Burst(duration, rate) => {
                let mut n = 0;
                // Handle via rate till n_tasks out of bound
                while n + rate < n_tasks {
                    compio::time::sleep(duration).await;
                    let now = std::time::Instant::now();
                    for _ in 0..rate {
                        tx.send(now)?;
                    }
                    n += rate;
                }
                // Handle the remaining tasks
                if n_tasks > n {
                    compio::time::sleep(duration).await;
                    let now = std::time::Instant::now();
                    for _ in 0..n_tasks - n {
                        tx.send(now)?;
                    }
                }
            }
        }

        // tx gone
        drop(tx);
        Ok::<(), kanal::SendError>(())
    };

    let rx = rx.to_async();
    match client.work_type() {
        #[cfg(feature = "http3")]
        HttpWorkType::H3 => unreachable!(),
        HttpWorkType::H2 => {
            let workers = spawn_workers(worker_threads.get(), n_connections, move || {
                let report_tx = report_tx.clone();
                let rx = rx.clone();
                let client = client.clone();
                async move {
                    let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
                    loop {
                        match setup_http2(&client, &mut rng).await {
                            Ok((connection_time, send_request)) => {
                                let futures = (0..n_http2_parallel)
                                    .map(|_| {
                                        let report_tx = report_tx.clone();
                                        let rx = rx.clone();
                                        let client = client.clone();
                                        let mut client_state = ClientStateHttp2 {
                                            rng: SeedableRng::from_rng(&mut rand::rng()),
                                            send_request: send_request.clone(),
                                        };
                                        compio::runtime::spawn(async move {
                                            while let Ok(start) = rx.recv().await {
                                                let (is_cancel, is_reconnect) = work_http2_once(
                                                    &client,
                                                    &mut client_state,
                                                    &report_tx,
                                                    connection_time,
                                                    Some(start),
                                                )
                                                .await;

                                                if is_cancel || is_reconnect {
                                                    return is_cancel;
                                                }
                                            }
                                            true
                                        })
                                    })
                                    .collect::<Vec<_>>();
                                let mut connection_gone = false;
                                for f in futures {
                                    match f.await {
                                        Ok(true) => {
                                            // All works done
                                            connection_gone = true;
                                        }
                                        Err(_) => {
                                            // Unexpected
                                            connection_gone = true;
                                        }
                                        _ => {}
                                    }
                                }
                                if connection_gone {
                                    return;
                                }
                            }
                            Err(err) => {
                                // Consume a task
                                if rx.recv().await.is_ok() {
                                    report_tx.send(Err(err)).unwrap();
                                } else {
                                    return;
                                }
                            }
                        }
                    }
                }
            });

            work_queue.await.unwrap();
            workers.join().await;
        }
        HttpWorkType::H1 => {
            let workers = spawn_workers(worker_threads.get(), n_connections, move || {
                let client = client.clone();
                let mut client_state = ClientStateHttp1::default();
                let report_tx = report_tx.clone();
                let rx = rx.clone();
                async move {
                    while let Ok(start) = rx.recv().await {
                        let mut res = client.work_http1(&mut client_state).await;
                        set_start_latency_correction(&mut res, start);
                        let is_cancel = is_cancel_error(&res);
                        report_tx.send(res).unwrap();
                        if is_cancel {
                            break;
                        }
                    }
                }
            });

            work_queue.await.unwrap();
            workers.join().await;
        }
    }
}

/// Run until dead_line by n workers
pub async fn work_until(
    client: Arc<Client>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    dead_line: std::time::Instant,
    n_connections: usize,
    n_http_parallel: usize,
    wait_ongoing_requests_after_deadline: bool,
    worker_threads: std::num::NonZeroUsize,
) {
    #[cfg(feature = "http3")]
    if matches!(client.work_type(), HttpWorkType::H3) {
        crate::client_h3::work_until(
            client,
            report_tx,
            dead_line,
            n_connections,
            n_http_parallel,
            wait_ongoing_requests_after_deadline,
            worker_threads,
        )
        .await;
        return;
    }

    match client.work_type() {
        #[cfg(feature = "http3")]
        HttpWorkType::H3 => unreachable!(),
        HttpWorkType::H2 => {
            let token = CancellationToken::new();

            let workers = spawn_workers(worker_threads.get(), n_connections, {
                let token = token.clone();
                move || {
                    let client = client.clone();
                    let report_tx = report_tx.clone();
                    let token = token.clone();
                    async move {
                        let token = token.clone();
                        // Keep trying to establish or re-establish connections up to the deadline
                        let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
                        loop {
                            match setup_http2(&client, &mut rng).await {
                                Ok((connection_time, send_request)) => {
                                    // Setup the parallel workers for each HTTP2 connection
                                    let futures = (0..n_http_parallel)
                                        .map(|_| {
                                            let client = client.clone();
                                            let report_tx = report_tx.clone();
                                            let mut client_state = ClientStateHttp2 {
                                                rng: SeedableRng::from_rng(&mut rand::rng()),
                                                send_request: send_request.clone(),
                                            };
                                            let token = token.clone();
                                            compio::runtime::spawn(async move {
                                                // This is where HTTP2 loops to make all the requests for a given client and worker
                                                loop {
                                                    let (is_cancel, is_reconnect) =
                                                        work_http2_once(
                                                            &client,
                                                            &mut client_state,
                                                            &report_tx,
                                                            connection_time,
                                                            None,
                                                        )
                                                        .await;

                                                    let is_cancel =
                                                        is_cancel || token.is_cancelled();
                                                    if is_cancel || is_reconnect {
                                                        break is_cancel;
                                                    }
                                                }
                                            })
                                        })
                                        .collect::<Vec<_>>();

                                    let mut connection_gone = false;
                                    for f in futures {
                                        match select(f, pin!(token.cancelled())).await {
                                            Either::Left((r, _)) => {
                                                match r {
                                                    Ok(true) => {
                                                        // All works done
                                                        connection_gone = true;
                                                    }
                                                    Err(_) => {
                                                        // Unexpected
                                                        connection_gone = true;
                                                    }
                                                    _ => {}
                                                }
                                            }
                                            Either::Right((_, f)) => {
                                                report_tx.send(Err(ClientError::Deadline)).unwrap();
                                                connection_gone = true;
                                                // Ongoing requests are waited
                                                let _ = f.await;
                                            }
                                        }
                                    }
                                    if connection_gone {
                                        return;
                                    }
                                }

                                Err(err) => {
                                    report_tx.send(Err(err)).unwrap();
                                    if token.is_cancelled() {
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
            });

            compio::time::sleep_until(dead_line).await;
            token.cancel();

            workers.join().await;
        }
        HttpWorkType::H1 => {
            let is_end = Arc::new(AtomicBool::new(false));
            let token = CancellationToken::new();

            let workers = spawn_workers(worker_threads.get(), n_connections, {
                let is_end = is_end.clone();
                let token = token.clone();
                move || {
                    let client = client.clone();
                    let report_tx = report_tx.clone();
                    let mut client_state = ClientStateHttp1::default();
                    let is_end = is_end.clone();
                    let token = token.clone();
                    async move {
                        let work = async {
                            loop {
                                let res = client.work_http1(&mut client_state).await;
                                let is_cancel = is_cancel_error(&res);
                                report_tx.send(res).unwrap();
                                if is_cancel || is_end.load(Relaxed) {
                                    break;
                                }
                            }
                        };
                        if token.run_until_cancelled(work).await.is_none() {
                            report_tx.send(Err(ClientError::Deadline)).unwrap();
                        }
                    }
                }
            });

            compio::time::sleep_until(dead_line).await;
            is_end.store(true, Relaxed);

            if !wait_ongoing_requests_after_deadline {
                token.cancel();
            }
            workers.join().await;
        }
    };
}

/// Run until dead_line by n workers limit to qps works in a second
#[allow(clippy::too_many_arguments)]
pub async fn work_until_with_qps(
    client: Arc<Client>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    query_limit: QueryLimit,
    start: std::time::Instant,
    dead_line: std::time::Instant,
    n_connections: usize,
    n_http2_parallel: usize,
    wait_ongoing_requests_after_deadline: bool,
    worker_threads: std::num::NonZeroUsize,
) {
    #[cfg(feature = "http3")]
    if matches!(client.work_type(), HttpWorkType::H3) {
        crate::client_h3::work_until_with_qps(
            client,
            report_tx,
            query_limit,
            start,
            dead_line,
            n_connections,
            n_http2_parallel,
            wait_ongoing_requests_after_deadline,
            worker_threads,
        )
        .await;
        return;
    }

    let rx = match query_limit {
        QueryLimit::Qps(qps) => {
            let (tx, rx) = kanal::unbounded::<()>();
            compio::runtime::spawn(async move {
                for i in 0.. {
                    if std::time::Instant::now() > dead_line {
                        break;
                    }
                    compio::time::sleep_until(
                        start + std::time::Duration::from_secs_f64(i as f64 * 1f64 / qps),
                    )
                    .await;
                    let _ = tx.send(());
                }
                // tx gone
            })
            .detach();
            rx
        }
        QueryLimit::Burst(duration, rate) => {
            let (tx, rx) = kanal::unbounded();
            compio::runtime::spawn(async move {
                // Handle via rate till deadline is reached
                for _ in 0.. {
                    if std::time::Instant::now() > dead_line {
                        break;
                    }

                    compio::time::sleep(duration).await;
                    for _ in 0..rate {
                        let _ = tx.send(());
                    }
                }
                // tx gone
            })
            .detach();
            rx
        }
    };

    let rx = rx.to_async();
    match client.work_type() {
        #[cfg(feature = "http3")]
        HttpWorkType::H3 => unreachable!(),
        HttpWorkType::H2 => {
            let token = CancellationToken::new();

            let workers = spawn_workers(worker_threads.get(), n_connections, {
                let token = token.clone();
                move || {
                    let client = client.clone();
                    let report_tx = report_tx.clone();
                    let rx = rx.clone();
                    let token = token.clone();
                    async move {
                        let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
                        loop {
                            match setup_http2(&client, &mut rng).await {
                                Ok((connection_time, send_request)) => {
                                    let futures = (0..n_http2_parallel)
                                        .map(|_| {
                                            let client = client.clone();
                                            let report_tx = report_tx.clone();
                                            let rx = rx.clone();
                                            let mut client_state = ClientStateHttp2 {
                                                rng: SeedableRng::from_rng(&mut rand::rng()),
                                                send_request: send_request.clone(),
                                            };
                                            let token = token.clone();
                                            compio::runtime::spawn(async move {
                                                while let Ok(()) = rx.recv().await {
                                                    let (is_cancel, is_reconnect) =
                                                        work_http2_once(
                                                            &client,
                                                            &mut client_state,
                                                            &report_tx,
                                                            connection_time,
                                                            None,
                                                        )
                                                        .await;

                                                    let is_cancel =
                                                        is_cancel || token.is_cancelled();
                                                    if is_cancel || is_reconnect {
                                                        return is_cancel;
                                                    }
                                                }
                                                true
                                            })
                                        })
                                        .collect::<Vec<_>>();
                                    let mut connection_gone = false;
                                    for f in futures {
                                        match select(f, pin!(token.cancelled())).await {
                                            Either::Left((r, _)) => {
                                                match r {
                                                    Ok(true) => {
                                                        // All works done
                                                        connection_gone = true;
                                                    }
                                                    Err(_) => {
                                                        // Unexpected
                                                        connection_gone = true;
                                                    }
                                                    _ => {}
                                                }
                                            }
                                            Either::Right((_, f)) => {
                                                report_tx.send(Err(ClientError::Deadline)).unwrap();
                                                connection_gone = true;
                                                // Ongoing requests are waited
                                                let _ = f.await;
                                            }
                                        }
                                    }
                                    if connection_gone {
                                        return;
                                    }
                                }
                                Err(err) => {
                                    // Consume a task
                                    if rx.recv().await.is_ok() {
                                        report_tx.send(Err(err)).unwrap();
                                    } else {
                                        return;
                                    }

                                    if token.is_cancelled() {
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }
            });

            compio::time::sleep_until(dead_line).await;
            token.cancel();

            workers.join().await;
        }
        HttpWorkType::H1 => {
            let is_end = Arc::new(AtomicBool::new(false));
            let token = CancellationToken::new();

            let workers = spawn_workers(worker_threads.get(), n_connections, {
                let is_end = is_end.clone();
                let token = token.clone();
                move || {
                    let client = client.clone();
                    let mut client_state = ClientStateHttp1::default();
                    let report_tx = report_tx.clone();
                    let rx = rx.clone();
                    let is_end = is_end.clone();
                    let token = token.clone();
                    async move {
                        let work = async {
                            while let Ok(()) = rx.recv().await {
                                let res = client.work_http1(&mut client_state).await;
                                let is_cancel = is_cancel_error(&res);
                                report_tx.send(res).unwrap();
                                if is_cancel || is_end.load(Relaxed) {
                                    break;
                                }
                            }
                        };
                        if token.run_until_cancelled(work).await.is_none() {
                            report_tx.send(Err(ClientError::Deadline)).unwrap();
                        }
                    }
                }
            });

            compio::time::sleep_until(dead_line).await;
            is_end.store(true, Relaxed);

            if !wait_ongoing_requests_after_deadline {
                token.cancel();
            }
            workers.join().await;
        }
    }
}

/// Run until dead_line by n workers limit to qps works in a second with latency correction
#[allow(clippy::too_many_arguments)]
pub async fn work_until_with_qps_latency_correction(
    client: Arc<Client>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    query_limit: QueryLimit,
    start: std::time::Instant,
    dead_line: std::time::Instant,
    n_connections: usize,
    n_http2_parallel: usize,
    wait_ongoing_requests_after_deadline: bool,
    worker_threads: std::num::NonZeroUsize,
) {
    #[cfg(feature = "http3")]
    if matches!(client.work_type(), HttpWorkType::H3) {
        crate::client_h3::work_until_with_qps_latency_correction(
            client,
            report_tx,
            query_limit,
            start,
            dead_line,
            n_connections,
            n_http2_parallel,
            wait_ongoing_requests_after_deadline,
            worker_threads,
        )
        .await;
        return;
    }

    let (tx, rx) = kanal::unbounded();
    match query_limit {
        QueryLimit::Qps(qps) => {
            compio::runtime::spawn(async move {
                for i in 0.. {
                    compio::time::sleep_until(
                        start + std::time::Duration::from_secs_f64(i as f64 * 1f64 / qps),
                    )
                    .await;
                    let now = std::time::Instant::now();
                    if now > dead_line {
                        break;
                    }
                    let _ = tx.send(now);
                }
                // tx gone
            })
            .detach();
        }
        QueryLimit::Burst(duration, rate) => {
            compio::runtime::spawn(async move {
                // Handle via rate till deadline is reached
                loop {
                    compio::time::sleep(duration).await;
                    let now = std::time::Instant::now();
                    if now > dead_line {
                        break;
                    }

                    for _ in 0..rate {
                        let _ = tx.send(now);
                    }
                }
                // tx gone
            })
            .detach();
        }
    };

    let rx = rx.to_async();
    match client.work_type() {
        #[cfg(feature = "http3")]
        HttpWorkType::H3 => unreachable!(),
        HttpWorkType::H2 => {
            let token = CancellationToken::new();

            let workers = spawn_workers(worker_threads.get(), n_connections, {
                let token = token.clone();
                move || {
                    let client = client.clone();
                    let report_tx = report_tx.clone();
                    let rx = rx.clone();
                    let token = token.clone();
                    async move {
                        let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
                        loop {
                            match setup_http2(&client, &mut rng).await {
                                Ok((connection_time, send_request)) => {
                                    let futures = (0..n_http2_parallel)
                                        .map(|_| {
                                            let client = client.clone();
                                            let report_tx = report_tx.clone();
                                            let rx = rx.clone();
                                            let mut client_state = ClientStateHttp2 {
                                                rng: SeedableRng::from_rng(&mut rand::rng()),
                                                send_request: send_request.clone(),
                                            };
                                            let token = token.clone();
                                            compio::runtime::spawn(async move {
                                                while let Ok(start) = rx.recv().await {
                                                    let (is_cancel, is_reconnect) =
                                                        work_http2_once(
                                                            &client,
                                                            &mut client_state,
                                                            &report_tx,
                                                            connection_time,
                                                            Some(start),
                                                        )
                                                        .await;
                                                    let is_cancel =
                                                        is_cancel || token.is_cancelled();
                                                    if is_cancel || is_reconnect {
                                                        return is_cancel;
                                                    }
                                                }
                                                true
                                            })
                                        })
                                        .collect::<Vec<_>>();
                                    let mut connection_gone = false;
                                    for f in futures {
                                        match select(f, pin!(token.cancelled())).await {
                                            Either::Left((r, _)) => {
                                                match r {
                                                    Ok(true) => {
                                                        // All works done
                                                        connection_gone = true;
                                                    }
                                                    Err(_) => {
                                                        // Unexpected
                                                        connection_gone = true;
                                                    }
                                                    _ => {}
                                                }
                                            }
                                            Either::Right((_, f)) => {
                                                report_tx.send(Err(ClientError::Deadline)).unwrap();
                                                connection_gone = true;
                                                // Ongoing requests are waited
                                                let _ = f.await;
                                            }
                                        }
                                    }
                                    if connection_gone {
                                        return;
                                    }
                                }

                                Err(err) => {
                                    if rx.recv().await.is_ok() {
                                        report_tx.send(Err(err)).unwrap();
                                    } else {
                                        return;
                                    }

                                    if token.is_cancelled() {
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }
            });

            compio::time::sleep_until(dead_line).await;
            token.cancel();

            workers.join().await;
        }
        HttpWorkType::H1 => {
            let is_end = Arc::new(AtomicBool::new(false));
            let token = CancellationToken::new();

            let workers = spawn_workers(worker_threads.get(), n_connections, {
                let is_end = is_end.clone();
                let token = token.clone();
                move || {
                    let client = client.clone();
                    let mut client_state = ClientStateHttp1::default();
                    let report_tx = report_tx.clone();
                    let rx = rx.clone();
                    let is_end = is_end.clone();
                    let token = token.clone();
                    async move {
                        let work = async {
                            while let Ok(start) = rx.recv().await {
                                let mut res = client.work_http1(&mut client_state).await;
                                set_start_latency_correction(&mut res, start);
                                let is_cancel = is_cancel_error(&res);
                                report_tx.send(res).unwrap();
                                if is_cancel || is_end.load(Relaxed) {
                                    break;
                                }
                            }
                        };
                        if token.run_until_cancelled(work).await.is_none() {
                            report_tx.send(Err(ClientError::Deadline)).unwrap();
                        }
                    }
                }
            });

            compio::time::sleep_until(dead_line).await;
            is_end.store(true, Relaxed);

            if !wait_ongoing_requests_after_deadline {
                token.cancel();
            }
            workers.join().await;
        }
    }
}

/// Optimized workers for `--no-tui` mode
pub mod fast {
    use std::{
        pin::pin,
        sync::{
            Arc,
            atomic::{AtomicBool, AtomicIsize, Ordering},
        },
    };

    use futures_util::future::select;
    use rand::SeedableRng;

    use crate::{
        client::{
            ClientError, ClientStateHttp1, ClientStateHttp2, HttpWorkType, is_cancel_error,
            is_hyper_error, set_connection_time, setup_http2,
        },
        pcg64si::Pcg64Si,
        result_data::ResultData,
        runtime::{CancellationToken, spawn_workers},
    };

    use super::Client;

    /// Run n tasks by m workers
    pub async fn work(
        client: Arc<Client>,
        report_tx: kanal::Sender<ResultData>,
        n_tasks: usize,
        n_connections: usize,
        n_http_parallel: usize,
        worker_threads: std::num::NonZeroUsize,
    ) {
        #[cfg(feature = "http3")]
        if matches!(client.work_type(), HttpWorkType::H3) {
            crate::client_h3::fast::work(
                client,
                report_tx,
                n_tasks,
                n_connections,
                n_http_parallel,
                worker_threads,
            )
            .await;
            return;
        }

        let counter = Arc::new(AtomicIsize::new(n_tasks as isize));
        let num_threads = worker_threads.get();
        let token = CancellationToken::new();

        let workers = match client.work_type() {
            #[cfg(feature = "http3")]
            HttpWorkType::H3 => unreachable!(),
            HttpWorkType::H2 => spawn_workers(num_threads, n_connections, {
                let token = token.clone();
                move || {
                    let report_tx = report_tx.clone();
                    let counter = counter.clone();
                    let client = client.clone();
                    let token = token.clone();
                    async move {
                        let mut has_err = false;
                        let mut result_data_err = ResultData::default();
                        let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
                        loop {
                            match setup_http2(&client, &mut rng).await {
                                Ok((connection_time, send_request)) => {
                                    let futures = (0..n_http_parallel)
                                        .map(|_| {
                                            let mut client_state = ClientStateHttp2 {
                                                rng: SeedableRng::from_rng(&mut rand::rng()),
                                                send_request: send_request.clone(),
                                            };
                                            let counter = counter.clone();
                                            let client = client.clone();
                                            let report_tx = report_tx.clone();
                                            let token = token.clone();
                                            compio::runtime::spawn(async move {
                                                let mut result_data = ResultData::default();

                                                let work = async {
                                                    while counter.fetch_sub(1, Ordering::Relaxed)
                                                        > 0
                                                    {
                                                        let mut res = client
                                                            .work_http2(&mut client_state)
                                                            .await;
                                                        let is_cancel = is_cancel_error(&res);
                                                        let is_reconnect = is_hyper_error(&res);
                                                        set_connection_time(
                                                            &mut res,
                                                            connection_time,
                                                        );

                                                        result_data.push(res);

                                                        if is_cancel || is_reconnect {
                                                            return is_cancel;
                                                        }
                                                    }
                                                    true
                                                };

                                                let is_cancel = token
                                                    .run_until_cancelled(work)
                                                    .await
                                                    .unwrap_or(true);

                                                report_tx.send(result_data).unwrap();
                                                is_cancel
                                            })
                                        })
                                        .collect::<Vec<_>>();

                                    let mut connection_gone = false;
                                    for f in futures {
                                        match f.await {
                                            Ok(true) => {
                                                // All works done
                                                connection_gone = true;
                                            }
                                            Err(_) => {
                                                // Unexpected
                                                connection_gone = true;
                                            }
                                            _ => {}
                                        }
                                    }

                                    if connection_gone {
                                        break;
                                    }
                                }
                                Err(err) => {
                                    if counter.fetch_sub(1, Ordering::Relaxed) > 0 {
                                        has_err = true;
                                        result_data_err.push(Err(err));
                                    } else {
                                        break;
                                    }
                                }
                            }
                        }
                        if has_err {
                            report_tx.send(result_data_err).unwrap();
                        }
                    }
                }
            }),
            HttpWorkType::H1 => spawn_workers(num_threads, n_connections, {
                let token = token.clone();
                move || {
                    let report_tx = report_tx.clone();
                    let counter = counter.clone();
                    let client = client.clone();
                    let token = token.clone();
                    async move {
                        let mut result_data = ResultData::default();

                        token
                            .run_until_cancelled(async {
                                let mut client_state = ClientStateHttp1::default();
                                while counter.fetch_sub(1, Ordering::Relaxed) > 0 {
                                    let res = client.work_http1(&mut client_state).await;
                                    let is_cancel = is_cancel_error(&res);
                                    result_data.push(res);
                                    if is_cancel {
                                        break;
                                    }
                                }
                            })
                            .await;
                        report_tx.send(result_data).unwrap();
                    }
                }
            }),
        };

        // Dropping the handle stops listening once all workers are done
        let _ctrl_c = compio::runtime::spawn(async move {
            compio::signal::ctrl_c().await.unwrap();
            token.cancel();
        });

        workers.join().await;
    }

    /// Run until dead_line by n workers
    pub async fn work_until(
        client: Arc<Client>,
        report_tx: kanal::Sender<ResultData>,
        dead_line: std::time::Instant,
        n_connections: usize,
        n_http_parallel: usize,
        wait_ongoing_requests_after_deadline: bool,
        worker_threads: std::num::NonZeroUsize,
    ) {
        #[cfg(feature = "http3")]
        if matches!(client.work_type(), HttpWorkType::H3) {
            crate::client_h3::fast::work_until(
                client,
                report_tx,
                dead_line,
                n_connections,
                n_http_parallel,
                wait_ongoing_requests_after_deadline,
                worker_threads,
            )
            .await;
            return;
        }

        let num_threads = worker_threads.get();

        let is_end = Arc::new(AtomicBool::new(false));
        let token = CancellationToken::new();
        let workers = match client.work_type() {
            #[cfg(feature = "http3")]
            HttpWorkType::H3 => unreachable!(),
            HttpWorkType::H2 => spawn_workers(num_threads, n_connections, {
                let token = token.clone();
                let is_end = is_end.clone();
                move || {
                    let report_tx = report_tx.clone();
                    let client = client.clone();
                    let token = token.clone();
                    let is_end = is_end.clone();
                    async move {
                        let mut has_err = false;
                        let mut result_data_err = ResultData::default();
                        let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
                        loop {
                            match setup_http2(&client, &mut rng).await {
                                Ok((connection_time, send_request)) => {
                                    let futures = (0..n_http_parallel)
                                        .map(|_| {
                                            let mut client_state = ClientStateHttp2 {
                                                rng: SeedableRng::from_rng(&mut rand::rng()),
                                                send_request: send_request.clone(),
                                            };
                                            let client = client.clone();
                                            let report_tx = report_tx.clone();
                                            let token = token.clone();
                                            let is_end = is_end.clone();
                                            compio::runtime::spawn(async move {
                                                let mut result_data = ResultData::default();

                                                let work = async {
                                                    loop {
                                                        let mut res = client
                                                            .work_http2(&mut client_state)
                                                            .await;
                                                        let is_cancel = is_cancel_error(&res)
                                                            || is_end.load(Ordering::Relaxed);
                                                        let is_reconnect = is_hyper_error(&res);
                                                        set_connection_time(
                                                            &mut res,
                                                            connection_time,
                                                        );

                                                        result_data.push(res);

                                                        if is_cancel || is_reconnect {
                                                            return is_cancel;
                                                        }
                                                    }
                                                };

                                                let is_cancel =
                                                    match token.run_until_cancelled(work).await {
                                                        Some(is_cancel) => is_cancel,
                                                        None => {
                                                            result_data
                                                                .push(Err(ClientError::Deadline));
                                                            true
                                                        }
                                                    };

                                                report_tx.send(result_data).unwrap();
                                                is_cancel
                                            })
                                        })
                                        .collect::<Vec<_>>();

                                    let mut connection_gone = false;
                                    for f in futures {
                                        match f.await {
                                            Ok(true) => {
                                                // All works done
                                                connection_gone = true;
                                            }
                                            Err(_) => {
                                                // Unexpected
                                                connection_gone = true;
                                            }
                                            _ => {}
                                        }
                                    }

                                    if connection_gone {
                                        break;
                                    }
                                }
                                Err(err) => {
                                    has_err = true;
                                    result_data_err.push(Err(err));
                                    if is_end.load(Ordering::Relaxed) {
                                        break;
                                    }
                                }
                            }
                        }
                        if has_err {
                            report_tx.send(result_data_err).unwrap();
                        }
                    }
                }
            }),
            HttpWorkType::H1 => spawn_workers(num_threads, n_connections, {
                let token = token.clone();
                let is_end = is_end.clone();
                move || {
                    let report_tx = report_tx.clone();
                    let is_end = is_end.clone();
                    let client = client.clone();
                    let token = token.clone();
                    async move {
                        let mut result_data = ResultData::default();

                        let work = async {
                            let mut client_state = ClientStateHttp1::default();
                            loop {
                                let res = client.work_http1(&mut client_state).await;
                                let is_cancel = is_cancel_error(&res);
                                result_data.push(res);
                                if is_cancel || is_end.load(Ordering::Relaxed) {
                                    break;
                                }
                            }
                        };

                        if token.run_until_cancelled(work).await.is_none() {
                            result_data.push(Err(ClientError::Deadline));
                        }
                        report_tx.send(result_data).unwrap();
                    }
                }
            }),
        };

        select(
            pin!(compio::time::sleep_until(dead_line)),
            pin!(compio::signal::ctrl_c()),
        )
        .await;

        is_end.store(true, Ordering::Relaxed);

        if !wait_ongoing_requests_after_deadline {
            token.cancel();
        }
        workers.join().await;
    }
}
