use bytes::Buf;
use bytes::Bytes;
use compio::quic;
use core::sync::atomic::Ordering;
use futures_channel::oneshot;
use futures_util::future::{Either, select};
use http::Request;
use http_body_util::BodyExt;
use hyper::http;
use kanal::AsyncReceiver;
use std::net::SocketAddr;
use std::net::UdpSocket;
use std::pin::pin;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicIsize;
use std::time::Instant;

use url::Url;

type Http3Connection = h3::client::Connection<quic::Connection, Bytes>;
type Http3SendRequest = h3::client::SendRequest<quic::h3::OpenStreams, Bytes>;

pub type SendRequestHttp3 = (Http3Connection, Http3SendRequest);

// HTTP3-specific error types
#[derive(thiserror::Error, Debug)]
pub enum Http3Error {
    #[error("QUIC Client: {0}")]
    QuicClientConfig(#[from] quic::crypto::rustls::NoInitialCipherSuite),
    #[error("QUIC connect: {0}")]
    QuicConnect(#[from] quic::ConnectError),
    #[error("QUIC connection: {0}")]
    QuicConnection(#[from] quic::ConnectionError),
    #[error("Quic connection closed earlier than expected")]
    QuicDriverClosedEarly(#[from] oneshot::Canceled),
    #[error("HTTP3 connection: {0}")]
    H3Connection(#[from] h3::error::ConnectionError),
    #[error("HTTP3 Stream: {0}")]
    H3Stream(#[from] h3::error::StreamError),
}

use crate::client::QueryLimit;
use crate::client::{
    Client, ClientError, ConnectionTime, RequestResult, Stream, is_cancel_error,
    set_connection_time, set_start_latency_correction,
};
use crate::pcg64si::Pcg64Si;
use crate::result_data::ResultData;
use crate::runtime::{CancellationToken, Workers, spawn_workers};
use rand::SeedableRng;
use rand::prelude::Rng;

pub(crate) struct ClientStateHttp3 {
    pub(crate) rng: Pcg64Si,
    pub(crate) send_request: Http3SendRequest,
}

impl ClientStateHttp3 {
    fn new(send_request: Http3SendRequest) -> Self {
        Self {
            rng: SeedableRng::from_rng(&mut rand::rng()),
            send_request,
        }
    }
}

impl Client {
    pub(crate) async fn connect_http3<R: Rng>(
        &self,
        url: &Url,
        rng: &mut R,
    ) -> Result<(ConnectionTime, SendRequestHttp3), ClientError> {
        let start = std::time::Instant::now();
        let addr = self.dns.lookup(url, rng).await?;
        let dns_lookup = std::time::Instant::now();
        let stream =
            match compio::time::timeout(self.connect_timeout, self.quic_client(addr, url)).await {
                Ok(Ok(stream)) => stream,
                Ok(Err(err)) => return Err(err),
                Err(_) => return Err(ClientError::Timeout),
            };
        let send_request = stream.handshake_http3().await?;
        let dialup = std::time::Instant::now();
        Ok((
            ConnectionTime {
                dns_lookup: dns_lookup - start,
                dialup: dialup - start,
            },
            send_request,
        ))
    }

    fn quic_endpoint(&self, is_ipv6: bool) -> Result<quic::Endpoint, ClientError> {
        let local_socket = if is_ipv6 {
            UdpSocket::bind("[::]:0").expect("couldn't bind to address")
        } else {
            UdpSocket::bind("0.0.0.0:0").expect("couldn't bind to address")
        };
        // Enlarge UDP buffers as far as the OS allows to avoid packet loss at high rates.
        {
            let socket_ref = socket2::SockRef::from(&local_socket);
            let _ = socket_ref.set_recv_buffer_size(8 * 1024 * 1024);
            let _ = socket_ref.set_send_buffer_size(8 * 1024 * 1024);
        }
        let tls_config = self.rustls_configs.config(http::Version::HTTP_3).clone();
        let mut client_config = quic::ClientConfig::new(Arc::new(
            quic::crypto::rustls::QuicClientConfig::try_from(tls_config)
                .map_err(Http3Error::from)?,
        ));
        let mut transport_config = quic::TransportConfig::default();
        transport_config
            // Align flow-control windows with the HTTP/2 client (from nghttp2's default)
            .stream_receive_window(quic::VarInt::from_u32((1 << 30) - 1))
            .send_window((1 << 30) - 1)
            // QUIC datagrams are not used
            .datagram_receive_buffer_size(None);
        client_config.transport_config(Arc::new(transport_config));

        Ok(quic::Endpoint::new(
            compio::net::UdpSocket::from_std(local_socket)?,
            quic::EndpointConfig::default(),
            None,
            Some(client_config),
        )?)
    }

    pub(crate) async fn quic_client(
        &self,
        addr: (std::net::IpAddr, u16),
        url: &Url,
    ) -> Result<Stream, ClientError> {
        let client_endpoint = self.quic_endpoint(addr.0.is_ipv6())?;

        let remote_socket_address = SocketAddr::new(addr.0, addr.1);
        let server_name = url.host_str().ok_or(ClientError::HostNotFound)?;
        let conn = client_endpoint
            .connect(remote_socket_address, server_name, None)
            .map_err(Http3Error::from)?
            .await
            .map_err(Http3Error::from)?;
        Ok(Stream::Quic(conn))
    }

    pub(crate) async fn work_http3(
        &self,
        client_state: &mut ClientStateHttp3,
    ) -> Result<RequestResult, ClientError> {
        let do_req = async {
            let (_url, request, rng) = self.generate_request(&mut client_state.rng)?;
            let start = std::time::Instant::now();
            let connection_time: Option<ConnectionTime> = None;
            let mut first_byte: Option<std::time::Instant> = None;

            // if we implement http_body::Body on our H3 SendRequest, we can do some nice streaming stuff
            // with the response here. However as we don't really use the response we can get away
            // with not doing this for now
            let (head, mut req_body) = request.into_parts();
            let request = http::request::Request::from_parts(head, ());
            let mut stream = client_state
                .send_request
                .send_request(request)
                .await
                .map_err(Http3Error::from)?;
            // send the request body now
            if let Some(Ok(frame)) = req_body.frame().await
                && let Ok(data) = frame.into_data()
            {
                stream.send_data(data).await.map_err(Http3Error::from)?;
            }
            stream.finish().await.map_err(Http3Error::from)?;

            // now read the response headers
            let response = stream.recv_response().await.map_err(Http3Error::from)?;
            let (parts, _) = response.into_parts();
            let status = parts.status;
            // now read the response body
            let mut len_bytes = 0;
            while let Some(chunk) = stream.recv_data().await.map_err(Http3Error::from)? {
                if first_byte.is_none() {
                    first_byte = Some(std::time::Instant::now())
                }
                len_bytes += chunk.remaining();
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
}

impl Stream {
    async fn handshake_http3(self) -> Result<SendRequestHttp3, Http3Error> {
        let Stream::Quic(quic_conn) = self else {
            panic!("You cannot call http3 handshake on a non-quic stream");
        };
        // TODO add configuration settings to allow 'send_grease' etc.

        Ok(h3::client::new(quic_conn).await?)
    }
}

pub(crate) async fn send_debug_request_http3(
    h3_connection: Http3Connection,
    mut client_state: Http3SendRequest,
    request: Request<http_body_util::Full<Bytes>>,
) -> Result<http::Response<Bytes>, Http3Error> {
    // Prepare a channel to stop the driver thread
    let (shutdown_tx, shutdown_rx) = oneshot::channel();
    // Run the driver
    let http3_driver = spawn_http3_driver(h3_connection, shutdown_rx);

    let (head, mut req_body) = request.into_parts();
    let request = http::request::Request::from_parts(head, ());

    let mut stream = client_state.send_request(request).await?;
    if let Some(Ok(frame)) = req_body.frame().await
        && let Ok(data) = frame.into_data()
    {
        stream.send_data(data).await?;
    }

    stream.finish().await?;

    let response = stream.recv_response().await.unwrap_or_else(|err| {
        panic!("{}", err);
    });
    let mut body_bytes = bytes::BytesMut::new();

    while let Some(mut chunk) = stream.recv_data().await? {
        let bytes = chunk.copy_to_bytes(chunk.remaining());
        body_bytes.extend_from_slice(&bytes);
    }
    let body = body_bytes.freeze();
    let (parts, _) = response.into_parts();
    let _ = shutdown_tx.send(());
    let _ = http3_driver.await.unwrap();
    Ok(http::Response::from_parts(parts, body))
}

/**
 * Create `n_connections` parallel HTTP3 connections (on independent QUIC connections).
 * On each of those, run `n_http3_parallel` requests continuously until `deadline` is reached.
 */
pub(crate) async fn parallel_work_http3(
    n_connections: usize,
    n_http_parallel: usize,
    rx: Option<AsyncReceiver<Option<Instant>>>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    client: Arc<Client>,
    deadline: Option<std::time::Instant>,
    worker_threads: std::num::NonZeroUsize,
) -> Workers {
    let token = CancellationToken::new();

    let workers = spawn_workers(worker_threads.get(), n_connections, {
        let token = token.clone();
        move || {
            create_and_load_up_single_connection_http3(
                n_http_parallel,
                rx.clone(),
                report_tx.clone(),
                client.clone(),
                token.clone(),
            )
        }
    });

    if let Some(deadline) = deadline {
        compio::time::sleep_until(deadline).await;
        token.cancel();
    }

    workers
}

/**
 * For use in the 'slow' functions - send a report of every response in real time for display to the end-user.
 * The token is cancelled to shut down all the tasks.
 * Very similar to how http2 loops work, just that we explicitly spawn the HTTP3 connection driver.
 * When `rx` is `None`, requests are issued continuously until the token is cancelled.
 */
async fn create_and_load_up_single_connection_http3(
    n_http_parallel: usize,
    rx: Option<AsyncReceiver<Option<Instant>>>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    client: Arc<Client>,
    token: CancellationToken,
) {
    let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
    loop {
        // create a HTTP3 connection
        match setup_http3(&client, &mut rng).await {
            Ok((connection_time, (h3_connection, send_request))) => {
                let (shutdown_tx, shutdown_rx) = oneshot::channel();
                let http3_driver = spawn_http3_driver(h3_connection, shutdown_rx);
                let futures = (0..n_http_parallel)
                    .map(|_| {
                        let report_tx = report_tx.clone();
                        let rx = rx.clone();
                        let client = client.clone();
                        let mut client_state = ClientStateHttp3::new(send_request.clone());
                        let token = token.clone();
                        compio::runtime::spawn(async move {
                            // This is where HTTP3 loops to make all the requests for a given client and worker
                            if let Some(rx) = rx {
                                while let Ok(start_time_option) = rx.recv().await {
                                    let (is_cancel, is_reconnect) = work_http3_once(
                                        &client,
                                        &mut client_state,
                                        &report_tx,
                                        connection_time,
                                        start_time_option,
                                    )
                                    .await;

                                    let is_cancel = is_cancel || token.is_cancelled();
                                    if is_cancel || is_reconnect {
                                        return is_cancel;
                                    }
                                }
                                true
                            } else {
                                loop {
                                    let (is_cancel, is_reconnect) = work_http3_once(
                                        &client,
                                        &mut client_state,
                                        &report_tx,
                                        connection_time,
                                        None,
                                    )
                                    .await;

                                    let is_cancel = is_cancel || token.is_cancelled();
                                    if is_cancel || is_reconnect {
                                        return is_cancel;
                                    }
                                }
                            }
                        })
                    })
                    .collect::<Vec<_>>();
                drop(send_request);

                // collect all the requests we have spawned, and end the process if/when the token says
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
                    // Try and politely shut down the HTTP3 connection
                    let _ = shutdown_tx.send(());
                    let _ = http3_driver.await;
                    return;
                }
            }
            Err(err) => {
                if token.is_cancelled() {
                    break;
                } else if let Some(rx) = &rx {
                    // Consume a task
                    if rx.recv().await.is_ok() {
                        report_tx.send(Err(err)).unwrap();
                    } else {
                        return;
                    }
                } else {
                    report_tx.send(Err(err)).unwrap();
                }
            }
        }
    }
}

/**
 * This is structured to work very similarly to the `setup_http2`
 * function in `client.rs`
 */
pub(crate) async fn setup_http3<R: Rng>(
    client: &Client,
    rng: &mut R,
) -> Result<(ConnectionTime, SendRequestHttp3), ClientError> {
    let url = client.request_generator.url_generator.generate(rng)?;
    // Whatever rng state, all urls should have the same authority
    let (connection_time, send_request) = client.connect_http3(&url, rng).await?;

    Ok((connection_time, send_request))
}

pub(crate) fn spawn_http3_driver(
    mut h3_connection: Http3Connection,
    shutdown_rx: oneshot::Receiver<()>,
) -> compio::runtime::JoinHandle<std::result::Result<(), Http3Error>> {
    compio::runtime::spawn(async move {
        // Drive the connection
        let drive = std::future::poll_fn(|cx| h3_connection.poll_close(cx));
        let closed = match select(pin!(drive), shutdown_rx).await {
            Either::Left((closed, _)) => closed,
            // Listen for shutdown condition
            Either::Right(_) => {
                // Initiate shutdown
                h3_connection.shutdown(0).await?;
                // Wait for ongoing work to complete
                std::future::poll_fn(|cx| h3_connection.poll_close(cx)).await
            }
        };
        if closed.is_h3_no_error() {
            Ok(())
        } else {
            Err(Http3Error::H3Connection(closed))
        }
    })
}

pub(crate) async fn work_http3_once(
    client: &Client,
    client_state: &mut ClientStateHttp3,
    report_tx: &kanal::Sender<Result<RequestResult, ClientError>>,
    connection_time: ConnectionTime,
    start_latency_correction: Option<Instant>,
) -> (bool, bool) {
    let mut res = client.work_http3(client_state).await;
    let is_cancel = is_cancel_error(&res);
    let is_reconnect = is_h3_error(&res);
    set_connection_time(&mut res, connection_time);
    if let Some(start_latency_correction) = start_latency_correction {
        set_start_latency_correction(&mut res, start_latency_correction);
    }
    report_tx.send(res).unwrap();
    (is_cancel, is_reconnect)
}

fn is_h3_error(res: &Result<RequestResult, ClientError>) -> bool {
    res.as_ref()
        .err()
        .map(|err| matches!(err, ClientError::Http3(_) | ClientError::Io(_)))
        .unwrap_or(false)
}

/**
 * 'Fast' implementation of HTTP3 load generation for a single connection.
 * If `n_tasks` is set, it will generate up to that many tasks.
 * Othrwise it will terminate when `is_end` becomes set to true.
 */
pub(crate) async fn http3_connection_fast_work_until(
    n_http_parallel: usize,
    report_tx: kanal::Sender<ResultData>,
    client: Arc<Client>,
    token: CancellationToken,
    counter: Option<Arc<AtomicIsize>>,
    is_end: Arc<AtomicBool>,
) {
    let is_counting_tasks = counter.is_some();
    let mut has_err = false;
    let mut result_data_err = ResultData::default();
    let mut rng: Pcg64Si = SeedableRng::from_rng(&mut rand::rng());
    loop {
        match setup_http3(&client, &mut rng).await {
            Ok((connection_time, (h3_connection, send_request))) => {
                let (shutdown_tx, shutdown_rx) = oneshot::channel();
                let http3_driver = spawn_http3_driver(h3_connection, shutdown_rx);
                let futures = (0..n_http_parallel)
                    .map(|_| {
                        let mut client_state = ClientStateHttp3::new(send_request.clone());
                        let client = client.clone();
                        let report_tx = report_tx.clone();
                        let token = token.clone();
                        let is_end = is_end.clone();
                        let counter = counter.clone();
                        compio::runtime::spawn(async move {
                            let mut result_data = ResultData::default();

                            let work = async {
                                loop {
                                    if is_counting_tasks
                                        && counter.as_ref().unwrap().fetch_sub(1, Ordering::Relaxed)
                                            <= 0
                                    {
                                        return true;
                                    }
                                    let mut res = client.work_http3(&mut client_state).await;
                                    let is_cancel =
                                        is_cancel_error(&res) || is_end.load(Ordering::Relaxed);
                                    let is_reconnect = is_h3_error(&res);
                                    set_connection_time(&mut res, connection_time);

                                    result_data.push(res);

                                    if is_cancel || is_reconnect {
                                        return is_cancel;
                                    }
                                }
                            };

                            let is_cancel = match token.run_until_cancelled(work).await {
                                Some(is_cancel) => is_cancel,
                                None => {
                                    result_data.push(Err(ClientError::Deadline));
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
                    let _ = shutdown_tx.send(());
                    let _ = http3_driver.await;
                    break;
                }
            }
            Err(err) => {
                has_err = true;
                result_data_err.push(Err(err));
                if is_end.load(Ordering::Relaxed)
                    || (is_counting_tasks
                        && counter.as_ref().unwrap().fetch_sub(1, Ordering::Relaxed) <= 0)
                {
                    break;
                }
            }
        }
    }
    if has_err {
        report_tx.send(result_data_err).unwrap();
    }
}

/// Work function for HTTP3 client that generates `n_tasks` tasks.
pub async fn work(
    client: Arc<Client>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    n_tasks: usize,
    n_connections: usize,
    n_http2_parallel: usize,
    worker_threads: std::num::NonZeroUsize,
) {
    let (tx, rx) = kanal::unbounded::<Option<Instant>>();
    let rx = rx.to_async();

    let n_tasks_emitter = async move {
        for _ in 0..n_tasks {
            tx.send(None)?
        }
        drop(tx);
        Ok::<(), kanal::SendError>(())
    };
    let workers = parallel_work_http3(
        n_connections,
        n_http2_parallel,
        Some(rx),
        report_tx,
        client,
        None,
        worker_threads,
    )
    .await;
    n_tasks_emitter.await.unwrap();
    workers.join().await;
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
    let (tx, rx) = kanal::unbounded::<Option<Instant>>();

    let work_queue = async move {
        match query_limit {
            QueryLimit::Qps(qps) => {
                let start = std::time::Instant::now();
                for i in 0..n_tasks {
                    compio::time::sleep_until(
                        start + std::time::Duration::from_secs_f64(i as f64 * 1f64 / qps),
                    )
                    .await;
                    tx.send(None)?;
                }
            }
            QueryLimit::Burst(duration, rate) => {
                let mut n = 0;
                // Handle via rate till n_tasks out of bound
                while n + rate < n_tasks {
                    compio::time::sleep(duration).await;
                    for _ in 0..rate {
                        tx.send(None)?;
                    }
                    n += rate;
                }
                // Handle the remaining tasks
                if n_tasks > n {
                    compio::time::sleep(duration).await;
                    for _ in 0..n_tasks - n {
                        tx.send(None)?;
                    }
                }
            }
        }
        // tx gone
        drop(tx);
        Ok::<(), kanal::SendError>(())
    };

    let rx = rx.to_async();
    let workers = parallel_work_http3(
        n_connections,
        n_http_parallel,
        Some(rx),
        report_tx,
        client,
        None,
        worker_threads,
    )
    .await;
    work_queue.await.unwrap();
    workers.join().await;
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
    let (tx, rx) = kanal::unbounded();

    let _work_queue = async move {
        match query_limit {
            QueryLimit::Qps(qps) => {
                let start = std::time::Instant::now();
                for i in 0..n_tasks {
                    compio::time::sleep_until(
                        start + std::time::Duration::from_secs_f64(i as f64 * 1f64 / qps),
                    )
                    .await;
                    let now = std::time::Instant::now();
                    tx.send(Some(now))?;
                }
            }
            QueryLimit::Burst(duration, rate) => {
                let mut n = 0;
                // Handle via rate till n_tasks out of bound
                while n + rate < n_tasks {
                    compio::time::sleep(duration).await;
                    let now = std::time::Instant::now();
                    for _ in 0..rate {
                        tx.send(Some(now))?;
                    }
                    n += rate;
                }
                // Handle the remaining tasks
                if n_tasks > n {
                    compio::time::sleep(duration).await;
                    let now = std::time::Instant::now();
                    for _ in 0..n_tasks - n {
                        tx.send(Some(now))?;
                    }
                }
            }
        }

        // tx gone
        drop(tx);
        Ok::<(), kanal::SendError>(())
    };

    let rx = rx.to_async();
    let workers = parallel_work_http3(
        n_connections,
        n_http2_parallel,
        Some(rx),
        report_tx,
        client,
        None,
        worker_threads,
    )
    .await;
    workers.join().await;
}

/// Run until dead_line by n workers
pub async fn work_until(
    client: Arc<Client>,
    report_tx: kanal::Sender<Result<RequestResult, ClientError>>,
    dead_line: std::time::Instant,
    n_connections: usize,
    n_http_parallel: usize,
    _wait_ongoing_requests_after_deadline: bool,
    worker_threads: std::num::NonZeroUsize,
) {
    let workers = parallel_work_http3(
        n_connections,
        n_http_parallel,
        None,
        report_tx.clone(),
        client.clone(),
        Some(dead_line),
        worker_threads,
    )
    .await;
    workers.join().await;
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
    _wait_ongoing_requests_after_deadline: bool,
    worker_threads: std::num::NonZeroUsize,
) {
    let rx = match query_limit {
        QueryLimit::Qps(qps) => {
            let (tx, rx) = kanal::unbounded::<Option<Instant>>();
            compio::runtime::spawn(async move {
                for i in 0.. {
                    if std::time::Instant::now() > dead_line {
                        break;
                    }
                    compio::time::sleep_until(
                        start + std::time::Duration::from_secs_f64(i as f64 * 1f64 / qps),
                    )
                    .await;
                    let _ = tx.send(None);
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
                        let _ = tx.send(None);
                    }
                }
                // tx gone
            })
            .detach();
            rx
        }
    };
    let rx = rx.to_async();
    let workers = parallel_work_http3(
        n_connections,
        n_http2_parallel,
        Some(rx),
        report_tx,
        client,
        Some(dead_line),
        worker_threads,
    )
    .await;
    workers.join().await;
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
    _wait_ongoing_requests_after_deadline: bool,
    worker_threads: std::num::NonZeroUsize,
) {
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
                    let _ = tx.send(Some(now));
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
                        let _ = tx.send(Some(now));
                    }
                }
                // tx gone
            })
            .detach();
        }
    };

    let rx = rx.to_async();
    let workers = parallel_work_http3(
        n_connections,
        n_http2_parallel,
        Some(rx),
        report_tx,
        client,
        Some(dead_line),
        worker_threads,
    )
    .await;
    workers.join().await;
}

pub mod fast {
    use std::{
        pin::pin,
        sync::{
            Arc,
            atomic::{AtomicBool, AtomicIsize, Ordering},
        },
    };

    use futures_util::future::select;

    use crate::{
        client::Client,
        client_h3::http3_connection_fast_work_until,
        result_data::ResultData,
        runtime::{CancellationToken, spawn_workers},
    };

    /// Run n tasks by m workers
    pub async fn work(
        client: Arc<Client>,
        report_tx: kanal::Sender<ResultData>,
        n_tasks: usize,
        n_connections: usize,
        n_http_parallel: usize,
        worker_threads: std::num::NonZeroUsize,
    ) {
        let counter = Arc::new(AtomicIsize::new(n_tasks as isize));
        let token = CancellationToken::new();
        // will let is_end just stay false permanently
        let is_end = Arc::new(AtomicBool::new(false));
        let workers = spawn_workers(worker_threads.get(), n_connections, {
            let token = token.clone();
            move || {
                http3_connection_fast_work_until(
                    n_http_parallel,
                    report_tx.clone(),
                    client.clone(),
                    token.clone(),
                    Some(counter.clone()),
                    is_end.clone(),
                )
            }
        });

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
        let is_end = Arc::new(AtomicBool::new(false));
        let token = CancellationToken::new();
        let workers = spawn_workers(worker_threads.get(), n_connections, {
            let token = token.clone();
            let is_end = is_end.clone();
            move || {
                http3_connection_fast_work_until(
                    n_http_parallel,
                    report_tx.clone(),
                    client.clone(),
                    token.clone(),
                    None,
                    is_end.clone(),
                )
            }
        });

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
