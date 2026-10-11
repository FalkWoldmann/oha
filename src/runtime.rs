use std::{
    future::Future,
    io,
    pin::pin,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use compio::{
    driver::ProactorBuilder,
    runtime::{Runtime, RuntimeBuilder},
};
use event_listener::Event;
use futures_util::future::{Either, select};

fn build_runtime_with(taskrun: bool) -> io::Result<Runtime> {
    let mut proactor = ProactorBuilder::new();
    // Recommended io_uring setup for a thread-per-core runtime: completions are processed when
    // the thread enters the kernel anyway instead of interrupting it. Needs Linux 5.19.
    proactor.coop_taskrun(taskrun).taskrun_flag(taskrun);
    RuntimeBuilder::new().with_proactor(proactor).build()
}

/// Build a compio runtime for the current thread.
pub fn build_runtime() -> io::Result<Runtime> {
    let runtime = build_runtime_with(true)?;
    // compio silently falls back to epoll when io_uring setup fails, which is also what happens
    // when an older kernel rejects the taskrun flags. Give io_uring another try without them.
    if cfg!(target_os = "linux") && runtime.driver_type().is_polling() {
        build_runtime_with(false)
    } else {
        Ok(runtime)
    }
}

/// [`hyper::rt::Executor`] that spawns on the runtime of the current thread.
#[derive(Clone, Copy)]
pub struct LocalExecutor;

impl<F: Future + 'static> hyper::rt::Executor<F> for LocalExecutor {
    fn execute(&self, fut: F) {
        compio::runtime::spawn(fut).detach();
    }
}

#[derive(Default)]
struct TokenInner {
    cancelled: AtomicBool,
    event: Event,
}

/// A cancellation signal which can be shared across threads.
#[derive(Clone, Default)]
pub struct CancellationToken(Arc<TokenInner>);

impl CancellationToken {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn cancel(&self) {
        self.0.cancelled.store(true, Ordering::Release);
        self.0.event.notify(usize::MAX);
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.cancelled.load(Ordering::Acquire)
    }

    pub async fn cancelled(&self) {
        while !self.is_cancelled() {
            let listener = self.0.event.listen();
            // `cancel` may have run between the check and the registration
            if self.is_cancelled() {
                break;
            }
            listener.await;
        }
    }

    /// Run a future until it completes or the token is cancelled. Returns `None` if cancelled.
    pub async fn run_until_cancelled<F: Future>(&self, fut: F) -> Option<F::Output> {
        match select(pin!(fut), pin!(self.cancelled())).await {
            Either::Left((output, _)) => Some(output),
            Either::Right(_) => None,
        }
    }
}

/// Number of connections for each worker thread. Threads without a connection are omitted.
fn connections_per_thread(n_connections: usize, num_threads: usize) -> impl Iterator<Item = usize> {
    (0..num_threads).filter_map(move |i| {
        let num_connection = n_connections / num_threads
            + (if (n_connections % num_threads) > i {
                1
            } else {
                0
            });
        if num_connection > 0 {
            Some(num_connection)
        } else {
            None
        }
    })
}

/// Worker threads spawned by [`spawn_workers`].
pub struct Workers(Vec<futures_channel::oneshot::Receiver<()>>);

impl Workers {
    /// Wait for all worker threads to finish.
    pub async fn join(self) {
        for done in self.0 {
            let _ = done.await;
        }
    }
}

/// Spread `n_connections` over up to `num_threads` threads. Each thread drives its own runtime
/// and runs one future made by `connection` for each of its connections.
pub fn spawn_workers<F, Fut>(num_threads: usize, n_connections: usize, connection: F) -> Workers
where
    F: Fn() -> Fut + Clone + Send + 'static,
    Fut: Future<Output = ()> + 'static,
{
    Workers(
        connections_per_thread(n_connections, num_threads)
            .map(|num_connection| {
                let connection = connection.clone();
                let (done_tx, done_rx) = futures_channel::oneshot::channel();
                std::thread::spawn(move || {
                    let runtime = build_runtime().expect("failed to build a runtime");
                    runtime.block_on(async move {
                        let tasks = (0..num_connection)
                            .map(|_| compio::runtime::spawn(connection()))
                            .collect::<Vec<_>>();
                        for task in tasks {
                            let _ = task.await;
                        }
                    });
                    drop(runtime);
                    let _ = done_tx.send(());
                });
                done_rx
            })
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_connections_per_thread() {
        assert_eq!(
            connections_per_thread(10, 4).collect::<Vec<_>>(),
            [3, 3, 2, 2]
        );
        assert_eq!(connections_per_thread(2, 4).collect::<Vec<_>>(), [1, 1]);
        assert_eq!(connections_per_thread(0, 4).count(), 0);
    }

    #[test]
    fn test_cancellation_token_across_threads() {
        let token = CancellationToken::new();
        let workers = spawn_workers(2, 4, {
            let token = token.clone();
            move || {
                let token = token.clone();
                async move {
                    assert!(
                        token
                            .run_until_cancelled(std::future::pending::<()>())
                            .await
                            .is_none()
                    );
                }
            }
        });

        build_runtime().unwrap().block_on(async move {
            assert!(!token.is_cancelled());
            token.cancel();
            workers.join().await;
        });
    }
}
