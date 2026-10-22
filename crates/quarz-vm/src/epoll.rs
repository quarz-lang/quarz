//! The reactor's poller on Linux: epoll used directly, with every
//! descriptor registered once, edge-triggered, for reading and writing.
//!
//! The `polling` crate (used elsewhere) is level-triggered and oneshot:
//! after each event the descriptor had to be armed again, and every wait
//! also re-armed a timerfd and its own notifier, about four system calls
//! besides the wait itself. Here a wait is one `epoll_wait`, with its
//! timeout in milliseconds (rounded up, so a timer never fires early).
//!
//! Edge-triggered events come only when a descriptor's state changes,
//! which is enough because a task waits only after its read, write or
//! accept found nothing to do (`WouldBlock`); an event that comes while
//! no task waits is dropped, and the next attempt succeeds or waits for
//! the next edge.

use std::io;
use std::os::fd::RawFd;
use std::time::Duration;

/// The key of the notifier's events (descriptors are non-negative).
const NOTIFY_KEY: u64 = u64::MAX;

/// What happened to a descriptor.
#[derive(Clone, Copy)]
pub struct Event {
    pub fd: RawFd,
    pub readable: bool,
    pub writable: bool,
    /// An error or a hang-up: whoever waits must try again to learn which.
    pub failed: bool,
}

pub struct Poller {
    epfd: RawFd,
    /// An eventfd that `notify` writes to, for helper threads to wake the
    /// run loop.
    notifier: RawFd,
}

// SAFETY: the descriptors are only used through system calls that are
// safe to issue from any thread.
unsafe impl Send for Poller {}
unsafe impl Sync for Poller {}

fn check(r: libc::c_int) -> io::Result<libc::c_int> {
    if r < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(r)
    }
}

impl Poller {
    pub fn new() -> io::Result<Poller> {
        // SAFETY: plain system calls; the descriptors returned are owned
        // by the poller and closed when it is dropped.
        unsafe {
            let epfd = check(libc::epoll_create1(libc::EPOLL_CLOEXEC))?;
            let notifier = match check(libc::eventfd(0, libc::EFD_CLOEXEC | libc::EFD_NONBLOCK)) {
                Ok(fd) => fd,
                Err(e) => {
                    libc::close(epfd);
                    return Err(e);
                }
            };
            let poller = Poller { epfd, notifier };
            poller.ctl(
                libc::EPOLL_CTL_ADD,
                notifier,
                NOTIFY_KEY,
                libc::EPOLLIN as u32,
            )?;
            Ok(poller)
        }
    }

    fn ctl(&self, op: libc::c_int, fd: RawFd, key: u64, events: u32) -> io::Result<()> {
        let mut ev = libc::epoll_event { events, u64: key };
        // SAFETY: `ev` lives across the call; epoll copies it.
        check(unsafe { libc::epoll_ctl(self.epfd, op, fd, &mut ev) })?;
        Ok(())
    }

    /// Watch `fd` for both directions, edge-triggered, until `delete`.
    pub fn add(&self, fd: RawFd) -> io::Result<()> {
        let events = (libc::EPOLLIN | libc::EPOLLOUT | libc::EPOLLRDHUP | libc::EPOLLET) as u32;
        self.ctl(libc::EPOLL_CTL_ADD, fd, fd as u64, events)
    }

    pub fn delete(&self, fd: RawFd) -> io::Result<()> {
        self.ctl(libc::EPOLL_CTL_DEL, fd, 0, 0)
    }

    /// Wake a `wait` in progress, or the next one (from any thread).
    pub fn notify(&self) -> io::Result<()> {
        let one: u64 = 1;
        // SAFETY: writes the 8 bytes of `one` to the eventfd.
        let r = unsafe { libc::write(self.notifier, (&one as *const u64).cast(), 8) };
        if r < 0 {
            let e = io::Error::last_os_error();
            // The counter is full: a wake-up is pending anyway.
            if e.kind() != io::ErrorKind::WouldBlock {
                return Err(e);
            }
        }
        Ok(())
    }

    /// Wait at most `timeout` (forever when `None`) and append what
    /// happened to `out`. A notification ends the wait without an event
    /// of its own.
    pub fn wait(&self, out: &mut Vec<Event>, timeout: Option<Duration>) -> io::Result<()> {
        const CAP: usize = 256;
        let mut buf = [libc::epoll_event { events: 0, u64: 0 }; CAP];
        let ms: libc::c_int = match timeout {
            None => -1,
            Some(t) => {
                // Rounded up: an early wake-up would find the timer not
                // yet due and wait again.
                let ms = t.as_nanos().div_ceil(1_000_000);
                ms.min(libc::c_int::MAX as u128) as libc::c_int
            }
        };
        // SAFETY: `buf` has room for `CAP` events.
        let n = unsafe { libc::epoll_wait(self.epfd, buf.as_mut_ptr(), CAP as libc::c_int, ms) };
        if n < 0 {
            let e = io::Error::last_os_error();
            return if e.kind() == io::ErrorKind::Interrupted {
                Ok(())
            } else {
                Err(e)
            };
        }
        for ev in &buf[..n as usize] {
            let key = ev.u64;
            let bits = ev.events;
            if key == NOTIFY_KEY {
                let mut count: u64 = 0;
                // SAFETY: reads the eventfd's 8-byte counter, resetting it.
                unsafe { libc::read(self.notifier, (&mut count as *mut u64).cast(), 8) };
                continue;
            }
            let failed = bits & (libc::EPOLLERR | libc::EPOLLHUP) as u32 != 0;
            out.push(Event {
                fd: key as RawFd,
                readable: bits & (libc::EPOLLIN | libc::EPOLLRDHUP) as u32 != 0,
                writable: bits & libc::EPOLLOUT as u32 != 0,
                failed,
            });
        }
        Ok(())
    }
}

impl Drop for Poller {
    fn drop(&mut self) {
        // SAFETY: the poller owns both descriptors.
        unsafe {
            libc::close(self.notifier);
            libc::close(self.epfd);
        }
    }
}
