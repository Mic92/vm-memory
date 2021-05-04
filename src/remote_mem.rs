
use libc::{c_int, c_void};
use nix::sys::uio::{process_vm_readv, process_vm_writev, IoVec, RemoteIoVec};
use nix::unistd::Pid;
use std::ffi::OsStr;
use std::marker::PhantomData;
use std::mem::size_of;
use std::mem::MaybeUninit;
use std::os::unix::io::AsRawFd;
use std::os::unix::prelude::RawFd;
use std::sync::{Arc, Mutex, RwLock, RwLockWriteGuard};

/// why must i document this?
#[derive(Debug)]
pub enum Error {
    /// process_vm_readv failed
    Rw(nix::Error),
    /// process_vm_readv read {} bytes when {} were expected
    ByteCount{
        /// ffs
        is: usize, 
        /// nope
        should: usize
    },
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Rw(e) => write!(f, "cannot read/write from remote process memory: {}", e),
            Error::ByteCount{is, should} => write!(f, "reading from remote process memory: {} bytes completed, {} bytes expected", is, should),
        }
    }
}

/// # Safety
///
/// None. See safety chapter of `std::slice::from_raw_parts`.
pub unsafe fn any_as_bytes<T: Sized>(p: &T) -> &[u8] {
    std::slice::from_raw_parts((p as *const T) as *const u8, size_of::<T>())
}


/// read from a virtual addr of the hypervisor
pub fn process_read<T: Sized + Copy>(pid: Pid, addr: *const c_void) -> Result<T, Error> {
    let len = size_of::<T>();
    let mut t_mem = MaybeUninit::<T>::uninit();
    let t_slice = unsafe { std::slice::from_raw_parts_mut(t_mem.as_mut_ptr() as *mut u8, len) };
    let read = process_read_bytes(pid, t_slice, addr)?;
    if read != len {
        return Err(Error::ByteCount{is: read, should: len});
    }
    let t: T = unsafe { t_mem.assume_init() };
    Ok(t)
}

/// read from a virtual addr of the hypervisor
pub fn process_read_bytes(pid: Pid, buf: &mut [u8], addr: *const c_void) -> Result<usize, Error> {
    let len = buf.len();
    let local_iovec = vec![IoVec::from_mut_slice(buf)];
    let remote_iovec = vec![RemoteIoVec {
        base: addr as usize,
        len,
    }];

    let f =
        process_vm_readv(pid, local_iovec.as_slice(), remote_iovec.as_slice()).map_err(Error::Rw)?
    ;
    Ok(f)
}

/// write to a virtual addr of the hypervisor
pub fn process_write<T: Sized + Copy>(pid: Pid, addr: *mut c_void, val: &T) -> Result<(), Error> {
    let len = size_of::<T>();
    // safe, because we won't need t_bytes for long
    let t_bytes = unsafe { any_as_bytes(val) };

    let local_iovec = vec![IoVec::from_slice(t_bytes)];
    let remote_iovec = vec![RemoteIoVec {
        base: addr as usize,
        len,
    }];

    let f = 
        process_vm_writev(pid, local_iovec.as_slice(), remote_iovec.as_slice()).map_err(Error::Rw)?
    ;
    if f != len {
        return Err(Error::ByteCount{is: f, should: len});
    }

    Ok(())
}

/// write to a virtual addr of the hypervisor TODO
pub fn process_write_bytes(pid: Pid, addr: *mut c_void, val: &[u8]) -> Result<usize, Error> {
    let len = val.len();
    //let len = size_of::<T>();
    // safe, because we won't need t_bytes for long
    //let t_bytes = unsafe { any_as_bytes(val) };

    let local_iovec = vec![IoVec::from_slice(val)];
    let remote_iovec = vec![RemoteIoVec {
        base: addr as usize,
        len,
    }];

    let f = 
        process_vm_writev(pid, local_iovec.as_slice(), remote_iovec.as_slice()).map_err(Error::Rw)?
    ;
    Ok(f)
}

