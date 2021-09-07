//! Can be used to read and write to memory of another process.
//!
//! While this is safe for the process using this module, it is very possibly not for the affected
//! process.
//!
//! Note: From the `process_vm_readv` man page: Permission  to  read  from  or  write to another
//! process is governed by a ptrace access mode PTRACE_MODE_AT‐TACH_REALCREDS check; see
//! `ptrace(2)`.
use libc::c_void;
use nix::sys::uio::{process_vm_readv, process_vm_writev, IoVec, RemoteIoVec};
use nix::unistd::Pid;
use std::mem::size_of;
use std::mem::MaybeUninit;

/// This is relevant for process_load/store. We assume the platforms memcopy (used in
/// process_vm_read/write) copies chunks of data aligned by a fixed n<=ALG atomically. 
///
/// The *rationale* is that all reasonable platforms rather introduce _one_ conditional to check
/// wether byte-wise mem-access can be replaced by the platforms native access width, rather than
/// e.g. copying a u64 in a byte copy loop containing _eight_ conditionals. 
/// The process_vm_read linux impls i checked (arm64+x64) do use atomic chunks of 8B or 4B and thus
/// adhere to this rationale.
/// 
/// # Safety
///
/// In theory we often access bytes before and after the memory we own. This is in practice not an
/// immediate issue because:
///
/// Memory before: In the current vmsh blkdev implementation only virtq_used.idx and .avail_event
/// are accessed (`vm_virtio::Queue::{avail_idx, set_avail_event}`). Experiments show that this struct always begins aligned. Therefore we only access
/// memory owned by us and never memory before the virtq_used struct (which might be unowned). As
/// long as we have only one thread operating on this virtq, we are therefore safe. (in principle
/// this should apply to all/most virtio-blk impls)
///
/// Memory after: As virtq_used is big (>=NR_QUEUES*8+4(+2)) and begins aligned, it is reasonable
/// to assume that there has been added enough spacing to accomondate the 2 bytes out-of-bound
/// access caused by .avail_event accesses.
const ALG: usize = 8;

use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;
/// fuck
pub static W_BYTES: AtomicU64 = AtomicU64::new(0);
/// docs
pub static W_COUNT: AtomicU64 = AtomicU64::new(0);
/// fuck
pub static R_BYTES: AtomicU64 = AtomicU64::new(0);
/// docs
pub static R_COUNT: AtomicU64 = AtomicU64::new(0);

/// An Error Type.
#[derive(Debug)]
pub enum Error {
    /// process_vm_readv failed
    Rw(nix::Error),
    /// process_vm_readv read {} bytes when {} were expected
    ByteCount {
        /// ffs
        is: usize,
        /// nope
        should: usize,
    },
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Rw(e) => write!(f, "cannot read/write from remote process memory: {}", e),
            Error::ByteCount { is, should } => write!(
                f,
                "reading from remote process memory: {} bytes completed, {} bytes expected",
                is, should
            ),
        }
    }
}

/// # Safety
///
/// None. See safety chapter of `std::slice::from_raw_parts`.
pub unsafe fn any_as_bytes<T: Sized>(p: &T) -> &[u8] {
    std::slice::from_raw_parts((p as *const T) as *const u8, size_of::<T>())
}

/// atomically read from a virtual addr of the hypervisor
///
/// # Safety
///
/// see `remote_mem::ALG`
pub fn process_load<T: Sized + Copy>(pid: Pid, addr: *const c_void) -> Result<T, Error> {
    let len = size_of::<T>();
    assert!(len <= ALG);

    let offset = ALG - addr.align_offset(ALG); // alignment border <--offset--> addr <----> algn b.
    log::trace!("load offset {}", offset);
    let aligned = unsafe { addr.sub(offset) } as usize;
    assert!(addr as usize + len <= aligned + ALG); // value must not extend beyond this 8b aligned space

    assert_eq!(size_of::<MaybeUninit::<T>>(), size_of::<T>());
    let mut t_mem = MaybeUninit::<T>::uninit();
    let t_slice = unsafe { std::slice::from_raw_parts_mut(t_mem.as_mut_ptr() as *mut u8, len) };
    let data: [u8; ALG] = process_read(pid, aligned as *const c_void)?;
    log::trace!("load::read {:?}", data);
    t_slice.copy_from_slice(&data[offset .. (offset+len)]);
    log::trace!("load = {:?}", t_slice);
    let t: T = unsafe { t_mem.assume_init() };

    Ok(t)
}

/// read from a virtual addr of the hypervisor
pub fn process_read<T: Sized + Copy>(pid: Pid, addr: *const c_void) -> Result<T, Error> {
    let len = size_of::<T>();
    let mut t_mem = MaybeUninit::<T>::uninit();
    let t_slice = unsafe { std::slice::from_raw_parts_mut(t_mem.as_mut_ptr() as *mut u8, len) };
    let read = process_read_bytes(pid, t_slice, addr)?;
    if read != len {
        return Err(Error::ByteCount {
            is: read,
            should: len,
        });
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

    R_BYTES.fetch_add(len as u64, Ordering::Release);
    R_COUNT.fetch_add(1, Ordering::Release);
    std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
    let f = process_vm_readv(pid, local_iovec.as_slice(), remote_iovec.as_slice())
        .map_err(Error::Rw)?;
    std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
    Ok(f)
}

/// atomically write to a virtual addr of the hypervisor
///
/// # Safety
///
/// see `remote_mem::ALG`
pub fn process_store<T: Sized + Copy>(pid: Pid, addr: *mut c_void, val: &T) -> Result<(), Error> {
    let len = size_of::<T>();
    assert!(len <= ALG);

    let offset = ALG - addr.align_offset(ALG); // alignment border <--offset--> addr <----> algn b.
    log::trace!("store offset {}", offset);
    let aligned = unsafe { addr.sub(offset) } as usize;
    assert!(addr as usize + len <= aligned + ALG); // value must not extend beyond this 8b aligned space

    let mut data: [u8; ALG] = process_read(pid, aligned as *const c_void)?;
    log::trace!("store::read {:?}", data); // 0
    let val_b: &[u8] = unsafe { any_as_bytes(val) };
    data[offset .. (offset+len)].copy_from_slice(val_b);
    log::trace!("store({:?}) = {:?}", val_b, data); // 0
    process_write(pid, aligned as *mut c_void, &data)?;

    Ok(())
}

/// write to a virtual addr of the hypervisor
pub fn process_write<T: Sized + Copy>(pid: Pid, addr: *mut c_void, val: &T) -> Result<(), Error> {
    let len = size_of::<T>();
    // safe, because we won't need t_bytes for long
    let t_bytes = unsafe { any_as_bytes(val) };
    let written = process_write_bytes(pid, addr, t_bytes)?;
    if written != len {
        return Err(Error::ByteCount {
            is: written,
            should: len,
        });
    }

    Ok(())
}

/// write to a virtual addr of the hypervisor
pub fn process_write_bytes(pid: Pid, addr: *mut c_void, val: &[u8]) -> Result<usize, Error> {
    let len = val.len();
    let local_iovec = vec![IoVec::from_slice(val)];
    let remote_iovec = vec![RemoteIoVec {
        base: addr as usize,
        len,
    }];

    W_BYTES.fetch_add(len as u64, Ordering::Release);
    W_COUNT.fetch_add(1, Ordering::Release);
    std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
    let f = process_vm_writev(pid, local_iovec.as_slice(), remote_iovec.as_slice())
        .map_err(Error::Rw)?;
    std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
    Ok(f)
}
