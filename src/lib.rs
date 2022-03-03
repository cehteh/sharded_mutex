#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]

use std::cell::UnsafeCell;
use std::ops::Deref;
use std::ops::DerefMut;

use parking_lot::lock_api::RawMutex as RawMutexTrait;
use parking_lot::RawMutex;

/// Wraps a 'T' that can only be accessed through global mutexes at zero memory overhead per object.
#[derive(Debug)]
#[repr(transparent)]
pub struct ShardedMutex<T>(UnsafeCell<T>);

impl<T> ShardedMutex<T> {
    /// Create a new ShardedMutex from the given value.
    pub fn new(value: T) -> Self {
        ShardedMutex(UnsafeCell::new(value))
    }

    // idea borrowed from crossbeam SeqLock
    fn get_mutex(&self) -> &'static RawMutex {
        const LEN: usize = 127;
        #[repr(align(128))] // cache line aligned
        struct Locks([RawMutex; LEN]);
        static LOCKS: Locks = Locks([RawMutex::INIT; LEN]);
        &LOCKS.0[self as *const ShardedMutex<T> as usize % LEN]
    }

    /// Acquire a global sharded lock guard with unlock on drop semantics
    pub fn lock(&self) -> ShardedMutexGuard<T> {
        self.get_mutex().lock();
        ShardedMutexGuard(&self)
    }

    /// Acquire a global sharded lock guard with unlock on drop semantics
    pub fn try_lock(&self) -> Option<ShardedMutexGuard<T>> {
        self.get_mutex()
            .try_lock()
            .then(|| ShardedMutexGuard(&self))
    }
}

/// The guard returned from locking a ShardedMutex. Dropping this will unlock the mutex.
/// Access to the underlying value is done by dereferencing this guard.
pub struct ShardedMutexGuard<'a, T>(&'a ShardedMutex<T>);

impl<T> Deref for ShardedMutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &*self.0 .0.get()
        }
    }
}

impl<T> DerefMut for ShardedMutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &mut *self.0 .0.get()
        }
    }
}

impl<T> Drop for ShardedMutexGuard<'_, T> {
    fn drop(&mut self) {
        unsafe {
            // SAFETY: the guard gurantees that the we have the lock
            self.0.get_mutex().unlock();
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ShardedMutex;

    #[test]
    fn smoke() {
        let x = ShardedMutex::new(123);
        assert_eq!(*x.lock(), 123);
    }

    #[test]
    fn simple_lock() {
        let x = ShardedMutex::new(123);
        assert_eq!(*x.lock(), 123);

        let mut guard = x.lock();

        *guard = 234;
        drop(guard);

        assert_eq!(*x.lock(), 234);
    }
}
