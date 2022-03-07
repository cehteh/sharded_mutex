#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]

use std::cell::UnsafeCell;
use std::ops::Deref;
use std::ops::DerefMut;

use assoc_static::*;
use parking_lot::lock_api::RawMutex as RawMutexTrait;
use parking_lot::RawMutex;

/// Wraps a 'T' that can only be accessed through global mutexes at zero memory overhead per object.
#[derive(Debug)]
#[repr(transparent)]
pub struct ShardedMutex<T>(UnsafeCell<T>)
where
    ShardedMutex<T>: AssocStatic<Locks>;

/// Only public for macro use
#[doc(hidden)]
pub const POOL_SIZE: usize = 127;

/// Only internally used but the macros need public access to this
#[doc(hidden)]
#[repr(align(128))] // cache line aligned
pub struct Locks(pub [RawMutex; POOL_SIZE]);

impl<T> ShardedMutex<T>
where
    ShardedMutex<T>: AssocStatic<Locks>,
{
    fn get_mutex(&self) -> &'static RawMutex {
        &<Self as AssocStatic<Locks>>::get_static().0[self as *const Self as usize % POOL_SIZE]
    }

    /// Create a new ShardedMutex from the given value.
    pub fn new(value: T) -> Self {
        ShardedMutex(UnsafeCell::new(value))
    }

    /// Acquire a global sharded lock guard with unlock on drop semantics
    pub fn lock(&self) -> ShardedMutexGuard<T> {
        self.get_mutex().lock();
        ShardedMutexGuard(self)
    }

    /// Acquire a global sharded lock guard with unlock on drop semantics
    pub fn try_lock(&self) -> Option<ShardedMutexGuard<T>> {
        self.get_mutex().try_lock().then(|| ShardedMutexGuard(self))
    }
}

/// The guard returned from locking a ShardedMutex. Dropping this will unlock the mutex.
/// Access to the underlying value is done by dereferencing this guard.
pub struct ShardedMutexGuard<'a, T>(&'a ShardedMutex<T>)
where
    ShardedMutex<T>: AssocStatic<Locks>;

impl<T> Deref for ShardedMutexGuard<'_, T>
where
    ShardedMutex<T>: assoc_static::AssocStatic<Locks>,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &*self.0 .0.get()
        }
    }
}

impl<T> DerefMut for ShardedMutexGuard<'_, T>
where
    ShardedMutex<T>: assoc_static::AssocStatic<Locks>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &mut *self.0 .0.get()
        }
    }
}

impl<T> AsRef<T> for ShardedMutexGuard<'_, T>
where
    ShardedMutex<T>: assoc_static::AssocStatic<Locks>,
{
    fn as_ref(&self) -> &T {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &*self.0 .0.get()
        }
    }
}

impl<T> AsMut<T> for ShardedMutexGuard<'_, T>
where
    ShardedMutex<T>: assoc_static::AssocStatic<Locks>,
{
    fn as_mut(&mut self) -> &mut T {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &mut *self.0 .0.get()
        }
    }
}

impl<T> Drop for ShardedMutexGuard<'_, T>
where
    ShardedMutex<T>: assoc_static::AssocStatic<Locks>,
{
    fn drop(&mut self) {
        unsafe {
            // SAFETY: the guard gurantees that the we have the lock
            self.0.get_mutex().unlock();
        }
    }
}

/// Every type that shall be used within a ShardedMutex needs to implement some boilerplate
/// (assoc_static) for common standard types this is already done. For your own types you need
/// to implement this by placing `sharded_mutex!(YourType)` into your source.  When some std
/// type is missing, please send me a note or a PR's. Types from external crates which can't
/// be implemented by 'sharded_mutex' nor by yourself need to be wraped in a newtype.
#[macro_export]
macro_rules! sharded_mutex {
    ($T:ty) => {
        assoc_static::assoc_static!(
            ShardedMutex<$T>,
            Locks,
            Locks([parking_lot::lock_api::RawMutex::INIT; $crate::POOL_SIZE])
        );
    };
}

sharded_mutex!(bool);
sharded_mutex!(i8);
sharded_mutex!(u8);
sharded_mutex!(i16);
sharded_mutex!(u16);
sharded_mutex!(i32);
sharded_mutex!(u32);
sharded_mutex!(i64);
sharded_mutex!(u64);
sharded_mutex!(i128);
sharded_mutex!(u128);
sharded_mutex!(isize);
sharded_mutex!(usize);
sharded_mutex!(char);
sharded_mutex!(String);

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
