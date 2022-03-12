#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]

use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::ops::Deref;
use std::ops::DerefMut;

pub use assoc_static::*;
pub use parking_lot;
use parking_lot::lock_api::RawMutex as RawMutexTrait;
use parking_lot::RawMutex;

/// Every type that shall be used within a ShardedMutex needs to implement some boilerplate
/// (assoc_static). For common non-generic standard types this is already done. For your own
/// types you need to implement this by placing `sharded_mutex!(YourType)` into your source.
/// When some std type is missing, please send me a note or a PR's. Types from external crates
/// which can't be implemented by 'sharded_mutex' or by yourself need to be wraped in a
/// newtype. The 'TAG' is required when you want to implement a sharded mutex over foreign
/// types that are not implemented in your crate. This can be any (non-generic) type your
/// crate defines, preferably you just make a zero-size struct just for this purpose.
#[macro_export]
macro_rules! sharded_mutex {
    ($T:ty, $TAG:ty) => {
        $crate::assoc_static!(
            $T,
            $TAG,
            $crate::MutexPool,
            $crate::MutexPool([$crate::parking_lot::lock_api::RawMutex::INIT; $crate::POOL_SIZE])
        );
    };
    ($T:ty) => {
        $crate::assoc_static!(
            $T,
            (),
            $crate::MutexPool,
            $crate::MutexPool([$crate::parking_lot::lock_api::RawMutex::INIT; $crate::POOL_SIZE])
        );
    };
}

/// Wraps a 'T' that can only be accessed through global mutexes at zero memory overhead per object.
#[derive(Debug)]
#[repr(transparent)]
pub struct ShardedMutex<T, TAG = ()>(UnsafeCell<T>, PhantomData<TAG>)
where
    T: AssocStatic<MutexPool, TAG>;

// SAFETY: Access to the UnsafeCell is protected by the mutex.
unsafe impl<T, TAG> Sync for ShardedMutex<T, TAG> where T: Send + AssocStatic<MutexPool, TAG> {}

// SAFETY: Access to the UnsafeCell is protected by the mutex.
unsafe impl<T, TAG> Send for ShardedMutex<T, TAG> where T: Send + AssocStatic<MutexPool, TAG> {}

/// Only exported for macro use
#[doc(hidden)]
pub const POOL_SIZE: usize = 127;

/// A Pool of Mutexes, should be treated opaque and never constructed, only exported because
/// the macro and AssocStatic signatures need it.
#[repr(align(128))] // cache line aligned
pub struct MutexPool(pub [RawMutex; POOL_SIZE]);

impl<T, TAG> ShardedMutex<T, TAG>
where
    T: AssocStatic<MutexPool, TAG>,
{
    fn get_mutex(&self) -> &'static RawMutex {
        &AssocStatic::<MutexPool, TAG>::from(
            // SAFETY: only used for getting the type, never dereferenced
            unsafe { &*self.0.get() },
        )
        .0[self as *const Self as usize % POOL_SIZE]
    }

    /// Create a new ShardedMutex from the given value.
    pub fn new(value: T) -> Self {
        ShardedMutex(UnsafeCell::new(value), PhantomData)
    }

    /// Acquire a global sharded lock guard with unlock on drop semantics
    pub fn lock(&self) -> ShardedMutexGuard<T, TAG> {
        self.get_mutex().lock();
        ShardedMutexGuard(self)
    }

    /// Acquire a global sharded lock guard with unlock on drop semantics
    pub fn try_lock(&self) -> Option<ShardedMutexGuard<T, TAG>> {
        self.get_mutex().try_lock().then(|| ShardedMutexGuard(self))
    }
}

/// The guard returned from locking a ShardedMutex. Dropping this will unlock the mutex.
/// Access to the underlying value is done by dereferencing this guard.
pub struct ShardedMutexGuard<'a, T, TAG>(&'a ShardedMutex<T, TAG>)
where
    T: AssocStatic<MutexPool, TAG>;

impl<T, TAG> Deref for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocStatic<MutexPool, TAG>,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &*self.0 .0.get()
        }
    }
}

impl<T, TAG> DerefMut for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocStatic<MutexPool, TAG>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &mut *self.0 .0.get()
        }
    }
}

impl<T, TAG> AsRef<T> for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocStatic<MutexPool, TAG>,
{
    fn as_ref(&self) -> &T {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &*self.0 .0.get()
        }
    }
}

impl<T, TAG> AsMut<T> for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocStatic<MutexPool, TAG>,
{
    fn as_mut(&mut self) -> &mut T {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &mut *self.0 .0.get()
        }
    }
}

impl<T, TAG> Drop for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocStatic<MutexPool, TAG>,
{
    fn drop(&mut self) {
        unsafe {
            // SAFETY: the guard gurantees that the we have the lock
            self.0.get_mutex().unlock();
        }
    }
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
