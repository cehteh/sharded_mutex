#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]

use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::ops::Deref;
use std::ops::DerefMut;

#[doc(hidden)]
pub use assoc_static::*;
#[doc(hidden)]
pub use parking_lot;
use parking_lot::lock_api::RawMutex as RawMutexTrait;
use parking_lot::RawMutex;

/// Every type that is used within a ShardedMutex needs to implement some boilerplate
/// (assoc_static). For common non-generic standard types this is already done. For your own
/// types you need to implement this by placing `sharded_mutex!(YourType)` into your source.
/// When some std type is missing, please send me a note or a PR's. Types from external crates
/// which can't be implemented by 'sharded_mutex' or by yourself need to be wraped in a
/// newtype. The 'TAG' is required when you want to implement a sharded mutex over foreign
/// types that are not implemented in your crate. This can be any (non-generic) type your
/// crate defines, preferably you just make a zero-size struct just for this purpose.
///
/// **Example:**
/// ```
/// use sharded_mutex::*;
///
/// // user defined type
/// struct MyType(String);
///
/// // provide sharded mutexes for it
/// sharded_mutex!(MyType);
///
/// // use a tag create an independent locking domain
/// struct SomeTag;
/// sharded_mutex!(MyType, SomeTag);
/// ```
#[macro_export]
macro_rules! sharded_mutex {
    ($T:ty, $TAG:ty) => {
        $crate::assoc_static!(
            $TAG: $T,
            $crate::MutexPool = $crate::MutexPool([$crate::MUTEXRC_INIT; $crate::POOL_SIZE])
        );
    };
    ($T:ty) => {
        $crate::assoc_static!(
            $T,
            $crate::MutexPool = $crate::MutexPool([$crate::MUTEXRC_INIT; $crate::POOL_SIZE])
        );
    };
}

/// Wraps a 'T' that can only be accessed through global mutexes at zero memory overhead per object.
/// The optional 'TAG' is used to create locking domains which share locks.
#[derive(Debug)]
#[repr(transparent)]
pub struct ShardedMutex<T, TAG = ()>(UnsafeCell<T>, PhantomData<TAG>)
where
    T: AssocStatic<MutexPool, TAG>;

// SAFETY: Access to the UnsafeCell is protected by the mutex.
unsafe impl<T, TAG> Sync for ShardedMutex<T, TAG> where T: Send + AssocStatic<MutexPool, TAG> {}
unsafe impl<T, TAG> Send for ShardedMutex<T, TAG> where T: Send + AssocStatic<MutexPool, TAG> {}

/// Only exported for macro use
// NOTE: must be less than 256, We use u8 as refcount below
#[doc(hidden)]
pub const POOL_SIZE: usize = 127;

/// Mutex with a reference count. This are not recursive mutexes!
/// Only exported for macro use
#[doc(hidden)]
pub struct RawMutexRc(RawMutex, UnsafeCell<u8>);

/// Only exported for macro use
#[doc(hidden)]
#[allow(clippy::declare_interior_mutable_const)] // This is exactly needed here
pub const MUTEXRC_INIT: RawMutexRc = RawMutexRc(RawMutex::INIT, UnsafeCell::new(0));

// SAFETY: Access to the UnsafeCell is protected by the mutex.
unsafe impl Sync for RawMutexRc {}
unsafe impl Send for RawMutexRc {}

impl RawMutexRc {
    /// Lock the Mutex.
    #[inline]
    fn lock(&self) {
        self.0.lock();
    }

    /// Tries to lock the Mutex.
    #[inline]
    fn try_lock(&self) -> bool {
        self.0.try_lock()
    }

    /// Increments the reference count. The mutex must be locked already.
    ///
    /// SAFETY: The mutex must be locked in the current context
    #[inline]
    unsafe fn again(&self) {
        *self.1.get() += 1;
    }

    /// Decrements refcount when it is greater than zero else unlocks the mutex.
    ///
    /// SAFETY: The mutex must be locked in the current context
    #[inline]
    unsafe fn unlock(&self) {
        if *self.1.get() == 0 {
            self.0.unlock()
        } else {
            *self.1.get() -= 1;
        }
    }
}

#[doc(hidden)]
/// A Pool of Mutexes, should be treated opaque and never constructed, only exported because
/// the macro and AssocStatic signatures need it.
#[repr(align(128))] // cache line aligned
pub struct MutexPool(pub [RawMutexRc; POOL_SIZE]);

impl<T, TAG> ShardedMutex<T, TAG>
where
    T: AssocStatic<MutexPool, TAG>,
{
    fn get_mutex(&self) -> &'static RawMutexRc {
        unsafe {
            // SAFETY: modulo constrains the length
            <T as AssocStatic<MutexPool, TAG>>::get_static()
                .0
                .get_unchecked(self as *const Self as usize % POOL_SIZE)
        }
    }

    /// Create a new ShardedMutex from the given value.
    pub fn new(value: T) -> Self {
        ShardedMutex(UnsafeCell::new(value), PhantomData)
    }

    /// Acquire a global sharded lock guard with unlock on drop semantics
    ///
    /// **SAFETY:** The current thread must not hold any sharded locks of the same type/domain
    /// as this will deadlock
    pub fn lock(&self) -> ShardedMutexGuard<T, TAG> {
        self.get_mutex().lock();
        ShardedMutexGuard(self)
    }

    /// Tries to acquire a global sharded lock guard with unlock on drop semantics
    pub fn try_lock(&self) -> Option<ShardedMutexGuard<T, TAG>> {
        self.get_mutex().try_lock().then(|| ShardedMutexGuard(self))
    }

    /// Acquire a global sharded locks guard on multiple objects passed as array of references.
    /// Returns an array `[ShardedMutexGuard; N]` reflecting the input arguments.
    /// The array of references should be reasonably small and must be smaller than 257.
    ///
    /// **SAFETY:** The current thread must not hold any sharded locks of the same type/domain
    /// as this will deadlock
    pub fn multi_lock<const N: usize>(objects: [&Self; N]) -> [ShardedMutexGuard<T, TAG>; N] {
        // TODO: compiletime check
        assert!(N <= u8::MAX as usize);

        // get a list of all required locks and sort them by address. This ensure consistent
        // locking order and will never deadlock (as long the current thread doesn't already
        // hold a lock)
        let mut locks = objects.map(|o| o.get_mutex());
        locks.sort_by(|a, b| {
            (*a as *const RawMutexRc as usize).cmp(&(*b as *const RawMutexRc as usize))
        });

        // lock in order with consecutive same locks only incrementing the reference count
        for i in 0..locks.len() {
            // SAFETY: we iterate to .len()
            unsafe {
                if i == 0
                    || *locks.get_unchecked(i - 1) as *const RawMutexRc
                        != *locks.get_unchecked(i) as *const RawMutexRc
                {
                    locks.get_unchecked(i).lock();
                } else {
                    locks.get_unchecked(i).again();
                }
            }
        }

        // create mutex guards for each
        objects.map(|o| ShardedMutexGuard(o))
    }

    /// Try to acquire a global sharded locks guard on multiple objects passed as array of
    /// references. Returns an optional array `Some([ShardedMutexGuard; N])` reflecting the input
    /// arguments when the locks could be obtained and `None` when locking failed.
    /// The array of references should be reasonably small and must be smaller than 257.
    pub fn try_multi_lock<const N: usize>(
        objects: [&Self; N],
    ) -> Option<[ShardedMutexGuard<T, TAG>; N]> {
        // TODO: compiletime check
        assert!(N <= u8::MAX as usize);

        // get a list of all required locks and sort them by address. This ensure consistent
        // locking order and will never deadlock (as long the current thread doesn't already
        // hold a lock)
        let mut locks = objects.map(|o| o.get_mutex());
        locks.sort_by(|a, b| {
            (*a as *const RawMutexRc as usize).cmp(&(*b as *const RawMutexRc as usize))
        });

        // lock in order with consecutive same locks only incrementing the reference count
        for i in 0..locks.len() {
            // SAFETY: we iterate to .len()
            unsafe {
                if i == 0
                    || *locks.get_unchecked(i - 1) as *const RawMutexRc
                        != *locks.get_unchecked(i) as *const RawMutexRc
                {
                    if !locks.get_unchecked(i).try_lock() {
                        // unlock all already obtained locks and bail out
                        for j in 0..i {
                            locks.get_unchecked(j).unlock();
                        }
                        return None;
                    }
                } else {
                    locks.get_unchecked(i).again();
                }
            }
        }

        // create mutex guards for each
        Some(objects.map(|o| ShardedMutexGuard(o)))
    }
}

/// Include this trait to get atomics like access for types that implement Copy and PartialEq
pub trait PseudoAtomicOps<T, TAG> {
    /// Returns a copy of the value stored in `self`.
    fn load(&self) -> T;

    /// Stores `value` in `self`.
    fn store(&self, value: &T);

    /// Swaps the contents of `self` and `value`.
    fn swap(&self, value: &mut T);

    /// Compares the value stored in `self` with `current`, when these are equal sets `self`
    /// to `new` and returns `true`, otherwise `false``is returned.
    fn compare_and_set(&self, current: &T, new: &T) -> bool;
}

impl<T, TAG> PseudoAtomicOps<T, TAG> for ShardedMutex<T, TAG>
where
    T: AssocStatic<MutexPool, TAG> + Copy + std::cmp::PartialEq,
{
    fn load(&self) -> T {
        *self.lock()
    }

    fn store(&self, value: &T) {
        *self.lock() = *value
    }

    fn swap(&self, value: &mut T) {
        std::mem::swap(&mut *self.lock(), value)
    }

    fn compare_and_set(&self, current: &T, new: &T) -> bool {
        let mut guard = self.lock();
        if *guard == *current {
            *guard = *new;
            true
        } else {
            false
        }
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
            // SAFETY: the guard guarantees that the we have the lock
            self.0.get_mutex().unlock();
        }
    }
}

// The integer types and bool are only here for completeness, it is better to use
// atomic types instead sharded_mutex
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
sharded_mutex!(f32);
sharded_mutex!(f64);
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

    #[test]
    fn multi_lock() {
        let x = ShardedMutex::new(123);
        let y = ShardedMutex::new(234);
        let z = ShardedMutex::new(345);

        let mut guards = ShardedMutex::multi_lock([&x, &z, &y]);

        assert_eq!(*guards[0], 123);
        assert_eq!(*guards[1], 345);
        assert_eq!(*guards[2], 234);

        *guards[1] = 456;
        drop(guards);

        assert_eq!(*z.lock(), 456);

        // again, different order
        let guards = ShardedMutex::multi_lock([&z, &y, &x]);

        assert_eq!(*guards[0], 456);
        assert_eq!(*guards[1], 234);
        assert_eq!(*guards[2], 123);
    }

    #[test]
    fn try_multi_lock() {
        let x = ShardedMutex::new(123);
        let y = ShardedMutex::new(234);
        let z = ShardedMutex::new(345);

        let guards = ShardedMutex::multi_lock([&x, &z, &y]);
        assert!(ShardedMutex::try_multi_lock([&x, &z, &y]).is_none());

        drop(guards);

        // now we can lock again
        let guards = ShardedMutex::try_multi_lock([&z, &y, &x]);
        assert!(guards.is_some());
        assert_eq!(*guards.as_ref().unwrap()[0], 345);
        assert_eq!(*guards.as_ref().unwrap()[1], 234);
        assert_eq!(*guards.as_ref().unwrap()[2], 123);
    }

    #[test]
    fn pseudo_atomic_ops() {
        use crate::PseudoAtomicOps;
        let x = ShardedMutex::new(123);

        let loaded = x.load();
        assert_eq!(loaded, 123);

        x.store(&234);
        assert_eq!(x.load(), 234);

        let mut swapping = 345;
        x.swap(&mut swapping);
        assert_eq!(swapping, 234);
        assert_eq!(x.load(), 345);

        assert!(!x.compare_and_set(&123, &456));
        assert!(x.compare_and_set(&345, &456));
        assert_eq!(x.load(), 456);
    }
}
