#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]

use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::ops::Deref;
use std::ops::DerefMut;

#[doc(hidden)]
pub use assoc_static::{assoc_static, AssocStatic};
#[cfg(debug_assertions)]
#[doc(hidden)]
pub use assoc_threadlocal::{assoc_threadlocal, AssocThreadLocal};
#[doc(hidden)]
pub use parking_lot;
use parking_lot::lock_api::RawMutex as RawMutexTrait;
use parking_lot::RawMutex;

/// Every type that is used within a `ShardedMutex` needs to implement some boilerplate
/// (`assoc_static!(T:TAG, MutexPool)`). For common non-generic standard types this is already
/// done. For your own types you need to implement this by placing `sharded_mutex!(YourType)`
/// into your source.  When some std type is missing, please send me a note or a PR's. Types
/// from external crates which can't be implemented by sharded mutex or by yourself need to
/// be wraped in a newtype. The 'TAG' is required when you want to implement a sharded mutex
/// over foreign types that are not implemented in your crate. This can be any (non-generic)
/// type your crate defines, preferably you just make a zero-size struct just for this
/// purpose.
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
/// sharded_mutex!(SomeTag:MyType);
/// ```
#[macro_export]
#[cfg(debug_assertions)]
macro_rules! sharded_mutex {
    ($TAG:ty : $T:ty) => {
        $crate::assoc_static!(
            $TAG: $T,
            $crate::MutexPool = $crate::MutexPool([$crate::MUTEXRC_INIT; $crate::POOL_SIZE])
        );
        $crate::assoc_threadlocal!($TAG: $T, LockCount = LockCount(0));
    };
    ($T:ty) => {
        $crate::assoc_static!(
            $T,
            $crate::MutexPool = $crate::MutexPool([$crate::MUTEXRC_INIT; $crate::POOL_SIZE])
        );
        $crate::assoc_threadlocal!($T, LockCount = LockCount(0));
    };
}

#[allow(missing_docs)]
#[macro_export]
#[cfg(not(debug_assertions))]
macro_rules! sharded_mutex {
    ($TAG:ty : $T:ty) => {
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

/// Used by the deadlock detector in debug builds. For each alive ShardedMutexGuard of a
/// type/domain a thread local counter is incremented and decremented when the guards are
/// destructed. Trying to lock the same type/domain again while this counter is not zero will
/// panic.
#[cfg(debug_assertions)]
#[doc(hidden)]
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct LockCount(pub usize);

/// The traits for the associated objects. In release builds only a MutexPool is associated,
/// for debug builds this includes a LockCount as well.
#[doc(hidden)]
#[cfg(debug_assertions)]
trait AssocObjects<TAG>:
    AssocStatic<MutexPool, TAG> + AssocThreadLocal<LockCount, TAG>
{
}

#[cfg(debug_assertions)]
impl<T, TAG> AssocObjects<TAG> for T where
    T: AssocStatic<MutexPool, TAG> + AssocThreadLocal<LockCount, TAG>
{
}

#[doc(hidden)]
#[cfg(not(debug_assertions))]
pub trait AssocObjects<TAG>: AssocStatic<MutexPool, TAG> {}
#[cfg(not(debug_assertions))]
impl<T, TAG> AssocObjects<TAG> for T where T: AssocStatic<MutexPool, TAG> {}

/// Only exported for macro use
// NOTE: must be less than 256, We use u8 as refcount below, we use our favorite mersenne prime to spread
// objects fairly uniformly on these mutexes.
#[doc(hidden)]
pub const POOL_SIZE: usize = 127;

/// Mutex with a reference count. This are not recursive mutexes!
/// Only exported for macro use
#[doc(hidden)]
#[cfg_attr(feature = "align_none", repr(align(1)))]
#[cfg_attr(feature = "align_narrow", repr(align(8)))]
#[cfg_attr(feature = "align_wide", repr(align(16)))]
#[cfg_attr(feature = "align_cacheline", repr(align(64)))]
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
            self.0.unlock();
        } else {
            *self.1.get() -= 1;
        }
    }
}

#[doc(hidden)]
/// A Pool of Mutexes, should be treated opaque and never constructed, only exported because
/// the macro and AssocStatic signatures need it.
#[repr(align(64))] // cache line aligned
pub struct MutexPool(pub [RawMutexRc; POOL_SIZE]);

#[allow(private_bounds)]
impl<T, TAG> ShardedMutex<T, TAG>
where
    T: AssocObjects<TAG>,
{
    fn get_mutex(&self) -> &'static RawMutexRc {
        unsafe {
            // SAFETY: modulo constrains the length
            <T as AssocStatic<MutexPool, TAG>>::get_static()
                .0
                .get_unchecked(self as *const Self as usize % POOL_SIZE)
        }
    }

    /// Create a new `ShardedMutex` from the given value.
    pub fn new(value: T) -> Self {
        ShardedMutex(UnsafeCell::new(value), PhantomData)
    }

    /// Create a new `ShardedMutex` from the given value and tag.
    pub fn new_with_tag(value: T, _: TAG) -> Self {
        ShardedMutex(UnsafeCell::new(value), PhantomData)
    }

    #[cfg(debug_assertions)]
    fn deadlock_check_before_locking() {
        assert_eq!(
            <T as AssocThreadLocal<LockCount, TAG>>::get_threadlocal(),
            LockCount(0),
            "already locked from the same thread"
        );
    }

    /// Acquire a global sharded lock guard with unlock on drop semantics
    ///
    /// **SAFETY:** The current thread must not hold any sharded locks of the same type/domain
    /// as this will deadlock
    pub fn lock(&self) -> ShardedMutexGuard<T, TAG> {
        #[cfg(debug_assertions)]
        Self::deadlock_check_before_locking();

        self.get_mutex().lock();
        ShardedMutexGuard::new(self)
    }

    /// Tries to acquire a global sharded lock guard with unlock on drop semantics
    pub fn try_lock(&self) -> Option<ShardedMutexGuard<T, TAG>> {
        self.get_mutex()
            .try_lock()
            .then(|| ShardedMutexGuard::new(self))
    }

    /// Acquire a global sharded locks guard on multiple objects passed as array of references.
    /// Returns an array `[ShardedMutexGuard; N]` reflecting the input arguments.
    ///
    /// The current thread must not hold any sharded locks of the same type/domain
    /// as this will deadlock. In debug builds this is asserted.
    ///
    /// The array of references should be reasonably small and must be smaller than 257.
    #[allow(private_bounds)]
    pub fn multi_lock<const N: usize>(objects: [&Self; N]) -> [ShardedMutexGuard<T, TAG>; N]
    where
        usize: LessOrEqual256<N>,
    {
        #[cfg(debug_assertions)]
        Self::deadlock_check_before_locking();

        // get a list of all required locks and sort them by address. This ensure consistent
        // locking order and will never deadlock (as long the current thread doesn't already
        // hold a lock)
        let mut locks = objects.map(ShardedMutex::get_mutex);
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
        objects.map(|o| ShardedMutexGuard::new(o))
    }

    /// Try to acquire a global sharded locks guard on multiple objects passed as array of
    /// references. Returns an optional array `Some([ShardedMutexGuard; N])` reflecting the input
    /// arguments when the locks could be obtained and `None` when locking failed.
    ///
    /// The array of references should be reasonably small and must be smaller than 257.
    #[allow(private_bounds)]
    pub fn try_multi_lock<const N: usize>(
        objects: [&Self; N],
    ) -> Option<[ShardedMutexGuard<T, TAG>; N]>
    where
        usize: LessOrEqual256<N>,
    {
        // get a list of all required locks and sort them by address. This ensure consistent
        // locking order and will never deadlock (as long the current thread doesn't already
        // hold a lock)
        let mut locks = objects.map(ShardedMutex::get_mutex);
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
        Some(objects.map(|o| ShardedMutexGuard::new(o)))
    }

    /// Returns a mutable reference to the contained value. Having self being a &mut ensures
    /// that we are the only user of the mutex, thus the reference can be obtained without
    /// locking.
    pub fn get_mut(&mut self) -> &mut T {
        &mut *self.0.get_mut()
    }

    /// Consumes the mutex and returns the inner data.
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

/// Include this trait to get atomics like access for types that implement `Copy` and `PartialEq`
pub trait PseudoAtomicOps<T, TAG> {
    /// Returns a copy of the value stored in `self`.
    fn load(&self) -> T;

    /// Stores `value` in `self`.
    fn store(&self, value: &T);

    /// Swaps the contents of `self` and `value`.
    fn swap(&self, value: &mut T);

    /// Compares the value stored in `self` with `current`, when these are equal sets `self`
    /// to `new` and returns `true`, otherwise `false` is returned.
    fn compare_and_set(&self, current: &T, new: &T) -> bool;
}

impl<T, TAG> PseudoAtomicOps<T, TAG> for ShardedMutex<T, TAG>
where
    T: AssocObjects<TAG> + Copy + std::cmp::PartialEq,
{
    fn load(&self) -> T {
        *self.lock()
    }

    fn store(&self, value: &T) {
        *self.lock() = *value;
    }

    fn swap(&self, value: &mut T) {
        std::mem::swap(&mut *self.lock(), value);
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

/// The guard returned from locking a `ShardedMutex`. Dropping this will unlock the mutex.
/// Access to the underlying value is done by dereferencing this guard.
#[allow(private_bounds)]
pub struct ShardedMutexGuard<'a, T, TAG>(&'a ShardedMutex<T, TAG>)
where
    T: AssocObjects<TAG>;

#[allow(private_bounds)]
impl<'a, T, TAG> ShardedMutexGuard<'a, T, TAG>
where
    T: AssocObjects<TAG>,
{
    fn new(mutex: &'a ShardedMutex<T, TAG>) -> ShardedMutexGuard<'a, T, TAG> {
        #[cfg(debug_assertions)]
        Self::deadlock_increment_lock_count();

        ShardedMutexGuard(mutex)
    }

    #[cfg(debug_assertions)]
    fn deadlock_increment_lock_count() {
        let LockCount(n) = <T as AssocThreadLocal<LockCount, TAG>>::get_threadlocal();
        <T as AssocThreadLocal<LockCount, TAG>>::set_threadlocal(LockCount(n + 1));
    }

    #[cfg(debug_assertions)]
    fn deadlock_decrement_lock_count() {
        let LockCount(n) = <T as AssocThreadLocal<LockCount, TAG>>::get_threadlocal();
        <T as AssocThreadLocal<LockCount, TAG>>::set_threadlocal(LockCount(n - 1));
    }
}

impl<T, TAG> Deref for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocObjects<TAG>,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            // SAFETY: the guard guarantees that the we own the object
            &*self.0.0.get()
        }
    }
}

impl<T, TAG> DerefMut for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocObjects<TAG>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &mut *self.0.0.get()
        }
    }
}

impl<T, TAG> AsRef<T> for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocObjects<TAG>,
{
    fn as_ref(&self) -> &T {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &*self.0.0.get()
        }
    }
}

impl<T, TAG> AsMut<T> for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocObjects<TAG>,
{
    fn as_mut(&mut self) -> &mut T {
        unsafe {
            // SAFETY: the guard gurantees that the we own the object
            &mut *self.0.0.get()
        }
    }
}

impl<T, TAG> Drop for ShardedMutexGuard<'_, T, TAG>
where
    T: AssocObjects<TAG>,
{
    fn drop(&mut self) {
        #[cfg(debug_assertions)]
        Self::deadlock_decrement_lock_count();

        unsafe {
            // SAFETY: the guard guarantees that the we have the lock
            self.0.get_mutex().unlock();
        }
    }
}

// A ugly workaround to compile-time check const generic bounds. Will eventually be replaced
// with something better when such is available in stable rust.
trait LessOrEqual256<const N: usize> {}
macro_rules! impl_less_or_equal_256 {
    ($($n:literal),*) => {
        $(
            impl LessOrEqual256<$n> for usize {}
        )*
    };
}
impl_less_or_equal_256![
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
    136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
    155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
    174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
    193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211,
    212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
    231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
    250, 251, 252, 253, 254, 255, 256
];

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
    #[cfg(debug_assertions)]
    #[should_panic(expected = "already locked from the same thread")]
    fn simple_deadlock() {
        let x = ShardedMutex::new(123);
        let _guard = x.lock();
        let _guard_deadlock = x.lock();
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
    #[cfg(debug_assertions)]
    #[should_panic(expected = "already locked from the same thread")]
    fn multi_deadlock() {
        let x = ShardedMutex::new(123);
        let y = ShardedMutex::new(234);
        let z = ShardedMutex::new(345);
        let _guards = ShardedMutex::multi_lock([&x, &z, &y]);
        let _guards_deadlock = ShardedMutex::multi_lock([&x, &z, &y]);
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

    // must fail to compile
    // #[test]
    // fn try_multi_lock_range() {
    //     let x = ShardedMutex::new(123);
    //
    //     let refs = [
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //         &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x, &x,
    //     ];
    //
    //     let _guards = ShardedMutex::multi_lock(refs);
    // }

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

    #[test]
    fn get_mut() {
        let mut x = ShardedMutex::new(123);
        *x.get_mut() = 234;
        assert_eq!(*x.get_mut(), 234);
    }

    #[test]
    fn into_inner() {
        let x = ShardedMutex::new(123);
        let v = x.into_inner();
        assert_eq!(v, 123);
    }
}
