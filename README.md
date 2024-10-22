# `ShardedMutex`, atomic Everything

This library provides global locks for (pseudo-) atomic access to data without memory overhead
per object. Concurrency is improved by selecting a Mutex from a pool based on the Address of
the object to be locked.

There is one pool of mutexes per guarded type, thus it is possible to lock values of different
types at the same time.

* Being sharded, these Mutexes act still as global and non-recursive locks. One must not
  `lock()` another object while a lock on the same type/domain is already hold, otherwise deadlocks
  will happen. The `try_lock()` and `try_lock_for()` methods do not have this limitation but
  will fail when the lock is already hold.
* The `multi_lock()` methods allow to obtain locks on multiple objects of the same type at the same
  time.
* The `then_lock()` method implements hand-over-hand locking where the lock of a new object is
  obtained before an lock already hold is dropped.

Same types may have different locking domains using type tags.

Provides pseudo atomic access for types that implement `Copy` and `PartialEq`. These can never
deadlock because they are always leaf locks.

In debug builds a deadlock detector is active which will panic when one tries to lock objects
from the same type/domain while already holding a lock.

**Example usage:**
```
use sharded_mutex::ShardedMutex;

// create 2 values that need locking
let x = ShardedMutex::new(123);
let y = ShardedMutex::new(234);

// a single lock
assert_eq!(*x.lock(), 123);

// Multiple locks
let mut guards = ShardedMutex::multi_lock([&x, &y]);

assert_eq!(*guards[0], 123);
assert_eq!(*guards[1], 234);

// can write as well
*guards[1] = 456;

// unlocks
drop(guards);

// lock again
assert_eq!(*y.lock(), 456);

// Pseudo atomic access
use sharded_mutex::PseudoAtomicOps;

x.store(&234);
assert_eq!(x.load(), 234);

let mut swapping = 345;
x.swap(&mut swapping);
assert_eq!(swapping, 234);
assert_eq!(x.load(), 345);

assert!(!x.compare_and_set(&123, &456));
assert!(x.compare_and_set(&345, &456));
assert_eq!(x.load(), 456);
```


# Features

## Alignment

`ShardedMutex` using arrays of mutexes for locking objects. This would pack Mutexes for
unrelated objects pretty close together which in turn impacts performance because of false
cache sharing. To alleviate this problem the internal aligment of these mutexes can be
increased. The cost for this is a larger memory footprint.

### *`align_none`*

Packs Mutexes as tight as possible. Good for embedded systems that have only little caches or
none at all and memory is premium.

### *`align_narrow`*

This is the **default**, it places 8 Mutexes per cacheline which should be a good compromise
between space and performance.

### *`align_wide`*

Places 4 mutexes per cacheline, should improve performance even further. Probably only
necessary when it is proven that there is cache contention.

### *`align_cacheline`*

Places one mutex per cacheline. This should give the best performance without any
cache contention, on the cost of wasting a lot memory.


## Pool Sizes

Locking performs best when there is little contention on the mutexes. We do this by sharding
accesses over pools of mutexes. The size of these pools can be adjusted to the expected number
of threads that will access the mutexes concurrently. The pool sizes are powers of two minus
one (or even mersenne-primes) for spreading the load evenly over the mutexes.

### *`normal_pool_size`*

Mutex pools have 127 entries. This should be good enough for most applications. This is the
default.

### *`tiny_pool_size`*

Mutex pools have 7 entries. This serverly limits concurrency. Use it only when memory is
at premium (embedded) and only very few threads try to lock objects.

### *`small_pool_size`*

Mutex pools have 31 entries. This may limit concurrency. Use it only when memory is
at premium (embedded) or only few threads try to lock objects.

### *`big_pool_size`*

Mutex pools have 511 entries. To be used for highly concurrent systems with many cores
where hundreds of threads locking objects concurrently.

### *`huge_pool_size`*

Mutex pools have 8191 entries. To be used for massively concurrent systems with many cores
where hundreds to thousands of threads locking objects concurrently.
