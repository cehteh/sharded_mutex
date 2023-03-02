# ShardedMutex, atomic Everything

This library provides global locks for (pseudo-) atomic access to data without memory overhead
per object. Concurrency is improved by selecting a Mutex from a pool based on the Address of
the object to be locked.

Even being sharded, these Mutexes act still as global and non-recursive locks. One must not
lock another object while a lock on the same type/domain is already hold, otherwise deadlocks
will happen.

There is one pool of mutexes per guarded type, thus it is possible to lock values of different
types at the same time. Further a 'multi_lock' API allows to obtain locks on multiple objects
of the same type at the same time.

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

ShardedMutex using arrays of 127 mutexes for locking objects. This would pack Mutexes for
unrelated objects pretty close together which in turn impacts performance because of false
cache sharing. To alleviate this problem the internal aligment of these mutexes can be
increased. The cost for this is a larger memory footprint.

## *align_none*

Packs Mutexes as tight as possible. Good for embedded systems that have only little caches or
none at all and memory is premium.

## *align_narrow*

This is the **default**, it places 8 Mutexes per cacheline which should be a good compromise
between space and performance.

## *align_wide*

Places 4 mutexes per cacheline, should improve performance even further. Probably only
necessary when its proven that there is cache contention.

## *align_cacheline*

Places one mutex per cacheline. This should give the best performance without any
cache contention, on the cost of wasting memory.
