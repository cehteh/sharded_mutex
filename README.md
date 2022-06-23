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

This pool of mutexes per types comes with a cost. In the current implementation each pool
needs 256 bytes. Thus using ShardedMutex makes only sense for types when significantly more
than 256 instances are to be expected.

Same types may have different locking domains using type tags.

Provides pseudo atomic access for types that implement `Copy` and `PartialEq`.

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
