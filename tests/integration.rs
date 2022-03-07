use sharded_mutex::*;

#[test]
fn simple_lock() {
    let x = ShardedMutex::new(123);
    assert_eq!(*x.lock(), 123);

    let mut guard = x.lock();

    *guard = 234;
    drop(guard);

    assert_eq!(*x.lock(), 234);
}
