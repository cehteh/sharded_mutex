use sharded_mutex::*;

#[test]
fn simple_i32() {
    let x = ShardedMutex::new(123);
    assert_eq!(*x.lock(), 123);

    let mut guard = x.lock();

    *guard = 234;
    drop(guard);

    assert_eq!(*x.lock(), 234);
}

#[test]
fn std_types_needs_tag() {
    struct TestTag;
    sharded_mutex!(Option<bool>, TestTag);

    let x = ShardedMutex::new(Some(true));
    assert_eq!(*x.lock(), Some(true));
}

#[test]
fn own_type1() {
    #[derive(Debug, PartialEq)]
    struct TestType;

    sharded_mutex!(TestType);

    let x = ShardedMutex::new(TestType);
    assert_eq!(*x.lock(), TestType);
}

#[test]
fn own_type2() {
    #[derive(Debug, PartialEq)]
    struct TestType(i32);

    sharded_mutex!(TestType);

    let x = ShardedMutex::new(TestType(123));
    assert_eq!(x.lock().0, 123);
}
