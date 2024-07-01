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

struct TestTag;
sharded_mutex!(TestTag: Option<bool>);

#[test]
fn std_types_needs_tag() {
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

#[test]
fn distinct_tags() {
    #[derive(Debug, PartialEq)]
    struct TestType(i32);

    // Create a tagged versions each providing their own locking domains
    struct MyTag1;
    sharded_mutex!(MyTag1: TestType);
    struct MyTag2;
    sharded_mutex!(MyTag2: TestType);

    // need an explicit tag
    let x: ShardedMutex<_, MyTag1> = ShardedMutex::new(TestType(123));
    assert_eq!(x.lock().0, 123);
    let y: ShardedMutex<_, MyTag2> = ShardedMutex::new(TestType(234));
    assert_eq!(y.lock().0, 234);
}

#[test]
fn distinct_with_tags() {
    #[derive(Debug, PartialEq)]
    struct TestType(i32);

    // Create a tagged versions each providing their own locking domains
    struct MyTag1;
    sharded_mutex!(MyTag1: TestType);
    struct MyTag2;
    sharded_mutex!(MyTag2: TestType);

    // need an explicit tag
    let x = ShardedMutex::new_with_tag(TestType(123), MyTag1);
    assert_eq!(x.lock().0, 123);
    let y = ShardedMutex::new_with_tag(TestType(234), MyTag2);
    assert_eq!(y.lock().0, 234);
}
