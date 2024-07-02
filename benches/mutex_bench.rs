#![allow(missing_docs)]
use criterion::{criterion_group, criterion_main, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    let mut baseline = c.benchmark_group("baseline");

    baseline.bench_function("std::sync::Mutex", |b| {
        let array = [const { std::sync::Mutex::new(0usize) }; 10_000];
        b.iter(|| {
            for item in &array {
                let mut guard = item.lock().unwrap();
                *guard += 1;
            }
        });
    });

    baseline.bench_function("parking_lot::Mutex", |b| {
        let array = [const { parking_lot::Mutex::new(0usize) }; 10_000];
        b.iter(|| {
            for item in &array {
                let mut guard = item.lock();
                *guard += 1;
            }
        });
    });

    baseline.bench_function("sharded_mutex::ShardedMutex", |b| {
        let array = [const { sharded_mutex::ShardedMutex::new(0usize) }; 10_000];
        b.iter(|| {
            for item in &array {
                let mut guard = item.lock();
                *guard += 1;
            }
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
