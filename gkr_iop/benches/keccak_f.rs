use std::{array, time::Duration};

use ark_std::test_rng;
use criterion::*;
use ff::Field;
use gkr_iop::precompiles::run_keccakf;
use goldilocks::GoldilocksExt2;
use itertools::Itertools;
use rand::{Rng, SeedableRng};
use subprotocols::{
    expression::{Constant, Expression, Witness},
    sumcheck::SumcheckProverState,
    test_utils::{random_point, random_poly},
    zerocheck::ZerocheckProverState,
};
criterion_group!(benches, keccak_f_fn);
criterion_main!(benches);

const NUM_SAMPLES: usize = 10;
const NV: [usize; 2] = [25, 26];

fn keccak_f_fn(c: &mut Criterion) {
    type E = GoldilocksExt2;

    // expand more input size once runtime is acceptable
    let mut group = c.benchmark_group(format!("keccak_f"));
    group.sample_size(NUM_SAMPLES);

    // Benchmark the proving time
    group.bench_function(BenchmarkId::new("keccak_f", format!("keccak_f")), |b| {
        b.iter_custom(|iters| {
            let mut time = Duration::new(0, 0);
            for _ in 0..iters {
                // Use seeded rng for debugging convenience
                let mut rng = rand::rngs::StdRng::seed_from_u64(42);
                let state: [u64; 25] = std::array::from_fn(|_| rng.gen());

                let instant = std::time::Instant::now();
                let _ = black_box(run_keccakf(state, false, false));
                let elapsed = instant.elapsed();
                time += elapsed;
            }

            time
        });
    });

    group.finish();
}
