use criterion::*;
use goldilocks::GoldilocksExt2;
use rand::RngCore;

use ceno_zkvm::scheme::utils::{infer_tower_logup_witness, infer_tower_product_witness};

use multilinear_extensions::{mle::IntoMLE, virtual_poly::ArcMultilinearExtension};

type E = GoldilocksExt2;

criterion_group!(benches, build_tower);
criterion_main!(benches);

const NUM_SAMPLES: usize = 10;

fn build_tower(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let mut group = c.benchmark_group("data_xfer");
    group.sample_size(NUM_SAMPLES);

    for nv in [15, 20, 24] {
        let polys: Vec<_> = (0..1 << nv).map(|_| E::from(rng.next_u64())).collect();
        let mle: ArcMultilinearExtension<E> = polys.into_mle().into();
        let p = vec![mle.clone(), mle.clone()];
        let q = vec![mle.clone(), mle.clone()];

        group.bench_function(
            BenchmarkId::new("build_logup_tower", format!("nv_{}", nv)),
            |b| {
                b.iter(|| {
                    infer_tower_logup_witness(Some(p.clone()), q.clone());
                })
            },
        );

        group.bench_function(
            BenchmarkId::new("build_product_tower", format!("nv_{}", nv)),
            |b| {
                b.iter(|| {
                    infer_tower_product_witness(nv, p.clone(), 2);
                })
            },
        );
    }

    group.finish();
}
