use std::{fs, path::PathBuf, time::Duration};

use ceno_emul::{CENO_PLATFORM, Platform, Program, WORD_SIZE};
use ceno_zkvm::{
    self,
    e2e::{run_e2e_gen_witness, run_e2e_proof, run_e2e_verify},
};
use criterion::*;

use goldilocks::GoldilocksExt2;
use mpcs::BasefoldDefault;

criterion_group! {
  name = is_prime;
  config = Criterion::default().warm_up_time(Duration::from_millis(20000));
  targets = bench_e2e
}

criterion_main!(is_prime);

const NUM_SAMPLES: usize = 10;

struct BenchVars {
    program: Program,
    platform: Platform,
    stack_size: u32,
    heap_size: u32,
    max_steps: Vec<usize>,
}

impl Default for BenchVars {
    fn default() -> Self {
        let mut file_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        file_path.push("examples/is_prime.elf");
        let stack_size = 32768;
        let heap_size = 2097152;
        let elf_bytes = fs::read(&file_path).expect("read elf file");
        let program = Program::load_elf(&elf_bytes, u32::MAX).unwrap();

        let platform = Platform {
            // The stack section is not mentioned in ELF headers, so we repeat the constant STACK_TOP here.
            stack_top: 0x0020_0400,
            rom: program.base_address
                ..program.base_address + (program.instructions.len() * WORD_SIZE) as u32,
            ram: 0x0010_0000..0xFFFF_0000,
            unsafe_ecall_nop: true,
            ..CENO_PLATFORM
        };

        Self {
            program,
            platform,
            stack_size,
            heap_size,
            max_steps: vec![1usize << 20, 1usize << 21, 1usize << 22],
        }
    }
}

fn bench_e2e(c: &mut Criterion) {
    // sanity check - don't care about benchmarks for invalid proofs.
    verify_is_prime();

    type E = GoldilocksExt2;
    type Pcs = BasefoldDefault<E>;

    let BenchVars {
        program,
        platform,
        stack_size,
        heap_size,
        max_steps,
    } = BenchVars::default();

    for max_steps in max_steps {
        // expand more input size once runtime is acceptable
        let mut group = c.benchmark_group(format!("is_prime_max_steps_{}", max_steps));
        group.sample_size(NUM_SAMPLES);

        // Benchmark the proving time
        group.bench_function(
            BenchmarkId::new(
                "prove_is_prime",
                format!("is_prime_max_steps_{}", max_steps),
            ),
            |b| {
                b.iter_with_setup(
                    || {
                        run_e2e_gen_witness::<E, Pcs>(
                            program.clone(),
                            platform.clone(),
                            stack_size,
                            heap_size,
                            vec![],
                            max_steps,
                        )
                    },
                    |(prover, _, zkvm_witness, pi, _, _, _)| {
                        let _ = run_e2e_proof(prover, zkvm_witness, pi);
                    },
                );
            },
        );

        group.finish();
    }
}

fn verify_is_prime() {
    type E = GoldilocksExt2;
    type Pcs = BasefoldDefault<E>;

    let BenchVars {
        program,
        platform,
        stack_size,
        heap_size,
        max_steps,
    } = BenchVars::default();

    let (prover, verifier, zkvm_witness, pi, _, _, exit_code) = run_e2e_gen_witness::<E, Pcs>(
        program.clone(),
        platform.clone(),
        stack_size,
        heap_size,
        vec![],
        max_steps[0],
    );

    let proof = run_e2e_proof(prover, zkvm_witness, pi);
    run_e2e_verify(&verifier, proof, exit_code, max_steps[0]);
}
