use gkr_iop::precompiles::{run_faster_keccakf, run_keccakf};
use rand::{Rng, SeedableRng};
fn main() {
    let random_u64: u64 = rand::random();
    // Use seeded rng for debugging convenience
    let mut rng = rand::rngs::StdRng::seed_from_u64(random_u64);
    let state: [u64; 25] = std::array::from_fn(|_| rng.gen());

    run_keccakf(state, true, true);
}
