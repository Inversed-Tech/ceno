extern crate ceno_rt;
use ceno_rt::println;
use core::fmt::Write;
use rand::{Rng, SeedableRng, rngs::StdRng};
use rkyv::vec::ArchivedVec;

fn main() {
    // let input: &ArchivedVec<u32> = ceno_rt::read();
    // let mut scratch: Vec<u32> = input.to_vec();

    let input: &ArchivedVec<u32> = ceno_rt::read();
    let n = input[0] as usize;

    let mut rng = StdRng::seed_from_u64(42); // Fixed seed for reproducibility
    let mut scratch: Vec<u32> = (0..n).map(|_| rng.gen()).collect();
    scratch.sort();
    // Print any output you feel like, eg the first element of the sorted vector:

    // Note: prints make proving fail
    // println!("{}", scratch[0]);
}
