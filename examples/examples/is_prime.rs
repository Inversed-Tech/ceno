extern crate ceno_rt;
use ceno_rt::println;
use core::fmt::Write;
use rkyv::Archived;

fn is_prime(n: u32) -> bool {
    if n < 2 {
        return false;
    }
    let mut i = 2;
    while i * i <= n {
        if n % i == 0 {
            return false;
        }
        i += 1;
    }

    return true;
}

fn main() {
    // let input: &Archived<u32> = ceno_rt::read();
    let n: &Archived<u32> = ceno_rt::read();
    // println!("{}", n);
    let mut cnt_primes = 0;

    for i in 0..=n.into() {
        cnt_primes += is_prime(i) as u32;
    }

    if cnt_primes > 1000 * 1000 {
        panic!();
    }
    // println!("{}", cnt_primes);
    // Print any output you feel like, eg the first element of the sorted vector:
    // println!("{}", scratch[0]);
}
