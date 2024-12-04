#![no_main]
#![no_std]

extern crate ceno_rt;

ceno_rt::entry!(main);
#[inline(never)]
fn main() {
    let _ = is_prime(707);
}

// taken from succinctlabs sp1 examples
// Returns if divisible via immediate checks than 6k ± 1.
// Source: https://en.wikipedia.org/wiki/Primality_test#Rust
fn is_prime(n: u64) -> bool {
    if n <= 1 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    if n % 2 == 0 || n % 3 == 0 {
        return false;
    }
    let mut i = 5;
    while i * i <= n {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    true
}
