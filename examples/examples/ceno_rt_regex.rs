#![no_main]
#![no_std]

extern crate ceno_rt;
use regex::Regex;

ceno_rt::entry!(main);
#[inline(never)]
fn main() {
    let _ = regex("[a-z]+", "abcdefG");
}

// adapted from succinctlabs sp1 examples
fn regex(pattern: &str, target: &str) -> bool {
    let re = Regex::new(&pattern).unwrap("Invalid regex pattern");
    re.is_match(&target)
}
