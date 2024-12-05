#![no_main]
#![no_std]
use core::ptr::{addr_of, read_volatile};

extern crate ceno_rt;

static mut OUTPUT: u32 = 0;

ceno_rt::entry!(main);
fn main() {
    let mut state = [0_u64; 25];

    syscalls::syscall_keccak_permute(&mut state);
}

/// Prevent compiler optimizations.
fn black_box<T>(x: *const T) -> T {
    unsafe { read_volatile(x) }
}

mod syscalls {

    // Based on https://github.com/succinctlabs/sp1/blob/013c24ea2fa15a0e7ed94f7d11a7ada4baa39ab9/crates/zkvm/entrypoint/src/syscalls/keccak_permute.rs

    const KECCAK_PERMUTE: u32 = 0x00_01_01_09;

    use core::arch::asm;

    /// Executes the Keccak256 permutation on the given state.
    ///
    /// ### Safety
    ///
    /// The caller must ensure that `state` is valid pointer to data that is aligned along a four
    /// byte boundary.
    #[allow(unused_variables)]
    #[no_mangle]
    pub extern "C" fn syscall_keccak_permute(state: &mut [u64; 25]) {
        unsafe {
            asm!(
                "ecall",
                in("t0") KECCAK_PERMUTE,
                in("a0") state as *mut [u64; 25],
                in("a1") 0
            );
        }
    }
}