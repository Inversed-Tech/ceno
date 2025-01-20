//! A simple program that takes a number `n` as input, and writes the `n-1`th and `n`th fibonacci
//! number as an output.

// These two lines are necessary for the program to properly compile.
//
// Under the hood, we wrap your main function with some extra code so that it behaves properly
// inside the zkVM.
#![no_main]
sp1_zkvm::entrypoint!(main);

use core::panic;

use alloy_sol_types::SolType;
use fibonacci_lib::{fibonacci, PublicValuesStruct};
use sp1_zkvm::lib::{
    syscall_keccak_permute, syscall_secp256k1_add, syscall_secp256k1_decompress,
    syscall_secp256k1_double,
};

const P: [u8; 65] = [
    4, 180, 53, 9, 32, 85, 226, 220, 154, 20, 116, 218, 199, 119, 48, 44, 23, 45, 222, 10, 64, 50,
    63, 8, 121, 191, 244, 141, 0, 37, 117, 182, 133, 190, 160, 239, 131, 180, 166, 242, 145, 107,
    249, 24, 168, 27, 69, 86, 58, 86, 159, 10, 210, 164, 20, 152, 148, 67, 37, 222, 234, 108, 57,
    84, 148,
];
const Q: [u8; 65] = [
    4, 117, 102, 61, 142, 169, 5, 99, 112, 146, 4, 241, 177, 255, 72, 34, 34, 12, 251, 37, 126,
    213, 96, 38, 9, 40, 35, 20, 186, 78, 125, 73, 44, 215, 29, 243, 127, 197, 147, 216, 206, 110,
    116, 63, 96, 72, 143, 182, 205, 11, 234, 96, 127, 206, 19, 1, 103, 103, 219, 255, 25, 229, 210,
    4, 141,
];
const P_PLUS_Q: [u8; 65] = [
    4, 188, 11, 115, 232, 35, 63, 79, 186, 163, 11, 207, 165, 64, 247, 109, 81, 125, 56, 83, 131,
    221, 140, 154, 19, 186, 109, 173, 9, 127, 142, 169, 219, 108, 17, 216, 218, 125, 37, 30, 87,
    86, 194, 151, 20, 122, 64, 118, 123, 210, 29, 60, 209, 138, 131, 11, 247, 157, 212, 209, 123,
    162, 111, 197, 70,
];

const DOUBLE_P: [u8; 65] = [
    4, 111, 137, 182, 244, 228, 50, 13, 91, 93, 34, 231, 93, 191, 248, 105, 28, 226, 251, 23, 66,
    192, 188, 66, 140, 44, 218, 130, 239, 101, 255, 164, 76, 202, 170, 134, 48, 127, 46, 14, 9,
    192, 64, 102, 67, 163, 33, 48, 157, 140, 217, 10, 97, 231, 183, 28, 129, 177, 185, 253, 179,
    135, 182, 253, 203,
];

const COMPRESSED: [u8; 33] = [
    2, 180, 53, 9, 32, 85, 226, 220, 154, 20, 116, 218, 199, 119, 48, 44, 23, 45, 222, 10, 64, 50,
    63, 8, 121, 191, 244, 141, 0, 37, 117, 182, 133,
];
const DECOMPRESSED: [u8; 64] = [
    180, 53, 9, 32, 85, 226, 220, 154, 20, 116, 218, 199, 119, 48, 44, 23, 45, 222, 10, 64, 50, 63,
    8, 121, 191, 244, 141, 0, 37, 117, 182, 133, 190, 160, 239, 131, 180, 166, 242, 145, 107, 249,
    24, 168, 27, 69, 86, 58, 86, 159, 10, 210, 164, 20, 152, 148, 67, 37, 222, 234, 108, 57, 84,
    148,
];

const KECCAK_ON_ZEROS: [u64; 25] = [
    17376452488221285863,
    9571781953733019530,
    15391093639620504046,
    13624874521033984333,
    10027350355371872343,
    18417369716475457492,
    10448040663659726788,
    10113917136857017974,
    12479658147685402012,
    3500241080921619556,
    16959053435453822517,
    12224711289652453635,
    9342009439668884831,
    4879704952849025062,
    140226327413610143,
    424854978622500449,
    7259519967065370866,
    7004910057750291985,
    13293599522548616907,
    10105770293752443592,
    10668034807192757780,
    1747952066141424100,
    1654286879329379778,
    8500057116360352059,
    16929593379567477321,
];

type DecompressedPoint = [u32; 16];

// interpret bytes for our internal interface [u32; 16]
fn from_bytes(bytes: [u8; 65]) -> DecompressedPoint {
    let mut bytes: [u8; 64] = bytes.clone()[1..].try_into().unwrap();
    bytes[0..32].reverse();
    bytes[32..].reverse();
    let mut ret =
        std::array::from_fn(|i| u32::from_le_bytes(bytes[4 * i..4 * (i + 1)].try_into().unwrap()));
    ret
}

pub fn make_calls() {
    unsafe {
        let mut p = from_bytes(P);
        let mut q = from_bytes(Q);
        let p_plus_q = from_bytes(P_PLUS_Q);
        syscall_secp256k1_add(&mut p, &mut q);

        assert!(p == p_plus_q);
    }

    unsafe {
        let mut p = from_bytes(P);
        let double_p = from_bytes(DOUBLE_P);

        syscall_secp256k1_double(&mut p);
        assert!(p == double_p);
    }

    unsafe {
        let is_odd = match COMPRESSED[0] {
            2 => false,
            3 => true,
            _ => panic!("parity byte should be 2 or 3"),
        };

        // ignore parity byte, append 32 zero bytes for writing Y
        let mut compressed_with_space: [u8; 64] = [COMPRESSED[1..].to_vec(), vec![0; 32]]
            .concat()
            .try_into()
            .unwrap();

        syscall_secp256k1_decompress(&mut compressed_with_space, is_odd);
        assert!(compressed_with_space == DECOMPRESSED);
    }

    unsafe {
        let mut state = [0u64; 25];

        syscall_keccak_permute(&mut state);
        assert!(state == KECCAK_ON_ZEROS);
    }
}

pub fn main() {
    // Read an input to the program.
    //
    // Behind the scenes, this compiles down to a custom system call which handles reading inputs
    // from the prover.

    let state = [0u64; 25];

    //TODO: why do Ceno syscalls work without unsafe?
    make_calls();
    // Encode the public values of the program.
    let bytes = PublicValuesStruct::abi_encode(&PublicValuesStruct { state });

    // Commit to the public values of the program. The final proof will have a commitment to all the
    // bytes that were committed to.
    sp1_zkvm::io::commit_slice(&bytes);
}
