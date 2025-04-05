//! NTT and related algorithms.

mod matrix;
mod ntt_impl;
mod transpose;
mod utils;
mod wavelet;

use self::matrix::MatrixMut;
use ark_ff::FftField;
use tracing::{debug_span, instrument};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub use self::{
    ntt_impl::{intt, intt_batch, ntt, ntt_batch},
    transpose::{transpose, transpose_bench_allocate, transpose_test},
    wavelet::wavelet_transform,
};

fn debug_f<F: FftField + std::fmt::Debug>() -> String {
    format!(
        "generator = {:?}, two_adicity = {:?}",
        F::GENERATOR,
        F::TWO_ADICITY
    )
}

/// RS encode at a rate 1/`expansion`.
#[instrument(skip_all, name="expand_from_coeff", fields(coeffs_len=coeffs.len(), expansion=expansion, dbg=debug_f::<F>()))]
pub fn expand_from_coeff<F: FftField>(coeffs: &[F], expansion: usize) -> Vec<F> {
    let engine = ntt_impl::NttEngine::<F>::new_from_cache();
    // println!(
    // "expand_from_coeff with order {} and expansion {} and len {}",
    // engine.order,
    // expansion,
    // coeffs.len()
    // );
    let expanded_size = coeffs.len() * expansion;
    let mut result = Vec::with_capacity(expanded_size);
    // Note: We can also zero-extend the coefficients and do a larger NTT.
    // But this is more efficient.

    // Do coset NTT.
    let root = engine.root(expanded_size);
    result.extend_from_slice(coeffs);
    #[cfg(not(feature = "parallel"))]
    for i in 1..expansion {
        let root = root.pow([i as u64]);
        let mut offset = F::ONE;
        result.extend(coeffs.iter().map(|x| {
            let val = *x * offset;
            offset *= root;
            val
        }));
    }
    // chunk, 0: w^0
    // chunk 1: c_0 * (w^1), c_1 * w^2, c_2 *  w^3
    // chunk 2: c_0 * w^2, c_1 * (w^2)^2, c_3 * (w^2)^3
    let twiddle_span = debug_span!("create twiddles").entered();
    #[cfg(feature = "parallel")]
    result.par_extend((1..expansion).into_par_iter().flat_map(|i| {
        let root_i = root.pow([i as u64]);
        coeffs
            .par_iter()
            .enumerate()
            .map_with(F::ZERO, move |root_j, (j, coeff)| {
                if root_j.is_zero() {
                    *root_j = root_i.pow([j as u64]);
                } else {
                    *root_j *= root_i;
                }
                *coeff * *root_j
            })
    }));
    drop(twiddle_span);

    ntt_batch(&mut result, coeffs.len());
    transpose(&mut result, expansion, coeffs.len());

    result
}
