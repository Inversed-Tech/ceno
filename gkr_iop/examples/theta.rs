use std::{marker::PhantomData, mem, sync::Arc};

use ff::Field;
use ff_ext::ExtensionField;
use gkr_iop::{
    ProtocolBuilder, ProtocolWitnessGenerator,
    chip::Chip,
    evaluation::{EvalExpression, PointAndEval},
    gkr::{
        GKRCircuitWitness, GKRProverOutput,
        layer::{self, Layer, LayerType, LayerWitness},
    },
};
use goldilocks::{Goldilocks, GoldilocksExt2};
use itertools::{Itertools, chain, iproduct, izip, zip_eq};
use rand::{Rng, SeedableRng, rngs::OsRng};
use subprotocols::expression::{Constant, Expression, Witness};
use transcript::{BasicTranscript, Transcript};

#[cfg(debug_assertions)]
use gkr_iop::gkr::mock::MockProver;
#[cfg(debug_assertions)]
use subprotocols::expression::VectorType;

type E = GoldilocksExt2;

#[derive(Clone, Debug, Default)]
struct KeccakParams {}

#[derive(Clone, Debug, Default)]
struct KeccakLayout<E> {
    params: KeccakParams,

    committed_bits_id: usize,

    result: Vec<EvalExpression>,
    _marker: PhantomData<E>,
}

const X: usize = 5;
const Y: usize = 5;
const Z: usize = 64;
const STATE_SIZE: usize = X * Y * Z;
const C_SIZE: usize = X * Z;
const D_SIZE: usize = X * Z;

fn to_xyz(i: usize) -> (usize, usize, usize) {
    assert!(i < STATE_SIZE);
    (i / 64 % 5, (i / 64) / 5, i % 64)
}

fn from_xyz(x: usize, y: usize, z: usize) -> usize {
    assert!(x < 5 && y < 5 && z < 64);
    64 * (5 * y + x) + z
}

fn xor<F: Field>(a: F, b: F) -> F {
    a + b - a * b - a * b
}

fn xor_expr(a: Expression, b: Expression) -> Expression {
    a.clone() + b.clone() - Expression::Const(Constant::Base(2)) * a * b
}

fn zero_expr() -> Expression {
    Expression::Const(Constant::Base(0))
}

fn c<F: Field>(x: usize, z: usize, bits: &[F]) -> F {
    (0..5)
        .map(|y| bits[from_xyz(x, y, z)])
        .fold(F::ZERO, |acc, x| xor(acc, x))
}

fn c_expr(x: usize, z: usize, state_wits: &[Witness]) -> Expression {
    (0..5)
        .map(|y| Expression::from(state_wits[from_xyz(x, y, z)]))
        .fold(zero_expr(), |acc, x| xor_expr(acc, x))
}

fn from_xz(x: usize, z: usize) -> usize {
    x * 64 + z
}

fn d<F: Field>(x: usize, z: usize, c_vals: &[F]) -> F {
    let lhs = from_xz((x + 5 - 1) % 5, z);
    let rhs = from_xz((x + 1) % 5, (z + 64 - 1) % 64);
    xor(c_vals[lhs], c_vals[rhs])
}

fn d_expr(x: usize, z: usize, c_wits: &[Witness]) -> Expression {
    let lhs = from_xz((x + 5 - 1) % 5, z);
    let rhs = from_xz((x + 1) % 5, (z + 64 - 1) % 64);
    xor_expr(c_wits[lhs].into(), c_wits[rhs].into())
}

fn theta<F: Field>(bits: Vec<F>) -> Vec<F> {
    assert_eq!(bits.len(), STATE_SIZE);

    let c_vals = iproduct!(0..5, 0..64)
        .map(|(x, z)| c(x, z, &bits))
        .collect_vec();

    let d_vals = iproduct!(0..5, 0..64)
        .map(|(x, z)| d(x, z, &c_vals))
        .collect_vec();

    bits.iter()
        .enumerate()
        .map(|(i, bit)| {
            let (x, _, z) = to_xyz(i);
            xor(*bit, d_vals[from_xz(x, z)])
        })
        .collect()
}

impl<E: ExtensionField> ProtocolBuilder for KeccakLayout<E> {
    type Params = KeccakParams;

    fn init(params: Self::Params) -> Self {
        Self {
            params,
            ..Default::default()
        }
    }

    fn build_commit_phase(&mut self, chip: &mut Chip) {
        [self.committed_bits_id] = chip.allocate_committed_base();
    }

    fn build_gkr_phase(&mut self, chip: &mut Chip) {
        let theta_output = chip.allocate_output_evals::<STATE_SIZE>();

        let (d_and_state, _) = chip.allocate_wits_in_layer::<{ D_SIZE + STATE_SIZE }, 0>();
        let (d, state) = d_and_state.split_at(D_SIZE);

        // Compute post-theta state using original state and D[][] values
        let exprs = (0..STATE_SIZE)
            .map(|i| {
                let (x, y, z) = to_xyz(i);
                xor_expr(state[i].0.into(), d[x * 64 + z].0.into())
            })
            .collect_vec();

        chip.add_layer(Layer::new(
            "compute final state".to_string(),
            LayerType::Zerocheck,
            exprs,
            // vec![challenge1, challenge2],
            vec![],
            d_and_state.iter().map(|e| e.1.clone()).collect_vec(),
            vec![],
            theta_output.to_vec(),
        ));

        let (c_and_state, []) = chip.allocate_wits_in_layer::<{ C_SIZE + STATE_SIZE }, 0>();
        let (c, state) = c_and_state.split_at(C_SIZE);

        let c_wits = c.into_iter().map(|e| e.0).collect_vec();
        let state_wits = state.into_iter().map(|e| e.0).collect_vec();

        // Compute D[][] from C[][] values
        let d_exprs = iproduct!(0..5usize, 0..64usize)
            .map(|(x, z)| d_expr(x, z, &c_wits))
            .collect_vec();

        // Copy state
        let id_exprs: Vec<Expression> = (0..STATE_SIZE).map(|i| state_wits[i].into()).collect_vec();

        chip.add_layer(Layer::new(
            "compute_D[x][z]".to_string(),
            LayerType::Zerocheck,
            chain!(d_exprs, id_exprs).collect_vec(),
            // vec![challenge1, challenge2],
            vec![],
            c_and_state.iter().map(|e| e.1.clone()).collect_vec(),
            vec![],
            d_and_state.iter().map(|e| e.1.clone()).collect_vec(),
        ));

        let (state, []) = chip.allocate_wits_in_layer::<STATE_SIZE, 0>();
        let state_wits = state.iter().map(|s| s.0).collect_vec();

        // Compute C[][] from state
        let c_exprs = iproduct!(0..5usize, 0..64usize)
            .map(|(x, z)| c_expr(x, z, &state_wits))
            .collect_vec();

        // Copy state
        let id_exprs: Vec<Expression> = (0..STATE_SIZE).map(|i| state_wits[i].into()).collect_vec();

        chip.add_layer(Layer::new(
            "compute_C[x][z]".to_string(),
            LayerType::Zerocheck,
            chain!(c_exprs, id_exprs).collect_vec(),
            // vec![challenge1, challenge2],
            vec![],
            state.iter().map(|t| t.1.clone()).collect_vec(),
            vec![],
            c_and_state.iter().map(|e| e.1.clone()).collect_vec(),
        ));

        // Skip base opening allocation
    }
}

pub struct KeccakTrace {
    pub bits: [bool; STATE_SIZE],
}

impl<E> ProtocolWitnessGenerator<E> for KeccakLayout<E>
where
    E: ExtensionField,
{
    type Trace = KeccakTrace;

    fn phase1_witness(&self, phase1: Self::Trace) -> Vec<Vec<E::BaseField>> {
        let mut res = vec![vec![]; 1];
        res[0] = phase1
            .bits
            .into_iter()
            .map(|b| E::BaseField::from(b as u64))
            .collect();
        res
    }

    fn gkr_witness(&self, phase1: &[Vec<E::BaseField>], challenges: &[E]) -> GKRCircuitWitness<E> {
        let bits = &phase1[self.committed_bits_id];

        let n_layers = 3;
        let mut layer_wits = Vec::<LayerWitness<E>>::with_capacity(n_layers + 1);

        layer_wits.push(LayerWitness::new(
            bits.clone().into_iter().map(|b| vec![b]).collect_vec(),
            vec![],
        ));

        let c_wits = iproduct!(0..5usize, 0..64usize)
            .map(|(x, z)| c(x, z, &bits))
            .collect_vec();

        layer_wits.push(LayerWitness::new(
            chain!(
                c_wits.clone().into_iter().map(|b| vec![b]),
                layer_wits[0].bases.clone()
            )
            .collect_vec(),
            vec![],
        ));

        let d_wits = iproduct!(0..5usize, 0..64usize)
            .map(|(x, z)| d(x, z, &c_wits))
            .collect_vec();

        layer_wits.push(LayerWitness::new(
            chain!(
                d_wits.clone().into_iter().map(|b| vec![b]),
                layer_wits[0].bases.clone()
            )
            .collect_vec(),
            vec![],
        ));

        layer_wits.reverse();

        GKRCircuitWitness { layers: layer_wits }
    }
}

fn main() {
    // Sanity
    for i in 0..STATE_SIZE {
        let (x, y, z) = to_xyz(i);
        assert_eq!(from_xyz(x, y, z), i);
    }

    let params = KeccakParams {};
    let (layout, chip) = KeccakLayout::build(params);
    let gkr_circuit = chip.gkr_circuit();

    let (out_evals, gkr_proof) = {
        let random_u64: u64 = rand::random();
        // Use seeded rng for debugging convenience
        let mut rng = rand::rngs::StdRng::seed_from_u64(random_u64);
        let bits: [bool; STATE_SIZE] = std::array::from_fn(|_| rng.gen());
        let phase1_witness = layout.phase1_witness(KeccakTrace { bits });

        let mut prover_transcript = BasicTranscript::<E>::new(b"protocol");

        // Omit the commit phase1 and phase2.

        let gkr_witness = layout.gkr_witness(&phase1_witness, &vec![]);

        let out_evals = {
            let point = Arc::new(vec![]);
            let bits = gkr_witness
                .layers
                .last()
                .unwrap()
                .bases
                .iter()
                .flatten()
                .cloned()
                .collect_vec();

            theta(bits)
                .iter()
                .map(|bit| PointAndEval {
                    point: point.clone(),
                    eval: GoldilocksExt2::new_from_base(&[*bit, Goldilocks::ZERO]),
                })
                .collect_vec()
        };

        let GKRProverOutput { gkr_proof, .. } = gkr_circuit
            .prove(gkr_witness, &out_evals, &vec![], &mut prover_transcript)
            .expect("Failed to prove phase");

        // Omit the PCS opening phase.

        (out_evals, gkr_proof)
    };

    {
        let mut verifier_transcript = BasicTranscript::<E>::new(b"protocol");

        gkr_circuit
            .verify(gkr_proof, &out_evals, &vec![], &mut verifier_transcript)
            .expect("GKR verify failed");

        // Omit the PCS opening phase.
    }
}
