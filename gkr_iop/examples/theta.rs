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
use itertools::{Itertools, iproduct, izip, zip_eq};
use rand::{Rng, SeedableRng, rngs::OsRng};
use subprotocols::expression::{Constant, Expression, Witness};
use transcript::{BasicTranscript, Transcript};

#[cfg(debug_assertions)]
use gkr_iop::gkr::mock::MockProver;
#[cfg(debug_assertions)]
use subprotocols::expression::VectorType;

type E = GoldilocksExt2;

#[derive(Clone, Debug, Default)]
struct TowerParams {
    height: usize,
}

#[derive(Clone, Debug, Default)]
struct KeccakParams {
    height: usize,
}

#[derive(Clone, Debug, Default)]
struct KeccakLayout<E> {
    params: KeccakParams,

    committed_bits_id: usize,

    result: Vec<EvalExpression>,
    _marker: PhantomData<E>,
}

fn to_cube(i: usize) -> (usize, usize, usize) {
    assert!(i < 1600);
    (i / 64 % 5, (i / 64) / 5, i % 64)
}

fn from_cube(x: usize, y: usize, z: usize) -> usize {
    assert!(x < 5 && y < 5 && z < 64);
    // dbg!(x, y, z);
    64 * (5 * y + x) + z
}

fn from_square(x: usize, y: usize) -> usize {
    x * 64 + y
}

fn xor<F: Field>(a: F, b: F) -> F {
    a + b - a * b - a * b
}

fn xor_expr(a: Expression, b: Expression) -> Expression {
    a.clone() + b.clone() - Expression::Const(Constant::Base(2)) * a * b
}

fn c_expr(x: usize, z: usize, state_wits: &[Witness]) -> Expression {
    let elems = (0..5)
        .map(|y| Expression::from(state_wits[from_cube(x, y, z)]))
        .collect_vec();
    let mut res = elems[0].clone();
    for i in 1..5 {
        res = xor_expr(res, elems[i].clone());
    }
    res
}

fn c<F: Field>(x: usize, z: usize, bits: &[F]) -> F {
    (0..5)
        .map(|y| bits[from_cube(x, y, z)])
        .fold(F::ZERO, |acc, x| xor(acc, x))
}

fn d<F: Field>(x: usize, z: usize, c_vals: &[F]) -> F {
    let lhs = from_square((x + 5 - 1) % 5, z);
    let rhs = from_square((x + 1) % 5, (z + 64 - 1) % 64);
    xor(c_vals[lhs], c_vals[rhs])
}

fn d_expr(x: usize, z: usize, c_wits: &[Witness]) -> Expression {
    let lhs = from_square((x + 5 - 1) % 5, z);
    let rhs = from_square((x + 1) % 5, (z + 64 - 1) % 64);
    xor_expr(c_wits[lhs].into(), c_wits[rhs].into())
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
        // Mihai: outputs need to be allocated before wits?
        let d = chip.allocate_output_evals::<320>();

        let (c, []) = chip.allocate_wits_in_layer::<320, 0>();
        let c_wits = c.iter().map(|s| s.0).collect_vec();

        let d_exprs = iproduct!(0..5usize, 0..64usize)
            .map(|(x, z)| d_expr(x, z, &c_wits))
            .collect_vec();

        chip.add_layer(Layer::new(
            "compute_D[x][z]".to_string(),
            LayerType::Zerocheck,
            d_exprs,
            // vec![challenge1, challenge2],
            vec![],
            c.iter().map(|t| t.1.clone()).collect_vec(),
            vec![],
            d.to_vec(),
        ));

        let (state, []) = chip.allocate_wits_in_layer::<STATE_BITS, 0>();
        let state_wits = state.iter().map(|s| s.0).collect_vec();

        let c_exprs = iproduct!(0..5usize, 0..64usize)
            .map(|(x, z)| c_expr(x, z, &state_wits))
            .collect_vec();

        chip.add_layer(Layer::new(
            "compute_C[x][z]".to_string(),
            LayerType::Zerocheck,
            c_exprs,
            // vec![challenge1, challenge2],
            vec![],
            state.iter().map(|t| t.1.clone()).collect_vec(),
            vec![],
            c.iter().map(|cc| cc.clone().1).collect_vec(),
        ));

        // Skip base opening allocation
    }
}

pub const STATE_BITS: usize = 1600;

pub struct KeccakTrace {
    pub bits: [bool; STATE_BITS],
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
            c_wits.clone().into_iter().map(|b| vec![b]).collect_vec(),
            vec![],
        ));

        layer_wits.reverse();

        GKRCircuitWitness { layers: layer_wits }
    }
}

fn main() {
    let log_size = 3;

    // Sanity
    for i in 0..1600 {
        let (x, y, z) = to_cube(i);
        assert_eq!(from_cube(x, y, z), i);
    }
    let params = KeccakParams { height: log_size };
    let (layout, chip) = KeccakLayout::build(params);
    let gkr_circuit = chip.gkr_circuit();

    let (out_evals, gkr_proof) = {
        let random_u64: u64 = rand::random();
        let mut rng = rand::rngs::StdRng::seed_from_u64(random_u64);
        let bits: [bool; STATE_BITS] = std::array::from_fn(|_| rng.gen());
        let phase1_witness = layout.phase1_witness(KeccakTrace { bits });

        let mut prover_transcript = BasicTranscript::<E>::new(b"protocol");

        // Omit the commit phase1 and phase2.

        let gkr_witness = layout.gkr_witness(&phase1_witness, &vec![]);

        // #[cfg(debug_assertions)]
        // {
        //     let last = gkr_witness.layers[0].exts.clone();
        //     MockProver::check(
        //         gkr_circuit.clone(),
        //         &gkr_witness,
        //         vec![
        //             VectorType::Ext(vec![last[0][0] * last[1][0]]),
        //             VectorType::Ext(vec![last[0][0] * last[3][0] + last[1][0] * last[2][0]]),
        //         ],
        //         challenges.clone(),
        //     )
        //     .expect("Mock prover failed");
        // }

        let out_evals = {
            let last = gkr_witness.layers[0]
                .bases
                .clone()
                .iter()
                .map(|bases| {
                    bases
                        .iter()
                        .map(|base| GoldilocksExt2::new_from_base(&[*base, Goldilocks::ZERO]))
                        .collect_vec()
                })
                .collect_vec();
            let point = Arc::new(vec![
                //GoldilocksExt2::ZERO,
                // GoldilocksExt2::ZERO,
                // GoldilocksExt2::ZERO,
            ]);
            // assert_eq!(last[0].len(), 1);
            // assert_eq!(last[1].len(), 1);

            let c_eval = last.into_iter().flatten().collect_vec();
            let evals = iproduct!(0..5usize, 0..64usize)
                .map(|(x, z)| PointAndEval {
                    point: point.clone(),
                    eval: d(x, z, &c_eval),
                })
                .collect_vec();

            evals
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
