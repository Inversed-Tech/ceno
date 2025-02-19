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
use itertools::{Itertools, izip, zip_eq};
use rand::{Rng, SeedableRng, rngs::OsRng};
use subprotocols::expression::{Constant, Expression};
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

    result: [EvalExpression; 3],
    _marker: PhantomData<E>,
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
        self.result = chip.allocate_output_evals();

        let (targets, []) = chip.allocate_wits_in_layer::<16, 0>();

        let sum_range = |x: usize, y: usize| {
            (x..y)
                .map(|i| Expression::from(targets[i].0))
                .fold(Expression::from(Constant::Base(0)), |acc, x| acc + x)
        };

        let expr1 = sum_range(0, 3);
        let expr2 = sum_range(3, 7);
        let expr3 = sum_range(7, 10);

        dbg!(&self.result);
        dbg!(&targets);

        chip.add_layer(Layer::new(
            "Bottom".to_string(),
            LayerType::Zerocheck,
            vec![expr1, expr2, expr3],
            // vec![challenge1, challenge2],
            vec![],
            targets.iter().map(|t| t.1.clone()).collect_vec(),
            vec![],
            self.result.clone().to_vec(),
        ));

        // Skip base opening allocation
    }
}

pub const STATE_BITS: usize = 16;

pub struct KeccakTrace {
    pub bits: [bool; STATE_BITS],
}

fn xor<F: Field>(a: F, b: F) -> F {
    a + b - a * b - a * b
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

        // // let results = [
        // //     bits[0] + bits[1] + bits[2],
        // //     bits[3] + bits[4] + bits[5] + bits[6],
        // //     bits[7] + bits[8] + bits[9],
        // //     E::BaseField::ZERO,
        // // ];

        // layer_wits.push(LayerWitness::new(vec![results.to_vec()], vec![]));

        layer_wits.reverse();

        GKRCircuitWitness { layers: layer_wits }
    }
}

fn main() {
    let log_size = 3;
    let params = KeccakParams { height: log_size };
    let (layout, chip) = KeccakLayout::build(params);
    let gkr_circuit = chip.gkr_circuit();

    let (out_evals, gkr_proof) = {
        let random_u64: u64 = rand::random();
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
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
            vec![
                PointAndEval {
                    point: point.clone(),
                    eval: last[0][0] + last[1][0] + last[2][0],
                },
                PointAndEval {
                    point: point.clone(),
                    eval: last[3][0] + last[4][0] + last[5][0] + last[6][0],
                },
                PointAndEval {
                    point: point.clone(),
                    eval: last[7][0] + last[8][0] + last[9][0],
                },
            ]
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
