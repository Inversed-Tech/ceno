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

    xor_sum: [EvalExpression; 1],
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
        self.xor_sum = chip.allocate_output_evals();

        let mut sum = self.xor_sum.clone();
        let mut challenges: Vec<Constant> = vec![];

        for level in 0..self.params.height {
            let ([lhs, rhs], []) = chip.allocate_wits_in_layer();

            let lhs_expr: Expression = lhs.clone().0.into();
            let rhs_expr: Expression = rhs.clone().0.into();

            let in_bases = vec![lhs.clone().1, rhs.clone().1];
            let in_exts = vec![];

            let expr = lhs_expr.clone() + rhs_expr.clone()
                - Expression::Const(Constant::Base(2)) * lhs_expr.clone() * rhs_expr.clone();

            chip.add_layer(Layer::new(
                format!("Tower_layer_{}", level),
                LayerType::Zerocheck,
                vec![expr],
                challenges.clone(),
                in_bases,
                in_exts,
                sum.to_vec(),
            ));

            let [challenge] = chip.allocate_challenges();
            dbg!(&challenge);

            sum = [EvalExpression::Partition(
                vec![Box::new(lhs.1), Box::new(rhs.1)],
                vec![(0, challenge.clone())],
            )];
            challenges = vec![challenge];
        }

        let ([bits], []) = chip.allocate_wits_in_layer();

        chip.add_layer(Layer::new(
            "Bottom".to_string(),
            LayerType::Linear,
            vec![bits.0.into()],
            challenges,
            vec![bits.1.clone()],
            vec![],
            vec![sum[0].clone()],
        ));
        // chip.allocate_base_opening(self.committed_bits_id, bits.1);
    }
}

pub const STATE_BITS: usize = 8;

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

        let n_layers = self.params.height;
        let mut layer_wits = Vec::<LayerWitness<E>>::with_capacity(n_layers + 1);

        layer_wits.push(LayerWitness::new(vec![bits.clone()], vec![]));
        let mut bits_ = bits.clone();
        let mut lhs_bits: Vec<<E as ExtensionField>::BaseField> = vec![];
        let mut rhs_bits: Vec<<E as ExtensionField>::BaseField> = vec![];

        for _ in 0..n_layers {
            (lhs_bits, rhs_bits) = bits_.iter().tuples().unzip();

            layer_wits.push(LayerWitness::new(
                vec![lhs_bits.clone(), rhs_bits.clone()],
                vec![],
            ));

            bits_ = zip_eq(lhs_bits, rhs_bits)
                .map(|(lhs, rhs)| xor(lhs, rhs))
                .collect_vec();
        }

        assert!(bits_.len() == 1);

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
            let point = Arc::new(vec![]);
            assert_eq!(last[0].len(), 1);
            assert_eq!(last[1].len(), 1);
            vec![PointAndEval {
                point: point.clone(),
                eval: xor(last[0][0], last[1][0]),
            }]
        };

        dbg!(&out_evals[0]);

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
