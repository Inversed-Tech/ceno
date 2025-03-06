use std::{array::from_fn, marker::PhantomData, sync::Arc};

use crate::{
    ProtocolBuilder, ProtocolWitnessGenerator,
    chip::Chip,
    evaluation::{EvalExpression, PointAndEval},
    gkr::{
        GKRCircuitWitness, GKRProverOutput,
        layer::{Layer, LayerType, LayerWitness},
    },
};
use ff::{Field, PrimeField};
use ff_ext::ExtensionField;
use goldilocks::{Goldilocks, GoldilocksExt2};
use itertools::{Itertools, chain, iproduct};
use subprotocols::expression::{Constant, Expression, Witness};
use tiny_keccak::keccakf;
use transcript::BasicTranscript;

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

fn zero_expr() -> Expression {
    Expression::Const(Constant::Base(0))
}

fn one_expr() -> Expression {
    Expression::Const(Constant::Base(1))
}

fn zero_eval() -> EvalExpression {
    EvalExpression::Linear(0, Constant::Base(0), Constant::Base(0))
}

fn expansion_expr<const SIZE: usize>(expansion: &[(usize, Witness)]) -> Expression {
    let (total, ret) = expansion
        .iter()
        .rev()
        .fold((0, zero_expr()), |acc, (sz, felt)| {
            (
                acc.0 + sz,
                acc.1 * Expression::Const(Constant::Base(1 << sz)) + felt.clone().into(),
            )
        });

    assert_eq!(total, SIZE);
    ret
}

// Constrains that lhs and rhs encode the same value of SIZE bits
// WARNING: Assumes that forall i, (lhs[i].1 < (2 ^ lhs[i].0))
// This needs to be constrained separately
fn constrain_eq_expr<const SIZE: usize>(
    lhs: &[(usize, Witness)],
    rhs: &[(usize, Witness)],
) -> Expression {
    expansion_expr::<SIZE>(lhs) - expansion_expr::<SIZE>(rhs)
}

struct Vars<const H: usize, const W: usize, const L: usize> {
    elems: Vec<(Witness, EvalExpression)>,
}

impl<const H: usize, const W: usize, const L: usize> Vars<H, W, L> {
    fn new(elems: Vec<(Witness, EvalExpression)>) -> Self {
        assert_eq!(elems.len(), H * W * L);
        Self { elems }
    }

    fn get(&self, h: usize, w: usize, l: usize) -> &(Witness, EvalExpression) {
        &self.elems[h * W * L + w * L + l]
    }

    fn get_mut(&mut self, h: usize, w: usize, l: usize) -> &mut (Witness, EvalExpression) {
        &mut self.elems[h * W * L + w * L + l]
    }

    fn set(&mut self, h: usize, w: usize, l: usize, value: (Witness, EvalExpression)) {
        self.elems[h * W * L + w * L + l] = value;
    }

    fn get_xz(&self, x: usize, z: usize) -> Vec<&(Witness, EvalExpression)> {
        (0..H).map(|h| self.get(h, x, z)).collect()
    }

    fn get_yz(&self, y: usize, z: usize) -> Vec<&(Witness, EvalExpression)> {
        (0..W).map(|w| self.get(y, w, z)).collect()
    }

    fn get_xy(&self, x: usize, y: usize) -> Vec<&(Witness, EvalExpression)> {
        (0..L).map(|l| self.get(x, y, l)).collect()
    }

    fn get_x(&self, x: usize) -> Vec<&(Witness, EvalExpression)> {
        (0..H)
            .flat_map(|h| (0..L).map(move |l| self.get(h, x, l)))
            .collect()
    }

    fn get_y(&self, y: usize) -> Vec<&(Witness, EvalExpression)> {
        (0..W)
            .flat_map(|w| (0..L).map(move |l| self.get(y, w, l)))
            .collect()
    }

    fn get_z(&self, z: usize) -> Vec<&(Witness, EvalExpression)> {
        (0..H)
            .flat_map(|h| (0..W).map(move |w| self.get(h, w, z)))
            .collect()
    }
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
        let final_output = chip.allocate_output_evals::<STATE_SIZE>();

        let cloned_evals =
            |v: &Vec<(Witness, EvalExpression)>| v.iter().map(|e| e.1.clone()).collect_vec();

        macro_rules! allocate_and_split {
            ($chip:expr, $total:expr, $( $size:expr ),* ) => {{
                let (witnesses, _) = $chip.allocate_wits_in_layer::<$total, 0>();
                let mut iter = witnesses.into_iter();
                (
                    $(
                        iter.by_ref().take($size).collect_vec(),
                    )*
                )
            }};
        }

        let (state, state8, c, c_aux, XOR_TABLE) =
            allocate_and_split!(chip, { 50 + 200 + 40 + 200 + 1000 }, 50, 200, 40, 200, 1000);
        // Check if the bit-expansion expressions match the words

        let state = Vars::new(state);

        let mut exprs: Vec<Expression> = vec![];
        let mut outputs: Vec<EvalExpression> = vec![];
        let mut xor_index = 0;

        let mut add_constraint = |expr: Expression| {
            exprs.push(expr);
            outputs.push(zero_eval());
        };

        let add_constraints = |exprs: &Vec<Expression>| {
            for expr in exprs {
                add_constraint(expr.clone());
            }
        };

        let mut constrain_eq = |lhs: Expression, rhs: Expression| {
            add_constraint(lhs - rhs);
        };

        // Assert that c == a xor b
        let constrain_xor = |c: Expression, a: Expression, b: Expression| {
            let key = (a * Expression::Const(Constant::Base((1 << 8))) + b);
            constrain_eq(key, XOR_TABLE[2 * xor_index].0.into());
            constrain_eq(c, XOR_TABLE[2 * xor_index + 1].0.into());
            xor_index += 1;
        };

        let state_to_state8 = {
            for i in 0..50 {
                let lhs = [(32, state[i].0)];
                let rhs: [(usize, Witness); 4] = from_fn(|j| (8, state8[i * 4 + j].0));
                // add_constraint(constrain_eq_expr::<32>(&lhs, &rhs));
            }
        };

        for i in 0..5 {
            constrain_eq(c_aux[i * 5].0.into(), state[i * 5].0.into());
            for j in 0..5 {}
        }

        // let zero_checks_expansions = (0..50usize)
        //     .into_iter()
        //     .map(|i| {
        //         let lhs = [(32, words[i].0)];
        //         let rhs: [(usize, Witness); 32] = from_fn(|j| (1, bits[32 * i + 31 - j].0));
        //         constrain_eq_expr::<32>(&lhs, &rhs)
        //     })
        //     .collect_vec();

        // // Check that elements of bits[] are indeed 0/1
        // let zero_checks_binary = (0..STATE_SIZE).into_iter().map(|i| {
        //     let bit = Expression::from(bits[i].0);
        //     bit.clone() * (bit - one_expr())
        // });

        // // Is this the correct args for outs when I want to force expr == 0?
        // let zero_evals =
        //     vec![EvalExpression::Linear(0, Constant::Base(0), Constant::Base(0)); 50 + STATE_SIZE];

        // let bits_copy = (0..STATE_SIZE)
        //     .into_iter()
        //     .map(|i| bits[i].0.clone().into())
        //     .collect_vec();
        // let exprs = chain!(zero_checks_expansions, zero_checks_binary, bits_copy).collect_vec();

        // chip.add_layer(Layer::new(
        //     "nobody cares".to_string(),
        //     LayerType::Zerocheck,
        //     exprs,
        //     vec![],
        //     cloned_evals(&chain!(words, bits).collect_vec()),
        //     vec![],
        //     chain!(zero_evals, final_output.to_vec()).collect_vec(),
        // ));
    }
}

pub struct KeccakTrace {
    // pub bits: [bool; STATE_SIZE],
    pub words: [u32; 2 * X * Y],
}

fn nest<E: ExtensionField>(v: &Vec<E::BaseField>) -> Vec<Vec<E::BaseField>> {
    v.clone().into_iter().map(|e| vec![e]).collect_vec()
}

impl<E> ProtocolWitnessGenerator<E> for KeccakLayout<E>
where
    E: ExtensionField,
{
    type Trace = KeccakTrace;

    fn phase1_witness(&self, phase1: Self::Trace) -> Vec<Vec<E::BaseField>> {
        let mut res = vec![vec![]; 2];
        res[0] = phase1
            .words
            .into_iter()
            .map(|b| E::BaseField::from(b as u64))
            .collect();
        res[1] = phase1
            .words
            .iter()
            .flat_map(|&word| (0..32).map(move |i| E::BaseField::from(((word >> i) & 1) as u64)))
            .collect();
        res
    }

    fn gkr_witness(&self, phase1: &[Vec<E::BaseField>], challenges: &[E]) -> GKRCircuitWitness<E> {
        let mut words = phase1[self.committed_bits_id].clone();
        let mut bits = phase1[1].clone();

        let n_layers = 100;
        let mut layer_wits = Vec::<LayerWitness<E>>::with_capacity(n_layers + 1);

        layer_wits.push(LayerWitness::new(
            nest::<E>(&chain!(words, bits).collect_vec()),
            vec![],
        ));

        // Assumes one input instance
        let total_witness_size: usize = layer_wits.iter().map(|layer| layer.bases.len()).sum();
        dbg!(total_witness_size);

        layer_wits.reverse();

        GKRCircuitWitness { layers: layer_wits }
    }
}

pub fn run_sequencer(state: [u32; 50], verify: bool, test: bool) -> () {
    let params = KeccakParams {};
    let (layout, chip) = KeccakLayout::build(params);
    let gkr_circuit = chip.gkr_circuit();

    // let bits = state
    //     .iter()
    //     .flat_map(|&word| (0..32).map(move |i| (word >> i) & 1))
    //     .collect::<Vec<u32>>();

    let phase1_witness = layout.phase1_witness(KeccakTrace {
        words: state.try_into().unwrap(),
    });
    let mut prover_transcript = BasicTranscript::<E>::new(b"protocol");

    // Omit the commit phase1 and phase2.
    let gkr_witness = layout.gkr_witness(&phase1_witness, &vec![]);

    let out_evals = {
        let point = Arc::new(vec![]);

        let witness = gkr_witness.layers[0]
            .bases
            .clone()
            .into_iter()
            .skip(50)
            .flatten()
            .collect_vec();

        witness
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

    if verify {
        {
            let mut verifier_transcript = BasicTranscript::<E>::new(b"protocol");

            gkr_circuit
                .verify(gkr_proof, &out_evals, &vec![], &mut verifier_transcript)
                .expect("GKR verify failed");

            // Omit the PCS opening phase.
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::{Rng, SeedableRng};

    use super::*;

    #[test]
    fn test_sequencer() {
        for _ in 0..3 {
            let random_u64: u64 = rand::random();
            // Use seeded rng for debugging convenience
            let mut rng = rand::rngs::StdRng::seed_from_u64(random_u64);
            let state: [u32; 50] = std::array::from_fn(|_| rng.gen());
            run_sequencer(state, true, true);
        }
    }
}
