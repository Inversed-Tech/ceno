use std::{array::from_fn, cmp::Ordering, marker::PhantomData, sync::Arc};

use crate::{
    ProtocolBuilder, ProtocolWitnessGenerator,
    chip::Chip,
    evaluation::{EvalExpression, PointAndEval},
    gkr::{
        GKRCircuitWitness, GKRProverOutput,
        layer::{Layer, LayerType, LayerWitness},
    },
};
use ndarray::{Array2, ArrayView, Ix2, Ix3, s};

use ff::Field;
use ff_ext::ExtensionField;
use goldilocks::{Goldilocks, GoldilocksExt2, SmallField};
use itertools::{Itertools, chain, iproduct, zip_eq};
use subprotocols::expression::{Constant, Expression, Witness};
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

struct ConstraintSystem {
    expressions: Vec<Expression>,
    expr_names: Vec<String>,
    evals: Vec<EvalExpression>,
    xor_table: Vec<Witness>,
    xor_index: usize,
    and_table: Vec<Witness>,
    and_index: usize,
}

impl ConstraintSystem {
    fn new(xor_table: Vec<Witness>, and_table: Vec<Witness>) -> Self {
        ConstraintSystem {
            expressions: vec![],
            evals: vec![],
            expr_names: vec![],
            xor_table,
            xor_index: 0,
            and_table,
            and_index: 0,
        }
    }

    fn add_constraint(&mut self, expr: Expression, name: String) {
        self.expressions.push(expr);
        self.evals.push(zero_eval());
        self.expr_names.push(name);
    }

    // fn add_constraints(&mut self, exprs: &Vec<Expression>) {
    //     for expr in exprs {
    //         self.add_constraint(expr.clone());
    //     }
    // }

    fn constrain_eq(&mut self, lhs: Expression, rhs: Expression, name: String) {
        self.add_constraint(lhs - rhs, name);
    }

    // Constrains that lhs and rhs encode the same value of SIZE bits
    // WARNING: Assumes that forall i, (lhs[i].1 < (2 ^ lhs[i].0))
    // This needs to be constrained separately
    fn constrain_reps_eq<const SIZE: usize>(
        &mut self,
        lhs: &[(usize, Witness)],
        rhs: &[(usize, Witness)],
        name: String,
    ) {
        self.add_constraint(
            expansion_expr::<SIZE>(lhs) - expansion_expr::<SIZE>(rhs),
            name,
        );
    }

    fn constrain_left_rotation64(
        &mut self,
        word8: &[Witness],
        wordX: &[(usize, Witness)],
        rotated_word8: &[Witness],
        delta: usize,
        label: String,
    ) {
        assert_eq!(word8.len(), 8);
        assert_eq!(rotated_word8.len(), 8);

        // Assert that the given split witnesses are correct for this delta
        let (sizes, chunks_rotation) = split_rotation64(delta);
        assert_eq!(sizes, wordX.iter().map(|e| e.0).collect_vec());

        // constrain the fact that rep8 and repX.rotate_left(chunks_rotation) are
        // the same 64 bitstring
        let mut helper = |rep8: &[Witness], repX: &[(usize, Witness)], chunks_rotation: usize| {
            // Do the same thing for the two 32-bit halves
            let mut repX = repX.to_owned();
            repX.rotate_right(chunks_rotation);

            for i in 0..2 {
                // The respective 4 elements in the byte representation
                let lhs = rep8[4 * i..4 * (i + 1)]
                    .iter()
                    .map(|wit| (8, wit.clone()))
                    .collect_vec();
                let cnt = repX.len() / 2;
                let rhs = &repX[cnt * i..cnt * (i + 1)];

                assert_eq!(rhs.iter().map(|e| e.0).sum::<usize>(), 32);

                self.constrain_reps_eq::<32>(
                    &lhs,
                    &rhs,
                    format!(
                        "rotation internal {label}, round {i}, rot: {chunks_rotation}, delta: {delta}, {:?}",
                        sizes
                    ),
                );
            }
        };

        helper(word8, wordX, 0);
        helper(rotated_word8, wordX, chunks_rotation);
    }

    // The prototype circuit acts on individual bits, so it has large witness size (1600 = 5 x 5 x 64 bits for every state rep)
    // This version described here stores Z-coordinate in words. This has size 5 x 5 x 2 (each Z coordinate/lane is stored in 2 felts)
    // And now instead of doing xor with expressions, it is done with lookups for chunks of 8 bits.

    fn constrain_xor8(&mut self, c: Expression, a: Expression, b: Expression, label: String) {
        let key = a * Expression::Const(Constant::Base(1 << 8)) + b;
        self.constrain_eq(
            key,
            self.xor_table[2 * self.xor_index].into(),
            label.clone(),
        );
        self.constrain_eq(c, self.xor_table[2 * self.xor_index + 1].into(), label);
        self.xor_index += 1;
    }

    fn constrain_and8(&mut self, c: Expression, a: Expression, b: Expression, label: String) {
        let key = a * Expression::Const(Constant::Base(1 << 8)) + b;
        self.constrain_eq(
            key,
            self.and_table[2 * self.and_index].into(),
            label.clone(),
        );
        self.constrain_eq(
            c,
            self.and_table[2 * self.and_index + 1].into(),
            label.clone(),
        );
        self.and_index += 1;
    }
}

fn not8_expr(expr: Expression) -> Expression {
    Expression::Const(Constant::Base(0xFF)) - expr
}

const ROUNDS: usize = 24;

const RC: [u64; ROUNDS] = [
    1u64,
    0x8082u64,
    0x800000000000808au64,
    0x8000000080008000u64,
    0x808bu64,
    0x80000001u64,
    0x8000000080008081u64,
    0x8000000000008009u64,
    0x8au64,
    0x88u64,
    0x80008009u64,
    0x8000000au64,
    0x8000808bu64,
    0x800000000000008bu64,
    0x8000000000008089u64,
    0x8000000000008003u64,
    0x8000000000008002u64,
    0x8000000000000080u64,
    0x800au64,
    0x800000008000000au64,
    0x8000000080008081u64,
    0x8000000000008080u64,
    0x80000001u64,
    0x8000000080008008u64,
];

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
        let final_output = chip.allocate_output_evals::<200>();

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

        #[allow(non_snake_case)]
        let (
            state,
            state8,
            c_aux,
            c_temp,
            c_rot,
            d,
            theta_output,
            rotation_witness,
            rhopi_output,
            nonlinear,
            chi_output,
            iota_output,
            AND_TABLE,
            XOR_TABLE,
        ) = allocate_and_split!(
            chip, 3264, 50, 200, 200, 20, 40, 40, 200, 98, 200, 200, 200, 200, 400, 1216
        );

        let total_witnesses =
            50 + 200 + 200 + 20 + 40 + 40 + 200 + 98 + 200 + 200 + 200 + 200 + 400 + 1216;
        dbg!(total_witnesses);
        assert_eq!(3264, total_witnesses);
        // println!("Total witnesses: {}", total_witnesses);

        // Lookups (both XOR/AND and keccak input) should be output. They don't need to be witness, they can be computed from
        // other witnesses. a + b * alfa + c * alfa^2 + beta (linear layer to apply this). Will there be witness for (a, b, c)?
        // Reuse from other witnesses where possible
        //
        // Question: if value X is argument to some lookup table, so for example we lookup XOR(X, something) => X is range-checked implicitly?
        // Ok.

        // Question: Trade-off between fewer layers and more layers?
        // Fewer layers => implies more witnesses? PCS more expensive than sumcheck

        let bases = chain!(
            state.clone(),  // state with 32-bit felts
            state8.clone(), // state with 8-bit felts
            c_aux.clone(),  // c array with 8-bit felts
            c_temp.clone(), // c with (1, 31) split for permutation
            c_rot.clone(),  // rotate_left(c, 1)
            d.clone(),      // d
            theta_output.clone(),
            rotation_witness.clone(),
            rhopi_output.clone(),
            nonlinear.clone(),
            chi_output.clone(),
            iota_output.clone(),
            AND_TABLE.clone(), // AND_TABLE lookup
            XOR_TABLE.clone()  // XOR_TABLE lookup
        )
        .collect_vec();
        // Check if the bit-expansion expressions match the words

        // ndarray crate

        let state: ArrayView<(Witness, EvalExpression), Ix3> =
            ArrayView::from_shape((5, 5, 2), &state).unwrap();

        let state8: ArrayView<(Witness, EvalExpression), Ix3> =
            ArrayView::from_shape((5, 5, 8), &state8).unwrap();

        let mut system = ConstraintSystem::new(
            XOR_TABLE.into_iter().map(|e| e.0).collect_vec(),
            AND_TABLE.into_iter().map(|e| e.0).collect_vec(),
        );

        for x in 0..5 {
            for y in 0..5 {
                for z in 0..2 {
                    // first rep: (32, value)
                    // second rep: (8, value1), (8, value2)... (8, value8)

                    let lhs = [(32, state[[x, y, z]].0)];
                    let rhs: [(usize, Witness); 4] = from_fn(|j| (8, state8[[x, y, 4 * z + j]].0));
                    system.constrain_reps_eq::<32>(
                        &lhs,
                        &rhs,
                        format!("state to state8: {x},{y},{z}"),
                    );
                }
            }
        }

        let c_aux: ArrayView<(Witness, EvalExpression), Ix3> =
            ArrayView::from_shape((5, 5, 8), &c_aux).unwrap();

        for i in 0..5 {
            for k in 0..8 {
                system.constrain_eq(
                    state8[[i, 0, k]].0.into(),
                    c_aux[[i, 0, k]].0.into(),
                    "init c_aux".to_string(),
                );
            }
            for j in 1..5 {
                // TODO see if it's worth using slicing
                for k in 0..8 {
                    system.constrain_xor8(
                        c_aux[[i, j, k]].0.into(),
                        c_aux[[i, j - 1, k]].0.into(),
                        state8[[i, j, k]].0.into(),
                        format!("c_aux{i},{j},{k}"),
                    );
                }
            }
        }

        // If I want to rotate 64 bits (X) with 1 to the left:
        // X := (1a, 31a, 1b, 31b) (4 different felts)
        // X := (8, 8, 8, 8, 8, 8, 8, 8)
        // Then rotation is just a permutation of these felts
        // rol(X, 1) = (31a, 1b, 31b, 1a)

        let c_temp: ArrayView<(Witness, EvalExpression), Ix2> =
            ArrayView::from_shape((5, 4), &c_temp).unwrap();
        let c_rot: ArrayView<(Witness, EvalExpression), Ix2> =
            ArrayView::from_shape((5, 8), &c_rot).unwrap();

        let (sizes, _) = split_rotation64(1);

        for i in 0..5 {
            system.constrain_left_rotation64(
                &c_aux.slice(s![i, 4, ..]).iter().map(|e| e.0).collect_vec(),
                &zip_eq(c_temp.slice(s![i, ..]).iter(), sizes.iter())
                    .map(|(e, sz)| (*sz, e.0))
                    .collect_vec(),
                &c_rot.slice(s![i, ..]).iter().map(|e| e.0).collect_vec(),
                1,
                "theta rotation 1".to_string(),
            );
        }

        let d: ArrayView<(Witness, EvalExpression), Ix2> =
            ArrayView::from_shape((5, 8), &d).unwrap();

        let theta_output: ArrayView<(Witness, EvalExpression), Ix3> =
            ArrayView::from_shape((5, 5, 8), &theta_output).unwrap();

        for i in 0..5 {
            for k in 0..8 {
                system.constrain_xor8(
                    d[[i, k]].0.into(),
                    c_aux[[(i + 5 - 1) % 5, 4, k]].0.into(),
                    c_rot[[(i + 1) % 5, k]].0.into(),
                    format!("d: {i}, {k}"),
                )
            }
        }

        for i in 0..5 {
            for j in 0..5 {
                for k in 0..8 {
                    system.constrain_xor8(
                        theta_output[[i, j, k]].0.into(),
                        state8[[i, j, k]].0.into(),
                        d[[i, k]].0.into(),
                        format!("theta_output: {i}, {j}, {k}"),
                    )
                }
            }
        }

        let rhopi_output: ArrayView<(Witness, EvalExpression), Ix3> =
            ArrayView::from_shape((5, 5, 8), &rhopi_output).unwrap();
        let mut rotation_witness = rotation_witness.iter();

        for i in 0..5 {
            for j in 0..5 {
                let arg = theta_output
                    .slice(s!(i, j, ..))
                    .iter()
                    .map(|e| e.0)
                    .collect_vec();
                let (sizes, _) = split_rotation64(ROTATION_CONSTANTS[j][i]);
                let many = sizes.len();
                let argX = zip_eq(sizes, rotation_witness.by_ref().take(many))
                    .map(|(sz, (wit, _))| (sz, wit.clone()))
                    .collect_vec();
                let arg_rotated = rhopi_output
                    .slice(s!(j, (2 * i + 3 * j) % 5, ..))
                    .iter()
                    .map(|e| e.0)
                    .collect_vec();
                system.constrain_left_rotation64(
                    &arg,
                    &argX,
                    &arg_rotated,
                    ROTATION_CONSTANTS[j][i],
                    format!("RHOPI {i}, {j}"),
                );
            }
        }

        let chi_output: ArrayView<(Witness, EvalExpression), Ix3> =
            ArrayView::from_shape((5, 5, 8), &chi_output).unwrap();

        let nonlinear: ArrayView<(Witness, EvalExpression), Ix3> =
            ArrayView::from_shape((5, 5, 8), &nonlinear).unwrap();

        for i in 0..5 {
            for j in 0..5 {
                for k in 0..8 {
                    system.constrain_and8(
                        nonlinear[[i, j, k]].0.into(),
                        not8_expr(rhopi_output[[(i + 1) % 5, j, k]].0.into()),
                        rhopi_output[[(i + 2) % 5, j, k]].0.into(),
                        format!("AND {i}, {j}, {k}"),
                    );

                    system.constrain_xor8(
                        chi_output[[i, j, k]].0.into(),
                        rhopi_output[[i, j, k]].0.into(),
                        nonlinear[[i, j, k]].0.into(),
                        format!("chi_output"),
                    );
                }
            }
        }

        let iota_output: ArrayView<(Witness, EvalExpression), Ix3> =
            ArrayView::from_shape((5, 5, 8), &iota_output).unwrap();

        for i in 0..5 {
            for j in 0..5 {
                if i == 0 && j == 0 {
                    for k in 0..8 {
                        system.constrain_xor8(
                            iota_output[[i, j, k]].0.into(),
                            chi_output[[i, j, k]].0.into(),
                            Expression::Const(Constant::Base(((RC[0] >> (k * 8)) & 0xFF) as i64)),
                            format!("iota"),
                        );
                    }
                } else {
                    for k in 0..8 {
                        system.constrain_eq(
                            iota_output[[i, j, k]].0.into(),
                            chi_output[[i, j, k]].0.into(),
                            "nothnig special".to_string(),
                        );
                    }
                }
            }
        }

        let ConstraintSystem {
            mut expressions,
            mut expr_names,
            mut evals,
            ..
        } = system;

        iota_output
            .into_iter()
            .enumerate()
            .map(|(i, val)| {
                expressions.push(val.0.into());
                expr_names.push(format!("iota_output {i}"));
                evals.push(final_output[i].clone());
            })
            .count();

        chip.add_layer(Layer::new(
            "Theta Layer".to_string(),
            LayerType::Zerocheck,
            expressions,
            vec![],
            bases.into_iter().map(|e| e.1).collect_vec(),
            vec![],
            evals,
            expr_names,
        ));
    }
}

pub struct KeccakTrace {
    // pub bits: [bool; STATE_SIZE],
    pub words: [u32; 2 * X * Y],
}

fn nest<E: ExtensionField>(v: &Vec<E::BaseField>) -> Vec<Vec<E::BaseField>> {
    v.clone().into_iter().map(|e| vec![e]).collect_vec()
}

fn u64s_to_felts<E: ExtensionField>(words: Vec<u64>) -> Vec<E::BaseField> {
    words
        .into_iter()
        .map(|word| E::BaseField::from(word as u64))
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Mask {
    size: usize,
    mask: u64,
}

impl Mask {
    fn new(size: usize, mask: u64) -> Self {
        if size < 64 {
            assert!(mask < (1 << size));
        }
        Self { size, mask }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct MaskRepresentation {
    rep: Vec<Mask>,
}

impl From<Mask> for (usize, u64) {
    fn from(mask: Mask) -> Self {
        (mask.size, mask.mask)
    }
}

impl From<(usize, u64)> for Mask {
    fn from(tuple: (usize, u64)) -> Self {
        Mask::new(tuple.0, tuple.1)
    }
}

impl From<MaskRepresentation> for Vec<(usize, u64)> {
    fn from(mask_rep: MaskRepresentation) -> Self {
        mask_rep.rep.into_iter().map(|mask| mask.into()).collect()
    }
}

impl From<Vec<(usize, u64)>> for MaskRepresentation {
    fn from(tuples: Vec<(usize, u64)>) -> Self {
        MaskRepresentation {
            rep: tuples.into_iter().map(|tuple| tuple.into()).collect(),
        }
    }
}

impl MaskRepresentation {
    fn new(masks: Vec<Mask>) -> Self {
        Self { rep: masks }
    }

    fn from_bits(bits: Vec<u64>, sizes: Vec<usize>) -> Self {
        assert_eq!(bits.len(), sizes.iter().sum::<usize>());
        let mut masks = Vec::new();
        let mut bit_iter = bits.into_iter();
        for size in sizes {
            let mut mask = 0;
            for i in 0..size {
                mask += (1 << i) * (bit_iter.next().unwrap() as u64);
            }
            masks.push(Mask::new(size, mask));
        }
        Self { rep: masks }
    }

    fn to_bits(&self) -> Vec<u64> {
        self.rep
            .iter()
            .flat_map(|mask| (0..mask.size).map(move |i| ((mask.mask >> i) & 1)))
            .collect()
    }

    fn convert(&self, new_sizes: Vec<usize>) -> Self {
        let bits = self.to_bits();
        Self::from_bits(bits, new_sizes)
    }

    fn masks(&self) -> Vec<u64> {
        self.rep.iter().map(|m| m.mask).collect_vec()
    }

    fn len(&self) -> usize {
        self.rep.len()
    }
}

fn split_rotation64(delta: usize) -> (Vec<usize>, usize) {
    let delta = delta % 64;

    if delta == 0 {
        return (vec![32, 32], 0);
    }

    match delta.cmp(&32) {
        Ordering::Less => (vec![32 - delta, delta, 32 - delta, delta], 1),
        Ordering::Equal => (vec![32, 32], 1),
        Ordering::Greater => (
            vec![32 - (delta - 32), delta - 32, 32 - (delta - 32), delta - 32],
            3,
        ),
    }
}

const ROTATION_CONSTANTS: [[usize; 5]; 5] = [
    [0, 1, 62, 28, 27],
    [36, 44, 6, 55, 20],
    [3, 10, 43, 25, 39],
    [41, 45, 15, 21, 8],
    [18, 2, 61, 56, 14],
];

impl<E> ProtocolWitnessGenerator<E> for KeccakLayout<E>
where
    E: ExtensionField,
{
    type Trace = KeccakTrace;

    fn phase1_witness(&self, phase1: Self::Trace) -> Vec<Vec<E::BaseField>> {
        let mut res = vec![vec![]; 2];
        res[0] = u64s_to_felts::<E>(phase1.words.into_iter().map(|e| e as u64).collect_vec());
        res
    }

    fn gkr_witness(&self, phase1: &[Vec<E::BaseField>], challenges: &[E]) -> GKRCircuitWitness<E> {
        let com_state = phase1[self.committed_bits_id].clone();

        let n_layers = 100;
        let mut layer_wits = Vec::<LayerWitness<E>>::with_capacity(n_layers + 1);

        fn conv64to8(input: u64) -> [u64; 8] {
            MaskRepresentation::new(vec![(64, input).into()])
                .convert(vec![8; 8])
                .masks()
                .try_into()
                .unwrap()
        }

        let state32 = com_state
            .into_iter()
            // TODO double check assumptions about canonical
            .map(|e| e.to_canonical_u64())
            .collect_vec();
        let mut state64 = [[0u64; 5]; 5];
        let mut state8 = [[[0u64; 8]; 5]; 5];

        let mut XOR_TABLE: Vec<u64> = vec![];
        let mut AND_TABLE: Vec<u64> = vec![];

        let mut add_xor = |a: u64, b: u64| {
            XOR_TABLE.push((a << 8) + b);
            XOR_TABLE.push(a ^ b);
        };

        let mut add_and = |a: u64, b: u64| {
            AND_TABLE.push((a << 8) + b);
            AND_TABLE.push(a & b);
        };

        zip_eq(iproduct!(0..5, 0..5), state32.iter().tuples())
            .map(|((x, y), (lo, hi))| {
                state64[x][y] = lo | (hi << 32);
                state8[x][y] = conv64to8(state64[x][y]);
            })
            .count();

        let mut c_aux64 = [[0u64; 5]; 5];
        let mut c_aux8 = [[[0u64; 8]; 5]; 5];

        for i in 0..5 {
            c_aux64[i][0] = state64[i][0];
            c_aux8[i][0] = conv64to8(c_aux64[i][0]);
            for j in 1..5 {
                c_aux64[i][j] = state64[i][j] ^ c_aux64[i][j - 1];
                c_aux8[i][j] = conv64to8(c_aux64[i][j]);

                for k in 0..8 {
                    add_xor(c_aux8[i][j - 1][k], state8[i][j][k]);
                }
            }
        }

        let mut c64 = [0u64; 5];
        let mut c8 = [[0u64; 8]; 5];

        for x in 0..5 {
            c64[x] = c_aux64[x][4];
            c8[x] = conv64to8(c64[x]);
        }

        let mut c_temp = [[0u64; 4]; 5];
        for i in 0..5 {
            c_temp[i] = MaskRepresentation::new(vec![(64, c64[i]).into()])
                .convert(vec![31, 1, 31, 1])
                .masks()
                .try_into()
                .unwrap();
        }

        let mut crot64 = [0u64; 5];
        let mut crot8 = [[0u64; 8]; 5];
        for i in 0..5 {
            crot64[i] = c64[i].rotate_left(1);
            crot8[i] = conv64to8(crot64[i]);
        }

        let mut d64 = [0u64; 5];
        let mut d8 = [[0u64; 8]; 5];
        for x in 0..5 {
            d64[x] = c64[(x + 4) % 5] ^ c64[(x + 1) % 5].rotate_left(1);
            d8[x] = conv64to8(d64[x]);
            for k in 0..8 {
                add_xor(c_aux8[(x + 4) % 5][4][k], crot8[(x + 1) % 5][k]);
            }
        }

        let mut theta_state64 = state64.clone();
        let mut theta_state8 = [[[0u64; 8]; 5]; 5];
        let mut rotation_witness = vec![];

        for x in 0..5 {
            for y in 0..5 {
                theta_state64[x][y] ^= d64[x];
                theta_state8[x][y] = conv64to8(theta_state64[x][y]);

                for k in 0..8 {
                    add_xor(state8[x][y][k], d8[x][k]);
                }

                let (sizes, _) = split_rotation64(ROTATION_CONSTANTS[y][x]);
                let rotwitness = MaskRepresentation::new(vec![(64, theta_state64[x][y]).into()])
                    .convert(sizes)
                    .masks();
                rotation_witness.extend(rotwitness);
            }
        }

        // Rho and Pi steps
        let mut rhopi_output64 = [[0u64; 5]; 5];
        let mut rhopi_output8 = [[[0u64; 8]; 5]; 5];

        for x in 0..5 {
            for y in 0..5 {
                rhopi_output64[y % 5][(2 * x + 3 * y) % 5] =
                    theta_state64[x][y].rotate_left(ROTATION_CONSTANTS[y][x] as u32);
                rhopi_output8[y % 5][(2 * x + 3 * y) % 5] =
                    conv64to8(rhopi_output64[y % 5][(2 * x + 3 * y) % 5]);
            }
        }

        // Chi step

        let mut nonlinear64 = [[0u64; 5]; 5];
        let mut nonlinear8 = [[[0u64; 8]; 5]; 5];
        for x in 0..5 {
            for y in 0..5 {
                nonlinear64[x][y] =
                    !rhopi_output64[(x + 1) % 5][y] & rhopi_output64[(x + 2) % 5][y];
                nonlinear8[x][y] = conv64to8(nonlinear64[x][y]);
                for k in 0..8 {
                    add_and(
                        0xFF - rhopi_output8[(x + 1) % 5][y][k],
                        rhopi_output8[(x + 2) % 5][y][k],
                    );
                }
            }
        }

        let mut chi_output64 = [[0u64; 5]; 5];
        let mut chi_output8 = [[[0u64; 8]; 5]; 5];
        for x in 0..5 {
            for y in 0..5 {
                chi_output64[x][y] = nonlinear64[x][y] ^ rhopi_output64[x][y];
                chi_output8[x][y] = conv64to8(chi_output64[x][y]);
                for k in 0..8 {
                    add_xor(rhopi_output8[x][y][k], nonlinear8[x][y][k])
                }
            }
        }

        // Iota step
        let mut iota_output64 = chi_output64.clone();
        let mut iota_output8 = [[[0u64; 8]; 5]; 5];
        iota_output64[0][0] ^= RC[0];

        for k in 0..8 {
            add_xor(chi_output8[0][0][k], RC[0] >> (k * 8) & 0xFF);
        }

        for x in 0..5 {
            for y in 0..5 {
                iota_output8[x][y] = conv64to8(iota_output64[x][y]);
            }
        }

        // dbg!(&AND_TABLE.len(), &XOR_TABLE.len());
        // println!("{}, {}", AND_TABLE.len(), XOR_TABLE.len());

        let all_wits64 = [
            state32,
            state8.into_iter().flatten().flatten().collect_vec(),
            c_aux8.into_iter().flatten().flatten().collect_vec(),
            c_temp.into_iter().flatten().collect_vec(),
            crot8.into_iter().flatten().collect_vec(),
            d8.into_iter().flatten().collect_vec(),
            theta_state8.into_iter().flatten().flatten().collect_vec(),
            rotation_witness,
            rhopi_output8.into_iter().flatten().flatten().collect_vec(),
            nonlinear8.into_iter().flatten().flatten().collect_vec(),
            chi_output8.into_iter().flatten().flatten().collect_vec(),
            iota_output8
                .clone()
                .into_iter()
                .flatten()
                .flatten()
                .collect_vec(),
            AND_TABLE,
            XOR_TABLE,
        ];

        let sizes = all_wits64.iter().map(|e| e.len()).collect_vec();
        dbg!(&sizes);

        let all_wits = nest::<E>(
            &all_wits64
                .into_iter()
                .flat_map(|v| u64s_to_felts::<E>(v))
                .collect_vec(),
        );

        layer_wits.push(LayerWitness::new(all_wits, vec![]));

        let final_output = nest::<E>(&u64s_to_felts::<E>(
            iota_output8.into_iter().flatten().flatten().collect_vec(),
        ));

        layer_wits.push(LayerWitness::new(final_output, vec![]));

        GKRCircuitWitness { layers: layer_wits }
    }
}

pub fn run_sequencer(state: [u32; 50], verify: bool, test: bool) -> () {
    let params = KeccakParams {};
    let (layout, chip) = KeccakLayout::build(params);
    let gkr_circuit = chip.gkr_circuit();

    let state_mask32 =
        MaskRepresentation::from(state.into_iter().map(|e| (32, e as u64)).collect_vec());

    let state_mask64 = state_mask32.convert(vec![64; 25]);
    let state_mask1 = state_mask32.convert(vec![1; 1600]);

    let phase1_witness = layout.phase1_witness(KeccakTrace {
        words: state.try_into().unwrap(),
    });
    let mut prover_transcript = BasicTranscript::<E>::new(b"protocol");

    // Omit the commit phase1 and phase2.
    let gkr_witness = layout.gkr_witness(&phase1_witness, &vec![]);

    let out_evals = {
        let point = Arc::new(vec![]);
        let iota_output = gkr_witness.layers[1]
            .bases
            .clone()
            .into_iter()
            .flatten()
            .collect_vec();

        iota_output
            .into_iter()
            .map(|elem| PointAndEval {
                point: point.clone(),
                eval: GoldilocksExt2::new_from_base(&[elem, Goldilocks::ZERO]),
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

    #[test]
    fn test_mask_representation_from_bits() {
        let bits = vec![1, 0, 1, 1, 0, 1, 0, 0];
        let sizes = vec![3, 5];
        let mask_rep = MaskRepresentation::from_bits(bits.clone(), sizes.clone());
        assert_eq!(mask_rep.rep.len(), 2);
        assert_eq!(mask_rep.rep[0], Mask::new(3, 0b101));
        assert_eq!(mask_rep.rep[1], Mask::new(5, 0b00101));
    }

    #[test]
    fn test_mask_representation_to_bits() {
        let masks = vec![Mask::new(3, 0b101), Mask::new(5, 0b00101)];
        let mask_rep = MaskRepresentation::new(masks);
        let bits = mask_rep.to_bits();
        assert_eq!(bits, vec![1, 0, 1, 1, 0, 1, 0, 0]);
    }

    #[test]
    fn test_mask_representation_convert() {
        let bits = vec![1, 0, 1, 1, 0, 1, 0, 0];
        let sizes = vec![3, 5];
        let mask_rep = MaskRepresentation::from_bits(bits.clone(), sizes.clone());
        let new_sizes = vec![4, 4];
        let new_mask_rep = mask_rep.convert(new_sizes);
        assert_eq!(new_mask_rep.rep.len(), 2);
        assert_eq!(new_mask_rep.rep[0], Mask::new(4, 0b1101));
        assert_eq!(new_mask_rep.rep[1], Mask::new(4, 0b0010));
    }
}
