use crate::{
    circuit_builder::{CircuitBuilder, ConstraintSystem},
    error::ZKVMError,
    expression::Expression,
    instructions::{Instruction, riscv::dummy::LargeEcallDummy},
    state::StateCircuit,
    tables::{RMMCollections, TableCircuit},
    witness::LkMultiplicity,
};
use ceno_emul::{CENO_PLATFORM, KeccakSpec, Platform, StepRecord};
use ff_ext::ExtensionField;
use gkr_iop::{
    ProtocolWitnessGenerator,
    precompiles::{KeccakLayout, KeccakTrace},
};
use itertools::{Itertools, chain};
use mpcs::PolynomialCommitmentScheme;
use multilinear_extensions::{
    mle::DenseMultilinearExtension, virtual_poly::ArcMultilinearExtension,
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use std::collections::{BTreeMap, HashMap};
use strum_macros::EnumIter;
use sumcheck::structs::IOPProverMessage;
use witness::RowMajorMatrix;

pub struct TowerProver;

#[derive(Clone, Serialize, Deserialize)]
#[serde(bound(
    serialize = "E::BaseField: Serialize",
    deserialize = "E::BaseField: DeserializeOwned"
))]
pub struct TowerProofs<E: ExtensionField> {
    pub proofs: Vec<Vec<IOPProverMessage<E>>>,
    // specs -> layers -> evals
    pub prod_specs_eval: Vec<Vec<Vec<E>>>,
    // specs -> layers -> point
    #[serde(skip)] // verifier can derive points itself
    pub prod_specs_points: Vec<Vec<Point<E>>>,
    // specs -> layers -> evals
    pub logup_specs_eval: Vec<Vec<Vec<E>>>,
    // specs -> layers -> point
    #[serde(skip)] // verifier can derive points itself
    pub logup_specs_points: Vec<Vec<Point<E>>>,
}

pub struct TowerProverSpec<'a, E: ExtensionField> {
    pub witness: Vec<Vec<ArcMultilinearExtension<'a, E>>>,
}

pub type WitnessId = u16;
pub type ChallengeId = u16;

#[derive(Copy, Clone, Debug, EnumIter, PartialEq, Eq, Hash)]
pub enum ROMType {
    U5 = 0,      // 2^5 = 32
    U8,          // 2^8 = 256
    U14,         // 2^14 = 16,384
    U16,         // 2^16 = 65,536
    And,         // a & b where a, b are bytes
    Or,          // a | b where a, b are bytes
    Xor,         // a ^ b where a, b are bytes
    Ltu,         // a <(usign) b where a, b are bytes and the result is 0/1.
    Pow,         // a ** b where a is 2 and b is 5-bit value
    Instruction, // Decoded instruction from the fixed program.
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum RAMType {
    GlobalState,
    Register,
    Memory,
}

/// A point is a vector of num_var length
pub type Point<F> = Vec<F>;

/// A point and the evaluation of this point.
#[derive(Clone, Debug, PartialEq)]
pub struct PointAndEval<F> {
    pub point: Point<F>,
    pub eval: F,
}

impl<E: ExtensionField> Default for PointAndEval<E> {
    fn default() -> Self {
        Self {
            point: vec![],
            eval: E::ZERO,
        }
    }
}

impl<F: Clone> PointAndEval<F> {
    /// Construct a new pair of point and eval.
    /// Caller gives up ownership
    pub fn new(point: Point<F>, eval: F) -> Self {
        Self { point, eval }
    }

    /// Construct a new pair of point and eval.
    /// Performs deep copy.
    pub fn new_from_ref(point: &Point<F>, eval: &F) -> Self {
        Self {
            point: (*point).clone(),
            eval: eval.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProvingKey<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> {
    pub fixed_traces: Option<Vec<DenseMultilinearExtension<E>>>,
    pub fixed_commit_wd: Option<PCS::CommitmentWithWitness>,
    pub vk: VerifyingKey<E, PCS>,
}

impl<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> ProvingKey<E, PCS> {
    pub fn get_cs(&self) -> &ConstraintSystem<E> {
        self.vk.get_cs()
    }
}

#[derive(Clone, Debug)]
pub struct VerifyingKey<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> {
    pub(crate) cs: ConstraintSystem<E>,
    pub fixed_commit: Option<PCS::Commitment>,
}

impl<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> VerifyingKey<E, PCS> {
    pub fn get_cs(&self) -> &ConstraintSystem<E> {
        &self.cs
    }
}

#[derive(Clone, Debug)]
pub struct GKRIOPProvingKey<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>, State> {
    pub fixed_traces: Option<Vec<DenseMultilinearExtension<E>>>,
    pub fixed_commit_wd: Option<PCS::CommitmentWithWitness>,
    pub vk: GKRIOPVerifyingKey<E, PCS, State>,
}

impl<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>, State: Default> Default
    for GKRIOPProvingKey<E, PCS, State>
{
    fn default() -> Self {
        Self {
            fixed_traces: None,
            fixed_commit_wd: None,
            vk: GKRIOPVerifyingKey::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct GKRIOPVerifyingKey<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>, State> {
    pub(crate) state: State,
    pub fixed_commit: Option<PCS::Commitment>,
}

impl<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>, State: Default> Default
    for GKRIOPVerifyingKey<E, PCS, State>
{
    fn default() -> Self {
        Self {
            state: State::default(),
            fixed_commit: None,
        }
    }
}

impl<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>, State>
    GKRIOPVerifyingKey<E, PCS, State>
{
    pub fn get_state(&self) -> &State {
        &self.state
    }
}

#[derive(Clone, Default, Debug)]
pub struct KeccakGKRIOP<E> {
    pub chip: gkr_iop::chip::Chip,
    pub layout: KeccakLayout<E>,
}

impl<E: ExtensionField> KeccakGKRIOP<E> {
    pub fn key_gen<PCS: PolynomialCommitmentScheme<E>>(
        self,
        pp: &PCS::ProverParam,
        fixed_traces: Option<RowMajorMatrix<E::BaseField>>,
    ) -> GKRIOPProvingKey<E, PCS, KeccakGKRIOP<E>> {
        // transpose from row-major to column-major
        let fixed_traces_polys = fixed_traces.as_ref().map(|rmm| rmm.to_mles());

        let fixed_commit_wd = fixed_traces.map(|traces| PCS::batch_commit(pp, traces).unwrap());
        let fixed_commit = fixed_commit_wd.as_ref().map(PCS::get_pure_commitment);

        GKRIOPProvingKey {
            fixed_traces: fixed_traces_polys,
            fixed_commit_wd,
            vk: GKRIOPVerifyingKey {
                state: self,
                fixed_commit,
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProgramParams {
    pub platform: Platform,
    pub program_size: usize,
    pub pub_io_len: usize,
    pub static_memory_len: usize,
}

impl Default for ProgramParams {
    fn default() -> Self {
        ProgramParams {
            platform: CENO_PLATFORM,
            program_size: (1 << 14),
            pub_io_len: (1 << 2),
            static_memory_len: (1 << 16),
        }
    }
}

#[derive(Clone)]
pub struct ZKVMConstraintSystem<E: ExtensionField> {
    pub(crate) circuit_css: BTreeMap<String, ConstraintSystem<E>>,
    pub(crate) initial_global_state_expr: Expression<E>,
    pub(crate) finalize_global_state_expr: Expression<E>,
    pub keccak_gkr_iop: KeccakGKRIOP<E>,
    pub params: ProgramParams,
}

impl<E: ExtensionField> Default for ZKVMConstraintSystem<E> {
    fn default() -> Self {
        ZKVMConstraintSystem {
            circuit_css: BTreeMap::new(),
            initial_global_state_expr: Expression::ZERO,
            finalize_global_state_expr: Expression::ZERO,
            params: ProgramParams::default(),
            keccak_gkr_iop: KeccakGKRIOP::default(),
        }
    }
}

impl<E: ExtensionField> ZKVMConstraintSystem<E> {
    pub fn new_with_platform(params: ProgramParams) -> Self {
        ZKVMConstraintSystem {
            params,
            ..Default::default()
        }
    }

    pub fn register_keccakf_circuit(
        &mut self,
    ) -> <LargeEcallDummy<E, KeccakSpec> as Instruction<E>>::InstructionConfig {
        // Add GKR-IOP instance
        let params = gkr_iop::precompiles::KeccakParams {};
        let (layout, chip) = <KeccakLayout<E> as gkr_iop::ProtocolBuilder>::build(params);
        self.keccak_gkr_iop = KeccakGKRIOP { layout, chip };

        self.register_opcode_circuit::<LargeEcallDummy<E, KeccakSpec>>()
    }

    pub fn register_opcode_circuit<OC: Instruction<E>>(&mut self) -> OC::InstructionConfig {
        let mut cs = ConstraintSystem::new(|| format!("riscv_opcode/{}", OC::name()));
        let mut circuit_builder =
            CircuitBuilder::<E>::new_with_params(&mut cs, self.params.clone());
        let config = OC::construct_circuit(&mut circuit_builder).unwrap();
        assert!(self.circuit_css.insert(OC::name(), cs).is_none());

        config
    }

    pub fn register_table_circuit<TC: TableCircuit<E>>(&mut self) -> TC::TableConfig {
        let mut cs = ConstraintSystem::new(|| format!("riscv_table/{}", TC::name()));
        let mut circuit_builder =
            CircuitBuilder::<E>::new_with_params(&mut cs, self.params.clone());
        let config = TC::construct_circuit(&mut circuit_builder).unwrap();
        assert!(self.circuit_css.insert(TC::name(), cs).is_none());

        config
    }

    pub fn register_global_state<SC: StateCircuit<E>>(&mut self) {
        let mut cs = ConstraintSystem::new(|| "riscv_state");
        let mut circuit_builder =
            CircuitBuilder::<E>::new_with_params(&mut cs, self.params.clone());
        self.initial_global_state_expr =
            SC::initial_global_state(&mut circuit_builder).expect("global_state_in failed");
        self.finalize_global_state_expr =
            SC::finalize_global_state(&mut circuit_builder).expect("global_state_out failed");
    }

    pub fn get_css(&self) -> &BTreeMap<String, ConstraintSystem<E>> {
        &self.circuit_css
    }

    pub fn get_cs(&self, name: &String) -> Option<&ConstraintSystem<E>> {
        self.circuit_css.get(name)
    }
}

#[derive(Default, Clone)]
pub struct ZKVMFixedTraces<E: ExtensionField> {
    pub circuit_fixed_traces: BTreeMap<String, Option<RowMajorMatrix<E::BaseField>>>,
}

impl<E: ExtensionField> ZKVMFixedTraces<E> {
    pub fn register_keccakf_circuit(&mut self, _cs: &ZKVMConstraintSystem<E>) {
        assert!(
            self.circuit_fixed_traces
                .insert(LargeEcallDummy::<E, KeccakSpec>::name(), None)
                .is_none()
        );
    }

    pub fn register_opcode_circuit<OC: Instruction<E>>(&mut self, _cs: &ZKVMConstraintSystem<E>) {
        assert!(self.circuit_fixed_traces.insert(OC::name(), None).is_none());
    }

    pub fn register_table_circuit<TC: TableCircuit<E>>(
        &mut self,
        cs: &ZKVMConstraintSystem<E>,
        config: &TC::TableConfig,
        input: &TC::FixedInput,
    ) {
        let cs = cs.get_cs(&TC::name()).expect("cs not found");
        assert!(
            self.circuit_fixed_traces
                .insert(
                    TC::name(),
                    Some(TC::generate_fixed_traces(config, cs.num_fixed, input)),
                )
                .is_none()
        );
    }
}

#[derive(Default, Clone)]
pub struct ZKVMWitnesses<E: ExtensionField> {
    keccak_phase1wit: Vec<Vec<E::BaseField>>,
    witnesses_opcodes: BTreeMap<String, RowMajorMatrix<E::BaseField>>,
    witnesses_tables: BTreeMap<String, RMMCollections<E::BaseField>>,
    lk_mlts: BTreeMap<String, LkMultiplicity>,
    combined_lk_mlt: Option<Vec<HashMap<u64, usize>>>,
}

impl<E: ExtensionField> ZKVMWitnesses<E> {
    pub fn get_opcode_witness(&self, name: &String) -> Option<&RowMajorMatrix<E::BaseField>> {
        self.witnesses_opcodes.get(name)
    }

    pub fn get_table_witness(&self, name: &String) -> Option<&RMMCollections<E::BaseField>> {
        self.witnesses_tables.get(name)
    }

    pub fn get_lk_mlt(&self, name: &String) -> Option<&LkMultiplicity> {
        self.lk_mlts.get(name)
    }

    pub fn assign_keccakf_circuit(
        &mut self,
        css: &ZKVMConstraintSystem<E>,
        config: &<LargeEcallDummy<E, KeccakSpec> as Instruction<E>>::InstructionConfig,
        records: Vec<StepRecord>,
    ) -> Result<(), ZKVMError> {
        // Ugly copy paste from assign_opcode_circuit, but we need to use the row major matrix
        let cs = css
            .get_cs(&LargeEcallDummy::<E, KeccakSpec>::name())
            .unwrap();
        let (witness, logup_multiplicity) = LargeEcallDummy::<E, KeccakSpec>::assign_instances(
            config,
            cs.num_witin as usize,
            records,
        )?;

        // Intercept row-major matrix, convert into KeccakTrace and obtain phase1_wit
        self.keccak_phase1wit = css
            .keccak_gkr_iop
            .layout
            .phase1_witness(KeccakTrace::from(witness.clone()));

        assert!(
            self.witnesses_opcodes
                .insert(LargeEcallDummy::<E, KeccakSpec>::name(), witness)
                .is_none()
        );
        assert!(
            !self
                .witnesses_tables
                .contains_key(&LargeEcallDummy::<E, KeccakSpec>::name())
        );
        assert!(
            self.lk_mlts
                .insert(LargeEcallDummy::<E, KeccakSpec>::name(), logup_multiplicity)
                .is_none()
        );

        Ok(())
    }

    pub fn assign_opcode_circuit<OC: Instruction<E>>(
        &mut self,
        cs: &ZKVMConstraintSystem<E>,
        config: &OC::InstructionConfig,
        records: Vec<StepRecord>,
    ) -> Result<(), ZKVMError> {
        assert!(self.combined_lk_mlt.is_none());

        let cs = cs.get_cs(&OC::name()).unwrap();
        let (witness, logup_multiplicity) =
            OC::assign_instances(config, cs.num_witin as usize, records)?;
        assert!(self.witnesses_opcodes.insert(OC::name(), witness).is_none());
        assert!(!self.witnesses_tables.contains_key(&OC::name()));
        assert!(
            self.lk_mlts
                .insert(OC::name(), logup_multiplicity)
                .is_none()
        );

        Ok(())
    }

    // merge the multiplicities in each opcode circuit into one
    pub fn finalize_lk_multiplicities(&mut self, is_keep_raw_lk_mlts: bool) {
        assert!(self.combined_lk_mlt.is_none());
        assert!(!self.lk_mlts.is_empty());

        let mut combined_lk_mlt = vec![];
        let keys = self.lk_mlts.keys().cloned().collect_vec();
        for name in keys {
            let lk_mlt = if is_keep_raw_lk_mlts {
                // mock prover needs the lk_mlt for processing, so we do not remove it
                self.lk_mlts
                    .get(&name)
                    .unwrap()
                    .deep_clone()
                    .into_finalize_result()
            } else {
                self.lk_mlts.remove(&name).unwrap().into_finalize_result()
            };

            if combined_lk_mlt.is_empty() {
                combined_lk_mlt = lk_mlt.to_vec();
            } else {
                combined_lk_mlt
                    .iter_mut()
                    .zip_eq(lk_mlt.iter())
                    .for_each(|(m1, m2)| {
                        for (key, value) in m2 {
                            *m1.entry(*key).or_insert(0) += value;
                        }
                    });
            }
        }

        self.combined_lk_mlt = Some(combined_lk_mlt);
    }

    pub fn assign_table_circuit<TC: TableCircuit<E>>(
        &mut self,
        cs: &ZKVMConstraintSystem<E>,
        config: &TC::TableConfig,
        input: &TC::WitnessInput,
    ) -> Result<(), ZKVMError> {
        assert!(self.combined_lk_mlt.is_some());
        let cs = cs.get_cs(&TC::name()).unwrap();
        let witness = TC::assign_instances(
            config,
            cs.num_witin as usize,
            cs.num_structural_witin as usize,
            self.combined_lk_mlt.as_ref().unwrap(),
            input,
        )?;
        assert!(self.witnesses_tables.insert(TC::name(), witness).is_none());
        assert!(!self.witnesses_opcodes.contains_key(&TC::name()));

        Ok(())
    }

    /// Iterate opcode circuits, then table circuits, sorted by name.
    pub fn into_iter_sorted(
        self,
    ) -> impl Iterator<Item = (String, Vec<RowMajorMatrix<E::BaseField>>)> {
        chain(
            self.witnesses_opcodes
                .into_iter()
                .map(|(name, witnesses)| (name, vec![witnesses])),
            self.witnesses_tables
                .into_iter()
                .map(|(name, witnesses)| (name, witnesses.to_vec())),
        )
    }
}

#[derive(Debug)]
pub struct ZKVMProvingKey<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> {
    pub pp: PCS::ProverParam,
    pub vp: PCS::VerifierParam,
    // pk for opcode and table circuits
    pub circuit_pks: BTreeMap<String, ProvingKey<E, PCS>>,
    pub keccak_pk: GKRIOPProvingKey<E, PCS, KeccakGKRIOP<E>>,

    // expression for global state in/out
    pub initial_global_state_expr: Expression<E>,
    pub finalize_global_state_expr: Expression<E>,
}

impl<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> ZKVMProvingKey<E, PCS> {
    pub(crate) fn new(pp: PCS::ProverParam, vp: PCS::VerifierParam) -> Self {
        Self {
            pp,
            vp,
            circuit_pks: BTreeMap::new(),
            keccak_pk: GKRIOPProvingKey::default(),
            initial_global_state_expr: Expression::ZERO,
            finalize_global_state_expr: Expression::ZERO,
        }
    }
}

impl<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> ZKVMProvingKey<E, PCS> {
    pub fn get_vk(&self) -> ZKVMVerifyingKey<E, PCS> {
        ZKVMVerifyingKey {
            vp: self.vp.clone(),
            circuit_vks: self
                .circuit_pks
                .iter()
                .map(|(name, pk)| (name.clone(), pk.vk.clone()))
                .collect(),
            // expression for global state in/out
            initial_global_state_expr: self.initial_global_state_expr.clone(),
            finalize_global_state_expr: self.finalize_global_state_expr.clone(),
        }
    }
}

#[derive(Clone)]
pub struct ZKVMVerifyingKey<E: ExtensionField, PCS: PolynomialCommitmentScheme<E>> {
    pub vp: PCS::VerifierParam,
    // vk for opcode and table circuits
    pub circuit_vks: BTreeMap<String, VerifyingKey<E, PCS>>,
    // expression for global state in/out
    pub initial_global_state_expr: Expression<E>,
    pub finalize_global_state_expr: Expression<E>,
}
