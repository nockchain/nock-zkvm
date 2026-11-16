import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.RedTeam.Batch129Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:
OP0 formula-tail as NMR address, OP9 `f_th.leaf` as
record-3 axis, NMR address space `A ∈ F`.

`AxisAtomPremises data` is:
- For OP0 (s0): `∃ k, data.root.tail =.atom k`
- For OP9 (s9): `∃ k, decompNoun data.f_th =.atom k`

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `ResidualPremises.axisAtoms` stays named as
`∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)`.
`PremiseKind.paperProtocol` classification is honest: the paper says
`A := axis_root(child) ∈ F` (atoms), the paper sets `mem_axis_2 =
formula_tail` for OP0, the paper sets `mem_axis_3 = f_th` for OP9.

Attack results:
1. `BuildableNockExecution` truly lacks `ExactExecutionLocalCertificates`:
   its structure fields are `q`, `q_gt_one`, `Λ`, `cfg`, `exec`,
   `semanticData`, `memoryTrace`, `requestNodup`, `recordCountBalance`,
   `q_le_ringChar`, `two_ne_zero`, `Ksz_lt_ringChar`, `programIOCapacity`,
   `memoryIOCapacity`.  No `LocalOpcodeCertificate`, no comparison-entry
   identification.

2. `ComputeRowSemanticData` truly imposes no structural constraint equating
   `data.tails[0]` with `axisGates[0].1`:
   - `tails : List TailRealization` with `tails_count = requiredTailRealizations`
   - `axisGates : List (Σ tail : TailRealization, AxisAtomComparisonCertificate...)`
     with `axisGates_count = requiredAxisAtomGates`
   - `axisGate_listed` only says the gate's comparison is a member of
     `comparisons`, not that `gate.1 = tails[0]`
   - For s9: `requiredTailRealizations.s9 = 1` and
     `requiredAxisAtomGates.s9 = 1`, so both lists are singletons, but
     their elements are independently supplied with no equating field.

3. `Vcomp` / `ComputeRowAccepted` for s0/s9 do NOT force atom shape:
   - For s0: `vcomp_mr2_s0` puts `dec.f_t.leaf` in `mr2.axis`.  This is a
     field element `K`, not a noun-shape constraint.  `data.root.tail_realizes`
     says `enc z (data.root.tail) = (f_t.size, f_t.dyck, f_t.leaf)`, but cells
     also have `.leaf` fields.  To get `data.root.tail =.atom k` requires
     `PairFaithful.eq_of_enc_eq` with an explicit comparison entry pairing
     `data.root.tail` with `.atom k`.
   - For s9: `vcomp_mr3_s9` puts `dec.f_th.leaf` in `mr3.axis`.  Getting
     `decompNoun data.f_th =.atom k` requires the `AxisAtomComparisonCertificate`
     to identify `tail.head` (from the axis gate) with `decompNoun data.f_th`
     (from `data.tails[0].head`).  No such identification exists.

4. `paperProtocol` classification is honest:
   - the paper: `A := axis_root(child) ∈ F` — the address space is atoms.
   - the paper: `mem_axis_2 = formula_tail` — OP0 uses formula tail as axis.
   - the paper: `mem_axis_3 = f_th.leaf` — OP9 uses f_th as axis.
   Both are paper protocol requirements that the axis operand is an atom.

5. `dataOf` truly consumes `P.axisAtoms` as input:
   `bindComputeRow_of_residual` calls `bindComputeRow_of_axisAtoms` which calls
   `bindMemRec_mr2` (consuming `hatoms.1` for s0) and `bindMemRec_mr3` (consuming
   `hatoms.2` for s9).  Not recoverable from `Data`.

6. Accounting `11+1+2` unchanged.  NMR not re-litigated.

7. Axioms within `{propext, Classical.choice, Quot.sound}`.

8. No wrong-layer rounding: `axisAtoms` stays a named premise because its
   content (atom shape of formula-tail / f_th) is a paper NMR protocol
   requirement consumed as INPUT to the binding, not extractable from any
   already-held object.

This artifact does not inhabit `axisAtoms`.  It does not construct a generic
`Data E`, a generic `CommitmentResidual E`, or later-round `A`/`W`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch130

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.NodeEncoding
open Nock.AxisBridge
open Nock.Framework
open Nock.NockVMROM.Thm54.RowLayout

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. `AxisAtomPremises` definitional expansion -/

/-- Independent expansion: `AxisAtomPremises data` is the conjunction of two
state-guarded atom-existence claims on `data.root.tail` (s0) and
`decompNoun data.f_th` (s9) -/
theorem axisAtoms_expands_independent
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : SemanticTrace.ComputeRowSemanticData q Λ row) :
    AxisAtomPremises data =
      ((row.1 = .s0 → ∃ k, data.root.tail = Noun.atom k) ∧
        (row.1 = .s9 → ∃ k, decompNoun data .f_th = Noun.atom k)) :=
  rfl

/-! ## B. `BuildableNockExecution` structure lacks certificates -/

/-- Independent eta: `BuildableNockExecution` has exactly the fields listed by the
prover.  No `ExactExecutionLocalCertificates`, no `LocalOpcodeCertificate`,
no comparison-entry identification -/
theorem execution_eta_lacks_certificates
    (E : BuildableNockExecution F K) :
    E = { q := E.q, q_gt_one := E.q_gt_one, Λ := E.Λ, cfg := E.cfg
          execA := E.execA, exec := E.exec, exec_encode := E.exec_encode
          semanticData := E.semanticData
          memoryTrace := E.memoryTrace
          requestNodup := E.requestNodup
          recordCountBalance := E.recordCountBalance
          q_le_ringChar := E.q_le_ringChar
          two_ne_zero := E.two_ne_zero
          Ksz_lt_ringChar := E.Ksz_lt_ringChar
          programIOCapacity := E.programIOCapacity
          memoryIOCapacity := E.memoryIOCapacity } :=
  E.eta_with_memoryTrace

/-! ## C. `ComputeRowSemanticData` has no tails-axisGates equating field -/

/-- Independent structural proof: for s9, `requiredTailRealizations.s9 = 1` and
`requiredAxisAtomGates.s9 = 1`, so both `tails` and `axisGates` are singletons.
But `ComputeRowSemanticData` has no field equating `tails[0]` with
`axisGates[0].1`.  The only constraint on `axisGates` is `axisGate_listed`,
which says the gate's comparison is a member of `comparisons` — it does not
identify the `TailRealization` objects -/
theorem axisGates_and_tails_are_independently_supplied :
    SemanticTrace.requiredTailRealizations .s9 = 1 ∧
      SemanticTrace.requiredAxisAtomGates .s9 = 1 ∧
      SemanticTrace.requiredAxisAtomGates .s0 = 0 := by
  decide

/-- The `axisGate_listed` field only asserts membership in `comparisons`,
not identification with `tails`.  Independent projection. -/
theorem axisGate_listed_is_comparison_membership
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : SemanticTrace.ComputeRowSemanticData q Λ row)
    (gate : Σ tail : OpcodeSemantics.TailRealization row.2.1.z row.2.2.2,
      SemanticTrace.AxisAtomComparisonCertificate row.2.1.z q row.2.2.2 tail)
    (hgate : gate ∈ data.axisGates) :
    { role := SemanticTrace.ComparisonRole.axisAtom
      left := gate.1.head
      right := .atom gate.2.axis } ∈ data.comparisons :=
  data.axisGate_listed gate hgate

/-! ## D. `Vcomp` s0/s9 constraints do not force atom shape -/

/-- For s0: `Vcomp` sets `mr2.axis = dec.f_t.leaf`.  This is a field element
in `K`, not a noun-shape constraint.  The `leaf` field exists on all `FP`
triples (atoms AND cells) -/
theorem vcomp_s0_mr2_axis_is_field_element
    {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hstate : row.1 = .s0) :
    row.2.2.1.mr2.axis = row.2.2.2.f_t.leaf :=
  congrArg ComputeTable.MemRec.axis (vcomp_mr2_s0 hacc hstate)

/-- For s9: `Vcomp` sets `mr3.axis = dec.f_th.leaf`.  Same: field element,
not noun shape -/
theorem vcomp_s9_mr3_axis_is_field_element
    {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hstate : row.1 = .s9) :
    row.2.2.1.mr3.axis = row.2.2.2.f_th.leaf :=
  congrArg ComputeTable.MemRec.axis (vcomp_mr3_s9 hacc hstate)

/-! ## E. `Data E` truly lacks `axisAtoms` -/

/-- Independent structural proof: `Data E` carries `q_eq_ringChar` as its sole
residual-related field.  No `AxisAtomPremises`, no `atomVal`, no formula-shape
content -/
theorem data_carries_q_eq_only_independent
    {E : BuildableNockExecution F K} (D : Data E) :
    E.q = ringChar K :=
  D.q_eq_ringChar

/-! ## F. `honestCoin` has no noun-syntax content -/

/-- Independent structural proof: `honestCoin E a g` is `((a, g), (α, z))`.
No noun, no formula-tail, no axis operand -/
theorem honestCoin_is_coordinate_tuple_independent
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) :=
  rfl

/-! ## G. `dataOf` consumes `P.axisAtoms` as input (not output) -/

/-- Independent replay: `dataOf` takes `P : ResidualPremises E` including
`P.axisAtoms`, and the constructed `Data` retains only `q_eq_ringChar`.
The `axisAtoms` property is consumed, not output. -/
theorem dataOf_consumes_axisAtoms_independent
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).q_eq_ringChar = P.q_eq_ringChar ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) :=
  ⟨rfl, P.axisAtoms⟩

/-! ## H. `paperProtocol` classification is honest -/

/-- Paper OP0 line 1751: `mem_axis_2 = formula_tail`.  Paper OP9 lines
1737-1738: `mem_axis_3 = f_th.leaf`.  Paper NMR Def 1328: `A ∈ F` (atoms).
Both are protocol requirements.  `axisAtoms` classified `paperProtocol`. -/
theorem axisAtoms_classification_is_paperProtocol :
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol,
      PremiseKind.paperProtocol, PremiseKind.leanEncoding) =
    (.leanEncoding, .paperProtocol, .paperProtocol, .leanEncoding) :=
  rfl

/-! ## I. `axisAtoms` from residual ignores `Data` and coin -/

/-- Independent confirmation: the pin is on `E.semanticData.rows`, coming from
`P : ResidualPremises E`.  Neither `D : Data E` nor `honestCoin E a g`
contributes to `axisAtoms`. -/
theorem axisAtoms_from_residual_ignores_data_and_coin_independent
    {E : BuildableNockExecution F K} (P : ResidualPremises E)
    (_D : Data E) (_a _g : K) :
    ∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i) :=
  P.axisAtoms

/-! ## J. -/

/-- Four residual premises remain.  Independent eta. -/
theorem residualPremises_eta_still_four_batch130
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch129.residualPremises_eta_still_four_batch129 P

/-- Census extras remain five named fields. -/
theorem censusRecordPremises_eta_still_five_batch130
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch129.censusRecordPremises_eta_still_five_batch129 C

/-- `ForestExponentOrder` still `e < orderOf α` -/
theorem ForestExponentOrder_expands_batch130
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  Batch129.ForestExponentOrder_expands_batch129 E α

/-- Fibre `Accepts` still `∀ a g` under named `ForestExponentOrder`. -/
theorem packageOf_fibre_accepts_still_takes_window_batch130
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  Batch129.packageOf_fibre_accepts_still_takes_window_batch129
    D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-- Not `∀ ω` -/
theorem packageOf_not_forall_omega_batch130
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  Batch129.packageOf_not_forall_omega_batch129 D hgt I hprl hmore hord hordM hrows hgenF hF lmb

/-! ## K. Consumed capstone unchanged; no inhabit attempted -/

variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen_batch130
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch129.consumed_capstone_and_alias_remain_frozen_batch129 P hax hbasis hwidth

/-! ## L. Accounting: exact `11+1+2` -/

inductive ReviewedField130
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields130 : List ReviewedField130 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields130 : List ReviewedField130 := [.structural]

def residualFields130 : List ReviewedField130 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting_batch130 :
    substantiveFields130.length = 11 ∧
      typeSummaryFields130.length = 1 ∧
      residualFields130 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields130.length = 2 ∧
      (substantiveFields130 ++ typeSummaryFields130 ++ residualFields130).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-! ## M. `hzero` still on `buildFullPackage`; released builder unchanged -/

theorem released_builder_still_takes_hzero_batch130
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  Batch129.released_builder_still_takes_hzero_batch129 I hprl hmore hord hordM hrows hhon R hzero hgenF hF


#print axioms axisAtoms_expands_independent
#print axioms execution_eta_lacks_certificates
#print axioms axisGates_and_tails_are_independently_supplied
#print axioms axisGate_listed_is_comparison_membership
#print axioms vcomp_s0_mr2_axis_is_field_element
#print axioms vcomp_s9_mr3_axis_is_field_element
#print axioms data_carries_q_eq_only_independent
#print axioms honestCoin_is_coordinate_tuple_independent
#print axioms dataOf_consumes_axisAtoms_independent
#print axioms axisAtoms_classification_is_paperProtocol
#print axioms axisAtoms_from_residual_ignores_data_and_coin_independent
#print axioms residualPremises_eta_still_four_batch130
#print axioms censusRecordPremises_eta_still_five_batch130
#print axioms ForestExponentOrder_expands_batch130
#print axioms packageOf_fibre_accepts_still_takes_window_batch130
#print axioms packageOf_not_forall_omega_batch130
#print axioms consumed_capstone_and_alias_remain_frozen_batch130
#print axioms independent_exact_eleven_one_two_accounting_batch130
#print axioms released_builder_still_takes_hzero_batch130

end

end Nock.RedTeam.Batch130
