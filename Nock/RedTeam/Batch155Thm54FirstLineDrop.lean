import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.FirstLineCarrier
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.RedTeam.AO123Thm54FirstLineConsumptionPin
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
import Nock.RedTeam.Batch129Thm54GenericHonestPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Construction files were not edited in this pass.  Paper
`V_comp` / constraint spec / walk RAP were re-read at source.

Paper frame (re-read at source):
Algorithm `V_comp` checks per-row `ln = ln_prev · z^k`
and never pins first-row `ln_prev`.  Constraint spec
is the increment `ln(i-1) * (α-weighted opcode sum) = ln(i)`.  Walk RAP
`ln(1)=α` is a different table.  Memory timestamps `α^i` stay absolute.

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`).

Five axes:
1. Vacuity / RAP faithfulness — relative `ComputeTimestampSpecializesAt`
   does not pin `ln_prev=1`; negatives at `V_comp` and compute RAP content;
   `computeOK` from the remaining three residual fields.
3. Definitional drift — relative form matches `V_comp` increment, not walk
   `ln(1)=α`; request-bridge still takes `horigin`; stale names compiled.
4. Axiom leak — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
5. Wrong layer — tick is “field left ResidualPremises”, not `∀ E, Data E`,
   not C6, not compute RAP `.boundary`, not generic constructor discharge.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch155

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FirstLineCarrier
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.Framework

noncomputable section

local instance batch155_prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩

/-! ## Fixtures: non-unit first-row origin (F73 OP1) -/

def dirtyFirstPub : ComputeTable.Pub K73cubic :=
  { computePub honestSeed honestAlpha with
      ln_prev := 2
      ln := 2 * honestAlpha
      mr1 := { (computePub honestSeed honestAlpha).mr1 with ts := 2 * honestAlpha } }

def dirtyFirstRow : ComputeTable.State × ComputeTable.DTcomp K73cubic :=
  (.s1, computeInputs honestSeed honestAlpha, dirtyFirstPub, computeDec honestSeed)

/-! ## Axis 1. Vacuity / RAP faithfulness -/

/-- Relative `ComputeTimestampSpecializesAt` is six conjuncts: state, `α`,
    public state, `ln = ln_prev * α^(Δe)`, active-record timestamps relative
    to published `ln_prev`, and padding zeros.  No `ln_prev = α^e` and no
    `ln_prev = 1`. -/
theorem specializesAt_is_six_conjuncts
    {α : K73cubic} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K73cubic}
    (h : ComputeTimestampSpecializesAt α stamp row) :
    row.1 = stamp.state ∧
      row.2.1.α = α ∧
      row.2.2.1.state = stamp.state ∧
      row.2.2.1.ln = row.2.2.1.ln_prev *
        α ^ (stamp.lnExponent - stamp.lnPrevExponent) ∧
      (∀ i : Fin 3,
        (computeMemRec row.2.2.1 i).ts =
          if computeMemRecKind stamp.state i = .active
          then row.2.2.1.ln_prev *
            α ^ (stamp.recordExponent i - stamp.lnPrevExponent)
          else 0) ∧
      (∀ i : Fin 3,
        computeMemRecKind stamp.state i = .padding →
          computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero) :=
  h

/-- Independent reference to the compiled `V_comp` negative: OP1 with
    `ln_prev = 2 ≠ 1` is accepted. -/
theorem vcomp_does_not_force_first_ln_prev :
    ComputeTable.Vcomp
      (computeInputs honestSeed honestAlpha) dirtyFirstPub
      (computeDec honestSeed) ∧
    (2 : K73cubic) ≠ 1 := by
  simpa [dirtyFirstPub] using
    GenericHonestCommitment.Concrete.f73_vcomp_accepts_nonzero_first_ln_prev

def batch129_vcomp_does_not_force_first_ln_prev :=
  Batch129.vcomp_does_not_force_first_ln_prev

/-- One-row compute RAP content (per-row `V_comp` plus vacuous chain) does
    not pin first-row `ln_prev`. -/
def rap_content_does_not_pin_first_ln_prev :=
  F73Probe.compute_rap_content_does_not_pin_first_ln_prev

/-- Relative specialization holds at origin `2 ≠ 1`.  `of_absolute` cannot
    inhabit this row: it still asks `ln_prev = α^e`. -/
theorem relative_specializes_at_nonunit_origin :
    ComputeTimestampSpecializesAt honestAlpha
      (computeStampOf 0 dirtyFirstRow) dirtyFirstRow ∧
      dirtyFirstRow.2.2.1.ln_prev ≠ 1 := by
  constructor
  · refine ⟨rfl, rfl, rfl, ?hln, ?hts, ?hpad⟩
    · simp [computeStampOf, dirtyFirstRow, dirtyFirstPub, recordCount, pow_one]
    · intro i
      fin_cases i
      · simp [computeStampOf, dirtyFirstRow, dirtyFirstPub, computeMemRec,
          computeMemRecKind, recordCount, pow_one]
      · simp [computeStampOf, dirtyFirstRow, dirtyFirstPub, computeMemRec,
          computeMemRecKind, recordCount, computePub, ComputeTable.MemRec.zero]
      · simp [computeStampOf, dirtyFirstRow, dirtyFirstPub, computeMemRec,
          computeMemRecKind, recordCount, computePub, ComputeTable.MemRec.zero]
    · intro i hi
      have hne : i ≠ 0 := by
        simp [computeStampOf, dirtyFirstRow, computeMemRecKind, recordCount] at hi
        exact hi
      fin_cases i
      · exact (hne rfl).elim
      · rfl
      · rfl
  · simpa [dirtyFirstRow, dirtyFirstPub] using
      GenericHonestCommitment.Concrete.f73_vcomp_accepts_nonzero_first_ln_prev.2

/-- `computeOK` from the remaining three residual fields; no
    `FirstLineStartsAtOne` hypothesis.  The old `computeOK_iff_firstLine`
    identifier is absent from `Nock.RedTeam.AO123` (grep: docstring only). -/
theorem computeOK_from_the_other_three
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K)
    (hin : InactiveDecPaddingExec E.exec)
    (hax : ∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i))
    (hq : E.q = ringChar K) :
    ComputeNodesOK E.cfg.challenges.z E.cfg.challenges.α
      (AO123.computeNodesFrom E) :=
  AO123.computeOK_from_the_other_three E hin hax hq

/-- Not an `Iff`. -/
def computeOK_no_longer_iff_firstLine :=
  @AO123.computeOK_no_longer_iff_firstLine

/-- Absolute origin-1 recovery still takes `ln_prev = α^e` as a hypothesis.
    Relative `SpecializesAt` does not supply it. -/
theorem firstLine_from_absolute_origin_zero
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hpow : row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
    (hstart : stamp.lnPrevExponent = 0) :
    row.2.2.1.ln_prev = 1 :=
  firstLine_of_absolute_zero hpow hstart

/-- Relative specialization at exponent zero still talks about `ln_prev`,
    not `1`. -/
theorem specializes_at_zero_keeps_published_origin
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row)
    (hstart : stamp.lnPrevExponent = 0) :
    row.2.1.α = α ∧
      row.2.2.1.ln = row.2.2.1.ln_prev * α ^ stamp.lnExponent :=
  specializes_at_zero_still_needs_alpha htime hstart

/-! ## Axis 2. Weakening / accounting -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Three-field eta: if `firstLine` were still a field this would not compile. -/
theorem residualPremises_eta_three
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem residualPremises_still_three_fields
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  residualPremises_still_three P

/-- `inactiveDec` remains a field (now `True`). -/
theorem inactiveDec_still_a_field
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec :=
  P.inactiveDec

theorem inactiveDec_of_residual_is_trivial
    {E : BuildableNockExecution F K} (P : ResidualPremises E)
    (i : Fin E.cfg.compRows) :
    InactiveDecPadding (E.exec.computeRowAt i) :=
  inactiveDec_of_residual P i

/-- `CensusRecordPremises` still five fields. -/
theorem censusRecordPremises_eta_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- `MemoryRecordPremises` still two fields. -/
theorem memoryRecordPremises_eta_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

/-- `root_line_exponent` remains on `Data`. -/
theorem data_still_has_root_line_exponent
    {E : BuildableNockExecution F K} (D : Data E) :
    D.computeNodes.label.stamp.lnPrevExponent = 0 :=
  D.root_line_exponent

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]
variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch128.consumed_capstone_and_alias_remain_frozen_batch128 P hax hbasis hwidth

theorem independent_exact_eleven_one_two_accounting :
    Batch91.reviewedSubstantiveFields.length = 11 ∧
      Batch91.reviewedTypeSummaryFields.length = 1 ∧
      Batch91.reviewedResidualFields =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      Batch91.reviewedResidualFields.length = 2 ∧
      (Batch91.reviewedSubstantiveFields ++ Batch91.reviewedTypeSummaryFields ++
        Batch91.reviewedResidualFields).Nodup ∧
      11 + 1 + 2 = 14 :=
  Batch91.exact_eleven_one_two_partition

/-! ## Axis 3. Definitional drift -/

/-- Walk RAP initial line is `ln(1)=α`, a different table. -/
theorem walk_ln1_is_sampled_alpha
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 = α :=
  walkSat_ln1_eq_alpha hw

/-- `ln_prev_pow_nat` base is `pow_zero` against the published origin, not
    `P.firstLine`. -/
theorem ln_prev_pow_nat_base_is_published_origin
    (E : BuildableNockExecution F K) (hk : 0 < E.cfg.compRows) :
    (E.exec.computeRowAt ⟨0, hk⟩).2.2.1.ln_prev =
      (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev *
        E.cfg.challenges.α ^ lnPrevExp E ⟨0, hk⟩ :=
  ln_prev_pow_nat E 0 hk

/-- Request-bridge still requires the absolute origin equation.  LogUp
    completeness for origin ≠ 1 is not claimed. -/
def request_bridge_still_takes_horigin :=
  @semanticRequestBridgeEquation

/-- Absolute specialization still takes `ln_prev = α^e`. -/
def of_absolute_still_takes_origin :=
  @ComputeTimestampSpecializesAt.of_absolute

/-- Stale name: `residualPremises_still_four` is a three-conjunct type. -/
theorem residualPremises_still_four_is_three_conjuncts
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_four P

/-- Stale name: `residualPremises_still_names_firstLine` does not mention
    `firstLine` in its type or body. -/
theorem residualPremises_still_names_firstLine_is_three_conjuncts
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  residualPremises_still_names_firstLine P

/-- Classification tuple is three kinds after the drop, not four. -/
theorem residualPremises_kinds_is_three :
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol, PremiseKind.leanEncoding) =
      (.leanEncoding, .paperProtocol, .leanEncoding) :=
  residualPremises_kinds

/-- `Data.firstLine` is a theorem taking `horigin`, not a residual field. -/
theorem data_firstLine_takes_horigin
    {E : BuildableNockExecution F K} (D : Data E)
    (horigin : D.computeNodes.label.row.2.2.1.ln_prev = 1) :
    FirstLineStartsAtOne E.exec :=
  Data.firstLine D horigin

/-- `computeTimestampSpecializesAt_of_residual` binds premises as `_P`. -/
theorem specializes_of_residual_from_three
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (i : Fin E.cfg.compRows) :
    ComputeTimestampSpecializesAt E.cfg.challenges.α
      (computeStampOf (lnPrevExp E i) (E.exec.computeRowAt i))
      (E.exec.computeRowAt i) :=
  computeTimestampSpecializesAt_of_residual E P i

/-! ## Axis 5. Wrong layer / overclaim (compiled bounds) -/

/-- C6 was not added: compute chained AIR `.boundary` is still empty. -/
theorem compute_air_boundary_still_empty :
    (Nock.Framework.Thm54.kindSeg Nock.Reified.Trans.computeAIRchained
      .boundary).constraints = [] :=
  Nock.Framework.Thm54.comp_boundary_terminal_segs_empty.1

theorem compute_vs_memory_boundary_contrast :
    (Nock.Framework.Thm54.kindSeg (Nock.Reified.Trans.memoryAIRchained (K := K73cubic))
        .boundary).constraints.length = 3 ∧
      (Nock.Framework.Thm54.kindSeg Nock.Reified.Trans.computeAIRchained
        .boundary).constraints.length = 0 :=
  ⟨Nock.Framework.Thm54.mem_seg_counts.2.2.1,
    Nock.Framework.Thm54.comp_seg_counts.2.2.1⟩

/-- Chained language still has no compute first-row pin -/
theorem chained_language_has_no_compute_firstLine
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    h = {
      semantic := h.semantic
      z_ne_zero := h.z_ne_zero
      compute_wf := h.compute_wf
      memory_wf := h.memory_wf
      compute_chain := h.compute_chain
      memory_chain := h.memory_chain
      memory_first_counts := h.memory_first_counts
      memory_first_indicator := h.memory_first_indicator
      memory_first_ipre := h.memory_first_ipre
      memory_last_icur := h.memory_last_icur
      memory_same_lambda := h.memory_same_lambda } :=
  chained_language_eta_without_firstLine h

/-- Fixture `firstLine_at_*` remains generator convention, not a RAP pin -/
theorem firstLine_at_concrete_is_generator_convention :
    FirstLineStartsAtOne BuildableConcrete.concreteExecution.exec :=
  firstLine_at_concrete

/-- Fibre `Accepts` still takes named `ForestExponentOrder` on a supplied `D`.
    Not `∀ D`. -/
theorem packageOf_fibre_still_takes_forest_order
    {E : BuildableNockExecution F K} (D : Data E)
    (hgt : 11 < ringChar K) (I : Inputs E)
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
  packageOf_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-- `packageOf` still takes `Data E` and `Inputs E`.  Not `∀ E, Data E`. -/
def packageOf_still_takes_data_and_inputs :=
  @packageOf

end

/-! ## Axis 4. -/

#print axioms specializesAt_is_six_conjuncts
#print axioms vcomp_does_not_force_first_ln_prev
#print axioms batch129_vcomp_does_not_force_first_ln_prev
#print axioms rap_content_does_not_pin_first_ln_prev
#print axioms relative_specializes_at_nonunit_origin
#print axioms computeOK_from_the_other_three
#print axioms computeOK_no_longer_iff_firstLine
#print axioms firstLine_from_absolute_origin_zero
#print axioms specializes_at_zero_keeps_published_origin
#print axioms residualPremises_eta_three
#print axioms residualPremises_still_three_fields
#print axioms inactiveDec_still_a_field
#print axioms inactiveDec_of_residual_is_trivial
#print axioms censusRecordPremises_eta_five
#print axioms memoryRecordPremises_eta_two
#print axioms data_still_has_root_line_exponent
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms independent_exact_eleven_one_two_accounting
#print axioms walk_ln1_is_sampled_alpha
#print axioms ln_prev_pow_nat_base_is_published_origin
#print axioms request_bridge_still_takes_horigin
#print axioms of_absolute_still_takes_origin
#print axioms residualPremises_still_four_is_three_conjuncts
#print axioms residualPremises_still_names_firstLine_is_three_conjuncts
#print axioms residualPremises_kinds_is_three
#print axioms data_firstLine_takes_horigin
#print axioms specializes_of_residual_from_three
#print axioms compute_air_boundary_still_empty
#print axioms compute_vs_memory_boundary_contrast
#print axioms chained_language_has_no_compute_firstLine
#print axioms firstLine_at_concrete_is_generator_convention
#print axioms packageOf_fibre_still_takes_forest_order
#print axioms packageOf_still_takes_data_and_inputs
#print axioms optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch155
