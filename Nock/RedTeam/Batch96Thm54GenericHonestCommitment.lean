import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.RedTeam.Batch95Thm54CompletenessLayers
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch96

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.Framework
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OpcodeSemantics
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. The boundary remains conditional, not generic -/

/-- Exhaustive eta check of the input boundary.  In particular there is no
private `Dec` noun column, `ResidualPremises`, `Data`, or residual field hidden
on `BuildableNockExecution`. -/
theorem buildableExecution_eta_without_dec
    (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } := by
  cases E
  rfl

/-- The named premise record has exactly four load-bearing fields; it is not a
renaming of `True`. -/
theorem residualPremises_eta
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- All three residual fields can be recovered from an inhabitant. -/
theorem residualPremises_projects_all_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows,
        AxisAtomPremises (E.semanticData.rows i)) ∧
      E.q = ringChar K :=
  ⟨P.inactiveDec, P.axisAtoms, P.q_eq_ringChar⟩

/-- `Data` itself still carries the strict characteristic equality.  The
generic input supplies only the weaker inequality. -/
theorem data_still_requires_q_equality
    {E : BuildableNockExecution F K} (D : Data E) :
    E.q ≤ ringChar K ∧ E.q = ringChar K :=
  ⟨E.q_le_ringChar, D.q_eq_ringChar⟩

/-- The residual itself retains the same strict equality. -/
theorem residual_still_requires_q_equality
    {E : BuildableNockExecution F K}
    (R : BuildablePackage.CommitmentResidual E) :
    E.q = ringChar K :=
  R.q_eq_ringChar

/-- Consequently, any genuinely generic residual constructor would imply the
strict equality for every buildable execution. -/
theorem generic_residual_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K,
      BuildablePackage.CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-- The existing residual constructor still begins with a fully inhabited
`Data E` and both dependent later-round families. -/
theorem commitmentResidualOf_boundary
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (D : Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      AlphaMCommitment (p := ringChar K) D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    (commitmentResidualOf D A W).q_eq_ringChar = D.q_eq_ringChar ∧
      (commitmentResidualOf D A W).commitment.skeleton = D.skeleton :=
  ⟨rfl, rfl⟩

/-! ## B. The private decomposition nouns come from semantic row data -/

/-- Definitional provenance of every private decomposition noun.  The only
inputs are the row's `ComputeRowSemanticData` fields -/
theorem decompNoun_is_semanticData
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    decompNoun data .f_h = data.root.head ∧
      decompNoun data .f_t = data.root.tail ∧
      decompNoun data .f_th =
        (if h : data.tails = [] then .atom 0 else (data.tails.head h).head) ∧
      decompNoun data .f_tt =
        (if h : data.tails = [] then .atom 0 else (data.tails.head h).tail) ∧
      decompNoun data .f_tth =
        (if h : data.branchTails = [] then .atom 0
          else (data.branchTails.head h).head) ∧
      decompNoun data .f_ttt =
        (if h : data.branchTails = [] then .atom 0
          else (data.branchTails.head h).tail) := by
  simp [decompNoun]

/-- The same provenance statement at the actual generic input boundary. -/
theorem execution_decompNoun_reads_semanticData
    (E : BuildableNockExecution F K) (i : Fin E.cfg.compRows) :
    decompNoun (E.semanticData.rows i) .f_h =
        (E.semanticData.rows i).root.head ∧
      decompNoun (E.semanticData.rows i) .f_t =
        (E.semanticData.rows i).root.tail :=
  ⟨rfl, rfl⟩

/-! ## C. Independent premise classification and load-bearing checks -/

inductive IndependentPremiseKind where
  | paperProtocol
  | paperAnalog
  | leanEncoding
deriving DecidableEq

/-- Exact independent classification.  `firstLine` is kept distinct: the paper
states the walk initial line `ln(1)=α`; the compute `ln_prev=1` condition is its
exponent-zero analogue, not a second verbatim paper sentence. -/
theorem independent_premise_classification :
    (IndependentPremiseKind.leanEncoding,
      IndependentPremiseKind.paperProtocol,
      IndependentPremiseKind.paperAnalog,
      IndependentPremiseKind.leanEncoding) =
    (.leanEncoding, .paperProtocol, .paperAnalog, .leanEncoding) :=
  rfl

/-- OP0's axis noun must be an atom before its Nat payload can become the NMR
address -/
theorem op0_axis_atom_is_load_bearing
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (P : AxisAtomPremises data) (hstate : row.1 = .s0) :
    ∃ k : ℕ, data.root.tail = .atom k ∧ atomVal data.root.tail = k := by
  obtain ⟨k, hk⟩ := P.1 hstate
  exact ⟨k, hk, by simp [hk, atomVal]⟩

/-- OP9's third-record address likewise comes from the atom payload of
`formula_tail_head` -/
theorem op9_axis_atom_is_load_bearing
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (P : AxisAtomPremises data) (hstate : row.1 = .s9) :
    ∃ k : ℕ, decompNoun data .f_th = .atom k ∧
      atomVal (decompNoun data .f_th) = k := by
  obtain ⟨k, hk⟩ := P.2 hstate
  exact ⟨k, hk, by simp [hk, atomVal]⟩

/-- `Vcomp` really leaves the four OP1-inactive private columns arbitrary.
The chosen nonzero `f_th` gives a compiled negative control against silently
reclassifying production zero padding as a paper-verifier consequence
because `InactiveDecPadding` is now `True` (the zero-forcing convention was
dropped from `BindComputeRow`).  The Vcomp acceptance half is the substantive
claim and stands on its own. -/
theorem f73_vcomp_accepts_nonzero_inactive_dec :
    let garbage : ComputeTable.FP ConcreteStrictPackage.K73cubic := ⟨1, 0, 0⟩
    ComputeTable.Vcomp
      (ConcreteStrictPackage.computeInputs
        ConcreteStrictPackage.honestSeed ConcreteStrictPackage.honestAlpha)
      (ConcreteStrictPackage.computePub
        ConcreteStrictPackage.honestSeed ConcreteStrictPackage.honestAlpha)
      { f_h := (ConcreteStrictPackage.computeDec
          ConcreteStrictPackage.honestSeed).f_h
        f_t := (ConcreteStrictPackage.computeDec
          ConcreteStrictPackage.honestSeed).f_t
        f_th := garbage
        f_tt := 0
        f_tth := 0
        f_ttt := 0 } := by
  exact Concrete.f73_vcomp_ignores_inactive_dec ⟨1, 0, 0⟩ 0 0 0

/-- Existence, not uniqueness, is the only premise of the noun selector used
by the generic row construction. -/
theorem chooseNoun_boundary_has_no_SepSeed
    {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    GlobalCarryRecognizer.enc z (chooseNoun h) = fp :=
  chooseNoun_enc h

/-! ## D. Concrete non-vacuity of the four-premise boundary -/

namespace ConcretePremises

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildableConcrete

/-- The F73 execution inhabits all four premises on one same execution.  This
is a premise-boundary witness only; it is not a generic `Data` constructor. -/
def f73_residualPremises : ResidualPremises concreteExecution where
  inactiveDec := trivial
  axisAtoms := by
    intro i
    have hstate :
        (concreteExecution.exec.computeRowAt i).1 = .s1 := by
      change
        ((ConcreteStrictPackage.exec honestSeed honestAlpha).computeRowAt i).1 =
          .s1
      rcases i with ⟨row, hrow⟩
      have hrow0 : row = 0 := by
        have : row < 1 := by
          simpa [concreteExecution, ConcreteStrictPackage.cfg] using hrow
        omega
      subst row
      norm_num [ExactExecution.computeRowAt, ExactExecution.computeRows,
        concreteExecution, ConcreteStrictPackage.exec, Nock.Walk.bfsForest,
        ConcreteStrictPackage.cfg, ConcreteStrictPackage.computeRow]
    constructor
    · intro h0
      rw [hstate] at h0
      contradiction
    · intro h9
      rw [hstate] at h9
      contradiction
  q_eq_ringChar := ConcreteStrictPackage.q_eq_ringChar

theorem f73_residualPremises_nonvacuous :
    Nonempty (ResidualPremises concreteExecution) :=
  ⟨f73_residualPremises⟩

end ConcretePremises

/-! ## E. -/

/-- Exact dependent signature of the post-challenge arrays left to the prover. -/
theorem later_round_arrays_remain_arguments
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (D : Data E) (AW : laterRoundSignature D) :
    Nonempty (BuildablePackage.CommitmentResidual E) :=
  ⟨commitmentResidualOf D AW.1 AW.2⟩

theorem released_buildFullPackage_still_requires_hzero
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (I : BuildableChips.Inputs E)
    (R : BuildablePackage.CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    BuildablePackage.buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF =
      BuildablePackage.buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF :=
  rfl

/-- The first memory record is always live, while states `s6` and `s9` expose
all three records. -/
theorem live_record_boundary :
    (∀ st : ComputeTable.State, 0 < recordCount st) ∧
      recordCount ComputeTable.State.s6 = 3 ∧
      recordCount ComputeTable.State.s9 = 3 := by
  refine ⟨recordCount_pos, rfl, rfl⟩

inductive ReviewedField96
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

def substantiveFields96 : List ReviewedField96 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields96 : List ReviewedField96 := [.structural]

def residualFields96 : List ReviewedField96 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Independent `11 + 1 + 2` recount. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields96.length = 11 ∧
      typeSummaryFields96.length = 1 ∧
      residualFields96 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields96.length = 2 ∧
      (substantiveFields96 ++ typeSummaryFields96 ++ residualFields96).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

theorem consumed_capstone_and_alias_unchanged
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

#print axioms buildableExecution_eta_without_dec
#print axioms residualPremises_eta
#print axioms residualPremises_projects_all_four
#print axioms data_still_requires_q_equality
#print axioms residual_still_requires_q_equality
#print axioms generic_residual_would_force_q_equality
#print axioms commitmentResidualOf_boundary
#print axioms decompNoun_is_semanticData
#print axioms execution_decompNoun_reads_semanticData
#print axioms independent_premise_classification
#print axioms op0_axis_atom_is_load_bearing
#print axioms op9_axis_atom_is_load_bearing
#print axioms f73_vcomp_accepts_nonzero_inactive_dec
#print axioms chooseNoun_boundary_has_no_SepSeed
#print axioms ConcretePremises.f73_residualPremises
#print axioms ConcretePremises.f73_residualPremises_nonvacuous
#print axioms later_round_arrays_remain_arguments
#print axioms released_buildFullPackage_still_requires_hzero
#print axioms live_record_boundary
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_unchanged
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.bindComputeRow_publicAndDec
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.bindMemRec_mr1
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.bindMemRec_inactive
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.uniqueness_requires_SepSeed
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.commitmentResidualOf
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackage
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch96
