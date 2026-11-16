import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.RedTeam.Batch97Thm54LiveMemoryRecords
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  The walk first line is the sampled-challenge value
`α = α^1`; the compute first-row `ln_prev = 1 = α^0` is a different column
obtained only after a zero-exponent timestamp stamp is specialized.  The exact
`BuildableNockExecution` eta boundary has no first-line field.  Its one-row
compute-chain condition, accepted `Vcomp` row, and a valid walk first-line
constraint coexist with compute `ln_prev = 2 ≠ 1`, so those exposed constraints
do not imply the endpoint pin.  `ResidualPremises` therefore remains four-field.

This artifact does not construct a generic `HonestCommitment.Data E`, a generic
`BuildablePackage.CommitmentResidual E`, `q_eq_ringChar`, or later-round `A`/`W`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch98

open scoped Classical
open Nock Nock.Walk
open Nock.Framework
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. The exact `E` boundary does not contain `firstLine` -/

/-- There is no `FirstLineStartsAtOne`, timestamp skeleton, `Data`, or residual
projection on this boundary. -/
theorem buildableExecution_eta_without_firstLine
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

/-- The semantic-data field nested inside `E` contains only the cumulative
language, accepted-row proofs, and row-local noun semantics. -/
theorem semanticData_eta_without_firstLine
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (d : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    d =
      { language := d.language
        rowAccepted := d.rowAccepted
        rows := d.rows } := by
  cases d
  rfl

/-- The cumulative noun-realized layer has only traversal and noun-existence
witnesses; it does not add a timestamp endpoint. -/
theorem nounRealizedLanguage_eta_without_firstLine
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec) :
    h =
      { traversable := h.traversable
        nounRealization := h.nounRealization } := by
  cases h
  rfl

/-- The traversal layer adds only compute/memory topology to the chained
language. -/
theorem traversableLanguage_eta_without_firstLine
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TraversableChainedSemanticExactLanguage cfg exec) :
    h =
      { chained := h.chained
        compute_topology := h.compute_topology
        memory_topology := h.memory_topology } := by
  cases h
  rfl

/-- The exact chained-language boundary has only adjacent compute-line hand-off
and memory-table endpoint fields.  In particular it has no compute first-row
`ln_prev` endpoint -/
theorem chainedLanguage_eta_has_no_compute_first_endpoint
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    h =
      { semantic := h.semantic
        z_ne_zero := h.z_ne_zero
        compute_wf := h.compute_wf
        memory_wf := h.memory_wf
        compute_chain := h.compute_chain
        memory_chain := h.memory_chain
        memory_first_counts := h.memory_first_counts
        memory_first_indicator := h.memory_first_indicator
        memory_first_ipre := h.memory_first_ipre
        memory_last_icur := h.memory_last_icur
        memory_same_lambda := h.memory_same_lambda } := by
  cases h
  rfl

/-! ## B. Walk and compute first lines are different objects -/

/-- Independent paper-shape projection: the walk starts at `α^1`. -/
theorem independent_walk_first_line_is_alpha_pow_one
    {cur : ℕ → K} {chld : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initialCount : K} {h : ℕ}
    (hw : WalkSat cur chld fo ln count acc α seed initialCount h) :
    ln 1 = α ^ 1 := by
  simpa using hw.ln1

/-- Relative specialization at exponent zero is the
RAP increment, not `ln_prev = 1` -/
theorem independent_compute_zero_exponent_is_one
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row)
    (hzero : stamp.lnPrevExponent = 0) :
    row.2.2.1.ln = row.2.2.1.ln_prev * α ^ stamp.lnExponent := by
  obtain ⟨_, _, _, hln, _⟩ := htime
  simpa [hzero] using hln

namespace Concrete

open Nock.NockVMROM.Thm54.ConcreteStrictPackage

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := concrete_char73

def zeroCur (_ : ℕ) : K73cubic := 0
def zeroChild (_ _ : ℕ) : K73cubic := 0
def zeroFanout (_ : ℕ) : ℕ := 0

/-- Concrete discrimination witness: a valid walk at the same challenge
`honestAlpha = 4` has first line `4`, while the concrete compute first row has
`ln_prev = 1`.  Hence the two endpoints are not definitionally the same
specialization -/
theorem walk_and_compute_first_lines_are_unequal :
    ∃ ln count acc : ℕ → K73cubic,
      WalkSat zeroCur zeroChild zeroFanout ln count acc
        honestAlpha 0 0 1 ∧
      ln 1 = honestAlpha ^ 1 ∧
      (computePub honestSeed honestAlpha).ln_prev = honestAlpha ^ 0 ∧
      ln 1 ≠ (computePub honestSeed honestAlpha).ln_prev := by
  obtain ⟨ln, count, acc, hw⟩ :=
    walkSat_exists zeroCur zeroChild zeroFanout honestAlpha 0 0
      (h := 1) (by norm_num)
  refine ⟨ln, count, acc, hw, ?_, ?_, ?_⟩
  · simpa using hw.ln1
  · norm_num [computePub, honestAlpha]
  · rw [hw.ln1]
    intro h
    have hk : (4 : K73cubic) = 1 := by
      simpa [honestAlpha, computePub] using h
    have hmap :
        algebraMap F73 K73cubic (4 : F73) =
          algebraMap F73 K73cubic (1 : F73) := by
      calc
        algebraMap F73 K73cubic (4 : F73) = (4 : K73cubic) :=
          map_natCast (algebraMap F73 K73cubic) 4
        _ = 1 := hk
        _ = algebraMap F73 K73cubic (1 : F73) := by
          simp
    have hbase : (4 : F73) = 1 :=
      (algebraMap F73 K73cubic).injective hmap
    exact (by decide : (4 : F73) ≠ 1) hbase

/-! ## C. `Vcomp` and one-row chaining do not enforce `ln_prev = 1` -/

/-- The adversarial OP1 public row changes only `ln_prev` and the two products
that Algorithm NockCompute actually checks. -/
def nonunitFirstPub : ComputeTable.Pub K73cubic :=
  { computePub honestSeed honestAlpha with
    ln_prev := 2
    ln := 2 * honestAlpha
    mr1 := { (computePub honestSeed honestAlpha).mr1 with
      ts := 2 * honestAlpha } }

/-- The accepted row has
`ln_prev = 2 ≠ 1` -/
theorem independent_op1_vcomp_accepts_nonunit_first_ln_prev :
    ComputeTable.Vcomp (computeInputs honestSeed honestAlpha)
      nonunitFirstPub (computeDec honestSeed) ∧
    nonunitFirstPub.ln_prev ≠ 1 := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact GlobalCarryRecognizer.enc_cons honestSeed_ne headNoun resultNoun
    · ext <;>
        norm_num [nonunitFirstPub, computePub, requestRecord, computeDec,
          computeInputs, honestSeed, honestAlpha]
    · simp [nonunitFirstPub, ComputeTable.SVhead, ComputeTable.headAtom,
        computePub, computeDec, computeInputs, fp, headNoun,
        GlobalCarryRecognizer.enc_atom, ComputeTable.State.toNat,
        honestSeed, honestAlpha]
    · norm_num [nonunitFirstPub, ComputeTable.memBlk, computePub,
        computeInputs, ComputeTable.MemRec.zero, honestSeed, honestAlpha]
    · simp [nonunitFirstPub, ComputeTable.evalV, ComputeTable.sfz1,
        ComputeTable.sfz2, ComputeTable.sfz3, computePub, computeDec]
  · intro h
    have hk : (2 : K73cubic) = 1 := by
      simpa [nonunitFirstPub] using h
    have hmap :
        algebraMap F73 K73cubic (2 : F73) =
          algebraMap F73 K73cubic (1 : F73) := by
      calc
        algebraMap F73 K73cubic (2 : F73) = (2 : K73cubic) :=
          map_natCast (algebraMap F73 K73cubic) 2
        _ = 1 := hk
        _ = algebraMap F73 K73cubic (1 : F73) := by
          simp
    have hbase : (2 : F73) = 1 :=
      (algebraMap F73 K73cubic).injective hmap
    exact (by decide : (2 : F73) ≠ 1) hbase

def oneRowPub (_ : Fin 1) : ComputeTable.Pub K73cubic := nonunitFirstPub

/-- Strong under-closure attack: exact adjacent-row hand-off for a one-row
compute trace, genuine OP1 `Vcomp`, and a valid walk `ln(1)=α` all coexist with
compute `ln_prev=2≠1`.  Thus the exposed chain plus walk constraint cannot
supply the missing endpoint equation -/
theorem chain_vcomp_and_walk_do_not_pin_compute_first_line :
    (∀ i : Fin 1, ∀ hi : (i : ℕ) + 1 < 1,
      (oneRowPub i).ln =
        (oneRowPub ⟨(i : ℕ) + 1, hi⟩).ln_prev) ∧
    ComputeTable.Vcomp (computeInputs honestSeed honestAlpha)
      nonunitFirstPub (computeDec honestSeed) ∧
    nonunitFirstPub.ln_prev ≠ 1 ∧
    ∃ ln count acc : ℕ → K73cubic,
      WalkSat zeroCur zeroChild zeroFanout ln count acc
        honestAlpha 0 0 1 ∧
      ln 1 = honestAlpha := by
  refine ⟨?_, independent_op1_vcomp_accepts_nonunit_first_ln_prev.1,
    independent_op1_vcomp_accepts_nonunit_first_ln_prev.2, ?_⟩
  · intro i hi
    omega
  · obtain ⟨ln, count, acc, hw⟩ :=
      walkSat_exists zeroCur zeroChild zeroFanout honestAlpha 0 0
        (h := 1) (by norm_num)
    exact ⟨ln, count, acc, hw, hw.ln1⟩

end Concrete

/-! ## D. Premises, non-generic boundary, accounting, and capstone -/

/-- Eta expansion pins exactly the unchanged four residual fields. -/
theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- A hypothetical constructor from `E` alone would still have to manufacture
both the first-line endpoint and strict characteristic equality. -/
theorem universal_residualPremises_would_force_both
    (g : ∀ E : BuildableNockExecution F K, ResidualPremises E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

theorem commitment_constructor_still_requires_D_A_W
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (D : Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      TemplateRawJointSoundness.AlphaMCommitment
        (p := ringChar K) D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (_lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    Nonempty (BuildablePackage.CommitmentResidual E) :=
  ⟨commitmentResidualOf D A W⟩

inductive ReviewedField98
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

def substantiveFields98 : List ReviewedField98 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields98 : List ReviewedField98 := [.structural]

def residualFields98 : List ReviewedField98 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields98.length = 11 ∧
      typeSummaryFields98.length = 1 ∧
      residualFields98 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields98.length = 2 ∧
      (substantiveFields98 ++ typeSummaryFields98 ++ residualFields98).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
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

#print axioms buildableExecution_eta_without_firstLine
#print axioms semanticData_eta_without_firstLine
#print axioms nounRealizedLanguage_eta_without_firstLine
#print axioms traversableLanguage_eta_without_firstLine
#print axioms chainedLanguage_eta_has_no_compute_first_endpoint
#print axioms independent_walk_first_line_is_alpha_pow_one
#print axioms independent_compute_zero_exponent_is_one
#print axioms Concrete.walk_and_compute_first_lines_are_unequal
#print axioms Concrete.independent_op1_vcomp_accepts_nonunit_first_ln_prev
#print axioms Concrete.chain_vcomp_and_walk_do_not_pin_compute_first_line
#print axioms residualPremises_eta_still_four
#print axioms universal_residualPremises_would_force_both
#print axioms commitment_constructor_still_requires_D_A_W
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch98
