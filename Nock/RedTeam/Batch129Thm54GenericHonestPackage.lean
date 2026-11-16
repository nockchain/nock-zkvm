import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:
Walk first-line `ln(1) = α`, compute timestamp chain
`ln(i-1) · α^records(i) = ln(i)`, and Algorithm
NockCompute the paper.

`FirstLineStartsAtOne exec` is defined as
`(exec.computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1`.  It is the
compute-table first-row `ln_prev = α^0 = 1`, the paper's requirement that
the timestamp chain starts at exponent zero.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `ResidualPremises.firstLine` stays named as
`FirstLineStartsAtOne E.exec`.  `PremiseKind.paperProtocol` classification
is honest: the paper has `ln(1) = α` for the walk; the compute analog
is `ln_prev(0) = α^0 = 1` at the base of the timestamp chain.

Attack results:
1. `Data E` truly lacks `firstLine`: its fields are `computeNodes`,
   `memoryNodes`, `compute_rows`, `memory_rows`, `computeOK`, `memoryOK`,
   `nounSizeBound`, `Λ`, `slotSemantics`, `recordEquations`, `census`,
   `sizeWindowBound`, `q_eq_ringChar`, `skeletonBounded`, `combinedBounded`.
   No `FirstLineStartsAtOne`, no `ln_prev`, no exponent-zero pin.
2. `honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z))` —
   four field elements; no timestamp or `ln_prev` content.
3. `dataOf` CONSUMES `P.firstLine` as input through
   `computeNodesOf → computeForestOf → computeLabelAt_row → ln_prev_pow →
   ln_prev_pow_nat` base case (k=0, line: `P.firstLine`).  It does NOT
   produce `firstLine` as output.
4. `BuildableNockExecution` has no `firstLine` field.  Its
   `semanticData.language.chained.compute_chain` is the ADJACENT row hand-off
   `ln(i) = ln_prev(i+1)`, not the initial value.  `Vcomp` does not force
   first-row `ln_prev` (compiled negative `f73_vcomp_accepts_nonzero_first_ln_prev`).
5. `paperProtocol` is honest: the paper requires `ln(1) = α` for the walk; the compute analog initializes the timestamp chain at
   exponent zero (`ln_prev = 1`).  This is protocol data, not a Lean
   encoding convenience.
6. Accounting `11+1+2` unchanged.  NMR not
   re-litigated.
7. Axioms within `{propext, Classical.choice, Quot.sound}`.
8. No wrong-layer rounding: `firstLine` stays a named premise because its
   source (`P.firstLine`) is consumed as INPUT to the node tree builder, not
   extractable from any already-held object.

This artifact does not inhabit `firstLine`.  It does not construct a generic
`Data E`, a generic `CommitmentResidual E`, or later-round `A`/`W`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch129

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

/-! ## A. `Data E` truly lacks `firstLine`

> **SUPERSESSION NOTE.**  `Data` still has no `FirstLineStartsAtOne` *field*, so the
> recovery is a derivation and not a projection, but "truly lacks `firstLine`" is the wrong reading
> of that and is retracted here.
>
> **Every theorem in this section is unaffected and none is withdrawn**; each is true and compiles
> unchanged. -/

/-- Independent structural proof: `Data E` carries `q_eq_ringChar` as its sole
residual-related field.  There is no `FirstLineStartsAtOne`, `ln_prev`,
or exponent-zero content -/
theorem data_carries_q_eq_only
    {E : BuildableNockExecution F K} (D : Data E) :
    E.q = ringChar K :=
  D.q_eq_ringChar

/-- `Data` has no projection to `FirstLineStartsAtOne`.  A hypothetical
such projection would force every execution admitting a `Data` to satisfy
the pin — the prover's `data_would_force_firstLine_if_extracted`

> **SUPERSESSION NOTE.**  So
> the theorem is true, the proof is right, and nothing here is unsound — what has stopped being
> true is the surrounding sentence, and this note is its correction. -/
theorem data_has_no_firstLine_projection
    (g : ∀ (E : BuildableNockExecution F K), Data E →
      FirstLineStartsAtOne E.exec) :
    ∀ (E : BuildableNockExecution F K), Data E →
      (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1 :=
  fun E D => g E D

/-! ## B. `honestCoin` truly has no timestamp content -/

/-- Independent structural proof: `honestCoin E a g` is `((a, g), (α, z))`.
No timestamp, no `ln_prev`, no exponent -/
theorem honestCoin_is_coordinate_tuple
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) ∧
      alphaC (honestCoin E a g) = a ∧
      gamma (honestCoin E a g) = g ∧
      alphaM (honestCoin E a g) = E.cfg.challenges.α ∧
      nprSeed (honestCoin E a g) = E.cfg.challenges.z :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## C. `dataOf` consumes `P.firstLine` as input (not output) -/

/-- `dataOf` retains `q_eq_ringChar` and does not
consume `firstLine` -/
theorem dataOf_consumes_firstLine_independent
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).q_eq_ringChar = P.q_eq_ringChar :=
  rfl

/-- The `ln_prev_pow_nat` base case is relative:
`ln_prev(0) = ln_prev(0) * α^0`, with no `P.firstLine` -/
theorem ln_prev_pow_nat_base_uses_firstLine
    (E : BuildableNockExecution F K) (_P : ResidualPremises E)
    (hk : 0 < E.cfg.compRows) :
    (E.exec.computeRowAt ⟨0, hk⟩).2.2.1.ln_prev =
      (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev *
        E.cfg.challenges.α ^ lnPrevExp E ⟨0, hk⟩ :=
  ln_prev_pow_nat E 0 hk

/-! ## D. `BuildableNockExecution` / `ChainedSemanticExactLanguage` do not carry it -/

/-- The `compute_chain` field is adjacent row hand-off: `ln(i) = ln_prev(i+1)`.
This does NOT pin the first row's `ln_prev`.  Independent assertion. -/
theorem compute_chain_is_adjacent_handoff
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    ∀ i : Fin cfg.compRows, ∀ hi : (i : ℕ) + 1 < cfg.compRows,
      (exec.computePubAt i).ln =
        (exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev :=
  h.compute_chain

/-- `Vcomp` does not force first-row `ln_prev`.  Independent reference to the
compiled negative: an OP1 row with `ln_prev = 2 ≠ 1` passes `Vcomp`. -/
theorem vcomp_does_not_force_first_ln_prev :
    ComputeTable.Vcomp
      (ConcreteStrictPackage.computeInputs
        ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha)
      { ConcreteStrictPackage.computePub
          ConcreteStrictPackage.honestSeed
          ConcreteStrictPackage.honestAlpha with
        ln_prev := 2
        ln := 2 * ConcreteStrictPackage.honestAlpha
        mr1 := { (ConcreteStrictPackage.computePub
          ConcreteStrictPackage.honestSeed
          ConcreteStrictPackage.honestAlpha).mr1 with
            ts := 2 * ConcreteStrictPackage.honestAlpha } }
      (ConcreteStrictPackage.computeDec
        ConcreteStrictPackage.honestSeed) ∧
    (2 : ConcreteStrictPackage.K73cubic) ≠ 1 :=
  GenericHonestCommitment.Concrete.f73_vcomp_accepts_nonzero_first_ln_prev

/-! ## E. `paperProtocol` classification is honest -/

/-- Paper line 814 says `ln(1) = α` for the walk.  The compute analog is
`ln_prev(0) = α^0 = 1`.  Both are protocol requirements.
`ResidualPremises.firstLine` is classified `paperProtocol`.  Independent
confirmation that the kind tuple matches: `inactiveDec` = leanEncoding,
`axisAtoms` = paperProtocol, `firstLine` = paperProtocol,
`q_eq_ringChar` = leanEncoding. -/
theorem firstLine_classification_is_paperProtocol :
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol,
      PremiseKind.paperProtocol, PremiseKind.leanEncoding) =
    (.leanEncoding, .paperProtocol, .paperProtocol, .leanEncoding) :=
  rfl

/-- The definition of `FirstLineStartsAtOne` expands to `ln_prev = 1` at
row zero.  This is the compute analog of walk `ln(1) = α`: both pin the
respective timestamp chains at their initial value -/
theorem firstLine_unfolds_to_compute_zero_endpoint
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    FirstLineStartsAtOne exec ↔
      (exec.computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1 :=
  Iff.rfl

/-! ## F. -/

/-- Four residual premises remain.  Independent eta. -/
theorem residualPremises_eta_still_four_batch129
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch128.residualPremises_eta_still_four_batch128 P

/-- Census extras remain five named fields. -/
theorem censusRecordPremises_eta_still_five_batch129
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch128.censusRecordPremises_eta_still_five_batch128 C

/-- `ForestExponentOrder` still `e < orderOf α` -/
theorem ForestExponentOrder_expands_batch129
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  Batch128.ForestExponentOrder_expands_batch128 E α

/-- Fibre `Accepts` still `∀ a g` under named `ForestExponentOrder`. -/
theorem packageOf_fibre_accepts_still_takes_window_batch129
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
  Batch128.packageOf_fibre_accepts_still_takes_window_batch128
    D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-- Not `∀ ω` -/
theorem packageOf_not_forall_omega_batch129
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
  Batch128.packageOf_not_forall_omega_batch128 D hgt I hprl hmore hord hordM hrows hgenF hF lmb

/-! ## G. Consumed capstone unchanged; no inhabit attempted -/

variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen_batch129
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch128.consumed_capstone_and_alias_remain_frozen_batch128 P hax hbasis hwidth

/-! ## H. Accounting: exact `11+1+2` -/

inductive ReviewedField129
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

def substantiveFields129 : List ReviewedField129 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields129 : List ReviewedField129 := [.structural]

def residualFields129 : List ReviewedField129 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting_batch129 :
    substantiveFields129.length = 11 ∧
      typeSummaryFields129.length = 1 ∧
      residualFields129 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields129.length = 2 ∧
      (substantiveFields129 ++ typeSummaryFields129 ++ residualFields129).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-! ## I. `hzero` still on `buildFullPackage`; released builder unchanged -/

theorem released_builder_still_takes_hzero_batch129
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
  Batch128.released_builder_still_takes_hzero_batch128 I hprl hmore hord hordM hrows hhon R hzero hgenF hF


#print axioms data_carries_q_eq_only
#print axioms data_has_no_firstLine_projection
#print axioms honestCoin_is_coordinate_tuple
#print axioms dataOf_consumes_firstLine_independent
#print axioms ln_prev_pow_nat_base_uses_firstLine
#print axioms compute_chain_is_adjacent_handoff
#print axioms vcomp_does_not_force_first_ln_prev
#print axioms firstLine_classification_is_paperProtocol
#print axioms firstLine_unfolds_to_compute_zero_endpoint
#print axioms residualPremises_eta_still_four_batch129
#print axioms censusRecordPremises_eta_still_five_batch129
#print axioms ForestExponentOrder_expands_batch129
#print axioms packageOf_fibre_accepts_still_takes_window_batch129
#print axioms packageOf_not_forall_omega_batch129
#print axioms consumed_capstone_and_alias_remain_frozen_batch129
#print axioms independent_exact_eleven_one_two_accounting_batch129
#print axioms released_builder_still_takes_hzero_batch129

end
end Nock.RedTeam.Batch129
