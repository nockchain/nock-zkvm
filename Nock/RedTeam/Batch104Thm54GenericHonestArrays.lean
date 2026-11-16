import Nock.NockVMROM.Thm54.GenericHonestArrays
import Nock.RedTeam.Batch103Thm54CensusExtras
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Pre-challenge `A` is independent of `(αc, γ)`.  Later-round
`W` is a genuine function of the walk coin: `WalkSat.ln1` on the assignment
used to build `W` forces `computeLn 1 = αc`, so `W` is not
constant in `(αc, γ)`.  That extraction uses `JointAssignment.sixFamilies`,
not production `Accepts`.

`commitmentResidualOfArrays` still requires inhabited `Data E` and named
`StateTagChar`.  There is no `∀ E, CommitmentResidual E`.  `StateTagChar` is
`InjOn natCast (Iic 11)`, fails at characteristic `2`, and is not a
consequence of `1 < q`.  `not_forall_omega_accepts` unfolds the production
raw `Accepts` (zero NPR seed).  The F73 residual inhabitant is not an
`Accepts` claim.  Accounting remains `11+1+2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch104

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.NodeEncoding

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Quantifier order: `A` pre-challenge, `W` a function of `(αc, γ)` -/

/-- The committed `afterAlphaM` API is `(z, hz, α)` only.  No walk pair. -/
theorem afterAlphaM_api_is_z_hz_alphaM
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    (rawStrategyOf D hchar).afterAlphaM = alphaMCommitmentOf D hchar :=
  rfl

/-- Pre-challenge tables are the reference assignment at `(0, 0)`, not a
function of the later-round walk pair -/
theorem A_tables_are_the_zero_zero_assignment
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) (α lmb : K) :
    (alphaMCommitmentOf D hchar z hz α lmb).tables.compute =
        (assignmentOf E hchar 0 0).computeTableAux ∧
      (alphaMCommitmentOf D hchar z hz α lmb).tables.memory =
        (assignmentOf E hchar 0 0).memoryTableAux :=
  afterAlphaM_tables_are_the_reference_assignment D hchar z hz α lmb

/-- The same committed tables at two distinct walk coins with the same
`(α, z)` -/
theorem A_identical_across_distinct_walk_pairs
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K)
    (z : K) (hz : z ≠ 0) (α a g a' g' lmb : K) :
    (rawStrategyOf D hchar).alphaMCommitment ((a, g), (α, z)) lmb hz =
      (rawStrategyOf D hchar).alphaMCommitment ((a', g'), (α, z)) lmb hz :=
  alphaMCommitment_same_across_walk_coins D hchar z hz α lmb a g a' g'

/-- `W` is exactly `afterCoins` -/
theorem afterCoins_api_is_walkArraysOf
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    (rawStrategyOf D hchar).afterCoins = walkArraysOf D hchar :=
  rfl

/-- Assignment used to build `W` satisfies the compute-walk RAP of the
family at that same pair.  This is `JointAssignment.sixFamilies`, not
`Strategy.Accepts` -/
theorem assignmentOf_satisfies_compute_walk
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    ∀ kind, ((honestFamily E hchar a g).computeWalkRAP kind).Satisfies
      (assignmentOf E hchar a g).computeWalkTrace :=
  (JointAssignment.six_family_satisfaction
    ((completion E hchar).assignment a g)).2.2.1

/-- `WalkSat.ln1` on that assignment: `ln(1) = αc`.
Not an `Accepts` claim. -/
theorem assignmentOf_computeLn1
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    (assignmentOf E hchar a g).computeWalk.ln 1 = a := by
  have hcert :
      PlusIOSameExecutionAssignment.ComputeWalkCertificate
        (assignmentOf E hchar a g) :=
    (PlusIOSameExecutionAssignment.computeWalkRAP_wholeTrace_iff
        (assignmentOf E hchar a g)).mp
      (assignmentOf_satisfies_compute_walk E hchar a g)
  have hln := hcert.1.ln1
  have hα : (honestFamily E hchar a g).computeWalkAlpha = a :=
    (honestFamily_endpoints E hchar a g a g).2.2.2.2.1
  exact hln.trans hα

/-- Later-round `W` reads the sampled `αc` in a verifier-facing column. -/
theorem walkArraysOf_computeLn1
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    (walkArraysOf D hchar ω lmb hz).computeLn 1 = alphaC ω := by
  have h := assignmentOf_computeLn1 E hchar (alphaC ω) (gamma ω)
  simpa [walkArraysOf] using h

/-- `W` is not constant in `(αc, γ)`.  Distinct later-round `αc` values
force distinct walk arrays -/
theorem walkArraysOf_nonconstant_on_distinct_alphaC
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a a' g : K) (hne : a ≠ a') :
    walkArraysOf D hchar (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne ≠
      walkArraysOf D hchar (honestCoin E a' g) E.cfg.challenges.lam D.honestSeed_ne := by
  intro hw
  have h1 := walkArraysOf_computeLn1 D hchar (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne
  have h2 := walkArraysOf_computeLn1 D hchar (honestCoin E a' g) E.cfg.challenges.lam D.honestSeed_ne
  have ha : alphaC (honestCoin E a g) = a := (honestCoin_coordinates E a g).1
  have ha' : alphaC (honestCoin E a' g) = a' := (honestCoin_coordinates E a' g).1
  apply hne
  calc
    a = (walkArraysOf D hchar (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeLn 1 :=
      (h1.trans ha).symm
    _ = (walkArraysOf D hchar (honestCoin E a' g) E.cfg.challenges.lam D.honestSeed_ne).computeLn 1 :=
      congrArg (fun W : RawWalkArrays K => W.computeLn 1) hw
    _ = a' := h2.trans ha'

/-- Walk arrays ignore NPR seed and `alphaM` -/
theorem W_reads_only_the_walk_pair
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K)
    (a g αm z αm' z' lmb lmb' : K) (hz : z ≠ 0) (hz' : z' ≠ 0) :
    walkArraysOf D hchar ((a, g), (αm, z)) lmb hz =
      walkArraysOf D hchar ((a, g), (αm', z')) lmb' hz' :=
  walkArraysOf_reads_only_walk_challenges D hchar a g αm z αm' z' lmb lmb' hz hz'

/-- Specialized family still reads the coin's four coordinates. -/
theorem familyAt_still_specializes_the_coin
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    ((rawStrategyOf D hchar).familyAt ω lmb hz).cfg.challenges.z = nprSeed ω ∧
      ((rawStrategyOf D hchar).familyAt ω lmb hz).cfg.challenges.α = alphaM ω ∧
      ((rawStrategyOf D hchar).familyAt ω lmb hz).computeWalkAlpha = alphaC ω ∧
      ((rawStrategyOf D hchar).familyAt ω lmb hz).walkGamma = gamma ω :=
  familyAt_specializes_the_coin D hchar ω lmb hz

/-! ## B. Residual is not `∀ E`; `Data` and `StateTagChar` remain inputs -/

/-- Exhaustive eta: `CommitmentResidual` has no `Accepts` field. -/
theorem commitmentResidual_eta_has_no_Accepts
    {E : BuildableNockExecution F K} (R : CommitmentResidual E) :
    R =
      { verifier := R.verifier
        commitment := R.commitment
        claim_eq := R.claim_eq
        scan := R.scan
        shapeMatch := R.shapeMatch
        rowFrame := R.rowFrame
        slotSemantics := R.slotSemantics
        recordEquations := R.recordEquations
        Λ := R.Λ
        census := R.census
        sizeWindowBound := R.sizeWindowBound
        honestSeed := R.honestSeed
        honestSeed_ne := R.honestSeed_ne
        honestAlpha := R.honestAlpha
        honest_specialization := R.honest_specialization
        computeLineOrigin := R.computeLineOrigin
        q_eq_ringChar := R.q_eq_ringChar
        skeletonBounded := R.skeletonBounded
        combinedBounded := R.combinedBounded
        KszBound := R.KszBound
        progCapacity := R.progCapacity
        memCapacity := R.memCapacity } := by
  cases R
  rfl

/-- Arrays constructor still starts from inhabited `Data` plus named
`StateTagChar` -/
theorem arrays_constructor_projects_data_and_seed
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    (commitmentResidualOfArrays D hchar).q_eq_ringChar = D.q_eq_ringChar ∧
      (commitmentResidualOfArrays D hchar).honestSeed = E.cfg.challenges.z ∧
      (commitmentResidualOfArrays D hchar).honestAlpha = E.cfg.challenges.α :=
  ⟨rfl, rfl, rfl⟩

/-- Hypothetical universal residual still manufactures the named
characteristic equality.  No such constructor is supplied. -/
theorem any_universal_residual_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestArrays.generic_residual_would_force_q_equality (F := F) (K := K) g

theorem any_universal_data_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestArrays.generic_data_would_force_q_equality (F := F) (K := K) g

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem censusRecordPremises_eta_still_five
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

/-! ## C. `StateTagChar` is a real named extra, not `True` and not `1 < q` -/

/-- The named extra is injectivity of `natCast` on `{0,...,11}`. -/
theorem stateTagChar_is_injOn_Iic_eleven :
    NodeEncoding.StateTagChar K =
      Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11) :=
  rfl

/-- `1 < q` does not force `11 < n` -/
theorem one_lt_q_does_not_force_char_gt_eleven :
    ¬ ∀ (q n : ℕ), 1 < q → q ≤ n → 11 < n := by
  intro h
  have hlt : 11 < 2 := h 2 2 (by omega) (by omega)
  omega

/-- Characteristic 2 is compatible with `1 < q` at `q = 2` and fails
`StateTagChar` -/
theorem stateTagChar_fails_at_char_two :
    ¬ NodeEncoding.StateTagChar (ZMod 2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hcast : ((0 : ℕ) : ZMod 2) = ((2 : ℕ) : ZMod 2) :=
    (ZMod.natCast_self 2).symm
  have heq : (0 : ℕ) = 2 :=
    h (by simp : (0 : ℕ) ∈ Set.Iic 11) (by simp : (2 : ℕ) ∈ Set.Iic 11) hcast
  omega

theorem one_lt_two : 1 < 2 := by
  decide

/-- `E.q_gt_one` is only `1 < q` -/
theorem q_gt_one_is_one_lt_q (E : BuildableNockExecution F K) :
    1 < E.q :=
  E.q_gt_one

/-- The extra remains an explicit hypothesis of the arrays constructor. -/
theorem arrays_constructor_takes_named_stateTagChar
    {E : BuildableNockExecution F K} (_D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    NodeEncoding.StateTagChar K :=
  GenericHonestArrays.stateTagChar_stays_named hchar

/-! ## D. `not_forall_omega_accepts` is production raw `Accepts` -/

theorem zero_seed_rejected_by_literal_Accepts
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (lmb : K) :
    ¬ (rawStrategyOf D hchar).Accepts ((0, 0), (0, 0)) lmb := by
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed]

/-- Unfolded: `Accepts` is `RawAccepts` on a nonzero seed and `False`
otherwise -/
theorem not_forall_omega_accepts_is_raw_Accepts
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (lmb : K) :
    ¬ ∀ ω : JointCoins K,
      if hz : nprSeed ω ≠ 0 then
        RawAccepts (rawStrategyOf D hchar).claim
          ((rawStrategyOf D hchar).familyAt ω lmb hz) ω
          ((rawStrategyOf D hchar).messageAt ω lmb hz)
      else False := by
  intro h
  have h0 := h ((0, 0), (0, 0))
  simp [nprSeed] at h0

/-- Fibre completeness of a different package is untouched. -/
theorem not_forall_omega_is_this_rawStrategy
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (rawStrategyOf D hchar).Accepts ω lmb := by
  intro h
  have h0 := h ((0, 0), (0, 0))
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed] at h0

/-! ## E. Residual inhabitant is not production acceptance -/

/-- `hzero` remains on the released builder. -/
theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    -- The package carries `rowsBound`.
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  GenericHonestArrays.released_builder_still_takes_hzero I R hzero hprl hmore hord hordM hrows hgenF hF

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- F73 residual is a `CommitmentResidual`, and its raw strategy still
rejects the zero NPR seed.  Residual inhabitation is not `Accepts`. -/
theorem residual73Honest_is_not_Accepts :
    Nonempty (CommitmentResidual concreteExecution) ∧
      ¬ (rawStrategyOf data73 stateTagChar73).Accepts ((0, 0), (0, 0))
        concreteExecution.cfg.challenges.lam :=
  ⟨residual73Honest_nonvacuous,
    zero_seed_rejected_by_literal_Accepts data73 stateTagChar73 _⟩

/-- Honest F73 walks are not the all-zero placeholder: `ln(1)` equals the
sampled `αc` -/
theorem residual73Honest_walks_read_alphaC (a g : K73cubic) :
    (walkArraysOf data73 stateTagChar73 (honestCoin concreteExecution a g)
        concreteExecution.cfg.challenges.lam data73.honestSeed_ne).computeLn 1 = a :=
  (walkArraysOf_computeLn1 data73 stateTagChar73
      (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).trans
    (honestCoin_coordinates concreteExecution a g).1

/-- Distinct F73 walk coins produce distinct `W`.  Still not `Accepts`. -/
theorem residual73Honest_W_nonconstant :
    walkArraysOf data73 stateTagChar73
        (honestCoin concreteExecution 0 0) concreteExecution.cfg.challenges.lam data73.honestSeed_ne ≠
      walkArraysOf data73 stateTagChar73
        (honestCoin concreteExecution 1 0) concreteExecution.cfg.challenges.lam data73.honestSeed_ne :=
  walkArraysOf_nonconstant_on_distinct_alphaC data73 stateTagChar73
    (0 : K73cubic) 1 0 zero_ne_one

/-- All-zero placeholder `computeLn` is the zero function; honest `W` at
`αc = 1` is not -/
theorem residual73Honest_W_is_not_zeroWalk :
    (walkArraysOf data73 stateTagChar73
        (honestCoin concreteExecution 1 0) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).computeLn 1 ≠
      (zeroWalk (K := K73cubic)).computeLn 1 := by
  have h := residual73Honest_walks_read_alphaC (1 : K73cubic) 0
  intro heq
  have hz : (zeroWalk (K := K73cubic)).computeLn 1 = 0 := rfl
  exact one_ne_zero (h.symm.trans (heq.trans hz))

end Concrete

/-! ## F. -/

inductive ReviewedField104
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

def substantiveFields104 : List ReviewedField104 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields104 : List ReviewedField104 := [.structural]

def residualFields104 : List ReviewedField104 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields104.length = 11 ∧
      typeSummaryFields104.length = 1 ∧
      residualFields104 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields104.length = 2 ∧
      (substantiveFields104 ++ typeSummaryFields104 ++ residualFields104).Nodup ∧
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

#print axioms afterAlphaM_api_is_z_hz_alphaM
#print axioms A_tables_are_the_zero_zero_assignment
#print axioms A_identical_across_distinct_walk_pairs
#print axioms afterCoins_api_is_walkArraysOf
#print axioms assignmentOf_satisfies_compute_walk
#print axioms assignmentOf_computeLn1
#print axioms walkArraysOf_computeLn1
#print axioms walkArraysOf_nonconstant_on_distinct_alphaC
#print axioms W_reads_only_the_walk_pair
#print axioms familyAt_still_specializes_the_coin
#print axioms commitmentResidual_eta_has_no_Accepts
#print axioms arrays_constructor_projects_data_and_seed
#print axioms any_universal_residual_still_forces_q_pin
#print axioms any_universal_data_still_forces_q_pin
#print axioms residualPremises_eta_still_four
#print axioms censusRecordPremises_eta_still_five
#print axioms stateTagChar_is_injOn_Iic_eleven
#print axioms one_lt_q_does_not_force_char_gt_eleven
#print axioms stateTagChar_fails_at_char_two
#print axioms one_lt_two
#print axioms q_gt_one_is_one_lt_q
#print axioms arrays_constructor_takes_named_stateTagChar
#print axioms zero_seed_rejected_by_literal_Accepts
#print axioms not_forall_omega_accepts_is_raw_Accepts
#print axioms not_forall_omega_is_this_rawStrategy
#print axioms released_builder_still_takes_hzero
#print axioms Concrete.residual73Honest_is_not_Accepts
#print axioms Concrete.residual73Honest_walks_read_alphaC
#print axioms Concrete.residual73Honest_W_nonconstant
#print axioms Concrete.residual73Honest_W_is_not_zeroWalk
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.alphaMCommitmentOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.walkArraysOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.walkArraysOf_reads_the_coin
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.commitmentResidualOfArrays
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.not_forall_omega_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.q_gt_one_does_not_give_stateTagChar
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch104
