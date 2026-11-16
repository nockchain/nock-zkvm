import Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
import Nock.RedTeam.Batch79Thm54AcceptingPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# nonzero walk challenges and quantifier order

Paper frame:
the paper,
1813-1843,1864-1868,2049-2088,2258-2303`.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The principal scope control is the quantifier order.  The production theorem constructs a
package separately for each `(a,g)` and proves that package accepts its own coin.  Its
`afterAlphaM` table/IO commitment closes over `(a,g)`, even though the type of each resulting
commitment does not expose those later coins.  Thus the compiled result is
`∀ a g, Accepts (packageHonestN hmoreM a g) (coinN a g)`, not one fixed package accepting all pairs.
-/

namespace Nock.RedTeam.Batch80

open scoped Classical Polynomial
open Nock Nock.Noun Nock.Walk Nock.NockVMROM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
variable (haxM : FormRAxisBound (packageHonestM hmoreM).optimized.sampled
    (packageHonestM hmoreM).optimized.basis)
variable (hbasisM : FormRBasis (packageHonestM hmoreM).optimized.basis)
variable (hwidthM : FormRWidth F97)
variable (hax : FormRAxisBound (packageNonzero hmoreM).optimized.sampled
    (packageNonzero hmoreM).optimized.basis)
variable (hbasis : FormRBasis (packageNonzero hmoreM).optimized.basis)
variable (hwidth : FormRWidth F97)

/-! ## A. Exact quantifier order and phase attribution -/

/-- This is the exact positive parametric theorem proved earlier. -/
theorem compiled_per_tuple_scope
    (hrootAt : ∀ a g, (packageHonestN hmoreM a g).strategy.RootAxisBoundaryAt
      (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    ∀ a g : K97cubic,
      (packageHonestN hmoreM a g).strategy.Accepts (coinN a g) cfgS.challenges.lam :=
  fun a g => packageHonestN_accepts hmoreM a g (hrootAt a g)

/-- The nonzero specialization is a genuine existential package/coin witness. -/
theorem compiled_nonzero_existential_scope
    (hrootAt : (packageNonzero hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinNonzero) seedM_ne (alphaM coinNonzero)) :
    ∃ (P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 4)
        (ω : JointCoins K97cubic),
      alphaC ω ≠ 0 ∧ gamma ω ≠ 0 ∧ P.strategy.Accepts ω cfgS.challenges.lam ∧
        ω ∉ FailureUnion P.strategy P.optimized.census cfgS.challenges.lam ∧
        GenuineTargetAt P.strategy 97 3 ω cfgS.challenges.lam :=
  ⟨packageNonzero hmoreM, coinNonzero, alphaCN_ne_zero, gammaN_ne_zero,
    packageNonzero_accepts hmoreM hrootAt, coinNonzero_not_failureUnion hmoreM,
    genuineTargetNonzero hmoreM hrootAt⟩

/-- The pre-`(alphaC,gamma)` commitment of each constructed strategy is nevertheless selected by
the outer pair indexing the strategy.  The phase-correct type does not prove cross-package
noninterference. -/
theorem precoin_commitment_is_pair_indexed
    (a g z : K97cubic) (hz : z ≠ 0) (α : K97cubic) :
    (rawStrategyN a g).afterAlphaM z hz α cfgS.challenges.lam = alphaMCommitmentN a g z hz α cfgS.challenges.lam :=
  rfl

/-- In particular, the table and IO data sent at the `afterAlphaM` phase are read from the
`Classical.choice` completion indexed by `(a,g)`. -/
theorem precoin_arrays_are_pair_completion_indexed
    (a g z : K97cubic) (hz : z ≠ 0) (α : K97cubic) :
    ((rawStrategyN a g).afterAlphaM z hz α cfgS.challenges.lam).tables.compute =
        (honestAssignmentN a g).computeTableAux ∧
      ((rawStrategyN a g).afterAlphaM z hz α cfgS.challenges.lam).tables.memory =
        (honestAssignmentN a g).memoryTableAux ∧
      ((rawStrategyN a g).afterAlphaM z hz α cfgS.challenges.lam).io.progAcc =
        (honestAssignmentN a g).exactIO.progAcc ∧
      ((rawStrategyN a g).afterAlphaM z hz α cfgS.challenges.lam).io.memAcc =
        (honestAssignmentN a g).exactIO.memAcc :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The earlier theorems invoke separate choice terms, even at `(0,0)`. -/
theorem separate_choice_origins :
    honestCompletionM = Classical.choice honestCompletionM_nonempty ∧
      honestCompletionN 0 0 = Classical.choice (honestCompletionN_nonempty 0 0) :=
  ⟨rfl, rfl⟩

/-- `atCoins` itself only inserts the later two coins: the problem, encoders, and endpoint arrays
of one fixed `AlphaMFamilyData` object are unchanged. -/
theorem atCoins_fixture_nonsplicing
    (a₁ g₁ a₂ g₂ : K97cubic) :
    (rawFamilyN a₁ g₁).problem = (rawFamilyN a₂ g₂).problem ∧
      (rawFamilyN a₁ g₁).compNodeEncode = (rawFamilyN a₂ g₂).compNodeEncode ∧
      (rawFamilyN a₁ g₁).memNodeEncode = (rawFamilyN a₂ g₂).memNodeEncode ∧
      (rawFamilyN a₁ g₁).requests = (rawFamilyN a₂ g₂).requests ∧
      (rawFamilyN a₁ g₁).responses = (rawFamilyN a₂ g₂).responses ∧
      (rawFamilyN a₁ g₁).outMem = (rawFamilyN a₂ g₂).outMem := by
  have h := AlphaMFamilyData.nonSplicing
    (familyDataM0 servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam) a₁ g₁ a₂ g₂
  exact ⟨h.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- The fixed execution and committed skeleton are threaded through every pair-indexed package. -/
theorem pair_packages_share_execution_and_skeleton (a g : K97cubic) :
    (packageHonestN hmoreM a g).objects.cfg = cfgS ∧
      (packageHonestN hmoreM a g).objects.exec = execS ∧
      (packageHonestN hmoreM a g).strategy.skeleton = skelM :=
  ⟨rfl, rfl, rfl⟩

/-- Acceptance by the fixed raw strategy `rawStrategyN a g` pins `alphaC` to `a`, because its
walk arrays ignore their coin argument while `WalkSat.ln1` enforces `ln(1)=alphaC`. -/
theorem rawStrategyN_accepts_only_alphaC
    (a g : K97cubic) (ω : JointCoins K97cubic) (hz : nprSeed ω ≠ 0)
    (hacc : (rawStrategyN a g).Accepts ω cfgS.challenges.lam) :
    alphaC ω = a := by
  have hsixω := ((rawStrategyN a g).accepts_iff_six_families ω cfgS.challenges.lam hz).1 hacc
  have hcertω :=
    ((rawStrategyN a g).messageAt ω cfgS.challenges.lam hz).computeWalkRAP_wholeTrace_iff.mp
      hsixω.2.2.2.1
  have hsixTarget :=
    ((rawStrategyN a g).accepts_iff_six_families (coinN a g) cfgS.challenges.lam seedM_ne).1
      (rawStrategyN_accepts_coinN a g)
  have hcertTarget :=
    ((rawStrategyN a g).messageAt (coinN a g) cfgS.challenges.lam seedM_ne).computeWalkRAP_wholeTrace_iff.mp
      hsixTarget.2.2.2.1
  have hω := hcertω.1.ln1
  have ht := hcertTarget.1.ln1
  change (honestAssignmentN a g).computeWalk.ln 1 = alphaC ω at hω
  change (honestAssignmentN a g).computeWalk.ln 1 = a at ht
  exact hω.symm.trans ht

/-- Consequently this particular fixed raw strategy cannot accept two tuples with distinct
`alphaC` coordinates. -/
theorem rawStrategyN_two_acceptances_same_alphaC
    (a g : K97cubic) (ω₁ ω₂ : JointCoins K97cubic)
    (hz₁ : nprSeed ω₁ ≠ 0) (hz₂ : nprSeed ω₂ ≠ 0)
    (h₁ : (rawStrategyN a g).Accepts ω₁ cfgS.challenges.lam)
    (h₂ : (rawStrategyN a g).Accepts ω₂ cfgS.challenges.lam) :
    alphaC ω₁ = alphaC ω₂ :=
  (rawStrategyN_accepts_only_alphaC a g ω₁ hz₁ h₁).trans
    (rawStrategyN_accepts_only_alphaC a g ω₂ hz₂ h₂).symm

/-- The downstream package theorem accepts arbitrary supplied phase functions `A` and `W`; it
contains no cross-pair array-independence premise. -/
theorem downstream_has_no_cross_pair_independence_premise
    (A : ∀ (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic),
      AlphaMCommitment (p := ringChar K97cubic) dataM.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K97cubic) (_lmb : K97cubic), nprSeed ω ≠ 0 → RawWalkArrays K97cubic)
    (hax : FormRAxisBound
      (BuildablePackage.buildFullPackage multiRootExecution inputsM
        (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (residualOf_generated A W) f97_primeField).optimized.sampled
      (BuildablePackage.buildFullPackage multiRootExecution inputsM
        (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (residualOf_generated A W) f97_primeField).optimized.basis)
    (hbasis : FormRBasis
      (BuildablePackage.buildFullPackage multiRootExecution inputsM
        (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (residualOf_generated A W) f97_primeField).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedFullStrictThm54Statement
      (BuildablePackage.buildFullPackage multiRootExecution inputsM
        (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (residualOf_generated A W) f97_primeField) :=
  statementM_of_arrays hmoreM A W hax hbasis hwidth

/-! ## B. -/

noncomputable def alteredAcceptingChallenges : Finset K97cubic :=
  Finset.univ.filter fun α =>
    ∃ ln count acc : ℕ → K97cubic,
      WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc α
        (alteredCurN 1 * α) α 2 ∧ acc 2 = 0

theorem alteredAcceptingChallenges_eq_singleton :
    alteredAcceptingChallenges = {0} := by
  ext α
  simp [alteredAcceptingChallenges, altered_walk_accepting_challenge_iff]

theorem alteredAcceptingChallenges_card :
    alteredAcceptingChallenges.card = 1 ∧ alteredAcceptingChallenges.card ≤ 2 := by
  rw [alteredAcceptingChallenges_eq_singleton]
  simp

theorem rejection_receipt_exact :
    (¬ IsFullBFT alteredCurN alteredChildN alteredFanoutN 2) ∧
      alteredAcceptingChallenges = {0} ∧
      (¬ ∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc alphaCN
          (alteredCurN 1 * alphaCN) alphaCN 2 ∧ acc 2 = 0) :=
  ⟨alteredN_not_isFullBFT, alteredAcceptingChallenges_eq_singleton,
    altered_non_bft_walk_rejected_at_alphaCN.2⟩

theorem nine_coordinate_shift_and_nonzero_gamma :
    Fintype.card (Fin 9) = 9 ∧
      (∀ c : Fin 9,
        ComputeLinkPayload.encode (computeActualPayload badComputeTreeN 0) c =
          ComputeLinkPayload.encode (computeExpectedPayload badComputeTreeN 0) c +
            (if c = 1 then 1 else 0)) ∧
      (∀ γ : K97cubic, γ ≠ 0 → γ ∉ computeSlotBadGammas badComputeTreeN 0) :=
  ⟨by decide, badComputeTreeN_single_unit_shift, nonzero_gamma_not_bad_for_unbound_treeN⟩

/-! ## C. Failure union, recount, and localization -/

/-- The production failure union has exactly the five enumerated components. -/
theorem failure_union_exactly_five (a g : K97cubic) :
    FailureUnion (packageHonestN hmoreM a g).strategy (packageHonestN hmoreM a g).optimized.census cfgS.challenges.lam =
      ((((zeroSeedFailureEvent ∪ collisionFailureEvent (packageHonestN hmoreM a g).optimized.census.census) ∪
        specializedTopologyFailureEvent (packageHonestN hmoreM a g).strategy.verifier.raw cfgS.challenges.lam) ∪
        guardedAxisFailureEvent (packageHonestN hmoreM a g).strategy cfgS.challenges.lam) ∪
        SizeWindowCounting.SizeWindowFailure (packageHonestN hmoreM a g).strategy.skeleton) :=
  rfl


theorem all_five_exclusions (a g : K97cubic) :
    coinN a g ∉ (zeroSeedFailureEvent : Finset (JointCoins K97cubic)) ∧
      coinN a g ∉ collisionFailureEvent censusM.census ∧
      coinN a g ∉ specializedTopologyFailureEvent (verifierN a g).raw cfgS.challenges.lam ∧
      coinN a g ∉ guardedAxisFailureEvent (packageHonestN hmoreM a g).strategy cfgS.challenges.lam ∧
      coinN a g ∉ SizeWindowCounting.SizeWindowFailure skelM :=
  ⟨coinN_not_zeroSeedFailureEvent a g, coinN_not_collisionFailureEvent a g,
    coinN_not_specializedTopologyFailureEvent a g,
    coinN_not_guardedAxisFailureEvent hmoreM a g, coinN_not_sizeWindowFailure a g⟩


theorem fourteen_field_statement_eta
    {P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 4}
    (S : OptimizedFullStrictThm54Statement P) :
    S =
      { structural := S.structural
        optimized_chips := S.optimized_chips
        shared_io := S.shared_io
        perfect_completeness := S.perfect_completeness
        containment := S.containment
        walk_bounds := S.walk_bounds
        p8_fixed_field_soundness := S.p8_fixed_field_soundness
        p8_fixed_field_bits := S.p8_fixed_field_bits
        acceptance_to_target := S.acceptance_to_target
        complete_false_acceptance_bound := S.complete_false_acceptance_bound
        complete_false_acceptance_bits := S.complete_false_acceptance_bits
        staged_false_acceptance_bound := S.staged_false_acceptance_bound
        exact_resources := S.exact_resources
        row_budgets := S.row_budgets
        shared_forest_axis := S.shared_forest_axis } := by
  cases S
  rfl

theorem batch79_batch80_statement_shapes_both_inhabited
    (haxM : FormRAxisBound (packageHonestM hmoreM).optimized.sampled
      (packageHonestM hmoreM).optimized.basis)
    (hbasisM : FormRBasis (packageHonestM hmoreM).optimized.basis)
    (hwidthM : FormRWidth F97)
    (hax : FormRAxisBound (packageNonzero hmoreM).optimized.sampled
      (packageNonzero hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageNonzero hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    Nonempty (OptimizedFullStrictThm54Statement (packageHonestM hmoreM)) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageNonzero hmoreM)) :=
  ⟨⟨statementHonestM hmoreM haxM hbasisM hwidthM⟩, ⟨statementNonzero hmoreM hax hbasis hwidth⟩⟩

/-- The earlier exact compiled localization, without classifying the two fixed-field fields. -/
theorem localization_receipt
    (hrootAt : (packageNonzero hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinNonzero) seedM_ne (alphaM coinNonzero))
    (hax : FormRAxisBound (packageNonzero hmoreM).optimized.sampled
      (packageNonzero hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageNonzero hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    (∃ ω : JointCoins K97cubic, (packageNonzero hmoreM).strategy.Accepts ω cfgS.challenges.lam) ∧
      (FalseAcceptanceSet (packageNonzero hmoreM).strategy 97 3 cfgS.challenges.lam ⊆
        Finset.univ.filter fun ω =>
          (packageNonzero hmoreM).strategy.Accepts ω cfgS.challenges.lam ∧
            ω ∈ FailureUnion (packageNonzero hmoreM).strategy (packageNonzero hmoreM).optimized.census cfgS.challenges.lam) ∧
      (∀ ω ∈ FalseAcceptanceSet (packageNonzero hmoreM).strategy 97 3 cfgS.challenges.lam,
        ω ∉ (zeroSeedFailureEvent : Finset (JointCoins K97cubic)) ∧
          ω ∈ FailureUnion (packageNonzero hmoreM).strategy (packageNonzero hmoreM).optimized.census cfgS.challenges.lam) ∧
      coinNonzero ∉ FalseAcceptanceSet (packageNonzero hmoreM).strategy 97 3 cfgS.challenges.lam := by
  refine ⟨packageHonestN_acceptance_nonempty hmoreM alphaCN gammaN hrootAt, ?subset, ?zero, coinNonzero_not_falseAcceptance hmoreM hrootAt⟩
  · exact
      falseAcceptanceN_subset_accepted_inside_failureUnion hmoreM alphaCN gammaN hax hbasis hwidth
  · simpa [packageNonzero] using
      falseAcceptanceN_not_zeroSeed hmoreM alphaCN gammaN hax hbasis hwidth

/-! ## D. Remaining stated limits and release regression -/

theorem batch79_memory_walk_challenge_was_nonzero :
    alphaM coinM = fixtureAlpha ∧ fixtureAlpha ≠ (0 : K97cubic) := by
  constructor
  · rfl
  · intro hk
    have hbase : (4 : F97) ≠ 0 := by decide
    apply hbase
    apply (algebraMap F97 K97cubic).injective
    simpa only [map_ofNat, map_zero, fixtureAlpha] using hk

theorem same_execution_regression :
    (packageNonzero hmoreM).objects.cfg = cfgS ∧ (packageNonzero hmoreM).objects.exec = execS ∧
      (packageNonzero hmoreM).computeChip.rap.w = 303 ∧ (packageNonzero hmoreM).computeChip.rap.s =
        418 ∧
      (packageNonzero hmoreM).memoryChip.rap.w = 205 ∧ (packageNonzero hmoreM).memoryChip.rap.s = 156 ∧
      (packageNonzero hmoreM).computeChip.rap.H.card = 2 :=
  packageNonzero_regression hmoreM

theorem released_aliases_and_control_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch79.released_aliases_unchanged

#print axioms compiled_per_tuple_scope
#print axioms compiled_nonzero_existential_scope
#print axioms precoin_commitment_is_pair_indexed
#print axioms precoin_arrays_are_pair_completion_indexed
#print axioms separate_choice_origins
#print axioms atCoins_fixture_nonsplicing
#print axioms pair_packages_share_execution_and_skeleton
#print axioms rawStrategyN_accepts_only_alphaC
#print axioms rawStrategyN_two_acceptances_same_alphaC
#print axioms downstream_has_no_cross_pair_independence_premise
#print axioms alteredAcceptingChallenges_eq_singleton
#print axioms alteredAcceptingChallenges_card
#print axioms rejection_receipt_exact
#print axioms nine_coordinate_shift_and_nonzero_gamma
#print axioms failure_union_exactly_five
#print axioms all_five_exclusions
#print axioms fourteen_field_statement_eta
#print axioms batch79_batch80_statement_shapes_both_inhabited
#print axioms localization_receipt
#print axioms batch79_memory_walk_challenge_was_nonzero
#print axioms same_execution_regression
#print axioms released_aliases_and_control_unchanged

#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.packageHonestN_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinN_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.genuineTargetN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.nonzero_challenge_witness
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.altered_walk_accepting_challenge_iff
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.badComputeTreeN_single_unit_shift
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.nonzero_gamma_not_bad_for_unbound_treeN
#print axioms
  Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.falseAcceptanceN_subset_accepted_inside_failureUnion
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.falseAcceptanceN_not_zeroSeed
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinNonzero_not_falseAcceptance
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.p8_fixed_field_status

#print axioms «Thm:IO_result»
#print axioms «Thm:Walk_IOP»
#print axioms «Corr:forest»
#print axioms «Thm:deterministic_Trace»
#print axioms «Lem:NPR_decomp»
#print axioms «Thm:Noun_Validation»
#print axioms «Thm:comp_38»
#print axioms «Thm:mem_38»
#print axioms «Thm:NockVMROM»
#print axioms «Lem:equiv_compute»
#print axioms «Lem:equiv_mem»
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch80
