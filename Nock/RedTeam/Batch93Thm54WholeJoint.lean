import Nock.NockVMROM.Thm54.DistinctCensusWholeJoint
import Nock.NockVMROM.Thm54.CompilerFoldCorrespondence
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed Lean objects:
`DistinctCensusFold2.packageR`,
`ProductionP8Containment.ProductionStrategy.Accepts`,
`OptimizedFullStrictThm54Statement (packageR hfirstD)`, and
`optimizedFullStrictNockVMROM_of_package packageR`.

The package really is outside the walk-pair quantifier, and production
`Accepts` really rejects zero seed and the three explicit off-fibre coins.
Neither `forall a g z` at fixed `alphaM = 4` nor `forall alphaM` at fixed
`z = 8` is inhabited at `packageR`.

The collision seed `z = -1` is the paper's actual SepSeed bad event for the
consumed unequal OP_5 pair, not a Lean-only compiler fold.  Rejecting that coin
is conservative: the two fingerprints coincide while honest Nock equality
returns the committed result `atom 1`.  But the paper's IOP completeness
definition requires probability exactly one over prover/verifier coins, and Theorem 5.4 claims perfect completeness.  The nonempty sampled collision event therefore exposes a
completeness/transcription delta at this fixture.  It is not a soundness defect.

The word "largest" is verified only relative to `packageR` and the two natural
one-coordinate extensions attacked below.  No theorem here rules out a new
package whose committed tables match every specialization.  Likewise,
`chained_at_honest_sample` exhibits one specialization; it does not prove
uninhabitance at every other specialization.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch93

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk
open Framework Framework.Reify Framework.Thm54
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
open Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance
open Nock.NockVMROM.Thm54.DistinctCensusWholeJoint
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.CompilerFoldCorrespondence
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97b93 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b93 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth F97)
variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hfirstD
include hrootAt
include hrootAtQ

/-! ## A. Quantifier order: one literal package -/

/-- The same closed definition is used at two distinct walk pairs.  The
package is not reconstructed under either pair -/
theorem one_literal_package_at_two_distinct_pairs :
    (fun _ _ : K97cubic => packageR hfirstD) 0 0 =
        (fun _ _ : K97cubic => packageR hfirstD) alphaCN gammaN ∧
      alphaCN ≠ 0 ∧ gammaN ≠ 0 ∧
      (packageR hfirstD).strategy.Accepts (coinQ 0 0) cfgD.challenges.lam ∧
      (packageR hfirstD).strategy.Accepts (coinQ alphaCN gammaN) cfgD.challenges.lam :=
  ⟨rfl, alphaCN_ne_zero, gammaN_ne_zero,
    packageR_accepts hfirstD hrootAt hrootAtQ 0 0,
    packageR_accepts hfirstD hrootAt hrootAtQ alphaCN gammaN⟩

/-- Exact exists-before-forall shape, with the witness identified after the
universal acceptance field -/
theorem packageR_is_outside_the_walk_pair_quantifier :
    ∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
      (∀ a g : K97cubic, P.strategy.Accepts (coinQ a g) cfgD.challenges.lam) ∧ P = packageR hfirstD :=
  ⟨packageR hfirstD, packageR_accepts hfirstD hrootAt hrootAtQ, rfl⟩

/-! ## B. Literal production `Accepts` rejects explicit coins -/

def zeroSeed93 : JointCoins K97cubic := ((0, 0), (alphaD, 0))
def offSeed93 : JointCoins K97cubic := ((0, 0), (alphaD, 1))
def offAlpha93 : JointCoins K97cubic := ((0, 0), (5, seedD))
def collision93 : JointCoins K97cubic := ((0, 0), (alphaD, -1))

theorem zero_seed_rejected_by_literal_production_Accepts :
    ¬ ProductionStrategy.Accepts (packageR hfirstD).strategy zeroSeed93 cfgD.challenges.lam := by
  intro h
  have hz0 : nprSeed zeroSeed93 = 0 := by
    rfl
  rw [ProductionStrategy.Accepts,
    dif_neg (fun hz => hz hz0)] at h
  exact h

omit hfirstD hrootAt hrootAtQ in
theorem one_ne_eight_independent : (1 : K97cubic) ≠ 8 := by
  intro h
  have hbase : (7 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  have h7 : (7 : K97cubic) = 0 := by linear_combination -h
  simpa only [map_ofNat, map_zero] using h7

omit hfirstD hrootAt hrootAtQ in
theorem five_ne_four_independent : (5 : K97cubic) ≠ 4 := by
  intro h
  have hbase : (1 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  have h1 : (1 : K97cubic) = 0 := by linear_combination h
  simpa only [map_one, map_zero] using h1

omit hfirstD hrootAt hrootAtQ in
theorem neg_one_ne_eight_independent : (-1 : K97cubic) ≠ 8 := by
  intro h
  have hbase : (9 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  have h9 : (9 : K97cubic) = 0 := by linear_combination -h
  simpa only [map_ofNat, map_zero] using h9

theorem exact_four_rejections :
    (¬ (packageR hfirstD).strategy.Accepts zeroSeed93 cfgD.challenges.lam) ∧
      (¬ (packageR hfirstD).strategy.Accepts offSeed93 cfgD.challenges.lam) ∧
      (¬ (packageR hfirstD).strategy.Accepts offAlpha93 cfgD.challenges.lam) ∧
      (¬ (packageR hfirstD).strategy.Accepts collision93 cfgD.challenges.lam) := by
  refine ⟨zero_seed_rejected_by_literal_production_Accepts hfirstD hrootAt hrootAtQ, ?_, ?_, ?_⟩
  · intro h
    have hp := production_acceptance_pins_seed hfirstD hrootAt hrootAtQ offSeed93 h
    exact one_ne_eight_independent
      (hp.trans (show seedD = (8 : K97cubic) from rfl))
  · intro h
    have hp := production_acceptance_pins_alphaM hfirstD hrootAt hrootAtQ offAlpha93 h
    exact five_ne_four_independent
      (hp.trans (show alphaD = (4 : K97cubic) from rfl))
  · intro h
    have hp := production_acceptance_pins_seed hfirstD hrootAt hrootAtQ collision93 h
    exact neg_one_ne_eight_independent
      ((show (-1 : K97cubic) = nprSeed collision93 from rfl).trans
        (hp.trans (show seedD = (8 : K97cubic) from rfl)))

/-- Wrong-layer guard: failure is at the exact `(packageR hfirstD).strategy.Accepts`. -/
theorem not_every_joint_coin_is_accepted :
    ¬ ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam := by
  intro h
  exact (exact_four_rejections hfirstD hrootAt hrootAtQ).1 (h zeroSeed93)

/-! ## C. Attack the two larger package-R fragments -/

/-- Fixing `alphaM = 4` does not permit universal NPR seed completeness:
the quantified family contains the zero seed -/
theorem no_forall_walk_pair_and_seed_at_fixed_alphaM :
    ¬ ∀ a g z : K97cubic,
        (packageR hfirstD).strategy.Accepts ((a, g), (alphaD, z)) cfgD.challenges.lam := by
  intro h
  exact zero_seed_rejected_by_literal_production_Accepts hfirstD hrootAt hrootAtQ (h 0 0 0)

/-- Fixing `z = 8` does not permit universal timestamp-`alphaM`
completeness: production acceptance pins `alphaM = 4`. -/
theorem no_forall_walk_pair_and_alphaM_at_fixed_seed :
    ¬ ∀ a g alpha : K97cubic,
        (packageR hfirstD).strategy.Accepts ((a, g), (alpha, seedD)) cfgD.challenges.lam := by
  intro h
  have hp := production_acceptance_pins_alphaM hfirstD hrootAt hrootAtQ offAlpha93 (h 0 0 5)
  exact five_ne_four_independent
    (hp.trans (show alphaD = (4 : K97cubic) from rfl))

/-! ## D. Collision seed: paper event, conservative rejection, completeness delta -/

omit hfirstD hrootAt hrootAtQ in
theorem operands_remain_distinct_nouns : operandLeft ≠ operandRight :=
  operands_ne

omit hfirstD hrootAt hrootAtQ in
theorem independent_collision_fingerprints_equal :
    GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft =
      GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight := by
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · rw [GlobalCarryRecognizer.enc_size, GlobalCarryRecognizer.enc_size,
      operands_leaves_eq]
  · rw [GlobalCarryRecognizer.enc_dyck, GlobalCarryRecognizer.enc_dyck,
      operands_dyckBits_eq]
  · rw [GlobalCarryRecognizer.enc_leaf, GlobalCarryRecognizer.enc_leaf,
      leafPoly_eval_left, leafPoly_eval_right]
    ring

omit hfirstD hrootAt hrootAtQ in
/-- At the collision seed, fingerprint equality computes Nock `=` as zero,
while the semantic execution committed result is `atom 1`. -/
theorem independent_collision_eqOp_zero_result_one :
    ComputeTable.FP.eqOp
        (GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft)
        (GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight) = 0 ∧
      (GlobalCarryRecognizer.enc (-1 : K97cubic) op5Result).leaf = 1 := by
  constructor
  · rw [independent_collision_fingerprints_equal,
      ComputeTable.FP.eqOp, if_pos rfl]
  · rw [show op5Result = Noun.atom 1 from rfl, GlobalCarryRecognizer.enc_atom,
      ComputeTable.FP.atomFP]
    rfl

/-- The event is the consumed package census's exact SepSeed event, and the
final production predicate rejects it.  This is not an `MTree` witness. -/
theorem consumed_collision_event_and_rejection :
    op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} ∧
      collision93 ∈
        collisionFailureEvent (packageR hfirstD).optimized.census.census ∧
      ¬ (packageR hfirstD).strategy.Accepts collision93 cfgD.challenges.lam := by
  refine ⟨op5Census_badSeeds, ?_, (exact_four_rejections hfirstD hrootAt hrootAtQ).2.2.2⟩
  rw [mem_collisionFailureEvent_iff]
  have hpair :=
    packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ
  obtain ⟨i, hi, _⟩ := hpair
  refine ⟨i, ?_⟩
  simpa [hi, collision93, nprSeed] using operands_not_sepSeed_at_neg_one

/-- The conservative rejection and the failed honest equality computation
occur together on a nonempty paper collision event. -/
theorem collision_rejection_is_sound_but_not_perfectly_complete :
    operandLeft ≠ operandRight ∧
      GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft =
        GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight ∧
      ComputeTable.FP.eqOp
          (GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft)
          (GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight) = 0 ∧
      (GlobalCarryRecognizer.enc (-1 : K97cubic) op5Result).leaf = 1 ∧
      ¬ (packageR hfirstD).strategy.Accepts collision93 cfgD.challenges.lam :=
  ⟨operands_remain_distinct_nouns,
    independent_collision_fingerprints_equal,
    independent_collision_eqOp_zero_result_one.1,
    independent_collision_eqOp_zero_result_one.2,
    (exact_four_rejections hfirstD hrootAt hrootAtQ).2.2.2⟩

/-! ## E. Mixed assignment and semantic/compiler challenge separation -/

/-- The pre-coin configuration freezes exactly the OP_5 semantic RLC inputs
`(a,b,c)=(0,0,1)` -/
theorem fixture_semantic_abc_are_zero_zero_one (z : K97cubic) :
    (configTemplateOf (distinctCensusExecution hfirstD) z).challenges.a = 0 ∧
      (configTemplateOf (distinctCensusExecution hfirstD) z).challenges.b = 0 ∧
      (configTemplateOf (distinctCensusExecution hfirstD) z).challenges.c = 1 :=
  ⟨rfl, rfl, rfl⟩

theorem op5_slots_are_not_compiler_slot36 :
    exactFinalChallengeWith
        (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
        (inputsR hfirstD).computeChallenges 2 = (0 : K97cubic) ∧
      exactFinalChallengeWith
        (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
        (inputsR hfirstD).computeChallenges 3 = (0 : K97cubic) ∧
      exactFinalChallengeWith
        (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
        (inputsR hfirstD).computeChallenges 4 = (1 : K97cubic) ∧
      finalScalarChallengeBase = 36 ∧
      computeChallenge (distinctCensusExecution hfirstD) (inputsR hfirstD)
        finalScalarChallengeBase = 0 ∧
      (2 : ℕ) ≠ 36 ∧ (3 : ℕ) ≠ 36 ∧ (4 : ℕ) ≠ 36 :=
  ⟨rfl, rfl, rfl, rfl, computeChallenge_slot36 (distinctCensusExecution hfirstD) (inputsR hfirstD),
    by decide, by decide, by decide⟩

/-- Later-round walk arrays depend only on `(alphaC,gamma)` and ignore the
two earlier coordinates -/
theorem walks_read_only_the_walk_pair
    (a g alpha z alpha' z' : K97cubic)
    (hz : z ≠ 0) (hz' : z' ≠ 0) :
    walkArraysQ hfirstD ((a, g), (alpha, z)) cfgD.challenges.lam hz =
      walkArraysQ hfirstD ((a, g), (alpha', z')) cfgD.challenges.lam hz' :=
  rfl

/-! ## F. Exact accounting and consumed capstone -/

inductive ReviewedField
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

def substantiveFields : List ReviewedField :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets, .shared_forest_axis]

def typeSummaryFields : List ReviewedField := [.structural]

def residualFields : List ReviewedField :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem exact_eleven_one_two_accounting :
    substantiveFields.length = 11 ∧
      typeSummaryFields.length = 1 ∧
      residualFields =
        [.complete_false_acceptance_bound, .complete_false_acceptance_bits] ∧
      residualFields.length = 2 ∧
      (substantiveFields ++ typeSummaryFields ++ residualFields).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- The finding does not mutate the package-conditional theorem. -/
theorem frozen_statement_and_consumed_capstone :
    statementR hfirstD haxR hbasisR hwidthR =
      { structural := (statementR hfirstD haxR hbasisR hwidthR).structural
        optimized_chips := (statementR hfirstD haxR hbasisR hwidthR).optimized_chips
        shared_io := (statementR hfirstD haxR hbasisR hwidthR).shared_io
        perfect_completeness := (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness
        containment := (statementR hfirstD haxR hbasisR hwidthR).containment
        walk_bounds := (statementR hfirstD haxR hbasisR hwidthR).walk_bounds
        p8_fixed_field_soundness := (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness
        p8_fixed_field_bits := (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits
        acceptance_to_target := (statementR hfirstD haxR hbasisR hwidthR).acceptance_to_target
        complete_false_acceptance_bound :=
          (statementR hfirstD haxR hbasisR hwidthR).complete_false_acceptance_bound
        complete_false_acceptance_bits :=
          (statementR hfirstD haxR hbasisR hwidthR).complete_false_acceptance_bits
        staged_false_acceptance_bound :=
          (statementR hfirstD haxR hbasisR hwidthR).staged_false_acceptance_bound
        exact_resources := (statementR hfirstD haxR hbasisR hwidthR).exact_resources
        row_budgets := (statementR hfirstD haxR hbasisR hwidthR).row_budgets
        shared_forest_axis := (statementR hfirstD haxR hbasisR hwidthR).shared_forest_axis } ∧
      OptimizedFullStrictThm54Statement (packageR hfirstD) ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package := by
  refine ⟨?_, optimizedFullStrictNockVMROM_of_package (packageR hfirstD) haxR hbasisR hwidthR, rfl⟩
  cases (statementR hfirstD haxR hbasisR hwidthR)
  rfl

#print axioms one_literal_package_at_two_distinct_pairs
#print axioms packageR_is_outside_the_walk_pair_quantifier
#print axioms zero_seed_rejected_by_literal_production_Accepts
#print axioms exact_four_rejections
#print axioms not_every_joint_coin_is_accepted
#print axioms no_forall_walk_pair_and_seed_at_fixed_alphaM
#print axioms no_forall_walk_pair_and_alphaM_at_fixed_seed
#print axioms operands_remain_distinct_nouns
#print axioms independent_collision_fingerprints_equal
#print axioms independent_collision_eqOp_zero_result_one
#print axioms consumed_collision_event_and_rejection
#print axioms collision_rejection_is_sound_but_not_perfectly_complete
#print axioms fixture_semantic_abc_are_zero_zero_one
#print axioms op5_slots_are_not_compiler_slot36
#print axioms walks_read_only_the_walk_pair
#print axioms exact_eleven_one_two_accounting
#print axioms frozen_statement_and_consumed_capstone

#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.largest_compiled_fragment
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.not_forall_omega_accepts
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.honest_eqOp_fails_at_collision_seed
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch93
