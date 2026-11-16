import Nock.NockVMROM.Thm54.DistinctCensusWholeJoint
import Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Whole-joint completeness correspondence: paper Pr=1 vs nonempty SepSeed

This module absorbs that FINDING into production.  It does **not** import
`Nock.RedTeam`.

Paper quotes, body then appendix:

* IOP completeness is
  `\Pr[\langle P(x,w),V(x)\rangle=1 | (x,w)\in L] = 1`.
* Theorem 5.4 says the verification of `N` opcodes and `L` memory records
  “has perfect completeness and negligible soundness error if
  `N,L \in negl(K)`”.
* NPR seed `z` is uniformly random.
* `Lem:ion_univariate_sec` bounds the nonempty collision event
  `\Pr_r[fn(n_1;r)=fn(n_2;r); n_1\neq n_2] \le 2\cdot(2\Lambda-1)/|K|`.
* The paper names that bound the “collision soundness error”
  `\epsilon^{\Lambda,F}_{col}`.
* There is no completeness-exception clause for SepSeed in
  `Thm:NockVMROM` or Def:IOP.  Completeness is not stated as `1-\epsilon`.

So this is **not** “the paper already excludes the collision event from
completeness”, and **not** “the paper’s completeness is 1-negligible”.
It is a fixture-level completeness/transcription delta at the consumed
production `Accepts` layer: unqualified probability-one completeness
together with a nonempty SepSeed event and no exclusion.  The construction
is not described as broken.  The released theorem is not weakened to hide
it.  Accounting stays **`11 + 1 + 2`**.

“Largest fragment” remains packageR-relative.  Off-fibre rejection is this
package’s production pin.  `chained_at_honest_sample` exhibits one
specialization; it does not refute every other one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence

open scoped Classical
open Nock Nock.Noun
open Framework Framework.Thm54
open SemanticStrategy SemanticTimestampStrategy
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
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97wjc : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97wjc : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth F97)
include haxR hbasisR hwidthR
variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hfirstD
include hrootAt
include hrootAtQ
variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
variable (hwidthP : FormRWidth F97)
variable (haxQ : FormRAxisBound (packageQ hfirstD).optimized.sampled
    (packageQ hfirstD).optimized.basis)
variable (hbasisQ : FormRBasis (packageQ hfirstD).optimized.basis)
variable (hwidthQ : FormRWidth F97)
variable (haxH : FormRAxisBound (packageH hfirstD).optimized.sampled
    (packageH hfirstD).optimized.basis)
variable (hbasisH : FormRBasis (packageH hfirstD).optimized.basis)
variable (hwidthH : FormRWidth F97)
variable (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled
    (packageD hfirstD).optimized.basis)
variable (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
variable (hwidthD : FormRWidth F97)

/-! ## A. Exact paper claims, compiled as Lean objects that coexist

Consumed `perfect_completeness` is algebraic `Language` membership of
`stmtOfExact`.  It is not `∀ ω, Accepts ω`.
Def:IOP completeness is probability one. -/

theorem consumed_perfect_completeness_is_algebraic_language :
    Language
      (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) :=
  (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness

theorem consumed_perfect_completeness_is_not_forall_omega :
    Language
      (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) ∧
      ¬ ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam :=
  ⟨consumed_perfect_completeness_is_algebraic_language
      hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    not_forall_omega_accepts hfirstD⟩

/-! ## B. Exact SepSeed claim: nonempty singleton, density `1/|K|`,
inside the paper SZ bound, classified as a soundness-union summand

`Lem:ion_univariate_sec` and the named collision
soundness error.  At this census the bad-seed set is
exactly `{−1}`. -/

theorem sepSeed_claim_is_the_singleton_neg_one :
    op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} ∧
      (op5Census.census.badSeeds (K := K97cubic)).card = 1 ∧
      (op5Census.census.badSeeds (K := K97cubic)).Nonempty :=
  ⟨op5Census_badSeeds, op5Census_badSeeds_card, op5Census_badSeeds_nonempty⟩

/-- Fixture seed-density of the collision singleton is `1/|K|`.
This sits inside `2(2Λ-1)/|K|`.  It is the paper's
collision event, not a completeness-exception clause -/
theorem collision_singleton_density_is_one_over_cardK :
    ((op5Census.census.badSeeds (K := K97cubic)).card : ℚ) /
        (Fintype.card K97cubic : ℚ) =
      (1 : ℚ) / (Fintype.card K97cubic : ℚ) := by
  rw [op5Census_badSeeds_card]
  norm_cast

theorem collision_singleton_within_paper_sz_bound :
    (op5Census.census.badSeeds (K := K97cubic)).card ≤
      op5Census.census.count * (2 * 7 - 1) :=
  op5Census_badSeeds_within_paper_bound

theorem collision_event_is_a_soundness_union_summand (lmb : K97cubic) :
    collisionFailureEvent (packageR hfirstD).optimized.census.census ⊆
      ProductionP8Containment.FailureUnion (packageR hfirstD).strategy
        (packageR hfirstD).optimized.census lmb := by
  intro ω hω
  simp only [ProductionP8Containment.FailureUnion]
  exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inl <|
    Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inr hω

theorem collision_coin_in_packageR_event :
    collisionSeedCoin ∈
      collisionFailureEvent (packageR hfirstD).optimized.census.census := by
  rw [mem_collisionFailureEvent_iff]
  have hpair :=
    packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ
  obtain ⟨i, hi, _⟩ := hpair
  refine ⟨i, ?_⟩
  simpa [hi, collisionSeedCoin, nprSeed] using operands_not_sepSeed_at_neg_one

/-- Production `Accepts` rejects the paper collision coin.  That is
conservative sound behavior for honest `OP_5`:
fingerprints collide while the committed result is `atom 1`. -/
theorem rejects_collision_and_honest_eqOp_fails :
    ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam ∧
      ComputeTable.FP.eqOp
          (GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft)
          (GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight) ≠
        (GlobalCarryRecognizer.enc (-1 : K97cubic) op5Result).leaf :=
  ⟨rejects_collision_seed hfirstD hrootAt hrootAtQ, honest_eqOp_fails_at_collision_seed⟩

/-- The transcription/completeness delta at this fixture: algebraic
consumed completeness is inhabited, the SepSeed event is nonempty, and
production `Accepts` rejects that coin.  Neither side is weakened. -/
theorem algebraic_completeness_coexists_with_nonempty_collision_rejection :
    Language
      (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) ∧
      op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} ∧
      collisionSeedCoin ∈
        collisionFailureEvent (packageR hfirstD).optimized.census.census ∧
      ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam :=
  ⟨consumed_perfect_completeness_is_algebraic_language
      hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    op5Census_badSeeds,
    collision_coin_in_packageR_event hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    rejects_collision_seed hfirstD hrootAt hrootAtQ⟩

/-! ## C. Lean `¬ ∀ ω` is strictly stronger than the collision singleton

Zero seed and off-fibre pins are packageR production facts, not the
paper’s `1/|K|` collision set.  So `¬ ∀ ω` is not the honest encoding
of “completeness is 1-negligible” -/

theorem not_forall_omega_is_strictly_stronger_than_collision :
    (¬ (packageR hfirstD).strategy.Accepts zeroSeedCoin cfgD.challenges.lam) ∧
      (¬ (packageR hfirstD).strategy.Accepts offFibreSeedCoin cfgD.challenges.lam) ∧
      (¬ (packageR hfirstD).strategy.Accepts offFibreAlphaCoin cfgD.challenges.lam) ∧
      (¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam) ∧
      (¬ ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :=
  ⟨rejects_zero_seed hfirstD,
    rejects_off_fibre_seed hfirstD hrootAt hrootAtQ,
    rejects_off_fibre_alphaM hfirstD hrootAt hrootAtQ,
    rejects_collision_seed hfirstD hrootAt hrootAtQ, not_forall_omega_accepts hfirstD⟩

theorem no_forall_walk_pair_and_seed_at_fixed_alphaM :
    ¬ ∀ a g z : K97cubic,
        (packageR hfirstD).strategy.Accepts ((a, g), (alphaD, z)) cfgD.challenges.lam := by
  intro h
  exact rejects_zero_seed hfirstD (h 0 0 0)

theorem no_forall_walk_pair_and_alphaM_at_fixed_seed :
    ¬ ∀ a g alpha : K97cubic,
        (packageR hfirstD).strategy.Accepts ((a, g), (alpha, seedD)) cfgD.challenges.lam := by
  intro h
  exact rejects_off_fibre_alphaM hfirstD hrootAt hrootAtQ (h 0 0 5)

/-! ## D. “Largest fragment” is packageR-relative

The compiled fragment is one package outside `∀ a g` on the committed
fibre.  Off-fibre rejection uses `production_acceptance_pins_*` at
`packageR`.  No theorem here says every other package rejects those
coins -/

theorem largest_fragment_is_packageR_on_committed_fibre :
    (∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
      (∀ a g : K97cubic, P.strategy.Accepts (coinQ a g) cfgD.challenges.lam) ∧ P = packageR hfirstD) ∧
      (∀ a g : K97cubic,
        alphaM (coinQ a g) = (4 : K97cubic) ∧
          nprSeed (coinQ a g) = (8 : K97cubic)) :=
  ⟨largest_compiled_fragment hfirstD hrootAt hrootAtQ,
    fragment_is_the_committed_fibre hfirstD hrootAt hrootAtQ⟩

theorem off_fibre_rejection_is_the_packageR_production_pin :
    (¬ (packageR hfirstD).strategy.Accepts offFibreSeedCoin cfgD.challenges.lam) ∧
      (¬ (packageR hfirstD).strategy.Accepts offFibreAlphaCoin cfgD.challenges.lam) ∧
      (¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam) ∧
      (¬ ∀ a g z : K97cubic,
          (packageR hfirstD).strategy.Accepts ((a, g), (alphaD, z)) cfgD.challenges.lam) ∧
      (¬ ∀ a g alpha : K97cubic,
          (packageR hfirstD).strategy.Accepts ((a, g), (alpha, seedD)) cfgD.challenges.lam) :=
  ⟨rejects_off_fibre_seed hfirstD hrootAt hrootAtQ,
    rejects_off_fibre_alphaM hfirstD hrootAt hrootAtQ,
    rejects_collision_seed hfirstD hrootAt hrootAtQ,
    no_forall_walk_pair_and_seed_at_fixed_alphaM hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    no_forall_walk_pair_and_alphaM_at_fixed_seed hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ⟩

/-- `chained_at_honest_sample` exhibits `(seedD, alphaD)`.  Binding holds
at every pair.  This is not uninhabitance at every other specialization. -/
theorem chained_compiled_at_honest_sample_and_binds_everywhere :
    ChainedAtSpecialization hfirstD seedD alphaD cfgD.challenges.lam seedH_ne ∧
      ∀ z α lmb : K97cubic,
        BindsAt z (dataD hfirstD).skeleton
          ((configTemplateOf (distinctCensusExecution hfirstD) z).specialize α lmb)
          (((dataD hfirstD).executionTemplate z).specialize α lmb) :=
  ⟨chained_at_honest_sample hfirstD hrootAt hrootAtQ,
    binds_at_every_specialization hfirstD hrootAt hrootAtQ⟩

/-! ## E. Accounting does not move; capstone untouched -/

theorem accounting_unchanged
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97)
    (haxQ : FormRAxisBound (packageQ hfirstD).optimized.sampled
      (packageQ hfirstD).optimized.basis)
    (hbasisQ : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidthQ : FormRWidth F97)
    (haxH : FormRAxisBound (packageH hfirstD).optimized.sampled
      (packageH hfirstD).optimized.basis)
    (hbasisH : FormRBasis (packageH hfirstD).optimized.basis)
    (hwidthH : FormRWidth F97)
    (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled
      (packageD hfirstD).optimized.basis)
    (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidthD : FormRWidth F97) :
    (11 + 1 + 2 = 14) ∧
      (∀ a g : K97cubic, (packageR hfirstD).strategy.Accepts (coinQ a g) cfgD.challenges.lam) ∧
      (¬ ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageR hfirstD)) ∧
      (8 + 1 + 5 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageQ hfirstD)) ∧
      (8 + 1 + 5 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageH hfirstD)) ∧
      (7 + 1 + 6 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageD hfirstD)) ∧
      (9 + 1 + 4 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageP hmoreM)) :=
  DistinctCensusWholeJoint.accounting_unchanged
    hfirstD hrootAt hrootAtQ hmoreM
    haxR hbasisR hwidthR
    haxP hbasisP hwidthP haxQ hbasisQ hwidthQ
    haxH hbasisH hwidthH haxD hbasisD hwidthD

theorem consumed_capstone_is_inhabited :
    OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  optimizedFullStrictNockVMROM_of_package (packageR hfirstD) haxR hbasisR hwidthR

theorem frozen_statement_untouched :
    (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness =
      (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness ∧
      OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  ⟨rfl, consumed_capstone_is_inhabited
    hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ⟩

end

end Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence

#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.consumed_perfect_completeness_is_algebraic_language
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.consumed_perfect_completeness_is_not_forall_omega
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.sepSeed_claim_is_the_singleton_neg_one
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.collision_singleton_density_is_one_over_cardK
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.collision_singleton_within_paper_sz_bound
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.collision_event_is_a_soundness_union_summand
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.collision_coin_in_packageR_event
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.rejects_collision_and_honest_eqOp_fails
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.algebraic_completeness_coexists_with_nonempty_collision_rejection
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.not_forall_omega_is_strictly_stronger_than_collision
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.no_forall_walk_pair_and_seed_at_fixed_alphaM
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.no_forall_walk_pair_and_alphaM_at_fixed_seed
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.largest_fragment_is_packageR_on_committed_fibre
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.off_fibre_rejection_is_the_packageR_production_pin
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.chained_compiled_at_honest_sample_and_binds_everywhere
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.accounting_unchanged
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.consumed_capstone_is_inhabited
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.frozen_statement_untouched
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
