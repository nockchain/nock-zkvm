import Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance
import Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Whole-joint completeness: largest compiled fragment and obstruction

Theorem 5.4 claims perfect completeness.  The paper samples more than
the walk pair `(αc, γ)`:

* walk `α, γ` after the leaf-walk commitment;
* timestamp powers `(α, α², α³)`;
* RAP inputs `(a, b, c)`;
* NPR seed `z` uniform.

Lean `JointCoins` is `((αc, γ), (αm, z))`.  This fixture freezes `(a, b, c) = (0, 0, 1)`
in `configTemplateOf` (`HonestCommitment`, from `cfgD`).  Current completeness is

> `∃ P, ∀ a g, P.strategy.Accepts (coinQ a g) cfgD.challenges.lam`

with `P = packageR` **outside** the quantifier, on the committed fibre
`(alphaM, nprSeed) = (4, 8)` only.

This module does **not** weaken `Accepts`.  It compiles that fragment, compiles that
`∀ ω` fails at this package, and compiles why a seed-varying package over the same
`dataD` census is not assembled: `afterAlphaM` tables are the seed-`8` assignment
while the problem specializes at the coin, production acceptance pins the fibre
, and honest `OP_5` `eqOp` fails at the unique collision seed `z = -1`.

Accounting stays **`11 + 1 + 2`**.  `OptimizedFullStrictThm54Statement`, the capstone,
the alias, the forest control, `packageP`, and `hzero` are untouched.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.DistinctCensusWholeJoint

open scoped Classical
open Nock Nock.Noun
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
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97wj : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97wj : CharP K97cubic 97 := inferInstance
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

/-! ## A. Paper coordinates vs this fixture

Walk `α, γ` are sampled after the walk commitment.
Timestamp `α` and NPR seed `z` are RAP inputs. -/

theorem config_template_freezes_rap_inputs (z : K97cubic) :
    (configTemplateOf (distinctCensusExecution hfirstD) z).challenges.a = 0 ∧
      (configTemplateOf (distinctCensusExecution hfirstD) z).challenges.b = 0 ∧
      (configTemplateOf (distinctCensusExecution hfirstD) z).challenges.c = 1 :=
  ⟨rfl, rfl, rfl⟩

theorem jointCoins_are_four_coordinates (ω : JointCoins K97cubic) :
    ω = ((alphaC ω, gamma ω), (alphaM ω, nprSeed ω)) := by
  rcases ω with ⟨⟨a, g⟩, ⟨α, z⟩⟩
  rfl

/-- The largest compiled completeness fragment: one package outside `∀ a g`,
on the committed fibre only.  This is **not** `∀ ω` -/
theorem largest_compiled_fragment :
    ∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
      (∀ a g : K97cubic, P.strategy.Accepts (coinQ a g) cfgD.challenges.lam) ∧
        P = packageR hfirstD :=
  ⟨packageR hfirstD, packageR_accepts hfirstD hrootAt hrootAtQ, rfl⟩

theorem fragment_is_the_committed_fibre (a g : K97cubic) :
    alphaM (coinQ a g) = (4 : K97cubic) ∧ nprSeed (coinQ a g) = (8 : K97cubic) :=
  ⟨rfl, rfl⟩

theorem fragment_quantifier_order :
    (∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
      ∀ a g : K97cubic, P.strategy.Accepts (coinQ a g) cfgD.challenges.lam) ∧
      ¬ ∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
          P = packageR hfirstD ∧ ∀ ω : JointCoins K97cubic, P.strategy.Accepts ω cfgD.challenges.lam := by
  refine ⟨⟨packageR hfirstD, packageR_accepts hfirstD hrootAt hrootAtQ⟩, ?_⟩
  rintro ⟨P, hP, hω⟩
  have h0 := hω ((0, 0), (alphaD, 0))
  exact accepts_seed_ne_zero (hP ▸ h0) rfl

/-! ## B. Mixed assignment: which JointCoins coordinates later-round arrays read

`afterCoins` is a function of `(αc, γ)` only.
`afterAlphaM` tables are the seed-`8` / `alphaM = 4` assignment at every
`(z, α)`; the specialized *problem* still reads the coin. -/

theorem walkArraysQ_reads_only_walk_challenges
    (a g αm z αm' z' : K97cubic) (hz : z ≠ 0) (hz' : z' ≠ 0) :
    walkArraysQ hfirstD ((a, g), (αm, z)) cfgD.challenges.lam hz = walkArraysQ hfirstD ((a, g), (αm', z')) cfgD.challenges.lam hz' :=
  rfl

theorem afterAlphaM_tables_ignore_seed_and_alphaM
    (z z' α α' : K97cubic) (hz : z ≠ 0) (hz' : z' ≠ 0) :
    (alphaMCommitmentQ hfirstD z hz α cfgD.challenges.lam).tables.compute =
        (alphaMCommitmentQ hfirstD z' hz' α' cfgD.challenges.lam).tables.compute ∧
      (alphaMCommitmentQ hfirstD z hz α cfgD.challenges.lam).tables.memory =
        (alphaMCommitmentQ hfirstD z' hz' α' cfgD.challenges.lam).tables.memory :=
  ⟨rfl, rfl⟩

theorem afterAlphaM_tables_are_the_seed8_assignment
    (z : K97cubic) (hz : z ≠ 0) (α : K97cubic) :
    (alphaMCommitmentQ hfirstD z hz α cfgD.challenges.lam).tables.compute =
      (assignmentQ hfirstD 0 0).computeTableAux ∧
      (alphaMCommitmentQ hfirstD z hz α cfgD.challenges.lam).tables.memory =
        (assignmentQ hfirstD 0 0).memoryTableAux :=
  alphaMCommitmentQ_tables_are_the_seed8_assignment hfirstD hrootAt hrootAtQ z hz α

theorem familyAt_specializes_the_coin (ω : JointCoins K97cubic) (hz : nprSeed ω ≠ 0) :
    ((rawStrategyQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.challenges.z = nprSeed ω ∧
      ((rawStrategyQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.challenges.α = alphaM ω ∧
      ((rawStrategyQ hfirstD).familyAt ω cfgD.challenges.lam hz).computeWalkAlpha = alphaC ω ∧
      ((rawStrategyQ hfirstD).familyAt ω cfgD.challenges.lam hz).walkGamma = gamma ω :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## C. `∀ ω` fails at this package: zero seed, then off-fibre pins

`Accepts` is definitionally `False` on a zero NPR seed.  Production acceptance
pins the remaining fibre `(nprSeed, alphaM) = (8, 4)`. -/

def zeroSeedCoin : JointCoins K97cubic := ((0, 0), (alphaD, 0))

def offFibreSeedCoin : JointCoins K97cubic := ((0, 0), (alphaD, 1))

def offFibreAlphaCoin : JointCoins K97cubic := ((0, 0), (5, seedD))

def collisionSeedCoin : JointCoins K97cubic := ((0, 0), (alphaD, -1))

omit hrootAt hrootAtQ in
theorem rejects_zero_seed : ¬ (packageR hfirstD).strategy.Accepts zeroSeedCoin cfgD.challenges.lam := by
  intro h
  exact accepts_seed_ne_zero h rfl

omit hrootAt hrootAtQ in
theorem not_forall_omega_accepts :
    ¬ ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam := by
  intro h
  exact rejects_zero_seed hfirstD (h zeroSeedCoin)

omit hfirstD hrootAt hrootAtQ in
theorem one_ne_eight_K97 : (1 : K97cubic) ≠ 8 := by
  intro h
  have hbase : (7 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  have h7 : (7 : K97cubic) = 0 := by linear_combination -h
  simpa only [map_ofNat, map_zero] using h7

omit hfirstD hrootAt hrootAtQ in
theorem five_ne_four_K97 : (5 : K97cubic) ≠ 4 := by
  intro h
  have hbase : (1 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  have h1 : (1 : K97cubic) = 0 := by linear_combination h
  simpa only [map_one, map_zero] using h1

theorem rejects_off_fibre_seed : ¬ (packageR hfirstD).strategy.Accepts offFibreSeedCoin cfgD.challenges.lam := by
  intro h
  have hpin := production_acceptance_pins_seed hfirstD hrootAt hrootAtQ offFibreSeedCoin h
  exact one_ne_eight_K97 (hpin.trans (show seedD = (8 : K97cubic) from rfl))

theorem rejects_off_fibre_alphaM : ¬ (packageR hfirstD).strategy.Accepts offFibreAlphaCoin cfgD.challenges.lam := by
  intro h
  have hpin := production_acceptance_pins_alphaM hfirstD hrootAt hrootAtQ offFibreAlphaCoin h
  exact five_ne_four_K97 (hpin.trans (show alphaD = (4 : K97cubic) from rfl))

theorem rejects_collision_seed : ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam := by
  intro h
  have hpin := production_acceptance_pins_seed hfirstD hrootAt hrootAtQ collisionSeedCoin h
  exact eight_ne_neg_one_K97
    ((show seedD = (8 : K97cubic) from rfl).symm.trans hpin.symm)

/-! ## D. SepSeed uniqueness is a singleton, and honest `OP_5` `eqOp` fails there

`Lem:ion_univariate_sec` is a probability over `r`, not a
promise that one seed separates every pair.  At this census the bad-seed set is
exactly `{-1}`.  Nock `=` on fingerprints returns `0` when they collide and `1`
otherwise; the committed result noun is `atom 1`. -/

omit hfirstD hrootAt hrootAtQ in
theorem sepSeed_uniqueness_is_a_singleton :
    op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} :=
  op5Census_badSeeds

omit hfirstD hrootAt hrootAtQ in
theorem collision_seed_is_nonzero : (-1 : K97cubic) ≠ 0 := by
  intro h
  exact (one_ne_zero (α := K97cubic)) (by linear_combination -h)

omit hfirstD hrootAt hrootAtQ in
theorem enc_operands_eq_at_collision_seed :
    GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft =
      GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight := by
  have hfn : NPR.fn operandLeft (-1 : K97cubic) =
      NPR.fn operandRight (-1 : K97cubic) :=
    (operands_fn_eq_iff (-1)).mpr rfl
  rw [GlobalCarryRecognizer.enc_eq_fn, GlobalCarryRecognizer.enc_eq_fn, hfn]

omit hfirstD hrootAt hrootAtQ in
/-- Honest `OP_5` evaluation is `1` (unequal).  At the collision seed the
fingerprints agree, so `eqOp` returns `0`.  Completeness of a re-rendered
row therefore fails at `z = -1` -/
theorem honest_eqOp_fails_at_collision_seed :
    ComputeTable.FP.eqOp
        (GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft)
        (GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight) ≠
      (GlobalCarryRecognizer.enc (-1 : K97cubic) op5Result).leaf := by
  rw [enc_operands_eq_at_collision_seed, ComputeTable.FP.eqOp, if_pos rfl]
  rw [show op5Result = Noun.atom 1 from rfl, GlobalCarryRecognizer.enc_atom,
    ComputeTable.FP.atomFP]
  exact zero_ne_one

/-! ## E. The missing seed-varying bridge, inhabited only at the honest sample

`dataD.binds z α` holds at every pair.  `jointVerification_complete` still needs `ChainedSemanticExactLanguage` at the
specialized execution.  That is compiled at `(seedD, alphaD)` and not
constructed for a general `(z, α)`. -/

def ChainedAtSpecialization (z α lmb : K97cubic) (hz : z ≠ 0) : Prop :=
  ChainedSemanticExactLanguage
    (specializedProblem (timestampD hfirstD) z hz α lmb).cfg
    (specializedProblem (timestampD hfirstD) z hz α lmb).exec

theorem chained_at_honest_sample :
    ChainedAtSpecialization hfirstD seedD alphaD cfgD.challenges.lam seedH_ne := by
  unfold ChainedAtSpecialization
  rw [specializedProblemD_honest hfirstD]
  exact chainedD hfirstD

theorem binds_at_every_specialization (z α lmb : K97cubic) :
    BindsAt z (dataD hfirstD).skeleton
      ((configTemplateOf (distinctCensusExecution hfirstD) z).specialize α lmb)
      (((dataD hfirstD).executionTemplate z).specialize α lmb) :=
  (dataD hfirstD).binds z α lmb

/-! ## F. Accounting does not move -/

theorem accounting_unchanged
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97)
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
  ⟨by norm_num, packageR_accepts hfirstD hrootAt hrootAtQ, not_forall_omega_accepts hfirstD,
    ⟨statementR hfirstD haxR hbasisR hwidthR⟩,
    by norm_num, ⟨statementQ hfirstD haxQ hbasisQ hwidthQ⟩,
    by norm_num, ⟨statementH hfirstD haxH hbasisH hwidthH⟩,
    by norm_num, ⟨statementD hfirstD haxD hbasisD hwidthD⟩,
    by norm_num, ⟨statementP hmoreM haxP hbasisP hwidthP⟩⟩

theorem consumed_capstone_is_inhabited 
    (hax : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidth : FormRWidth F97):
    OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth

end

end Nock.NockVMROM.Thm54.DistinctCensusWholeJoint

#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.config_template_freezes_rap_inputs
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.largest_compiled_fragment
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.fragment_is_the_committed_fibre
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.fragment_quantifier_order
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.walkArraysQ_reads_only_walk_challenges
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.afterAlphaM_tables_ignore_seed_and_alphaM
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.familyAt_specializes_the_coin
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.rejects_zero_seed
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.not_forall_omega_accepts
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.rejects_off_fibre_seed
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.rejects_off_fibre_alphaM
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.rejects_collision_seed
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.sepSeed_uniqueness_is_a_singleton
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.honest_eqOp_fails_at_collision_seed
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.chained_at_honest_sample
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.binds_at_every_specialization
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.accounting_unchanged
#print axioms Nock.NockVMROM.Thm54.DistinctCensusWholeJoint.consumed_capstone_is_inhabited
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR
