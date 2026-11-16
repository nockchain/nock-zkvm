import Nock.NockVMROM.Thm54.DistinctCensusWholeJoint
import Nock.NockVMROM.Thm54.EqualityOperandCensus
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Completeness layers at `packageR`: paper text, consumed field, production `Accepts`

This module absorbs that FINDING into production.  It does
**not** import `Nock.RedTeam`.

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

Three layers, recorded separately, not collapsed into one completeness failure:

1. **Paper text** remains unqualified probability-one completeness.
2. **Lean capstone field** `(statementR hfirstD haxR hbasisR hwidthR).perfect_completeness` is algebraic
   `Language` membership of `stmtOfExact` and remains inhabited.
3. **Production `Accepts`** rejects the nonempty SepSeed coin `z = -1`.

The seed denominator is the cubic extension: `K97cubic = GaloisField 97 3`,
hence `|K| = 97^3 = 912673`, not `|F97| = 97`.  Accounting stays
**`11 + 1 + 2`**.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers

open scoped Classical
open Nock Nock.Noun
open Framework Framework.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusWholeJoint
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97cl : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97cl : CharP K97cubic 97 := inferInstance
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

/-! ## A. Consumed field holds; collision rejection does not fail it

The exact consumed field at the paper is algebraic language membership.
Its type contains no `JointCoins` or production `Accepts`. -/

theorem consumed_perfect_completeness_holds :
    Language
      (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) :=
  (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness

/-- Same package, same consumed capstone, and the exact rejected collision
coin.  The capstone field remains inhabited despite rejection. -/
theorem consumed_capstone_holds_despite_collision_rejection :
    OptimizedFullStrictThm54Statement (packageR hfirstD) ∧
      Language
        (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
          (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
        (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) ∧
      ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam :=
  ⟨(statementR hfirstD haxR hbasisR hwidthR),
    consumed_perfect_completeness_holds hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    rejects_collision_seed hfirstD hrootAt hrootAtQ⟩

/-- On this fixed package the algebraic field cannot imply universal coin
acceptance: its antecedent is inhabited and its conclusion has a compiled
counterexample -/
theorem algebraic_field_does_not_entail_forall_Accepts :
    ¬ (Language
          (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
            (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
          (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) →
        ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) := by
  intro h
  exact rejects_collision_seed hfirstD hrootAt hrootAtQ
    (h (consumed_perfect_completeness_holds hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ)
      collisionSeedCoin)

/-- The three layers on one package, without promoting rejection to a
consumed-field failure -/
theorem three_layers_on_same_package :
    Language
      (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) ∧
      OptimizedFullStrictThm54Statement (packageR hfirstD) ∧
      op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} ∧
      ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam ∧
      ¬ (Language
            (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
              (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
            (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) →
          ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :=
  ⟨consumed_perfect_completeness_holds hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    statementR hfirstD haxR hbasisR hwidthR,
    op5Census_badSeeds, rejects_collision_seed hfirstD hrootAt hrootAtQ,
    algebraic_field_does_not_entail_forall_Accepts hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ⟩

omit hfirstD hrootAt hrootAtQ haxR hbasisR hwidthR

/-! ## B. Exact denominator: the cubic extension, not the base field

The seed field is `K97cubic = GaloisField 97 3`, so
`|K| = 97^3 = 912673`, not `|F97| = 97` -/

theorem card_K97cubic_is_97_cubed :
    Fintype.card K97cubic = 97 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 97 3 (by norm_num)

theorem card_K97cubic_is_912673 :
    Fintype.card K97cubic = 912673 := by
  rw [card_K97cubic_is_97_cubed]
  norm_num

theorem card_F97_is_97 : Fintype.card F97 = 97 := by
  rfl

theorem cubic_denominator_is_not_base_denominator :
    Fintype.card K97cubic ≠ Fintype.card F97 := by
  rw [card_K97cubic_is_912673, card_F97_is_97]
  norm_num

theorem collision_density_is_one_over_912673 :
    ((op5Census.census.badSeeds (K := K97cubic)).card : ℚ) /
        (Fintype.card K97cubic : ℚ) =
      (1 : ℚ) / 912673 := by
  rw [op5Census_badSeeds_card, card_K97cubic_is_912673]
  norm_num

theorem collision_density_is_not_one_over_97 :
    ((op5Census.census.badSeeds (K := K97cubic)).card : ℚ) /
        (Fintype.card K97cubic : ℚ) ≠
      (1 : ℚ) / 97 := by
  rw [collision_density_is_one_over_912673]
  norm_num

include hfirstD hrootAt hrootAtQ haxR hbasisR hwidthR
include haxP hbasisP hwidthP haxQ hbasisQ hwidthQ
include haxH hbasisH hwidthH haxD hbasisD hwidthD

/-! ## C. Accounting does not move; capstone and alias untouched -/

theorem accounting_unchanged :
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

theorem frozen_fourteen_fields_capstone_and_alias :
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
  refine ⟨?_, statementR hfirstD haxR hbasisR hwidthR, rfl⟩
  cases (statementR hfirstD haxR hbasisR hwidthR)
  rfl

end

end Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers

#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.consumed_perfect_completeness_holds
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.consumed_capstone_holds_despite_collision_rejection
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.algebraic_field_does_not_entail_forall_Accepts
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.three_layers_on_same_package
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.card_K97cubic_is_97_cubed
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.card_K97cubic_is_912673
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.card_F97_is_97
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.cubic_denominator_is_not_base_denominator
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.collision_density_is_one_over_912673
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.collision_density_is_not_one_over_97
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.accounting_unchanged
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.frozen_fourteen_fields_capstone_and_alias
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
