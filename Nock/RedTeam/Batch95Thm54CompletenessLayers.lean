import Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed Lean objects:
`DistinctCensusFold2.(packageR hfirstD)`,
`OptimizedFullStrictThm54Statement (packageR hfirstD)`,
`optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth`,
and `ProductionP8Containment.ProductionStrategy.Accepts`.

Result: scoped PASS.  The consumed algebraic field is inhabited on the same
literal package whose production predicate rejects `collisionSeedCoin`.
`K97cubic` has cardinality `97^3 = 912673`, so the singleton density is
`1/912673`, not `1/97`.  It does not identify algebraic `Language` with universal
coin acceptance and does not close generic `CommitmentResidual` or construct
seed-varying tables.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch95

open scoped Classical
open Nock Nock.Noun
open Framework Framework.Thm54
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
open Nock.NockVMROM.Thm54.DistinctCensusWholeJoint
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97b95 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b95 : CharP K97cubic 97 := inferInstance
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

/-! ## A. Capstone and exact algebraic field are independently inhabited -/

theorem independent_capstone_inhabited :
    OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  optimizedFullStrictNockVMROM_of_package (packageR hfirstD) haxR hbasisR hwidthR

/-- Exact projection from the independently replayed capstone.  The conclusion
is `Language (stmtOfExact...)`, not a coin-acceptance proposition. -/
theorem independent_capstone_perfect_completeness_field :
    Language
      (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) :=
  (independent_capstone_inhabited hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ).perfect_completeness

theorem independent_statementR_perfect_completeness_field :
    Language
      (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) :=
  (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness

/-- `Language` unfolds to an accepted verifier witness. -/
theorem consumed_language_unfolds_to_verifier_witness :
    Language
        (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
          (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
        (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) ↔
      ∃ w : VMSystem.Witness
          (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
            (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz),
        VMSystem.accepts
          (ι := Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
            (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
          (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) w :=
  Iff.rfl

/-- Closed witness form of the consumed field, for non-vacuity. -/
theorem consumed_language_has_verifier_witness :
    ∃ w : VMSystem.Witness
        (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
          (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz),
      VMSystem.accepts
        (ι := Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
          (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
        (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) w :=
  independent_capstone_perfect_completeness_field
    hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ

/-! ## B. Same-package collision rejection and non-entailment -/

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem neg_one_ne_eight_independent : (-1 : K97cubic) ≠ 8 := by
  intro h
  have hbase : (9 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  have h9 : (9 : K97cubic) = 0 := by linear_combination -h
  simpa only [map_ofNat, map_zero] using h9

theorem independent_collision_coin_rejected :
    ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam := by
  intro h
  have hp := production_acceptance_pins_seed hfirstD hrootAt hrootAtQ collisionSeedCoin h
  exact neg_one_ne_eight_independent
    ((show (-1 : K97cubic) = nprSeed collisionSeedCoin from rfl).trans
      (hp.trans (show seedD = (8 : K97cubic) from rfl)))

/-- The capstone, its exact field, and the real rejected coin all use the same
literal `(packageR hfirstD)`; there are no independently quantified packages. -/
theorem independent_same_package_capstone_field_and_rejection :
    OptimizedFullStrictThm54Statement (packageR hfirstD) ∧
      Language
        (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
          (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
        (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) ∧
      ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam :=
  ⟨independent_capstone_inhabited hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    independent_capstone_perfect_completeness_field
      hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    independent_collision_coin_rejected hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ⟩

/-- Negative control with the explicit collision coin: the inhabited algebraic
field does not entail universal production acceptance on `(packageR hfirstD)`. -/
theorem independent_language_does_not_entail_forall_Accepts :
    ¬ (Language
          (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
            (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
          (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) →
        ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) := by
  intro h
  exact independent_collision_coin_rejected
      hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ
    (h (independent_capstone_perfect_completeness_field
          hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ) collisionSeedCoin)

/-! ## C. Cubic cardinality and literal singleton density -/

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem independent_card_K97cubic_is_97_cubed :
    Fintype.card K97cubic = 97 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 97 3 (by norm_num)

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem independent_card_K97cubic_is_912673 :
    Fintype.card K97cubic = 912673 := by
  rw [independent_card_K97cubic_is_97_cubed]
  norm_num

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem independent_card_F97_is_97 : Fintype.card F97 = 97 := by
  rfl

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem independent_cubic_card_is_not_base_card :
    Fintype.card K97cubic ≠ Fintype.card F97 := by
  rw [independent_card_K97cubic_is_912673, independent_card_F97_is_97]
  norm_num

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem literal_neg_one_singleton_density_is_one_over_card :
    ((({(-1 : K97cubic)} : Finset K97cubic).card : ℚ) /
        (Fintype.card K97cubic : ℚ)) =
      (1 : ℚ) / (Fintype.card K97cubic : ℚ) := by
  simp

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem literal_neg_one_singleton_density_is_one_over_912673 :
    ((({(-1 : K97cubic)} : Finset K97cubic).card : ℚ) /
        (Fintype.card K97cubic : ℚ)) =
      (1 : ℚ) / 912673 := by
  rw [literal_neg_one_singleton_density_is_one_over_card,
    independent_card_K97cubic_is_912673]
  norm_num

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem consumed_bad_seed_density_is_one_over_912673 :
    ((op5Census.census.badSeeds (K := K97cubic)).card : ℚ) /
        (Fintype.card K97cubic : ℚ) =
      (1 : ℚ) / 912673 := by
  rw [op5Census_badSeeds, independent_card_K97cubic_is_912673]
  norm_num

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem consumed_bad_seed_density_is_not_one_over_97 :
    ((op5Census.census.badSeeds (K := K97cubic)).card : ℚ) /
        (Fintype.card K97cubic : ℚ) ≠
      (1 : ℚ) / 97 := by
  rw [consumed_bad_seed_density_is_one_over_912673]
  norm_num

/-! ## D. -/

inductive ReviewedField95
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

def substantiveFields95 : List ReviewedField95 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets, .shared_forest_axis]

def typeSummaryFields95 : List ReviewedField95 := [.structural]

def residualFields95 : List ReviewedField95 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields95.length = 11 ∧
      typeSummaryFields95.length = 1 ∧
      residualFields95 =
        [.complete_false_acceptance_bound, .complete_false_acceptance_bits] ∧
      residualFields95.length = 2 ∧
      (substantiveFields95 ++ typeSummaryFields95 ++ residualFields95).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

theorem independent_frozen_fourteen_fields_capstone_and_alias :
    (statementR hfirstD haxR hbasisR hwidthR) =
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
  refine ⟨?_, independent_capstone_inhabited hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ, rfl⟩
  cases (statementR hfirstD haxR hbasisR hwidthR)
  rfl

#print axioms independent_capstone_inhabited
#print axioms independent_capstone_perfect_completeness_field
#print axioms independent_statementR_perfect_completeness_field
#print axioms consumed_language_unfolds_to_verifier_witness
#print axioms consumed_language_has_verifier_witness
#print axioms neg_one_ne_eight_independent
#print axioms independent_collision_coin_rejected
#print axioms independent_same_package_capstone_field_and_rejection
#print axioms independent_language_does_not_entail_forall_Accepts
#print axioms independent_card_K97cubic_is_97_cubed
#print axioms independent_card_K97cubic_is_912673
#print axioms independent_card_F97_is_97
#print axioms independent_cubic_card_is_not_base_card
#print axioms literal_neg_one_singleton_density_is_one_over_card
#print axioms literal_neg_one_singleton_density_is_one_over_912673
#print axioms consumed_bad_seed_density_is_one_over_912673
#print axioms consumed_bad_seed_density_is_not_one_over_97
#print axioms independent_exact_eleven_one_two_accounting
#print axioms independent_frozen_fourteen_fields_capstone_and_alias
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.consumed_perfect_completeness_holds
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.consumed_capstone_holds_despite_collision_rejection
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.algebraic_field_does_not_entail_forall_Accepts
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.three_layers_on_same_package
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.card_K97cubic_is_912673
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.collision_density_is_one_over_912673
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.accounting_unchanged
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch95
