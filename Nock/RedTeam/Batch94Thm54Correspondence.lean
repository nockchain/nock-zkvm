import Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed Lean objects:
`DistinctCensusFold2.(packageR hfirstD)`,
`ProductionP8Containment.ProductionStrategy.Accepts`,
`OptimizedFullStrictThm54Statement (packageR hfirstD)`, and
`optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth`.

Result: FINDING with a scoped pass on the literal Lean correspondence facts.

The paper text is unqualified: Def:IOP states probability-one completeness, Theorem 5.4 says perfect completeness, and the NPR seed is uniform.
The only collision qualification found in the complete body/appendix/proof
search is the collision *soundness* error;
there is no completeness exception or `1 - epsilon` completeness statement.

The Lean capstone, however, does not consume universal coin acceptance as its
`perfect_completeness` field.  It consumes only algebraic `Language`
membership of the fixed `stmtOfExact`.  This field is inhabited on the same
`(packageR hfirstD)` for which production `Accepts` rejects the collision coin.
Consequently the collision rejection is not a failure of the consumed Lean
capstone field.  The honest disposition is a wrong-layer finding against
that characterization: the paper-to-Lean perfect-completeness transcription
is weaker/different, while the consumed field itself holds.

The seed denominator is the cubic extension field:
`K97cubic = GaloisField 97 3`, hence `|K97cubic| = 97^3 = 912673`, not `97`.
Accounting remains exactly `11 + 1 + 2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch94

open scoped Classical
open Nock Nock.Noun
open Nock.NockVMROM
open Framework Framework.Thm54
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
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97b94 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b94 : CharP K97cubic 97 := inferInstance
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

/-! ## A. Wrong-layer attack: the consumed field holds -/

/-- The exact consumed field at the paper is algebraic language
membership.  Its type contains no `JointCoins` or production `Accepts`. -/
theorem consumed_perfect_completeness_exact_field :
    Language
      (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) :=
  (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem neg_one_ne_eight_independent : (-1 : K97cubic) ≠ 8 := by
  intro h
  have hbase : (9 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  have h9 : (9 : K97cubic) = 0 := by linear_combination -h
  simpa only [map_ofNat, map_zero] using h9

theorem collision_rejected_by_literal_production_Accepts :
    ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam := by
  intro h
  have hp := production_acceptance_pins_seed hfirstD hrootAt hrootAtQ collisionSeedCoin h
  exact neg_one_ne_eight_independent
    ((show (-1 : K97cubic) = nprSeed collisionSeedCoin from rfl).trans
      (hp.trans (show seedD = (8 : K97cubic) from rfl)))

/-- Same package, same consumed capstone, and the exact rejected collision
coin.  This proves the capstone field remains inhabited despite rejection. -/
theorem consumed_capstone_holds_despite_collision_rejection :
    OptimizedFullStrictThm54Statement (packageR hfirstD) ∧
      Language
        (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
          (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
        (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) ∧
      ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam :=
  ⟨(statementR hfirstD haxR hbasisR hwidthR), (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness,
    collision_rejected_by_literal_production_Accepts
      hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ⟩

/-- On this fixed package the algebraic field cannot imply universal coin
acceptance: its antecedent is inhabited and its conclusion has a compiled
counterexample. -/
theorem algebraic_field_does_not_entail_forall_Accepts :
    ¬ (Language
          (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
            (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
          (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) →
        ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) := by
  intro h
  exact collision_rejected_by_literal_production_Accepts
      hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ
    (h (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness collisionSeedCoin)

/-! ## B. Collision classification and non-vacuous coexistence -/

theorem collision_event_is_in_consumed_soundness_union :
    collisionSeedCoin ∈
        collisionFailureEvent (packageR hfirstD).optimized.census.census ∧
      collisionFailureEvent (packageR hfirstD).optimized.census.census ⊆
        ProductionP8Containment.FailureUnion (packageR hfirstD).strategy
          (packageR hfirstD).optimized.census cfgD.challenges.lam := by
  constructor
  · rw [mem_collisionFailureEvent_iff]
    obtain ⟨i, hi, _⟩ :=
      packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ
    refine ⟨i, ?_⟩
    simpa [hi, collisionSeedCoin, nprSeed] using operands_not_sepSeed_at_neg_one
  · intro ω hω
    simp only [ProductionP8Containment.FailureUnion]
    exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inl <|
      Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inr hω

/-- The coexistence claim is not `True` and does not detach its objects:
the capstone, algebraic field, exact singleton, consumed event membership, and
production rejection all use the same literal `(packageR hfirstD)`. -/
theorem same_package_nonvacuous_coexistence :
    OptimizedFullStrictThm54Statement (packageR hfirstD) ∧
      Language
        (Tag F97 K97cubic (packageR hfirstD).objects.cfg.challenges.α
          (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
        (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) ∧
      op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} ∧
      collisionSeedCoin ∈
        collisionFailureEvent (packageR hfirstD).optimized.census.census ∧
      ¬ (packageR hfirstD).strategy.Accepts collisionSeedCoin cfgD.challenges.lam :=
  ⟨optimizedFullStrictNockVMROM_of_package (packageR hfirstD) haxR hbasisR hwidthR,
    (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness, op5Census_badSeeds,
    (collision_event_is_in_consumed_soundness_union
      hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ).1,
    collision_rejected_by_literal_production_Accepts
      hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ⟩

/-! ## C. Exact denominator: the cubic extension, not the base field -/

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem card_K97cubic_is_97_cubed :
    Fintype.card K97cubic = 97 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 97 3 (by norm_num)

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem card_K97cubic_is_912673 :
    Fintype.card K97cubic = 912673 := by
  rw [card_K97cubic_is_97_cubed]
  norm_num

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem card_F97_is_97 : Fintype.card F97 = 97 := by
  rfl

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem cubic_denominator_is_not_base_denominator :
    Fintype.card K97cubic ≠ Fintype.card F97 := by
  rw [card_K97cubic_is_912673, card_F97_is_97]
  norm_num

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem collision_density_is_one_over_912673 :
    ((op5Census.census.badSeeds (K := K97cubic)).card : ℚ) /
        (Fintype.card K97cubic : ℚ) =
      (1 : ℚ) / 912673 := by
  rw [op5Census_badSeeds_card, card_K97cubic_is_912673]
  norm_num

/-! ## D. -/

inductive ReviewedField94
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

def substantiveFields94 : List ReviewedField94 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets, .shared_forest_axis]

def typeSummaryFields94 : List ReviewedField94 := [.structural]

def residualFields94 : List ReviewedField94 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

omit haxR hbasisR hwidthR hfirstD hrootAt hrootAtQ in
theorem exact_eleven_one_two_accounting :
    substantiveFields94.length = 11 ∧
      typeSummaryFields94.length = 1 ∧
      residualFields94 =
        [.complete_false_acceptance_bound, .complete_false_acceptance_bits] ∧
      residualFields94.length = 2 ∧
      (substantiveFields94 ++ typeSummaryFields94 ++ residualFields94).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

theorem frozen_fourteen_fields_capstone_and_alias :
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
  refine ⟨?_, optimizedFullStrictNockVMROM_of_package (packageR hfirstD) haxR hbasisR hwidthR, rfl⟩
  cases (statementR hfirstD haxR hbasisR hwidthR)
  rfl

#print axioms consumed_perfect_completeness_exact_field
#print axioms neg_one_ne_eight_independent
#print axioms collision_rejected_by_literal_production_Accepts
#print axioms consumed_capstone_holds_despite_collision_rejection
#print axioms algebraic_field_does_not_entail_forall_Accepts
#print axioms collision_event_is_in_consumed_soundness_union
#print axioms same_package_nonvacuous_coexistence
#print axioms card_K97cubic_is_97_cubed
#print axioms card_K97cubic_is_912673
#print axioms card_F97_is_97
#print axioms cubic_denominator_is_not_base_denominator
#print axioms collision_density_is_one_over_912673
#print axioms exact_eleven_one_two_accounting
#print axioms frozen_fourteen_fields_capstone_and_alias
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusWholeJointCorrespondence.algebraic_completeness_coexists_with_nonempty_collision_rejection
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch94
