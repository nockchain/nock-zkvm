import Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed Lean objects:
`DistinctCensusFold2.packageR`,
`OptimizedFullStrictThm54Statement packageR`, and
`optimizedFullStrictNockVMROM_of_package packageR`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch92

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk
open Framework Framework.Reify Framework.Thm54
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97b92 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b92 : CharP K97cubic 97 := inferInstance
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

abbrev boundR : ℚ :=
  optimizedProductionFailureProbabilityBound
    (Fintype.card K97cubic) (Fintype.card F97)
    (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
      OptimizedHostileTimestamps.timestampCollisionBound
        (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
        pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
    ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
    (packageR hfirstD).optimized.family.problem.cfg.compRows
    (packageR hfirstD).optimized.family.problem.cfg.memRows

/-! ## A. -/

/-- In particular,
the support condition is exactly `boundR hfirstD * 2^b ≤ 1`. -/
theorem exact_frozen_bits_projection :
    ∀ (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
      (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]) (b : ℕ),
      boundR hfirstD * 2 ^ b ≤ 1 →
      (((packageR hfirstD).OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
          Fintype.card (OptimizedProductionChallengeTuple K97cubic F97) ≤
        1 / 2 ^ b :=
  (packageR hfirstD).optimizedFalseAcceptance_probability_le_two_pow_neg_legacy haxR hbasisR hwidthR

omit hrootAt hrootAtQ haxR hbasisR hwidthR in
/-- The complete bound has three displayed summands.  The `20+14M` term
uses `|F|` as denominator; it does not use a second copy of `q` or `|K|`. -/
theorem exact_bound_decomposition :
    boundR hfirstD =
      (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
        OptimizedHostileTimestamps.timestampCollisionBound (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
        pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows +
        494 * (packageR hfirstD).optimized.family.problem.cfg.compRows + 1 +
        61 * (packageR hfirstD).optimized.family.problem.cfg.memRows : ℚ) /
          Fintype.card K97cubic +
      (((packageR hfirstD).hostileIOWork : ℚ) + ((packageR hfirstD).hostileInterWork : ℚ)) /
        Fintype.card K97cubic ^ 2 +
      (20 + 14 * (packageR hfirstD).optimized.family.problem.cfg.memRows : ℚ) /
        Fintype.card F97 := by
  simp only [boundR, optimizedProductionFailureProbabilityBound, Nat.cast_add]

omit hrootAt hrootAtQ haxR hbasisR hwidthR in
/-- Independent numeric replay: `q=97`, `|F97|=97`, `memRows=21`, the
memory summand is exactly `314/97`, and that summand is a lower bound for
the complete failure bound -/
theorem independent_numeric_lower_bound :
    (packageR hfirstD).q = 97 ∧
      Fintype.card F97 = 97 ∧
      (packageR hfirstD).q = Fintype.card F97 ∧
      (packageR hfirstD).optimized.family.problem.cfg.memRows = 21 ∧
      ((20 + 14 * (packageR hfirstD).optimized.family.problem.cfg.memRows : ℚ) /
        Fintype.card F97 = (314 / 97 : ℚ)) ∧
      (1 : ℚ) < 314 / 97 ∧
      (314 / 97 : ℚ) ≤ boundR hfirstD := by
  have hq : (packageR hfirstD).q = 97 := rfl
  have hF : Fintype.card F97 = 97 := by simp [F97]
  have hM : (packageR hfirstD).optimized.family.problem.cfg.memRows = 21 := rfl
  refine ⟨hq, hF, ?_, hM, ?_, by norm_num, ?_⟩
  · rw [hq, hF]
  · rw [hF, hM]
    norm_num
  · rw [exact_bound_decomposition hfirstD, hF, hM]
    generalize OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ = w
    have hrest :
        (0 : ℚ) ≤
          (w +
            OptimizedHostileTimestamps.timestampCollisionBound (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
            pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              21 +
            494 * (packageR hfirstD).optimized.family.problem.cfg.compRows + 1 +
            61 * 21 : ℚ) / Fintype.card K97cubic +
          (((packageR hfirstD).hostileIOWork : ℚ) + ((packageR hfirstD).hostileInterWork : ℚ)) /
            Fintype.card K97cubic ^ 2 := by
      positivity
    linarith [hrest]

omit hrootAt hrootAtQ haxR hbasisR hwidthR in
/-- Independent attack on the support premise.  It uses the fresh lower-bound
replay above, not the production impossibility theorem -/
theorem independent_support_impossible_for_every_b (b : ℕ) :
    ¬ (boundR hfirstD * 2 ^ b ≤ 1) := by
  intro h
  have hlower : (314 / 97 : ℚ) ≤ boundR hfirstD :=
    (independent_numeric_lower_bound hfirstD).2.2.2.2.2.2
  have hstrict : (1 : ℚ) < 314 / 97 :=
    (independent_numeric_lower_bound hfirstD).2.2.2.2.2.1
  have hpow : (1 : ℚ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  nlinarith

omit hrootAt hrootAtQ haxR hbasisR hwidthR in
theorem independent_no_applicable_b :
    ¬ ∃ b : ℕ, boundR hfirstD * 2 ^ b ≤ 1 := by
  rintro ⟨b, hb⟩
  exact independent_support_impossible_for_every_b hfirstD b hb

/-! ## B. Carrier attack -/

omit hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ in
/-- Independent cardinality inequality for the two carriers. -/
theorem independent_carrier_cardinality_lt :
    Fintype.card (JointCoins K97cubic) <
      Fintype.card (OptimizedProductionChallengeTuple K97cubic F97) := by
  rw [card_jointCoins, card_optimizedProductionChallengeTuple]
  exact Nat.pow_lt_pow_right Fintype.one_lt_card (by norm_num)

omit hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ in
/-- In particular, they cannot be
definitionally equal. -/
theorem p8_and_optimized_carriers_not_equivalent :
    ¬ Nonempty
      (JointCoins K97cubic ≃
        OptimizedProductionChallengeTuple K97cubic F97) := by
  rintro ⟨e⟩
  have hcard := Fintype.card_congr e
  exact (Nat.ne_of_lt independent_carrier_cardinality_lt) hcard

theorem independent_nonreflexive_carrier_receipt :
    (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam :
        Finset (JointCoins K97cubic)) = ∅ ∧
      (∀ c : OptimizedProductionChallengeTuple K97cubic F97,
        c ∈ (packageR hfirstD).OptimizedFalseAcceptanceSet (computeTraceR hfirstD) (memoryTraceR hfirstD) ↔
          (packageR hfirstD).OptimizedProductionAcceptanceAt (computeTraceR hfirstD) (memoryTraceR hfirstD) c ∧
            ¬ (packageR hfirstD).OptimizedProductionGenuineTargetAt
              (computeTraceR hfirstD) (memoryTraceR hfirstD) c) ∧
      ¬ Nonempty
        (JointCoins K97cubic ≃
          OptimizedProductionChallengeTuple K97cubic F97) := by
  refine ⟨falseAcceptanceR_empty hfirstD hrootAt hrootAtQ, ?_,
    p8_and_optimized_carriers_not_equivalent⟩
  intro c
  simp [OptimizedFullStrictNockVMROMPackage.OptimizedFalseAcceptanceSet]

/-! ## C. -/

/-- The ordinary bound remains the actual universally quantified inequality
field and can be applied at arbitrary candidate traces.  The bit support is
empty only at this F97 fixture -/
theorem bound_contentful_bits_vacuous :
    (∀ (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
        (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]),
      (((packageR hfirstD).OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
          Fintype.card (OptimizedProductionChallengeTuple K97cubic F97) ≤
        boundR hfirstD) ∧
      (¬ ∃ b : ℕ, boundR hfirstD * 2 ^ b ≤ 1) :=
  ⟨(packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR,
    independent_no_applicable_b hfirstD⟩

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

/-- The vacuous-at-F97 rewrite remains one of the two residual fields; it does
not become substantive emptiness. -/
theorem exact_eleven_one_two_residual_partition :
    substantiveFields.length = 11 ∧
      typeSummaryFields.length = 1 ∧
      residualFields =
        [.complete_false_acceptance_bound, .complete_false_acceptance_bits] ∧
      residualFields.length = 2 ∧
      (substantiveFields ++ typeSummaryFields ++ residualFields).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

theorem frozen_statement_eta :
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
        shared_forest_axis := (statementR hfirstD haxR hbasisR hwidthR).shared_forest_axis } := by
  cases (statementR hfirstD haxR hbasisR hwidthR)
  rfl

theorem frozen_package_capstone_and_alias :
    (packageR hfirstD).q = 97 ∧
      OptimizedFullStrictThm54Statement (packageR hfirstD) ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨rfl, optimizedFullStrictNockVMROM_of_package (packageR hfirstD) haxR hbasisR hwidthR, rfl⟩


#print axioms exact_frozen_bits_projection
#print axioms exact_bound_decomposition
#print axioms independent_numeric_lower_bound
#print axioms independent_support_impossible_for_every_b
#print axioms independent_no_applicable_b
#print axioms independent_carrier_cardinality_lt
#print axioms p8_and_optimized_carriers_not_equivalent
#print axioms independent_nonreflexive_carrier_receipt
#print axioms bound_contentful_bits_vacuous
#print axioms exact_eleven_one_two_residual_partition
#print axioms frozen_statement_eta
#print axioms frozen_package_capstone_and_alias
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.statementR

end
end Nock.RedTeam.Batch92
