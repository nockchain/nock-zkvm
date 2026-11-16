import Nock.NockVMROM.Thm54.EqualityOperandCensus
import Nock.RedTeam.Batch82Thm54OptimizedAcceptance
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The distinct comparison census

Paper frame:

Consumed production layer:
`EdgeComparisonCensus.CombinedSkeletonCensus`, its `ComparisonCensus.badSeeds`,
`collisionFailureEvent`, and
`ProductionP8Containment.combined_pairFaithful`.

This artifact verifies a genuine distinct pair and a nonempty collision event at
the bare pre-seed census layer.  It deliberately does not turn the skeleton into
a `BuildableNockExecution`, `HonestCommitment.Data`, package, accepted
transcript, failure-union exclusion, or `GenuineTargetAt`.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch83

open scoped Classical
open Nock Nock.Walk Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic


variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
variable (hwidthP : FormRWidth F97)
variable (hrootAt : ∀ a g : K97cubic,
  (packageP hmoreM).strategy.RootAxisBoundaryAt
    (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
include hmoreM
include hrootAt
omit hmoreM hrootAt

/-! ## A. Production provenance and exact multiplicity -/

theorem pair_list_is_production_combinedSkeletonPairs :
    op5Pairs =
      EdgeComparisonCensus.combinedSkeletonPairs K97cubic op5Skeleton :=
  rfl

/-- The production census is indexed by exactly the production pair list. -/
theorem census_is_occurrence_preserving_production_list :
    op5Census.census.count = op5Pairs.length ∧
      (∀ i : Fin op5Census.census.count,
        op5Census.census.pair i ∈ op5Pairs) :=
  ⟨rfl, op5Census_pair_mem⟩

/-- Independent enumeration receipt: there are twenty-four occurrences and the
filter of genuinely distinct pairs is the singleton exceptional pair. -/
theorem exact_distinct_occurrence_filter :
    op5Pairs.length = 24 ∧
      op5Pairs.filter (fun P => decide (P.1 ≠ P.2)) =
        [(operandLeft, operandRight)] := by
  rw [op5Pairs_eq]
  decide

/-- The exceptional pair is distinct iff it is the unique non-self occurrence
in the production list. -/
theorem nonself_iff_exceptional_pair
    (P : Noun × Noun) (hP : P ∈ op5Pairs) :
    P.1 ≠ P.2 ↔ P = (operandLeft, operandRight) := by
  constructor
  · intro hne
    rcases op5Pairs_dichotomy P hP with hself | hexception
    · exact absurd hself hne
    · exact hexception
  · rintro rfl
    exact operands_ne

/-- In particular, the two displayed operand names are not aliases for one
noun. -/
theorem exceptional_operands_are_genuinely_distinct :
    operandLeft ≠ operandRight ∧
      (operandLeft, operandRight) ∈ op5Pairs :=
  ⟨by decide, operands_mem_op5Pairs⟩

/-! ## B. -/

/-- Independent case split over the complete state type.  The equality-operand
role occurs exactly at `OP_5`; no assertion about every other comparison role is
made here. -/
theorem equality_operand_role_exactly_s5 (st : ComputeTable.State) :
    SemanticTrace.ComparisonRole.equalityOperand ∈
        SemanticTrace.requiredComparisonRoles st ↔
      st = ComputeTable.State.s5 := by
  cases st <;> decide

/-- Independent unfolding of the two `OP_6` branch-formula occurrences. -/
theorem s6_contains_both_branch_formula_occurrences
    (K : Type*) [Field K] (s : ComputeRowSkeleton)
    (h : s.state = ComputeTable.State.s6)
    (hne :
      P8Census.skeletonDec s DecSlot.f_tth ≠
        P8Census.skeletonDec s DecSlot.f_ttt) :
    (P8Census.skeletonUse SemanticTrace.ComparisonRole.recursiveFormula
        (P8Census.skeletonSubformula s 0 TripleSlot.formula)
        (P8Census.skeletonDec s DecSlot.f_tth) ∈
          P8Census.skeletonComparisons (K := K) s) ∧
      (P8Census.skeletonUse SemanticTrace.ComparisonRole.recursiveFormula
        (P8Census.skeletonSubformula s 0 TripleSlot.formula)
        (P8Census.skeletonDec s DecSlot.f_ttt) ∈
          P8Census.skeletonComparisons (K := K) s) ∧
      ¬ (P8Census.skeletonSubformula s 0 TripleSlot.formula =
            P8Census.skeletonDec s DecSlot.f_tth ∧
          P8Census.skeletonSubformula s 0 TripleSlot.formula =
            P8Census.skeletonDec s DecSlot.f_ttt) := by
  refine ⟨by simp [P8Census.skeletonComparisons, h],
    by simp [P8Census.skeletonComparisons, h], ?_⟩
  rintro ⟨h₁, h₂⟩
  exact hne (h₁.symm.trans h₂)

/-! ## C. The Nock evaluation is genuine -/

/-- The reference evaluator and the bounded evaluator agree on the parent and
both child calls. -/
theorem real_nock_and_bounded_evaluations :
    (Nock.evalN 8 op5Subject op5Formula = some op5Result ∧
      Nock.evalN 8 op5Subject leftFormula = some operandLeft ∧
      Nock.evalN 8 op5Subject rightFormula = some operandRight) ∧
    (FieldEmbedding.evalFBy 97 8 op5Subject op5Formula = some op5Result ∧
      FieldEmbedding.evalFBy 97 8 op5Subject leftFormula = some operandLeft ∧
      FieldEmbedding.evalFBy 97 8 op5Subject rightFormula = some operandRight) :=
  by
    constructor <;> refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## D. Exact bad seed and a concrete event inhabitant -/

/-- The exact singleton, its cardinality, the paper-counting bound at `Λ = 7`,
and an explicit production-event member. -/
theorem exact_bad_seed_and_collision_event :
    op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} ∧
      (op5Census.census.badSeeds (K := K97cubic)).card = 1 ∧
      (op5Census.census.badSeeds (K := K97cubic)).card ≤
        op5Census.census.count * (2 * 7 - 1) ∧
      (((0, 0), (0, -1)) : JointCoins K97cubic) ∈
        collisionFailureEvent (K := K97cubic) op5Census.census := by
  have hbad :
      op5Census.census.badSeeds (K := K97cubic) =
        {(-1 : K97cubic)} := by
    ext z
    rw [ComparisonCensus.mem_badSeeds_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hself :
          (op5Census.census.pair i).1 =
            (op5Census.census.pair i).2
      · exfalso
        apply hi
        rw [hself]
        exact sepSeed_self z _
      · have hpair :=
          (nonself_iff_exceptional_pair
            (op5Census.census.pair i) (op5Census_pair_mem i)).mp hself
        rw [hpair] at hi
        exact (operands_not_sepSeed_iff z).mp hi
    · rintro rfl
      obtain ⟨i, hi⟩ := op5Census_has_distinct_pair
      exact ⟨i, by rw [hi]; exact operands_not_sepSeed_at_neg_one⟩
  refine ⟨hbad, ?_, op5Census_badSeeds_within_paper_bound, ?_⟩
  · rw [hbad, Finset.card_singleton]
  rw [mem_collisionFailureEvent_iff]
  obtain ⟨i, hi⟩ := op5Census_has_distinct_pair
  exact ⟨i, by rw [hi]; exact operands_not_sepSeed_at_neg_one⟩

/-- The good and bad sides use the same production census and same two distinct
nouns.  At seed `1`, every one of the twenty-four occurrences is faithful; at
seed `-1`, the exceptional operands collide under production `enc` and
`PairFaithful` fails. -/
theorem production_good_and_bad_sides :
    (∀ P ∈ EdgeComparisonCensus.combinedSkeletonPairs K97cubic op5Skeleton,
      OpcodeSemantics.PairFaithful (1 : K97cubic) 97 P.1 P.2) ∧
    operandLeft ≠ operandRight ∧
    GlobalCarryRecognizer.enc (1 : K97cubic) operandLeft ≠
      GlobalCarryRecognizer.enc (1 : K97cubic) operandRight ∧
    GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft =
      GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight ∧
    ¬ OpcodeSemantics.PairFaithful (-1 : K97cubic) 97
      operandLeft operandRight := by
  refine ⟨?_, operands_ne, operands_enc_ne_at_good_seed,
    operands_enc_eq_at_neg_one, operands_not_pairFaithful_at_neg_one⟩
  intro P hP
  exact ProductionP8Containment.combined_pairFaithful
    op5Skeleton op5Census 97 op5_combinedBounded 1
      op5Census_one_not_badSeed P hP

/-! ## E. Scope and the released fixture remain separate -/

/-- The census reads the compute tree only; this is the exact reason an empty
memory forest is legitimate at census scope and insufficient at execution
scope. -/
theorem memory_forest_is_invisible_to_this_layer
    (K : Type) [Field K] (t : NTree ComputeRowSkeleton)
    (F₁ F₂ : List (NTree MemoryRowSkeleton)) :
    EdgeComparisonCensus.combinedSkeletonPairs K ⟨t, F₁⟩ =
      EdgeComparisonCensus.combinedSkeletonPairs K ⟨t, F₂⟩ :=
  rfl

/-- The new skeleton is visibly not a completed execution fixture: its memory
forest is empty while its three compute rows emit four records in total. -/
theorem skeleton_scope_boundary :
    op5Skeleton.memoryForest = [] ∧
      computeSkeletonRows op5Skeleton =
        [op5Row, op1RowOf leftFormula operandLeft,
          op1RowOf rightFormula operandRight] ∧
      ((computeSkeletonRows op5Skeleton).map
        (fun s => Nock.Framework.recordCount s.state)).sum = 4 :=
  ⟨rfl, op5Skeleton_rows, op5Skeleton_record_budget.2.2⟩

include hmoreM
include hrootAt
/-- `packageP`
still carries `skelM` and `censusM`, whose count remains fourteen, while the new
census has count twenty-four. -/
theorem released_fixture_is_untouched_and_distinct :
    (packageP hmoreM).optimized.commitment.skeleton = skelM ∧
      (packageP hmoreM).optimized.census = censusM ∧
      censusM.census.count = 14 ∧
      op5Census.census.count = 24 ∧
      op5Census.census.count ≠ censusM.census.count := by
  refine ⟨(packageP_commitment_unchanged hmoreM).2.2.1,
    (packageP_commitment_unchanged hmoreM).2.2.2.2.2,
    Nock.RedTeam.Batch82.censusM_count_is_fourteen hmoreM hrootAt,
    op5Census_count, ?_⟩
  rw [op5Census_count, Nock.RedTeam.Batch82.censusM_count_is_fourteen hmoreM hrootAt]
  norm_num

theorem authoritative_recount_still_nine_one_four
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97) :
    (9 + 1 + 4 = 14) ∧
      Nonempty
        (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageP hmoreM)) :=
  ⟨by norm_num, ⟨statementP hmoreM haxP hbasisP hwidthP⟩⟩

theorem released_aliases_and_control_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» =
        @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch82.released_aliases_unchanged hmoreM hrootAt

/-! ## F. Interaction with the existing fixture seed -/

/-- The current multi-root fixture seed is exactly the new census's unique bad
seed; `8` is a good alternative of multiplicative order sixteen. -/
theorem fixture_seed_collision_and_candidate_repair :
    (servedSeed : K97cubic) = -1 ∧
      servedSeed ∈ op5Census.census.badSeeds (K := K97cubic) ∧
      orderOf (8 : K97cubic) = 16 ∧
      (8 : K97cubic) ∉ op5Census.census.badSeeds (K := K97cubic) :=
  ⟨rfl, servedSeed_is_the_collision_seed,
    op5Census_good_seed_of_order_sixteen.1,
    op5Census_good_seed_of_order_sixteen.2⟩


#print axioms pair_list_is_production_combinedSkeletonPairs
#print axioms census_is_occurrence_preserving_production_list
#print axioms exact_distinct_occurrence_filter
#print axioms nonself_iff_exceptional_pair
#print axioms exceptional_operands_are_genuinely_distinct
#print axioms equality_operand_role_exactly_s5
#print axioms s6_contains_both_branch_formula_occurrences
#print axioms real_nock_and_bounded_evaluations
#print axioms exact_bad_seed_and_collision_event
#print axioms production_good_and_bad_sides
#print axioms memory_forest_is_invisible_to_this_layer
#print axioms skeleton_scope_boundary
#print axioms released_fixture_is_untouched_and_distinct
#print axioms authoritative_recount_still_nine_one_four
#print axioms released_aliases_and_control_unchanged
#print axioms fixture_seed_collision_and_candidate_repair

#print axioms EqualityOperandCensus.op5Pairs_eq
#print axioms EqualityOperandCensus.op5Pairs_dichotomy
#print axioms EqualityOperandCensus.op5Census_badSeeds
#print axioms EqualityOperandCensus.op5Census_badSeeds_card
#print axioms EqualityOperandCensus.op5Census_badSeeds_within_paper_bound
#print axioms EqualityOperandCensus.op5_collisionFailureEvent_nonempty
#print axioms EqualityOperandCensus.op5_pairFaithful_at_good_seed
#print axioms EqualityOperandCensus.operands_enc_eq_at_neg_one
#print axioms EqualityOperandCensus.operands_not_pairFaithful_at_neg_one
#print axioms EqualityOperandCensus.op5_is_real_nock
#print axioms EqualityOperandCensus.op5_is_real_bounded_nock
#print axioms EqualityOperandCensus.census_ignores_memoryForest

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
end Nock.RedTeam.Batch83
