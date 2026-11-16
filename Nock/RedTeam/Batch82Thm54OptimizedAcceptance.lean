import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
import Nock.RedTeam.Batch81Thm54PhaseCorrect
import Nock.NockVMROM.Thm54.Walk37.PaperNames

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# optimized acceptance and the fixture-scoped P8 residue

Paper frame:
the paper,
1813-1848,1864-1868,2049-2088,2258-2303`.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The former is a genuine connective result at one canonical trace pair. The latter becomes easier for a fixture-specific reason: every one of the
fourteen comparison-census entries is a self-comparison, and the sole window noun
is an atom. Thus this fixture does not exercise nontrivial noun separation. -/

set_option autoImplicit false

namespace Nock.RedTeam.Batch82

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.Concrete
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableAxisWitness

noncomputable section

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
variable (hwidthP : FormRWidth F97)
variable (hrootAt : ∀ a g : K97cubic,
  (packageP hmoreM).strategy.RootAxisBoundaryAt
    (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
include hrootAt

/-! ## A. The acceptance factorization and challenge chronology -/

/-- `envOfTrace` stores challenges independently of the row-evaluation point. -/
theorem envOfTrace_challenge_is_row_independent
    {F : Type} [Field F] {w : ℕ} (Q : Fin w → F[X])
    (ω x y : F) (chal pub : ℕ → F) :
    (envOfTrace Q ω x chal pub).chal = (envOfTrace Q ω y chal pub).chal :=
  rfl

/-- The extension-field gatherer also reads only the challenge field, never
the current or next-row fields. -/
theorem gatherEnv_challenge_uses_challenge_field_only
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (E₁ E₂ : Env F) (hchal : E₁.chal = E₂.chal) :
    (gatherEnv b col0 E₁).chal = (gatherEnv b col0 E₂).chal := by
  funext i
  simp only [gatherEnv]
  rw [hchal]

/-- All row-indexed sampled challenge reads at the exhibited traces are
constant across rows.  This is stronger than checking only row zero. -/
theorem canonical_sampled_challenges_are_row_independent :
    (∀ i j : Fin (packageP hmoreM).optimized.family.problem.cfg.compRows,
      ((packageP hmoreM).computeSourceEnv (computeTraceP hmoreM) i).chal compilerChallengeBase =
        ((packageP hmoreM).computeSourceEnv (computeTraceP hmoreM) j).chal compilerChallengeBase) ∧
    (∀ i j : Fin (packageP hmoreM).optimized.family.problem.cfg.memRows,
      ((packageP hmoreM).memorySourceEnv (memoryTraceP hmoreM) i).chal 6 =
        ((packageP hmoreM).memorySourceEnv (memoryTraceP hmoreM) j).chal 6) ∧
    (∀ i j : Fin (packageP hmoreM).optimized.family.problem.cfg.memRows,
      ((packageP hmoreM).memoryBaseEnv (memoryTraceP hmoreM) i).chal 0 =
        ((packageP hmoreM).memoryBaseEnv (memoryTraceP hmoreM) j).chal 0) ∧
    (∀ i j : Fin (packageP hmoreM).optimized.family.problem.cfg.memRows,
      ((packageP hmoreM).memoryBaseEnv (memoryTraceP hmoreM) i).chal 1 =
        ((packageP hmoreM).memoryBaseEnv (memoryTraceP hmoreM) j).chal 1) ∧
    (∀ i j : Fin (packageP hmoreM).optimized.family.problem.cfg.memRows,
      ((packageP hmoreM).memoryBaseEnv (memoryTraceP hmoreM) i).chal 2 =
        ((packageP hmoreM).memoryBaseEnv (memoryTraceP hmoreM) j).chal 2) ∧
    (∀ i j : Fin (packageP hmoreM).optimized.family.problem.cfg.memRows,
      ((packageP hmoreM).memoryBaseEnv (memoryTraceP hmoreM) i).chal 3 =
        ((packageP hmoreM).memoryBaseEnv (memoryTraceP hmoreM) j).chal 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i j <;> rfl

/-- Independent decomposition of the exhibited optimized acceptance through
the released factorization. -/
theorem packageP_acceptance_factorization (a g : K97cubic)
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97) :
    (packageP hmoreM).strategy.Accepts (coinN a g) cfgS.challenges.lam ∧
      (packageP hmoreM).OptimizedSameProblemAt (coinN a g) cfgS.challenges.lam ∧
      (packageP hmoreM).OptimizedHistoricalTraceAcceptanceAt (computeTraceP hmoreM) (memoryTraceP hmoreM)
        (((packageP hmoreM).optimized.sampled.sampled.coins.gamma,
            (packageP hmoreM).optimized.sampled.sampled.coins.pole),
          (canonicalComputeChallengeTuple (packageP hmoreM),
            canonicalMemoryChallengeTuple (packageP hmoreM))) :=
  ((packageP hmoreM).optimizedHistoricalAcceptanceAt_iff (computeTraceP hmoreM) (memoryTraceP hmoreM)
    (coinN a g) _).1 (packageP_optimized_acceptance hmoreM a g haxP hbasisP hwidthP (hrootAt a g))

/-! `released_acceptance_connective_fires` was deleted at H1.5b Part 2a. -/

/-! ## B. The two-row ingredient and nondegenerate selector exclusion -/

theorem packageP_has_exactly_two_compute_rows :
    (packageP hmoreM).optimized.family.problem.cfg.compRows = 2 :=
  rfl

/-- The source family count stated earlier is exact: seventeen folds cover
all 511 non-IO source expressions. -/
theorem final_nonIO_source_counts_are_exact :
    finalNonIOSourceFamilies17.length = 17 ∧
      finalNonIOSourceFamilies17.flatten.length = 511 := by
  set_option maxRecDepth 100000 in
    decide

/-- Row zero is genuinely nonterminal and every non-IO source vanishes there
by the new generic lemma. -/
theorem packageP_row_zero_nonIO_sources_vanish
    (e : Expr) (he : e ∈ finalNonIOSourceFamilies17.flatten) :
    e.eval ((packageP hmoreM).computeSourceEnv (computeTraceP hmoreM)
      ⟨0, (packageP hmoreM).optimized.family.problem.cfg.compRows_pos⟩) = 0 := by
  exact canonical_nonterminal_nonIO_source_zero (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.computeObligations
    (packageP hmoreM).optimized.family.problem.cfg.compRows_pos (packageP hmoreM).optimized.computeNodes
    (packageP hmoreM).optimized.computeNodes_injective (packageP hmoreM).optimized.basis
    (packageP hmoreM).optimized.computeChallenge (packageP hmoreM).optimized.computePublic
    (packageP hmoreM).optimized.orbit (packageP hmoreM).optimized.computeAdjacentOrbit
    (packageP hmoreM).optimized.computeChallengePins
    ⟨0, (packageP hmoreM).optimized.family.problem.cfg.compRows_pos⟩
    (by
      have hrows := packageP_has_exactly_two_compute_rows hmoreM hrootAt
      change 1 < (packageP hmoreM).optimized.family.problem.cfg.compRows
      omega) e he

/-- The terminal selector error list is not all zero: its head is exactly `-1`. The dropped
conjuncts are not restated here. -/
theorem terminal_selector_exclusion_is_computed :
    (-1 : F97) ∈ selectorErrors ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)) 31 ∧
      ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)).trace 0 -
          ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)).pub 31 = -1 := by
  refine ⟨?_, packageP_selector31_head hmoreM⟩
  simp only [selectorErrors, List.mem_cons]
  left
  exact (packageP_selector31_head hmoreM).symm

/-! ## C. Recount: one newly informative connective, two empty-set bounds -/

/-! `false_acceptance_is_empty_only_at_the_exhibited_pair` was deleted at H1.5b Part 2a. -/


theorem authoritative_nine_one_four_recount :
    (9 + 1 + 4 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageP hmoreM)) ∧
      (statementP hmoreM haxP hbasisP hwidthP) =
        { structural := (statementP hmoreM haxP hbasisP hwidthP).structural
          optimized_chips := (statementP hmoreM haxP hbasisP hwidthP).optimized_chips
          shared_io := (statementP hmoreM haxP hbasisP hwidthP).shared_io
          perfect_completeness := (statementP hmoreM haxP hbasisP hwidthP).perfect_completeness
          containment := (statementP hmoreM haxP hbasisP hwidthP).containment
          walk_bounds := (statementP hmoreM haxP hbasisP hwidthP).walk_bounds
          p8_fixed_field_soundness := (statementP hmoreM haxP hbasisP hwidthP).p8_fixed_field_soundness
          p8_fixed_field_bits := (statementP hmoreM haxP hbasisP hwidthP).p8_fixed_field_bits
          acceptance_to_target := (statementP hmoreM haxP hbasisP hwidthP).acceptance_to_target
          complete_false_acceptance_bound := (statementP hmoreM haxP hbasisP hwidthP).complete_false_acceptance_bound
          complete_false_acceptance_bits := (statementP hmoreM haxP hbasisP hwidthP).complete_false_acceptance_bits
          staged_false_acceptance_bound := (statementP hmoreM haxP hbasisP hwidthP).staged_false_acceptance_bound
          exact_resources := (statementP hmoreM haxP hbasisP hwidthP).exact_resources
          row_budgets := (statementP hmoreM haxP hbasisP hwidthP).row_budgets
          shared_forest_axis := (statementP hmoreM haxP hbasisP hwidthP).shared_forest_axis } := by
  refine ⟨by norm_num, ⟨(statementP hmoreM haxP hbasisP hwidthP)⟩, ?_⟩
  cases (statementP hmoreM haxP hbasisP hwidthP)
  rfl

/-! ## D. The optimized/P8 asymmetry and fixture triviality -/

/-- P8 acceptance unfolds to the production verifier plus root-axis boundary;
there is no `OptimizedSameProblemAt` field in this predicate. -/
theorem p8_acceptance_has_no_same_problem_field (ω : JointCoins K97cubic) (lmb : K97cubic) :
    (packageP hmoreM).strategy.Accepts ω lmb =
      if hz : nprSeed ω ≠ 0 then
        ProductionAxisStructureAccepts (packageP hmoreM).strategy.verifier ω lmb ∧
          (packageP hmoreM).strategy.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω)
      else False :=
  rfl

/-- The layer asymmetry is constructive in the forward direction only:
optimized acceptance projects `same_problem`, while fibre coins are accepted
at P8 without deriving the converse characterization. -/
theorem same_problem_is_an_extra_optimized_acceptance_field :
    (∀ c : OptimizedProductionChallengeTuple K97cubic F97,
      (packageP hmoreM).OptimizedHistoricalAcceptanceAt (computeTraceP hmoreM) (memoryTraceP hmoreM) c →
        (packageP hmoreM).OptimizedSameProblemAt c.1 c.2.2.2.lambda) ∧
    (∀ ω : JointCoins K97cubic,
      nprSeed ω = servedSeed → alphaM ω = fixtureAlpha →
        (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam) :=
  ⟨fun _ h => h.same_problem, fun _ hz hα => packageP_accepts_fibre hmoreM hrootAt hz hα⟩

/-- Exact count of the fixture census. -/
theorem censusM_count_is_fourteen : censusM.census.count = 14 := by
  rw [EdgeComparisonCensus.CombinedSkeletonCensus.census_count,
    BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusM,
    List.length_append, EdgeComparisonCensus.edgePairs]
  norm_num [EdgeComparisonCensus.combinedSkeletonPairs,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    P8Census.skeletonSubformula, P8Census.skeletonMemoryAxis,
    SemanticTrace.ComparisonUse.pair, skelM, skeletonOfNodes, computeNodesM,
    mapNTree, parentNode, servedNode, bfsForest,
    EdgeComparisonCensus.rowEdgePairs, EdgeComparisonCensus.edgeTriple,
    NTree.childOpt, parentSkeletonRow, servedSkeletonRow,
    SemanticSkeleton.publicClaim, decActive, hasTailDecomposition,
    servedRecordSkeleton, ComputeTable.fanoutComp]

/-- Stronger than `SepSeed`: every census pair is literally a self-comparison.
Consequently this fixture does not test nontrivial NPR separation. -/
theorem censusM_every_pair_is_self
    (i : Fin censusM.census.count) :
    (censusM.census.pair i).1 = (censusM.census.pair i).2 := by
  set P := censusM.census.pair i with hP
  have hmem : P ∈ EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelM := by
    rw [hP]
    change
      (ComparisonCensus.ofPairList
        (EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelM) _).pair i ∈
          EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelM
    erw [ComparisonCensus.ofPairList_pair]
    exact List.get_mem _ _
  clear_value P
  clear hP
  rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rw [BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusM] at hmem
    simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
      P8Census.skeletonSubformula, P8Census.skeletonMemoryAxis,
      SemanticTrace.ComparisonUse.pair, skelM, skeletonOfNodes, computeNodesM,
      mapNTree, parentNode, parentSkeletonRow, servedSkeletonRow,
      SemanticSkeleton.publicClaim, decActive, hasTailDecomposition,
      servedRecordSkeleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [parentFormulaS, parentHeadS, formulaS, subjectS, resultS, headS, tailS,
        parentResultS, ComputeTable.fanoutComp, incMod_atom7_eq,
        Nock.Framework.recordCount]
  · rw [EdgeComparisonCensus.edgePairs] at hmem
    simp [skelM, skeletonOfNodes, computeNodesM, mapNTree, parentNode, servedNode,
      bfsForest, EdgeComparisonCensus.rowEdgePairs,
      EdgeComparisonCensus.edgeTriple, NTree.childOpt,
      P8Census.skeletonSubformula, parentSkeletonRow, servedSkeletonRow,
      ComputeTable.fanoutComp] at hmem
    rcases hmem with rfl | rfl | rfl <;>
      simp [formulaS, subjectS, headS, tailS]

/-- The fixture's size-window content is one atom of leaf count one. -/
theorem size_window_fixture_is_single_atom :
    SizeWindowCounting.skeletonSizeWindowNouns skelM = [resultS] ∧
      resultS = Noun.atom 7 ∧ resultS.leaves = 1 :=
  ⟨sizeWindowNounsM, rfl, rfl⟩

/-- The empty fixture event follows together with the literal reason for it. -/
theorem fixture_collision_emptiness_is_self_comparison_triviality :
    censusM.census.count = 14 ∧
      (∀ i : Fin censusM.census.count,
        (censusM.census.pair i).1 = (censusM.census.pair i).2) ∧
      collisionFailureEvent censusM.census =
        (∅ : Finset (JointCoins K97cubic)) :=
  ⟨censusM_count_is_fourteen hmoreM hrootAt, censusM_every_pair_is_self hmoreM hrootAt,
    collisionFailureEventM_empty⟩


theorem nonself_NPR_separation_negative_control :
    ¬ GlobalCarryRecognizer.SepSeed servedSeed
      Nock.RedTeam.Batch78.collidingSubject subjectS :=
  Nock.RedTeam.Batch79.servedSeed_not_separating

/-! ## E. -/


theorem prior_F73_optimized_acceptance_existed
    (hbasis : FormRBasis basis73)
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    concreteOptimizedFullStrictPackage.OptimizedHistoricalAcceptanceAt
      concreteComputeTrace concreteMemoryTrace concreteProductionChallenge :=
  concrete_production_acceptance hbasis hmore

theorem released_aliases_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch81.released_aliases_direct_capstone_and_control_unchanged

theorem single_execution_threading_unchanged
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97) :
    (packageP hmoreM).objects.cfg = cfgS ∧ (packageP hmoreM).objects.exec = execS ∧
      (packageP hmoreM).computeChip.rap.H.card = 2 ∧
      Nonempty (packageP hmoreM).optimized.OptimizedSharedMemoryConnective := by
  refine ⟨rfl, rfl, (Nock.RedTeam.Batch81.single_execution_threading_regression hmoreM haxP hbasisP).2.2.1,
    (Nock.RedTeam.Batch81.single_execution_threading_regression hmoreM haxP hbasisP).2.2.2.2⟩



#print axioms envOfTrace_challenge_is_row_independent
#print axioms gatherEnv_challenge_uses_challenge_field_only
#print axioms canonical_sampled_challenges_are_row_independent
#print axioms packageP_acceptance_factorization
#print axioms packageP_has_exactly_two_compute_rows
#print axioms final_nonIO_source_counts_are_exact
#print axioms packageP_row_zero_nonIO_sources_vanish
#print axioms terminal_selector_exclusion_is_computed
#print axioms authoritative_nine_one_four_recount
#print axioms p8_acceptance_has_no_same_problem_field
#print axioms same_problem_is_an_extra_optimized_acceptance_field
#print axioms censusM_count_is_fourteen
#print axioms censusM_every_pair_is_self
#print axioms size_window_fixture_is_single_atom
#print axioms fixture_collision_emptiness_is_self_comparison_triviality
#print axioms nonself_NPR_separation_negative_control
#print axioms prior_F73_optimized_acceptance_existed
#print axioms released_aliases_unchanged
#print axioms single_execution_threading_unchanged

#print axioms canonical_nonterminal_nonIO_source_zero
#print axioms packageP_optimized_acceptance
#print axioms fibre_pinning_is_carried_by_same_problem_only
#print axioms censusM_sepSeed_everywhere
#print axioms collisionFailureEventM_empty
#print axioms sizeWindowFailureM_iff
#print axioms falseAcceptanceP_empty_of_three_events
#print axioms p8_fixed_field_status_after_census

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
end Nock.RedTeam.Batch82
