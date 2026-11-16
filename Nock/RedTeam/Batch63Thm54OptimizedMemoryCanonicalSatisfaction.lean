import Nock.NockVMROM.Thm54.OptimizedMemoryConcrete
import Nock.RedTeam.Thm54P3Nonvacuity
import Nock.RedTeam.Batch63Compatibility

/-!
# Optimized memory canonical satisfaction

Paper frame:
* memory IO: the paper;
* aggregate forest walk: the paper;
* carried NMR axes and timestamps: the paper;
* memory body: the paper;
* Memspec and equality table: the paper;
* final chip: the paper.

The author-selected `6/55` codec and `14/21` fold are a recorded correctness
delta, not a literal appendix transcription.  This artifact records a narrow
FAIL: base gate IDs `7..13` are algebraic multiples of IDs `0..3`, so all seven
are implied by the preceding selector-booleanity gates and are not independent
semantic/load-bearing gates.  It also records the exact remaining axis and
malformed-control boundary without promoting the standalone `MTree` control to
a capstone-level verdict.
-/

namespace Nock.RedTeam.Batch63

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open Polynomial
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryCodec
open Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace.Concrete

noncomputable section

/-! ## 1. Exact role census and decoder ranges -/

theorem exact_role_census :
    Fintype.card BaseRole = 6 ∧
      Fintype.card MemoryTablePayloadRole = 31 ∧
      Fintype.card ForestWalkRole = 6 ∧
      Fintype.card SampledMemoryIORole = 14 ∧
      Fintype.card StateSelectorMirrorRole = 4 ∧
      Fintype.card ExtensionRole = 56 := by
  decide

theorem memory_payload_columns_are_exactly_4_through_34 :
    ((Finset.univ : Finset MemoryTablePayloadRole).image
      (fun r => (memoryTableSourceColumn r : ℕ))) = Finset.Icc 4 34 := by
  decide

theorem extension_indices_are_exactly_0_through_54 :
    ((Finset.univ : Finset ExtensionRole).image
      (fun r => (extensionIndex r : ℕ))) = Finset.range 56 := by
  decide

/-- The seven physical cuts are exhaustive and pairwise exclusive, including
all boundary positions `0,15,19,27,31,37,51,55`. -/
theorem extension_range_partition_unique (j : Fin 56) :
    [decide ((j : ℕ) < 15),
      decide (15 ≤ (j : ℕ) ∧ (j : ℕ) < 19),
      decide (19 ≤ (j : ℕ) ∧ (j : ℕ) < 27),
      decide (27 ≤ (j : ℕ) ∧ (j : ℕ) < 31),
      decide (31 ≤ (j : ℕ) ∧ (j : ℕ) < 37),
      decide (37 ≤ (j : ℕ) ∧ (j : ℕ) < 51),
      decide (51 ≤ (j : ℕ) ∧ (j : ℕ) < 55),
      decide (55 ≤ (j : ℕ) ∧ (j : ℕ) < 56)].count true = 1 := by
  fin_cases j <;> decide

theorem source_coordinate_ranges_fit_width :
    (∀ j : Fin 6, (j : ℕ) < 174) ∧
      (∀ r : Fin 56, ∀ k : Fin 3, 6 + 3 * (r : ℕ) + (k : ℕ) < 174) := by
  constructor <;> intro <;> omega

/-- `memoryRowSources`, `walkBoundarySources`,
`walkTransitionSources`, `sampledSources` and `transitionSources` are the production definitions
from `OptimizedMemoryGateBasis`. **`extensionTransitionGates` is NOT**: it resolves by shadowing to
`Nock.RedTeam.Batch63.extensionTransitionGates` (`Batch63Compatibility.lean:67`), which is
`List.ofFn (foldAt : Fin 21 → _)` and so has length `21` by construction rather than by a fact
about the shipped basis. Read that conjunct as fixing the compatibility fold's arity, not as a
production resource claim; the production tie is `Batch64.exact_source_and_final_fingerprints`
and `Batch65`'s receipt. -/
theorem source_transition_partition_count :
    memoryRowSources (K := ConcreteStrictPackage.K73cubic).length = 33 ∧
      walkBoundarySources.length = 3 ∧
      walkTransitionSources.length = 3 ∧
      sampledSources.length = 10 ∧
      transitionSources (K := ConcreteStrictPackage.K73cubic).length = 50 ∧
      (extensionTransitionGates (K := ConcreteStrictPackage.K73cubic)).length = 21 := by
  decide

theorem every_source_has_exact_fold_bucket
    (i : Fin (transitionSources (K := ConcreteStrictPackage.K73cubic)).length) :
    ∃! j : Fin 21, (i : ℕ) % 21 = j := by
  refine ⟨⟨(i : ℕ) % 21, Nat.mod_lt _ (by omega)⟩, rfl, ?_⟩
  intro j hj
  exact Fin.ext hj.symm

/-! ## 2. Aggregate forest seed and a genuine two-root control -/

theorem aggregate_seed_is_paper_weighted_sum
    {K : Type*} [Field K] (cur : ℕ → K) (k : ℕ) (α : K) :
    (Nock.Walk.nodeListP cur k).eval α =
      ∑ i ∈ Finset.Icc 1 k, cur i * α ^ i :=
  Nock.Walk.nodeListP_eval cur k α

theorem two_root_seed_formula
    {K : Type*} [Field K] (cur : ℕ → K) (α : K) :
    (Nock.Walk.nodeListP cur 2).eval α =
      cur 1 * α + cur 2 * α ^ 2 := by
  rw [Nock.Walk.nodeListP_eval]
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  simp

/-- Existing exact carrier with two ordered roots and one aggregate BFS forest,
used here only as a multi-root control. -/
theorem concrete_two_root_carrier :
    Nock.RedTeam.Thm54P3Nonvacuity.cfg.kMem = 2 ∧
      Nock.RedTeam.Thm54P3Nonvacuity.exec.memoryForest.length = 2 ∧
      Nock.RedTeam.Thm54P3Nonvacuity.exec.memoryRows =
        (Nock.Walk.bfsForest
          Nock.RedTeam.Thm54P3Nonvacuity.exec.memoryForest).map
            (fun n => n.label) := by
  exact ⟨rfl, rfl, rfl⟩

abbrev K17 := ZMod 17

theorem two_root_reorder_changes_seed :
    (1 : K17) * 4 + 2 * 4 ^ 2 ≠
      (2 : K17) * 4 + 1 * 4 ^ 2 := by
  decide

theorem two_root_duplicate_changes_seed :
    (1 : K17) * 4 + 2 * 4 ^ 2 ≠
      (1 : K17) * 4 + 1 * 4 ^ 2 := by
  decide

theorem two_root_initial_count_and_wrong_count :
    (4 : K17) ^ 2 = 16 ∧ (4 : K17) ^ 2 ≠ 15 := by
  decide

/-! ## 3. Production finding: base IDs 7--13 are redundant -/

/-- Exact syntax of the seven purported extra semantic base gates.  Each is a
scalar multiple of one of selector-booleanity IDs `0..3`. -/
theorem base_ids_7_13_exact_multiples {F : Type} [Field F] :
    (baseTransitionGates (F := F)).drop 7 =
      [(CoeffExpr.mul (bcur 4) (bbool (bcur 0)) : CoeffExpr F),
       CoeffExpr.mul (bcur 4) (bbool (bcur 1)),
       CoeffExpr.mul (bcur 4) (bbool (bcur 2)),
       CoeffExpr.mul (bcur 4) (bbool (bcur 3)),
       CoeffExpr.mul (bcur 5) (bbool (bcur 0)),
       CoeffExpr.mul (bcur 5) (bbool (bcur 1)),
       CoeffExpr.mul (bcur 5) (bbool (bcur 2))] := by
  rfl

/-- Compiled accepting-set redundancy: once selector booleanity IDs `0..3`
vanish, every gate at IDs `7..13` vanishes for arbitrary first/last masks. -/
theorem base_ids_7_13_implied_by_0_3
    {F : Type} [Field F] (env : Env F)
    (h0 : (bbool (bcur 0)).eval env = 0)
    (h1 : (bbool (bcur 1)).eval env = 0)
    (h2 : (bbool (bcur 2)).eval env = 0)
    (h3 : (bbool (bcur 3)).eval env = 0) :
    ((.mul (bcur 4) (bbool (bcur 0)) : CoeffExpr F).eval env = 0) ∧
    ((.mul (bcur 4) (bbool (bcur 1)) : CoeffExpr F).eval env = 0) ∧
    ((.mul (bcur 4) (bbool (bcur 2)) : CoeffExpr F).eval env = 0) ∧
    ((.mul (bcur 4) (bbool (bcur 3)) : CoeffExpr F).eval env = 0) ∧
    ((.mul (bcur 5) (bbool (bcur 0)) : CoeffExpr F).eval env = 0) ∧
    ((.mul (bcur 5) (bbool (bcur 1)) : CoeffExpr F).eval env = 0) ∧
    ((.mul (bcur 5) (bbool (bcur 2)) : CoeffExpr F).eval env = 0) := by
  simp only [CoeffExpr.eval]
  simp [h0, h1, h2, h3]

/-- Deleting IDs `7..13` cannot change acceptance when IDs `0..6` hold. -/
theorem deleting_base_ids_7_13_preserves_acceptance
    {F : Type} [Field F] (env : Env F)
    (hprefix :
      ∀ g ∈ (baseTransitionGates (F := F)).take 7, g.eval env = 0) :
    ∀ g ∈ (baseTransitionGates (F := F)).drop 7, g.eval env = 0 := by
  have h0 : (bbool (bcur 0)).eval env = 0 := hprefix _ (by simp [baseTransitionGates])
  have h1 : (bbool (bcur 1)).eval env = 0 := hprefix _ (by simp [baseTransitionGates])
  have h2 : (bbool (bcur 2)).eval env = 0 := hprefix _ (by simp [baseTransitionGates])
  have h3 : (bbool (bcur 3)).eval env = 0 := hprefix _ (by simp [baseTransitionGates])
  have htail := base_ids_7_13_implied_by_0_3 env h0 h1 h2 h3
  intro g hg
  rw [base_ids_7_13_exact_multiples] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact htail.1
  · exact htail.2.1
  · exact htail.2.2.1
  · exact htail.2.2.2.1
  · exact htail.2.2.2.2.1
  · exact htail.2.2.2.2.2.1
  · exact htail.2.2.2.2.2.2

/-! ## 4. -/

abbrev structuralWrongAxisTree : MTree (ZMod 73) :=
  .read 0 (.verify 0 2 .halt)

/-- The production structural fields (ancestry, unique read timestamp, per-root
intermediate matching) do not by themselves contain the omitted per-root
`countsP` boundary.  This is an `MTree` boundary control only; it is not promoted
to a source/final-RAP counterexample. -/
theorem structural_fields_do_not_imply_root_acceptance :
    ReadVerifyNested structuralWrongAxisTree ∧
      (readExps structuralWrongAxisTree).Nodup ∧
      IO.LmIO 2 (readExps structuralWrongAxisTree)
        (verifyExps structuralWrongAxisTree) ∧
      vaxis 0 structuralWrongAxisTree ≠ Relaxis 0 structuralWrongAxisTree ∧
      (countsP_bin structuralWrongAxisTree).eval 4 ≠ 0 := by
  norm_num [structuralWrongAxisTree, ReadVerifyNested, readExps, verifyExps,
    IO.LmIO_iff, IO.InRange, vaxis, Relaxis, vaddr, vdep, readCount,
    verifyCount, countsP_bin]
  decide

/-- The actual batching consequence needs the root boundary omitted from
`ExactAxisStructuralRefinement`; this is the precise theorem shape required for
each used timestamp. -/
theorem actual_axis_batching_consequence
    {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (t : MTree K)
    (hroot : countsP_bin t = 0) (e : ℕ)
    (hn : Nested e t) (hr : readCount e t = 1) (hv : verifyCount e t = 1) :
    vaxis e t = Relaxis e t :=
  axis_batching_sound h2 t hroot e hn hr hv

/-- Existing concrete wrong-axis control has only coordinate-separation shape;
it does not conclude that a source/final RAP gate is nonzero. -/
theorem existing_wrong_axis_control_exact_boundary :
    ∀ (actual wrongAxis : K73cubic), wrongAxis ≠ actual →
      ∃ k : Fin 3, coord basis73 (wrongAxis - actual) k ≠ 0 :=
  honest_wrong_axis_control

/-! ## 5. Fold premise, all-row non-vacuity, and resources -/

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- The named reverse premise is inhabited on every row of the concrete honest
five-row assignment.  All source bodies vanish there, so no implication is
vacuous through an impossible environment. -/
theorem honest_foldCollisionExcluded_nonvacuous
    (i : Fin honestLegacyFamily.problem.cfg.memRows) :
    OptimizedMemoryGateBasis.FoldCollisionExcluded
      (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i) :=
  foldCollisionExcluded_of_nonagg _
    (fun e he h23 h24 =>
      canonical_transitionSources honestSampled honestProduction
        honestLegacyFamily.problem.memory_same_lambda
        honestMemoryNodes honestMemoryNodes_injective basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit honestMemoryPins
        honestMemoryNodes_aligned honestMemoryDenominatorsSafe i e
        (extensionFoldSources_subset_transitionSources e he) h23 h24)
    (by
      have hpin :
          OptimizedMemoryGateBasis.foldChallenge.eval
            (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
              honestMemoryChalVal honestMemoryPubVal strictOrbit i) =
            (2 : K73cubic) :=
        honestMemoryPins.sampledInterPole
      rw [hpin]
      exact honest_two_ne_zero)

theorem concrete_memory_rows_are_six :
    honestLegacyFamily.problem.cfg.memRows = 6 := by
  rfl

theorem concrete_source_and_final_nonvacuous
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    RAP.SatisfiesWithPreprocessing
        (namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
          honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
        (canonicalSourceTrace honestSampled honestMemoryNodes basis73 honestLegacyFamily.problem.cfg.kMem) ∧
      RAP.SatisfiesWithPreprocessing
        (namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
          honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
        (canonicalFinalMemoryTrace honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit) :=
  ⟨honest_source_memory_satisfies hmore, honest_final_memory_satisfies hmore⟩

theorem exact_source_and_final_resources :
    let S := namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    let Q := namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    S.rap.w = 182 ∧ S.rap.s = 156 ∧ S.rap.d = 4 ∧ S.rap.k = 1 ∧
      Q.rap.w = 205 ∧ Q.rap.s = 156 ∧ Q.rap.d = 4 ∧ Q.rap.k = 1 ∧
      RAPPadding.memoryResidualColumns 3 = 23 ∧
      RAPPadding.memoryResidualTransitionGates 3 = 0 := by
  refine ⟨
    (sourceMemoryRAP_fingerprint basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit (rowNodeSet honestMemoryNodes)).1,
    (sourceMemoryRAP_fingerprint basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit (rowNodeSet honestMemoryNodes)).2.1,
    (sourceMemoryRAP_fingerprint basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit (rowNodeSet honestMemoryNodes)).2.2.1,
    (sourceMemoryRAP_fingerprint basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit (rowNodeSet honestMemoryNodes)).2.2.2,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.2.1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.2.2,
    rfl, rfl⟩

/-- **Pre-retyping bucket arithmetic, kept verbatim.**  These are pure numerals
and remain true; they record the accounting *before* the `𝔽 → 𝕂` retyping of the four memory
scalar gates. -/
theorem exact_coordinate_expanded_constraint_buckets :
    14 + 3 * 21 = 77 ∧
      77 + 3 * 2 + 3 * 2 + 4 = 93 ∧
      77 + 11 = 88 ∧
      93 + 11 = 104 := by
  decide

theorem concrete_row_budget_is_M_plus_2L :
    (ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows =
      RowLayout.memoryM (ConcreteStrictPackage.exec honestSeed honestAlpha) +
        2 * RowLayout.memoryL (ConcreteStrictPackage.exec honestSeed honestAlpha) :=
by
  exact RowLayout.memRows_eq_M_add_two_mul_L_of_count_balance
    ConcreteStrictPackage.recordCountBalance

theorem final_padding_is_semantically_inert :
    let S := namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    let Q := namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    ∀ P : Fin Q.rap.w → F73[X],
      RAP.SatisfiesWithPreprocessing Q P ↔
        RAP.SatisfiesWithPreprocessing S
          (RAPPadding.projectTrace S.rap
            (RAPPadding.firstRoundExtra S.rap S.rounds_pos
              (RAPPadding.memoryResidualColumns 3)) P) := by
  dsimp only
  intro P
  exact final_satisfies_iff_source honestLegacyFamily.problem.cfg.memRows_pos
    honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestLegacyFamily.problem.cfg.kMem P

theorem paper_alias_unchanged :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

#print axioms exact_role_census
#print axioms memory_payload_columns_are_exactly_4_through_34
#print axioms extension_range_partition_unique
#print axioms aggregate_seed_is_paper_weighted_sum
#print axioms concrete_two_root_carrier
#print axioms two_root_reorder_changes_seed
#print axioms deleting_base_ids_7_13_preserves_acceptance
#print axioms structural_fields_do_not_imply_root_acceptance
#print axioms actual_axis_batching_consequence
#print axioms existing_wrong_axis_control_exact_boundary
#print axioms honest_foldCollisionExcluded_nonvacuous
#print axioms concrete_source_and_final_nonvacuous
#print axioms exact_source_and_final_resources
#print axioms exact_coordinate_expanded_constraint_buckets
#print axioms concrete_row_budget_is_M_plus_2L
#print axioms final_padding_is_semantically_inert
#print axioms paper_alias_unchanged

end
end Nock.RedTeam.Batch63
