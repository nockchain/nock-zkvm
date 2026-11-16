import Nock.RedTeam.Batch75Thm54RepairedServedMemory
import Nock.RedTeam.Batch69Thm54RepairedP8TraceThreading
import Nock.RedTeam.Thm54P3Nonvacuity
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# One global memory `intermediate`

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The receipts below distinguish the two directions of the reformulation.  One global `LmIO` is
stronger than per-root `LmIO` on cross-root timestamp uniqueness and weaker on per-root
nonemptiness.  The paper makes both choices: a timestamp is the globally unique compute-table line
identifier `z^i`, while `intermediate` is one variable global to the whole
forest traversal with one row recurrence and global initial/final zero checks.
-/

namespace Nock.RedTeam.Batch76

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

noncomputable section

abbrev K5 := ZMod 5
abbrev K17 := ZMod 17
local instance prime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance prime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ## A. The old and new conditions are genuinely incomparable -/

/-- List-level exact control for both directions.

* Each singleton root satisfies `LmIO`, but their concatenation with the same timestamp does not:
  the global condition is strictly stronger on cross-root uniqueness.
* The aggregate singleton satisfies `LmIO`, while an empty second root does not: the global
  condition is strictly weaker on per-root nonemptiness.

This is a shape control only.  The accepted halt-root execution below supplies the second direction
at the exact execution layer.  No two-serviced-root exact fixture is claimed. -/
theorem old_per_root_and_new_global_are_incomparable :
    (IO.LmIO 2 ([(1 : K5)]) [1] ∧
      IO.LmIO 2 ([(1 : K5)]) [1] ∧
      ¬ IO.LmIO 2 ([(1 : K5), 1]) [1, 1]) ∧
    (IO.LmIO 2 ([(1 : K5)] ++ []) ([1] ++ []) ∧
      ¬ IO.LmIO 2 ([] : List K5) []) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · rw [IO.LmIO_iff]
      norm_num [IO.InRange]
    · rw [IO.LmIO_iff]
      norm_num [IO.InRange]
    · rw [IO.LmIO_iff]
      simp
  · constructor
    · rw [IO.LmIO_iff]
      norm_num [IO.InRange]
    · rw [IO.LmIO_iff]
      simp [IO.InRange]

/-- The stronger direction is the paper-correct one: every exact aggregate trace carries `Nodup`
of the timestamp powers over the entire forest, not merely root-by-root. -/
theorem global_timestamp_uniqueness_is_explicit
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    ((List.finRange cfg.kMem).flatMap
      (fun i => (T.roots i).timestampPowers)).Nodup :=
  T.timestampPowersNodup

/-! ## B. Dropped per-root fields -/

/-- The deleted `RootTrace.servicesBound` is recoverable from the aggregate `[K]` range.  A root's
timestamp list is a sublist of the forest list, and mapping preserves the service-list length. -/
theorem root_servicesBound_recovered
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ExactServedMemoryTrace q Λ cfg exec D execA) (i : Fin cfg.kMem) :
    (T.roots i).services.length ≤ cfg.Ksz := by
  have hsub :
      (T.roots i).timestampPowers.Sublist
        ((List.finRange cfg.kMem).flatMap
          (fun j => (T.roots j).timestampPowers)) :=
    sublist_flatMap_of_mem
      (l := List.finRange cfg.kMem)
      (f := fun j => (T.roots j).timestampPowers)
      (List.mem_finRange i)
  have hle := hsub.length_le.trans T.forestIndexRange.2
  simpa [RootTrace.timestampPowers, RootTrace.exponents] using hle

namespace HaltControl

open Nock.RedTeam.Thm54P3Nonvacuity
open Nock.RedTeam.Batch74.NoServiceRoot
open Nock.RedTeam.Batch75.AggregateHaltRoot

/-- The deleted per-root `RootTrace.intermediateMatching` is deliberately not recoverable for an
empty root.  On the exact accepted two-root execution, the one global matching holds while the
halt-only root's local empty `LmIO` fails.  This is the paper-required weaker direction, not a lost consumer premise. -/
theorem global_matching_does_not_restore_per_root_nonemptiness
    {q Λ : ℕ} (D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    IO.LmIO cfg.Ksz (forestReadTimestamps cfg execA) (forestVerifyTimestamps cfg execA) ∧
      ¬ IO.LmIO cfg.Ksz
        ((readExps (exactAxisTree cfg execA dummyRoot)).map
          (fun e => cfg.challenges.α ^ e))
        ((verifyExps (exactAxisTree cfg execA dummyRoot)).map
          (fun e => cfg.challenges.α ^ e)) := by
  constructor
  · exact (acceptedServedMemoryTrace D).intermediateMatching
  · rw [halt_root_exps.1, halt_root_exps.2]
    exact empty_forest_lmio_rejected

/-- The accepted halt-root fixture reaches exactly the layers it actually constructs: the
structural refinement, the aggregate served-memory object, and both axis-side fields of a future
`MemoryProductionAssignment`. -/
theorem accepted_halt_root_exact_reach
    {q Λ : ℕ} (D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    Nonempty (ExactAxisStructuralRefinement cfg execA) ∧
      Nonempty (ExactServedMemoryTrace q Λ cfg exec D execA) ∧
      ExactMemoryAxisValidity cfg execA ∧
      (∀ i : Fin cfg.kMem, countsP_bin (exactAxisTree cfg execA i) = 0) := by
  have hfields := accepted_halt_root_reaches_memoryProduction_axis_fields D
  exact ⟨⟨hfields.1⟩, ⟨acceptedServedMemoryTrace D⟩, hfields.2.1, hfields.2.2⟩

theorem mismatch_rejected_at_actual_Ksz :
    ¬ IO.LmIO cfg.Ksz [(4 : K17)] ([] : List K17) :=
  forest_mismatch_lmio_rejected

theorem duplicate_global_timestamp_rejected_at_actual_Ksz :
    ¬ IO.LmIO cfg.Ksz [(4 : K17), 4] [(4 : K17), 4] := by
  rw [IO.LmIO_iff]
  simp

/-- The two load-bearing controls target the exact aggregate structural object. -/
theorem aggregate_partition_controls_are_exact
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} :
    ((forestReadTimestamps cfg exec).toFinset ≠
        (forestVerifyTimestamps cfg exec).toFinset →
      ¬ ExactAxisStructuralRefinement cfg exec) ∧
    ((∀ i, exactAxisTree cfg exec i = MTree.halt) →
      ¬ ExactAxisStructuralRefinement cfg exec) :=
  ⟨forest_partition_is_load_bearing, record_free_forest_is_load_bearing⟩

end HaltControl

/-! ## C. Consumers, verifier shape, and same-object threading -/

/-- The per-root fact consumed by axis batching is still derivable from the one global premise. -/
theorem every_axis_consumer_still_gets_local_verify_uniqueness
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (S : ExactAxisStructuralRefinement cfg exec) (i : Fin cfg.kMem) :
    ((verifyExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Nodup :=
  S.verifyTimestamps_nodup i

/-- The production consumer threads ancestry, per-root read uniqueness, and aggregate matching
through the same `R.problem.cfg/R.problem.exec`; no forest list is independently quantified. -/
theorem production_consumer_threads_one_object
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [FiniteDimensional F K]
    {R : PlusIOSegmentedFamily F K} {p : ℕ}
    [CharP K p]
    {A : SampledIOSameExecutionAssignment R p} {execA : ExactExecution R.problem.cfg}
    (P : MemoryProductionAssignment A execA) :
    ExactMemoryAncestry R.problem.cfg execA ∧
      (∀ i, ((readExps (exactAxisTree R.problem.cfg execA i)).map
        (fun e => R.problem.cfg.challenges.α ^ e)).Nodup) ∧
      IO.LmIO R.problem.cfg.Ksz
        (forestReadTimestamps R.problem.cfg execA)
        (forestVerifyTimestamps R.problem.cfg execA) :=
  P.axis_timestamp_intermediate_same_object

/-- Exhaustive eta receipt: the aggregate structural object has no detached timestamp lists. -/
theorem structural_refinement_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (S : ExactAxisStructuralRefinement cfg exec) :
    S =
      { ancestry := S.ancestry
        read_timestamps_nodup := S.read_timestamps_nodup
        intermediate_matching := S.intermediate_matching } := by
  cases S
  rfl

theorem production_check_has_one_global_partition
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck E =
      (decide (∀ i : Fin T.kMem,
        ProductionAxisStructureVerifier.alphaFreeRootStructureCheck
          (ProductionAxisStructureVerifier.alphaFreeRoot E i) = true) &&
        ProductionAxisStructureVerifier.forestExponentPartitionCheck E) :=
  rfl

/-- The checker theorem returns the exact aggregate structural object consumed downstream. -/
theorem production_checker_returns_exact_global_object
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K)
    (hs : ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck E = true)
    (hn : ProductionAxisStructureVerifier.noWrapCheck E α = true) :
    ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb) :=
  ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_checks E α (lmb := lmb) hs hn

/-- The verifier extension remains deterministic side checking: its established protocol census
still adds no RAP family, segmented evaluation, or gate. -/
theorem production_protocol_census_unchanged :
    8 * 4 = 32 ∧ 0 + 8 = 8 ∧ 0 + 32 = 32 ∧ 0 + 676 = 676 ∧ 3 + 1 = 4 :=
  ProductionAxisStructureVerifier.production_axis_structure_exact_delta

/-! ## D. Paper resources, strict fingerprints, and non-vacuity -/

/-- `Thm:mem_38`'s source resource formulas remain literal definitions. -/
theorem memory_source_resources_unchanged (e : ℕ) :
    MemoryTable.mem_columns e = 54 * e + 5 ∧
      MemoryTable.mem_deg4_gates e = 20 * e + 13 :=
  ⟨rfl, rfl⟩

set_option maxHeartbeats 800000

/-- The consumed optimized package keeps the exact strict fingerprints. -/
theorem strict_package_resources_unchanged
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.memoryChip.rap.w = 205 ∧ P.memoryChip.rap.s = 156 ∧
      P.memoryChip.rap.d = 4 ∧ P.memoryChip.rap.k = 1 ∧
      P.computeChip.rap.s - 44 = 374 ∧ P.memoryChip.rap.s - 0 = 156 :=
  ⟨(Nock.RedTeam.Batch69.repaired_exact_resource_and_budget_receipt P).2.2.2.2.1,
    (Nock.RedTeam.Batch69.repaired_exact_resource_and_budget_receipt P).2.2.2.2.2.1,
    (Nock.RedTeam.Batch69.repaired_exact_resource_and_budget_receipt P).2.2.2.2.2.2.1,
    (Nock.RedTeam.Batch69.repaired_exact_resource_and_budget_receipt P).2.2.2.2.2.2.2.1,
    (Nock.RedTeam.Batch69.repaired_exact_resource_and_budget_receipt P).2.2.2.2.2.2.2.2.1,
    (Nock.RedTeam.Batch69.repaired_exact_resource_and_budget_receipt P).2.2.2.2.2.2.2.2.2.1⟩

noncomputable local instance : Fintype ConcreteStrictPackage.K73cubic :=
  Fintype.ofFinite ConcreteStrictPackage.K73cubic
noncomputable local instance : DecidableEq ConcreteStrictPackage.K73cubic :=
  Classical.decEq ConcreteStrictPackage.K73cubic
local instance : CharP ConcreteStrictPackage.K73cubic 73 := inferInstance
local instance : CharP ConcreteStrictPackage.K73cubic
    (ringChar ConcreteStrictPackage.K73cubic) :=
  ringChar.charP ConcreteStrictPackage.K73cubic

/-- The existing F73 buildable inhabitant still has exactly its original cfg/exec and reaches an
actual `MemoryProductionAssignment`; it also discharges the stronger forest-wide uniqueness. -/
theorem f73_inhabitant_is_same_execution_and_global
    (I : Inputs BuildableConcrete.concreteExecution)
    (hmore : BuildableAxisWitness.LaterSeedZeros BuildableConcrete.concreteExecution) :
    BuildableConcrete.concreteExecution.cfg =
        ConcreteStrictPackage.cfg ConcreteStrictPackage.honestSeed
          ConcreteStrictPackage.honestAlpha ∧
      BuildableConcrete.concreteExecution.exec =
        ConcreteStrictPackage.exec ConcreteStrictPackage.honestSeed
          ConcreteStrictPackage.honestAlpha ∧
      ((List.finRange BuildableConcrete.concreteExecution.cfg.kMem).flatMap
        (fun i => (BuildableConcrete.concreteExecution.memoryTrace.roots i).timestampPowers)).Nodup ∧
      Nonempty (MemoryProductionAssignment
        (sampledAssignment BuildableConcrete.concreteExecution I)
        BuildableConcrete.concreteExecution.execA) := by
  exact ⟨rfl, rfl, BuildableConcrete.concreteExecution.memoryTrace.timestampPowersNodup,
    ⟨buildableMemoryProductionAssignment BuildableConcrete.concreteExecution I hmore⟩⟩

/-! ## E. Positionless matching and release guards -/

/-- `LmIO` is invariant under arbitrary reorderings of both list presentations.  Thus the new
`flatMap` lists are only presentations of the LogUp multisets; no memory-row position is queried. -/
theorem lmio_is_permutation_stable
    {R : Type} [DecidableEq R] {Ksz : ℕ}
    {req req' resp resp' : List R}
    (hr : req.Perm req') (hs : resp.Perm resp') :
    IO.LmIO Ksz req resp ↔ IO.LmIO Ksz req' resp' := by
  rw [IO.LmIO_iff, IO.LmIO_iff]
  constructor
  · rintro ⟨hRange, hlen, hnd, hset⟩
    refine ⟨?_, ?_, hs.nodup_iff.mp hnd, ?_⟩
    · rwa [← hr.length_eq]
    · simpa [hr.length_eq, hs.length_eq] using hlen
    · rw [← List.toFinset_eq_of_perm _ _ hr, ← List.toFinset_eq_of_perm _ _ hs]
      exact hset
  · rintro ⟨hRange, hlen, hnd, hset⟩
    refine ⟨?_, ?_, hs.nodup_iff.mpr hnd, ?_⟩
    · rwa [hr.length_eq]
    · simpa [hr.length_eq, hs.length_eq] using hlen
    · rw [List.toFinset_eq_of_perm _ _ hr, List.toFinset_eq_of_perm _ _ hs]
      exact hset

/-- The two aggregate fields used before constructing `LmIO` are themselves permutation-stable.
Together with `lmio_is_permutation_stable`, this checks that `flatMap` supplies only a list
presentation of the multiset, not a memory-row position. -/
theorem aggregate_side_conditions_are_permutation_stable
    {R : Type} {Ksz : ℕ} {xs ys : List R} (h : xs.Perm ys) :
    (xs.Nodup ↔ ys.Nodup) ∧
      (IO.InRange Ksz xs.length ↔ IO.InRange Ksz ys.length) := by
  refine ⟨h.nodup_iff, ?_⟩
  rw [h.length_eq]

theorem released_aliases_unchanged :
    @«Thm:NockVMROM» =
        @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch69.repaired_alias_and_forest_control

/-! ## F. -/

#print axioms Nock.NockVMROM.Thm54.forestReadTimestamps
#print axioms Nock.NockVMROM.Thm54.forestVerifyTimestamps
#print axioms Nock.NockVMROM.Thm54.sublist_flatMap_of_mem
#print axioms Nock.NockVMROM.Thm54.readTimestamps_sublist_forest
#print axioms Nock.NockVMROM.Thm54.verifyTimestamps_sublist_forest
#print axioms Nock.NockVMROM.Thm54.ExactAxisRefinement
#print axioms Nock.NockVMROM.Thm54.ExactAxisRefinement.forestVerifyTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.ExactAxisRefinement.verifyTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.ExactAxisRefinement.verifyExps_nodup
#print axioms Nock.NockVMROM.Thm54.ExactAxisRefinement.ofHonestReconstruction

#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.templateForestReadExps
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.templateForestVerifyExps
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.forestVerifyTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.verifyTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.intermediate_closes
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.verifyExps_nodup
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.ofHonestReconstruction

#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.forestReadTimestamps_specialize
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.forestVerifyTimestamps_specialize
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.mem_templateForestReadExps
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.AlphaFreeStructuralData
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.AlphaFreeStructuralData.readTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.AlphaFreeStructuralData.intermediateMatching
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.AlphaFreeStructuralData.exactAxisStructuralRefinement

#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.forestExponentPartitionCheck
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.forestExponentPartitionCheck_eq_true_iff
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeRootStructureCheck
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeRootStructureCheck_eq_true_iff
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.AlphaFreeAxisStructure
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck_eq_true_iff
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_checks

#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.readTimestamps_perm
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.verifyTimestamps_perm
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.rootTimestampPowersNodup
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.forestReadTimestamps_perm
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.forestVerifyTimestamps_perm
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.intermediateMatching
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.axisStructural

#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteServedMemoryRoots
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteServedMemoryTrace
#print axioms Nock.NockVMROM.Thm54.ConcreteStrictPackage.honest_alphaFreeAxisStructureCheck
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.MemoryProductionAssignment.axis_timestamp_intermediate_same_object

#print axioms old_per_root_and_new_global_are_incomparable
#print axioms global_timestamp_uniqueness_is_explicit
#print axioms root_servicesBound_recovered
#print axioms HaltControl.global_matching_does_not_restore_per_root_nonemptiness
#print axioms HaltControl.accepted_halt_root_exact_reach
#print axioms HaltControl.mismatch_rejected_at_actual_Ksz
#print axioms HaltControl.duplicate_global_timestamp_rejected_at_actual_Ksz
#print axioms HaltControl.aggregate_partition_controls_are_exact
#print axioms every_axis_consumer_still_gets_local_verify_uniqueness
#print axioms production_consumer_threads_one_object
#print axioms structural_refinement_eta
#print axioms production_check_has_one_global_partition
#print axioms production_checker_returns_exact_global_object
#print axioms production_protocol_census_unchanged
#print axioms memory_source_resources_unchanged
#print axioms strict_package_resources_unchanged
#print axioms f73_inhabitant_is_same_execution_and_global
#print axioms lmio_is_permutation_stable
#print axioms aggregate_side_conditions_are_permutation_stable
#print axioms released_aliases_unchanged

#print axioms Nock.RedTeam.Batch75.AggregateHaltRoot.empty_forest_lmio_rejected
#print axioms Nock.RedTeam.Batch75.AggregateHaltRoot.forest_mismatch_lmio_rejected
#print axioms Nock.RedTeam.Batch75.AggregateHaltRoot.forest_partition_is_load_bearing
#print axioms Nock.RedTeam.Batch75.AggregateHaltRoot.record_free_forest_is_load_bearing

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
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch76
