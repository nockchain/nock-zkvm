import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.RedTeam.Thm54P3Nonvacuity

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# buildable served-memory closure

Paper frame:
the paper.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The route convention, same-execution record partition, generic builder threading, and the exact
terminal-OP1 scope of the F73 fixture are unchanged and still pinned here.
-/

namespace Nock.RedTeam.Batch74

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution

noncomputable section

/-! ## A. Route convention: Nock root axis one, left zero-bit, right one-bit -/

abbrev K5 := ZMod 5

local instance prime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem path_axis_convention :
    pathAxis [] = 1 ∧
      pathAxis [false] = 2 ∧
      pathAxis [true] = 3 ∧
      pathAxis [false, false] = 4 ∧
      pathAxis [false, true] = 5 ∧
      pathAxis [true, false] = 6 ∧
      pathAxis [true, true] = 7 := by
  norm_num [pathAxis, pathAddress]

/-- The repaired route is indexed by `axisPath`, so the same convention is read off the axis
itself: `axisPath` inverts `pathAxis`. -/
theorem axis_path_convention :
    axisPath 1 = [] ∧
      axisPath 2 = [false] ∧
      axisPath 3 = [true] ∧
      axisPath 5 = [false, true] ∧
      axisPath 6 = [true, false] := by
  refine ⟨by rw [axisPath_of_lt_two (by norm_num)], ?_, ?_, ?_, ?_⟩ <;>
    norm_num [axisPath_of_two_le, axisPath_of_lt_two]

def leftRouteTree : MTree K5 :=
  .read 7 (.decompose (.verify 7 2 .halt) .halt)

def rightRouteTree : MTree K5 :=
  .read 9 (.decompose .halt (.verify 9 3 .halt))

def depthRouteTree : MTree K5 :=
  .read 11 (.decompose
    (.decompose .halt (.verify 11 5 .halt))
    .halt)

theorem path_vaxis_relaxis_agree :
    pathAxis [false] = 2 ∧
      vaxis 7 leftRouteTree = 2 ∧
      Relaxis 7 leftRouteTree = 2 ∧
      pathAxis [true] = 3 ∧
      vaxis 9 rightRouteTree = 3 ∧
      Relaxis 9 rightRouteTree = 3 ∧
      pathAxis [false, true] = 5 ∧
      vaxis 11 depthRouteTree = 5 ∧
      Relaxis 11 depthRouteTree = 5 := by
  norm_num [pathAxis, pathAddress, leftRouteTree, rightRouteTree, depthRouteTree,
    vaxis, Relaxis, vaddr, vdep, readCount, verifyCount]

/-! ## B. The axis conclusions are DERIVED by the repaired operational walk

The repaired `VerifyRoute`/`ServiceWalk` are noun-indexed and accept only bindings: the walked
noun at each node, the record bound at a `read_root`, the child noun and the committed `address`
column bound at the matching `verify_child`, and absence side conditions. -/


theorem root_trace_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (R : RootTrace cfg exec i) :
    R =
      { subject := R.subject
        services := R.services
        recordPartition := R.recordPartition
        readPartition := R.readPartition
        verifyPartition := R.verifyPartition
        traversal := R.traversal } := by
  cases R
  rfl


theorem exact_served_memory_trace_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    T =
      { roots := T.roots
        timestampPowersNodup := T.timestampPowersNodup
        forestIndexRange := T.forestIndexRange
        semanticCoverage := T.semanticCoverage } := by
  cases T
  rfl

/-- The route DERIVES its Nock slot fact from the two noun bindings plus the axis descent. -/
theorem route_derives_slot
    {K : Type} [Field K] {e : ℕ} {child : Noun} {recAxis : K} {bs : List Bool} {n : Noun}
    {t : MTree K} (h : VerifyRoute e child recAxis bs n t) :
    Noun.slot (pathAxis bs) n = some child :=
  h.served

/-- A service's compute-side `served` fact is INDEPENDENTLY re-derived on the memory side: the
walk's descent along `axisPath s.axis` reaches the bound child noun. -/
theorem service_slot_rederived_by_walk
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : Service cfg exec) {t : MTree K}
    (h : VerifyRoute s.exponent s.child s.record.axis (axisPath s.axis) s.root t) :
    Noun.slot s.axis s.root = some s.child := by
  have hslot := h.served
  rwa [pathAxis_axisPath s.axis s.axis_pos] at hslot

/-- Ancestry, noun shape and the axis conclusion are all theorems about the walk. -/
theorem walk_derives_shape_ancestry_and_axis
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {services : List (Service cfg exec)} {n : Noun} {t : MTree K}
    (h : ServiceWalk services n t)
    (hr : (readExps t).Nodup) (hv : (verifyExps t).Nodup) :
    NounShape n t ∧
      ReadVerifyNested t ∧
      ∀ e ∈ readExps t, vaxis e t = Relaxis e t :=
  ⟨h.nounShape, h.readVerifyNested, h.axisValidity hr hv⟩

/-- The per-root axis conclusion is produced by `RootTrace.axisValidity`, which is a function of
the traversal and the aggregate timestamp premise, not a projection of a stored field. -/
theorem root_trace_axis_is_derived_from_traversal
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (R : RootTrace cfg exec i) (hts : R.timestampPowers.Nodup) (e : ℕ)
    (he : e ∈ readExps (exactAxisTree cfg exec i)) :
    vaxis e (exactAxisTree cfg exec i) =
      Relaxis e (exactAxisTree cfg exec i) :=
  R.axisValidity hts e he

/-- The generic production assignment's two axis fields are functions of the supplied
`E.memoryTrace`; primitive memory obligations remain the Milestone-3 assignment. -/
theorem generic_builder_is_memoryTrace_derivation
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros) :
    (buildableMemoryProductionAssignment E I hmore).obligations =
        (memoryChipAssignment E I).obligations ∧
      (buildableMemoryProductionAssignment E I hmore).axisStructural =
        E.memoryTrace.axisStructural ∧
      (buildableMemoryProductionAssignment E I hmore).axisRootPolynomial =
        rootPolynomial_of_exactMemoryAxisValidity E.two_ne_zero
          E.memoryTrace.axisStructural E.memoryTrace.axisValidity E.memoryTrace.support := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## C. Same-execution partition controls -/

theorem every_service_is_actual_root_response
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (R : RootTrace cfg exec i) (s : Service cfg exec) (hs : s ∈ R.services) :
    s.record ∈ rootResponseRecords exec i := by
  rw [R.recordPartition]
  exact List.mem_map.mpr ⟨s, hs, rfl⟩

theorem every_root_response_has_service
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (R : RootTrace cfg exec i) (record : ComputeTable.MemRec K)
    (hrecord : record ∈ rootResponseRecords exec i) :
    ∃ s ∈ R.services, s.record = record := by
  rw [R.recordPartition] at hrecord
  obtain ⟨s, hs, hsr⟩ := List.mem_map.mp hrecord
  exact ⟨s, hs, hsr⟩

theorem invented_service_rejected
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (R : RootTrace cfg exec i) (s : Service cfg exec)
    (hnew : s.record ∉ rootResponseRecords exec i) :
    s ∉ R.services := by
  intro hs
  exact hnew (every_service_is_actual_root_response R s hs)

theorem service_is_global_request_and_root_response
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (R : RootTrace cfg exec i) (s : Service cfg exec) (hs : s ∈ R.services) :
    s.record ∈ exec.rawRequests ∧ s.record ∈ rootResponseRecords exec i :=
  ⟨s.request_mem, every_service_is_actual_root_response R s hs⟩

theorem semantic_lookup_cannot_escape
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ExactServedMemoryTrace q Λ cfg exec D execA)
    (row : Fin cfg.compRows) :
    ∀ lookup ∈ (D.rows row).needs.served,
      ∃ (i : Fin cfg.kMem) (s : Service cfg execA),
        s ∈ (T.roots i).services ∧
          s.record = lookup.record ∧
          s.root = lookup.root ∧
          s.child = lookup.child ∧
          s.axis = lookup.axis :=
  T.semanticCoverage row

/-! ## D. -/

namespace NoServiceRoot

open Nock.RedTeam.Thm54P3Nonvacuity

def dummyRoot : Fin cfg.kMem := ⟨0, by norm_num [cfg]⟩

/-- This is a pre-existing accepted, chained exact execution with two supplied roots.  Its second
root is the valid halt-only noun root and emits no `read_root` response. -/
theorem accepted_two_root_execution_with_halt_only_root :
    ChainedSemanticExactLanguage cfg exec ∧
      exec.memoryForest = [dummyTree, readTreeP3] ∧
      (exec.memoryTreeAt dummyRoot).label.1 = MemoryTable.MState.halt ∧
      rootResponseRecords exec dummyRoot = [] := by
  refine ⟨production_chained, rfl, ?_, ?_⟩
  · norm_num [dummyRoot, ExactExecution.memoryTreeAt, exec, dummyTree, dummyLabel, cfg]
  · simp [dummyRoot, rootResponseRecords, ExactExecution.memoryTreeAt, exec,
      dummyTree, dummyLabel, pDummy, MemoryTable.responseRecords, cfg, bfsForest]

/-- The halt-only root's exact axis tree is the terminal leaf. -/
theorem halt_only_axis_tree :
    exactAxisTree cfg exec dummyRoot = MTree.halt := by
  norm_num [dummyRoot, exactAxisTree, ExactExecution.memoryTreeAt, exec, dummyTree, dummyLabel,
    AxisBridge.ofNTree, AxisBridge.MemWalk.toMTree, cfg]

/-- **Repaired:** the halt-only root now has a legal, empty root trace.  `servicesNonempty` is no
longer a `RootTrace` field, and the empty partition satisfies every remaining field
. -/
def haltOnlyRootTrace : RootTrace cfg exec dummyRoot where
  subject := .atom 0
  services := []
  recordPartition := by
    rw [accepted_two_root_execution_with_halt_only_root.2.2.2]
    simp
  readPartition := by
    rw [halt_only_axis_tree]
    simp [readExps]
  verifyPartition := by
    rw [halt_only_axis_tree]
    simp [verifyExps]
  traversal := by
    rw [halt_only_axis_tree]
    exact ServiceWalk.halt

theorem halt_only_root_is_accepted :
    Nonempty (RootTrace cfg exec dummyRoot) ∧
      haltOnlyRootTrace.services = [] :=
  ⟨⟨haltOnlyRootTrace⟩, rfl⟩

end NoServiceRoot

/-! ## E. -/

/-- Two nested reads may be verified in the reverse order.  This is a valid positionless
intermediate permutation: both timestamps are unique, supports agree, nesting holds, and the axis
polynomial vanishes. -/
def permutedIntermediateTree : MTree K5 :=
  .read 0 (.read 1 (.verify 1 1 (.verify 0 1 .halt)))

theorem permuted_intermediate_is_semantically_valid :
    readExps permutedIntermediateTree = [0, 1] ∧
      verifyExps permutedIntermediateTree = [1, 0] ∧
      (readExps permutedIntermediateTree).Nodup ∧
      (verifyExps permutedIntermediateTree).Nodup ∧
      ReadVerifyNested permutedIntermediateTree ∧
      (∀ e, e ∈ readExps permutedIntermediateTree →
        vaxis e permutedIntermediateTree = Relaxis e permutedIntermediateTree) ∧
      IO.LmIO 2
        ((readExps permutedIntermediateTree).map (fun e => (2 : K5) ^ e))
        ((verifyExps permutedIntermediateTree).map (fun e => (2 : K5) ^ e)) ∧
      countsP permutedIntermediateTree = 0 ∧
      readExps permutedIntermediateTree ≠ verifyExps permutedIntermediateTree := by
  refine ⟨rfl, rfl, by decide, by decide, ?_, ?_, ?_, ?_, by decide⟩
  · norm_num [permutedIntermediateTree, ReadVerifyNested, verifyCount]
  · intro e he
    have he' : e = 0 ∨ e = 1 := by
      simpa [permutedIntermediateTree, readExps] using he
    rcases he' with rfl | rfl
    · norm_num [permutedIntermediateTree, vaxis, Relaxis, vaddr, vdep,
        readCount, verifyCount]
    · norm_num [permutedIntermediateTree, vaxis, Relaxis, vaddr, vdep,
        readCount, verifyCount]
  · rw [IO.LmIO_iff]
    refine ⟨⟨by norm_num [permutedIntermediateTree, readExps, IO.InRange],
      by norm_num [permutedIntermediateTree, readExps]⟩,
      by norm_num [permutedIntermediateTree, readExps, verifyExps],
      by decide, by decide⟩
  · simp only [permutedIntermediateTree, countsP]
    norm_num

/-- **Repaired:** the two exponent partitions are `List.Perm`, so a `RootTrace` forces only a
positionless multiset match, never traversal-order equality
. -/
theorem rootTrace_forces_only_permutation
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (R : RootTrace cfg exec i) :
    (readExps (exactAxisTree cfg exec i)).Perm
      (verifyExps (exactAxisTree cfg exec i)) :=
  R.readPartition.trans R.verifyPartition.symm

/-- **Repaired:** the reversed-verify tree satisfies both repaired partition fields against one
common service exponent list, while still failing the old literal list equality.  Every derived
tree-level consequence (support, timestamp `Nodup`, `L_mIO`, zero polynomial) holds. -/
theorem permuted_intermediate_accepted :
    (readExps permutedIntermediateTree).Perm [0, 1] ∧
      (verifyExps permutedIntermediateTree).Perm [0, 1] ∧
      readExps permutedIntermediateTree ≠ verifyExps permutedIntermediateTree ∧
      (∀ e, e ∈ readExps permutedIntermediateTree ↔
        e ∈ verifyExps permutedIntermediateTree) ∧
      IO.LmIO 2
        ((readExps permutedIntermediateTree).map (fun e => (2 : K5) ^ e))
        ((verifyExps permutedIntermediateTree).map (fun e => (2 : K5) ^ e)) ∧
      countsP permutedIntermediateTree = 0 := by
  have hread : readExps permutedIntermediateTree = [0, 1] := rfl
  have hverify : verifyExps permutedIntermediateTree = [1, 0] := rfl
  refine ⟨by rw [hread], ?_, permuted_intermediate_is_semantically_valid.2.2.2.2.2.2.2.2,
    ?_, permuted_intermediate_is_semantically_valid.2.2.2.2.2.2.1,
    permuted_intermediate_is_semantically_valid.2.2.2.2.2.2.2.1⟩
  · rw [hverify]
    exact List.Perm.swap 0 1 []
  · intro e
    rw [hread, hverify]
    constructor <;> intro h <;> simp at h ⊢ <;> tauto

/-! ## F. Global timestamp uniqueness is now a NAMED aggregate premise -/

def sameTimestampDistinctRecords : List (ComputeTable.MemRec K5) :=
  [{ root := 0, child := 0, axis := 1, ts := 2 },
    { root := 0, child := 0, axis := 2, ts := 2 }]

/-- Distinct full request records may share a timestamp.  Thus `E.requestNodup` by itself does not
give global timestamp uniqueness across roots; that requires the compute timestamp semantics. -/
theorem request_nodup_does_not_imply_timestamp_nodup :
    (sameTimestampDistinctRecords.map NockVM.encRec).Nodup ∧
      ¬ (sameTimestampDistinctRecords.map ComputeTable.MemRec.ts).Nodup := by
  constructor
  · decide
  · decide

/-- **Repaired:** cross-root `z^i` uniqueness is an explicit field of the aggregate CORE
, and the per-root uniqueness the axis derivation needs is a theorem about
it, not a separate assumption. -/
theorem global_timestamp_uniqueness_is_named
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    ((List.finRange cfg.kMem).flatMap (fun i => (T.roots i).timestampPowers)).Nodup ∧
      ∀ i, (T.roots i).timestampPowers.Nodup :=
  ⟨T.timestampPowersNodup, T.rootTimestampPowersNodup⟩

/-! ## G. The projection-only field defaults are gone -/

/-- Every premise must now be named: neither `memoryTrace` nor `two_ne_zero` has a default, so a
copy has to list all fourteen fields. -/
def copyBuildableExecution
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) : BuildableNockExecution F K where
  q := E.q
  q_gt_one := E.q_gt_one
  Λ := E.Λ
  cfg := E.cfg
  execA := E.execA
  exec := E.exec
  exec_encode := E.exec_encode
  semanticData := E.semanticData
  memoryTrace := E.memoryTrace
  requestNodup := E.requestNodup
  recordCountBalance := E.recordCountBalance
  q_le_ringChar := E.q_le_ringChar
  two_ne_zero := E.two_ne_zero
  Ksz_lt_ringChar := E.Ksz_lt_ringChar
  programIOCapacity := E.programIOCapacity
  memoryIOCapacity := E.memoryIOCapacity

theorem copy_names_every_premise
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) :
    (copyBuildableExecution E).memoryTrace = E.memoryTrace ∧
      copyBuildableExecution E = E := by
  refine ⟨rfl, ?_⟩
  cases E
  rfl

/-! ## H. Same-object builder and concrete F73 scope -/

theorem builder_uses_exact_E_and_I
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros) :
    (exactFamilyCompletion E I).family.problem.cfg = E.cfg ∧
      HEq (exactFamilyCompletion E I).family.problem.exec E.exec ∧
      (buildableMemoryProductionAssignment E I hmore).axisStructural =
        E.memoryTrace.axisStructural ∧
      (buildableMemoryProductionAssignment E I hmore).obligations =
        (memoryChipAssignment E I).obligations := by
  exact ⟨rfl, HEq.rfl, rfl, rfl⟩

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open BuildableChips.Concrete

/-- The OP1 read-root is forest index 1; index 0 is the dummy halt seed. -/
def root0 : Fin concreteExecution.cfg.kMem :=
  ⟨1, by norm_num [concreteExecution, ConcreteStrictPackage.cfg]⟩

theorem actual_root_record_partition :
    rootResponseRecords concreteExecution.execA root0 =
      [ConcreteStrictPackage.requestRecord honestSeed honestAlpha] ∧
      (concreteExecution.memoryTrace.roots root0).services.map Service.record =
        [ConcreteStrictPackage.requestRecord honestSeed honestAlpha] := by
  have hroot :
      rootResponseRecords concreteExecution.execA root0 =
        [ConcreteStrictPackage.requestRecord honestSeed honestAlpha] := by
    simp [root0, concreteExecution, rootResponseRecords, ExactExecution.memoryTreeAt,
      ConcreteStrictPackage.execA, ConcreteStrictPackage.readTreeA,
      ConcreteStrictPackage.decomposeTreeA, ConcreteStrictPackage.verifyTreeA,
      ConcreteStrictPackage.readRowA, ConcreteStrictPackage.verifyRowA,
      ConcreteStrictPackage.readPubA, ConcreteStrictPackage.verifyPubA,
      ConcreteStrictPackage.exec, ConcreteStrictPackage.readTree,
      ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
      ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
      ConcreteStrictPackage.readRow, ConcreteStrictPackage.decomposeRow,
      ConcreteStrictPackage.headRow, ConcreteStrictPackage.verifyRow,
      ConcreteStrictPackage.tailRow, ConcreteStrictPackage.readPub,
      ConcreteStrictPackage.decomposePub, ConcreteStrictPackage.headPub,
      ConcreteStrictPackage.verifyPub, ConcreteStrictPackage.tailPub,
      ConcreteStrictPackage.requestRecord, MemoryTable.responseRecords, bfsForest]
    erw [if_pos rfl]
    simp
    refine ⟨rfl, ?_⟩
    intro x hx
    erw [bfsForest_cons_eq _ (by intro h; cases h)] at hx
    -- 4.35: walk the BFS levels explicitly
    rcases List.mem_append.1 hx with h | h
    · change x ∈ [_] at h
      rw [List.mem_singleton] at h
      subst h; rfl
    · erw [bfsForest_cons_eq _ (by intro h; cases h)] at h
      rcases List.mem_append.1 h with h | h
      · change x ∈ [_, _] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> (subst h; rfl)
      · erw [bfsForest_cons_eq _ (by intro h; cases h)] at h
        rcases List.mem_append.1 h with h | h
        · change x ∈ [_] at h
          rw [List.mem_singleton] at h
          subst h; rfl
        · change x ∈ bfsForest [] at h
          rw [bfsForest_nil] at h
          cases h
  refine ⟨hroot, ?_⟩
  exact (concreteExecution.memoryTrace.roots root0).recordPartition.symm.trans hroot

/-- The concrete fixture inhabits the repaired, noun-indexed CORE: the right-descent route is
`axisPath 3`, the memory-side walk re-derives the Nock slot fact, and the used axis consequence is
derived from the traversal plus the named aggregate timestamp premise. -/
theorem actual_route_and_used_axis :
    pathAxis [true] = 3 ∧
      axisPath concreteMemoryService.axis = [true] ∧
      Noun.slot concreteMemoryService.axis concreteMemoryService.root =
        some concreteMemoryService.child ∧
      vaxis concreteMemoryService.exponent
          (exactAxisTree concreteExecution.cfg concreteExecution.execA root0) =
        Relaxis concreteMemoryService.exponent
          (exactAxisTree concreteExecution.cfg concreteExecution.execA root0) := by
  refine ⟨by norm_num [pathAxis, pathAddress], BuildableConcrete.concreteAxisPath,
    concreteMemoryService.served, ?_⟩
  refine (concreteExecution.memoryTrace.roots root0).axisValidity
    (concreteExecution.memoryTrace.rootTimestampPowersNodup root0)
    concreteMemoryService.exponent ?_
  refine ((concreteExecution.memoryTrace.roots root0).readPartition.mem_iff).mpr ?_
  change concreteMemoryService.exponent ∈
    ([concreteMemoryService].map Service.exponent)
  simp

/-- The only concrete buildable fixture is terminal OP1.  Its row-level OP0/OP9 service coverage is
empty even though the memory root has a real ordinary read/decompose/verify service. -/
theorem terminal_op1_empty_semanticCoverage :
    concreteExecution.cfg.compRows = 1 ∧
      (∀ row : Fin concreteExecution.cfg.compRows,
        (concreteExecution.semanticData.rows row).needs.served = []) ∧
      (concreteExecution.memoryTrace.roots root0).services ≠ [] := by
  refine ⟨rfl, ?_, ?_⟩
  · intro row
    apply List.eq_nil_of_length_eq_zero
    rw [(concreteExecution.semanticData.rows row).needs.served_count]
    have hstate0 :
        ((ConcreteStrictPackage.exec honestSeed honestAlpha).computeRowAt row).1 = .s1 := by
      rcases row with ⟨row, hrow⟩
      have hrow0 : row = 0 := by
        have : row < 1 := by
          simpa [concreteExecution, ConcreteStrictPackage.cfg] using hrow
        omega
      subst row
      norm_num [ExactExecution.computeRowAt,
        ExactExecution.computeRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.computeRow, ConcreteStrictPackage.computePub,
        ConcreteStrictPackage.cfg, bfsForest]
    have hstate :
        (concreteExecution.exec.computeRowAt row).1 = .s1 := by
      simpa [concreteExecution] using hstate0
    simp [SemanticTrace.requiredServedLookups, hstate]
  · simp [root0, concreteExecution, BuildableConcrete.concreteServedMemoryTrace,
      BuildableConcrete.concreteServedMemoryRoots, BuildableConcrete.concreteReadServedRoot]

end Concrete

#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAddress
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAxis
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.axisPath
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAxis_axisPath
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.nounAt
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.slot_pathAxis
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute.spec
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute.served
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.Service
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.Service.axis_pos
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.rootResponseRecords
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.nounShape
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.readVerifyNested
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.support
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.intermediateMatching
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.rootTimestampPowersNodup
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.axisStructural
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.support
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.honestReconstruction
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.buildableMemoryProductionAssignment
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteAxisTree
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteAxisPath
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteServedMemoryRoots
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteServedMemoryTrace
#print axioms path_axis_convention
#print axioms axis_path_convention
#print axioms path_vaxis_relaxis_agree
#print axioms root_trace_eta
#print axioms exact_served_memory_trace_eta
#print axioms route_derives_slot
#print axioms service_slot_rederived_by_walk
#print axioms walk_derives_shape_ancestry_and_axis
#print axioms root_trace_axis_is_derived_from_traversal
#print axioms generic_builder_is_memoryTrace_derivation
#print axioms every_service_is_actual_root_response
#print axioms every_root_response_has_service
#print axioms invented_service_rejected
#print axioms semantic_lookup_cannot_escape
#print axioms NoServiceRoot.accepted_two_root_execution_with_halt_only_root
#print axioms NoServiceRoot.halt_only_axis_tree
#print axioms NoServiceRoot.haltOnlyRootTrace
#print axioms NoServiceRoot.halt_only_root_is_accepted
#print axioms permuted_intermediate_is_semantically_valid
#print axioms rootTrace_forces_only_permutation
#print axioms permuted_intermediate_accepted
#print axioms request_nodup_does_not_imply_timestamp_nodup
#print axioms global_timestamp_uniqueness_is_named
#print axioms copy_names_every_premise
#print axioms builder_uses_exact_E_and_I
#print axioms Concrete.actual_root_record_partition
#print axioms Concrete.actual_route_and_used_axis
#print axioms Concrete.terminal_op1_empty_semanticCoverage

end
end Nock.RedTeam.Batch74
