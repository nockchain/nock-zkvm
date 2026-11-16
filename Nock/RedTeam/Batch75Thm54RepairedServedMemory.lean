import Nock.RedTeam.Batch69Thm54RepairedP8TraceThreading
import Nock.RedTeam.Batch73Thm54BuildableSemanticAxis
import Nock.RedTeam.Batch74Thm54BuildableServedMemory
import Nock.NockVMROM.Thm54.Walk37.PaperNames

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# repaired generic served-memory CORE

Paper frame:
the paper,
2228-2240,2379-2384`.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The noun-indexed route repair, positionless exponent partitions, explicit timestamp premise,
field-default removal, same-execution threading, and recurrence conventions pass the compiled
controls below.

The paper instead keeps one
forest-wide `intermediate` accumulator while seeding record-free atom subjects into the same forest
 and admitting `halt` leaves. Section C is now
restated, prover-side, against that global formulation: the same accepted two-root execution with a
halt-only second root inhabits `ExactAxisStructuralRefinement`, the aggregate
`ExactServedMemoryTrace`, and both axis-side production fields, while the retained counter-controls
show the one global condition is still load-bearing. -/

namespace Nock.RedTeam.Batch75

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.BuildableTopologyCorrectness
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

/-! ## A. The route computes the Nock axis and rejects detached answers -/

abbrev K5 := ZMod 5

/-- The P2/P3 fixture field, named locally so that no statement below can silently auto-bind an
uninstantiated type variable in its place. -/
abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17

local instance prime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def depthTwoNoun : Noun :=
  .cell (.cell (.atom 10) (.atom 11)) (.cell (.atom 12) (.atom 13))

/-- Depth-two left/right examples compile the paper's root `1`, left `2a`, right `2a+1`
convention. -/
theorem depth_two_slot_convention :
    axisPath 4 = [false, false] ∧
      axisPath 5 = [false, true] ∧
      axisPath 6 = [true, false] ∧
      axisPath 7 = [true, true] ∧
      Noun.slot 4 depthTwoNoun = some (.atom 10) ∧
      Noun.slot 5 depthTwoNoun = some (.atom 11) ∧
      Noun.slot 6 depthTwoNoun = some (.atom 12) ∧
      Noun.slot 7 depthTwoNoun = some (.atom 13) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [axisPath_of_two_le, axisPath_of_lt_two]
  · norm_num [axisPath_of_two_le, axisPath_of_lt_two]
  · norm_num [axisPath_of_two_le, axisPath_of_lt_two]
  · norm_num [axisPath_of_two_le, axisPath_of_lt_two]
  all_goals norm_num [depthTwoNoun, Noun.slot]

def forcedDepthRoute :
    VerifyRoute (K := K5) 17 (.atom 13) 7 [true, true] depthTwoNoun
      (.decompose .halt (.decompose .halt (.verify 17 7 .halt))) := by
  exact VerifyRoute.right (by simp [readCount]) (by simp [verifyCount])
    (VerifyRoute.right (by simp [readCount]) (by simp [verifyCount])
      (VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])))

/-- The route is a genuine operational certificate: its indices force the depth-two slot result,
and no slot equation is supplied to the constructor. -/
theorem forced_depth_route_rederives_slot :
    Noun.slot (pathAxis [true, true]) depthTwoNoun = some (.atom 13) :=
  forcedDepthRoute.served

/-- A detached path cannot be substituted: axis `6` reaches atom `12`, not the claimed atom `13`. -/
theorem wrong_depth_route_rejected :
    ¬ VerifyRoute (K := K5) 17 (.atom 13) 7 (axisPath 6) depthTwoNoun
      (.decompose .halt (.decompose .halt (.verify 17 7 .halt))) := by
  intro h
  have hs := h.served
  rw [pathAxis_axisPath 6 (by norm_num)] at hs
  norm_num [depthTwoNoun, Noun.slot] at hs

/-- On a terminal matching verify row, `VerifyRoute` forces the committed column to equal the
record axis; `hcommitted` is a row binding, not a freely retained conclusion. -/
theorem terminal_route_forces_committed_axis
    {e : ℕ} {child n : Noun} {recAxis a : K5}
    (h : VerifyRoute e child recAxis [] n (.verify e a .halt)) :
    a = recAxis := by
  have haxis := h.spec.2.2.2.1
  simpa [vaxis, verifyCount] using haxis

/-- The actual F73 route, named independently of the stored aggregate trace. -/
noncomputable def concreteForcedRoute :
    VerifyRoute
      BuildableConcrete.concreteMemoryService.exponent
      BuildableConcrete.concreteMemoryService.child
      BuildableConcrete.concreteMemoryService.record.axis
      (axisPath BuildableConcrete.concreteMemoryService.axis)
      BuildableConcrete.concreteMemoryService.root
      (.decompose .halt
        (.verify BuildableConcrete.concreteMemoryService.exponent
          (3 : ConcreteStrictPackage.K73cubic) .halt)) := by
  rw [show BuildableConcrete.concreteMemoryService.axis = 3 from rfl,
    BuildableConcrete.concreteAxisPath]
  exact VerifyRoute.right (by simp [readCount]) (by simp [verifyCount])
    (VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount]))

/-- A concrete `ServiceWalk` whose route index is computed from the record's axis. -/
noncomputable def concreteForcedWalk :
    ServiceWalk [BuildableConcrete.concreteMemoryService]
      BuildableConcrete.concreteMemoryService.root
      (.read BuildableConcrete.concreteMemoryService.exponent
        (.decompose .halt
          (.verify BuildableConcrete.concreteMemoryService.exponent
            (3 : ConcreteStrictPackage.K73cubic) .halt))) := by
  exact ServiceWalk.read BuildableConcrete.concreteMemoryService (by simp) rfl rfl
    concreteForcedRoute
    (ServiceWalk.decompose ServiceWalk.halt (ServiceWalk.verify ServiceWalk.halt))

/-- The concrete service walk is inhabited on the actual execution tree, while independently
re-deriving the compute-side slot fact from the memory route. -/
theorem concrete_walk_is_operational :
    Nonempty
        (ServiceWalk
          [BuildableConcrete.concreteMemoryService]
          BuildableConcrete.concreteMemoryService.root
          (.read BuildableConcrete.concreteMemoryService.exponent
            (.decompose .halt
              (.verify BuildableConcrete.concreteMemoryService.exponent
                (3 : ConcreteStrictPackage.K73cubic) .halt)))) ∧
      Noun.slot BuildableConcrete.concreteMemoryService.axis
          BuildableConcrete.concreteMemoryService.root =
        some BuildableConcrete.concreteMemoryService.child := by
  refine ⟨⟨concreteForcedWalk⟩, ?_⟩
  have hs := concreteForcedRoute.served
  simpa [show BuildableConcrete.concreteMemoryService.axis = 3 from rfl,
    BuildableConcrete.concreteAxisPath, pathAxis, pathAddress] using hs

/-! ## B. Positionless partitions and their load-bearing scope -/

/-- The two permutation premises jointly force exact read/verify support. -/
theorem two_permutations_force_support
    {α : Type} (reads verifies services : List α)
    (hr : reads.Perm services) (hv : verifies.Perm services) :
    ∀ x, x ∈ reads ↔ x ∈ verifies := by
  intro x
  rw [hr.mem_iff, hv.mem_iff]

/-- If the read permutation is dropped, the verify permutation alone does not bind support. -/
theorem read_partition_is_load_bearing :
    ([1] : List ℕ).Perm [1] ∧
      ¬ (∀ x, x ∈ ([0] : List ℕ) ↔ x ∈ ([1] : List ℕ)) := by
  refine ⟨List.Perm.refl _, ?_⟩
  intro h
  have := (h 0).1 (by simp)
  simp at this

/-- If the verify permutation is dropped, the read permutation alone does not bind support. -/
theorem verify_partition_is_load_bearing :
    ([0] : List ℕ).Perm [0] ∧
      ¬ (∀ x, x ∈ ([0] : List ℕ) ↔ x ∈ ([1] : List ℕ)) := by
  refine ⟨List.Perm.refl _, ?_⟩
  intro h
  have := (h 0).1 (by simp)
  simp at this

/-- Literal `recordPartition` is exactly equality with the root's emitted `read_root` list.  It
contains no committed row index or lookup into the memory multiset. -/
theorem record_partition_is_emission_equality
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (R : RootTrace cfg exec i) :
    rootResponseRecords exec i = R.services.map Service.record :=
  R.recordPartition

/-- Local timestamp uniqueness at every root does not imply the named cross-root premise. -/
theorem local_timestamp_nodup_does_not_imply_global :
    ([(1 : K5)] : List K5).Nodup ∧
      ([(1 : K5)] : List K5).Nodup ∧
      ¬ (([(1 : K5)] : List K5) ++ [(1 : K5)]).Nodup := by
  decide

/-- Timestamp uniqueness remains load-bearing for the reverse polynomial conclusion. -/
theorem timestamp_uniqueness_load_bearing :
    countsP_bin Nock.RedTeam.Batch73.duplicateExponentTree ≠ 0 :=
  Nock.RedTeam.Batch73.timestamp_nodup_is_load_bearing.2.2.2.2.2

/-- The repaired exponent partitions accept a reverse verify order, as required by the global
LogUp/intermediate multiset. -/
theorem permuted_matching_remains_accepted :
    (readExps Nock.RedTeam.Batch74.permutedIntermediateTree).Perm [0, 1] ∧
      (verifyExps Nock.RedTeam.Batch74.permutedIntermediateTree).Perm [0, 1] ∧
      readExps Nock.RedTeam.Batch74.permutedIntermediateTree ≠
        verifyExps Nock.RedTeam.Batch74.permutedIntermediateTree :=
  ⟨Nock.RedTeam.Batch74.permuted_intermediate_accepted.1,
    Nock.RedTeam.Batch74.permuted_intermediate_accepted.2.1,
    Nock.RedTeam.Batch74.permuted_intermediate_accepted.2.2.1⟩

/-! ## C.

The
`IO.LmIO`-level refutations are retained as the counter-controls that keep the global condition
load-bearing. -/

namespace AggregateHaltRoot

open Nock.RedTeam.Thm54P3Nonvacuity
open Nock.RedTeam.Thm54P2Nonvacuity
  (sharedRecord cLabel raw_requests_singleton rootFP headFP tailFP)
open Nock.RedTeam.Batch74.NoServiceRoot

/-- `IO.LmIO` still rejects an empty request list through `InRange` — but that is
now a statement about the ONE aggregate forest multiset, not about each seeded root. -/
theorem empty_forest_lmio_rejected :
    ¬ IO.LmIO cfg.Ksz ([] : List K17) [] := by
  rw [IO.LmIO_iff]
  simp [IO.InRange]

/-- Counter-control at the actual `Ksz`: a forest whose aggregate response multiset misses a
requested `z^i` is still rejected, so the global condition is load-bearing. -/
theorem forest_mismatch_lmio_rejected :
    ¬ IO.LmIO cfg.Ksz [(4 : K17)] ([] : List K17) := by
  rw [IO.LmIO_iff]
  rintro ⟨-, -, -, hfin⟩
  have h4 : (4 : K17) ∈ ([] : List K17).toFinset := by
    rw [← hfin]
    simp
  simp at h4

/-- Generic counter-control at the consumed object: an execution whose global `intermediate`
request and response multisets disagree cannot inhabit `ExactAxisStructuralRefinement`, however
well-formed each individual root may be. -/
theorem forest_partition_is_load_bearing
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hmiss : (forestReadTimestamps cfg exec).toFinset ≠
      (forestVerifyTimestamps cfg exec).toFinset) :
    ¬ ExactAxisStructuralRefinement cfg exec := by
  intro S
  exact hmiss ((IO.LmIO_iff _ _ _).1 S.intermediate_matching).2.2.2

/-- Generic counter-control for the paper's global terminal check: a forest with no memory record at
all is still rejected, because the `[K]` index range is `1 ≤ k` on the aggregate multiset
. -/
theorem record_free_forest_is_load_bearing
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hall : ∀ i, exactAxisTree cfg exec i = MTree.halt) :
    ¬ ExactAxisStructuralRefinement cfg exec := by
  intro S
  have hempty : forestReadTimestamps cfg exec = [] := by
    rw [forestReadTimestamps]
    apply List.flatMap_eq_nil_iff.2
    intro i _
    rw [hall i]
    simp [readExps]
  have hrange := ((IO.LmIO_iff _ _ _).1 S.intermediate_matching).1
  rw [hempty] at hrange
  simp [IO.InRange] at hrange

/-! ### The serviced first root of the accepted two-root P3 execution -/

/-- 28th: the served trace lives on the a-bearing view `Thm54P3Nonvacuity.execA` (the executed
`exec` is its Form R row encode); the halt-only root is shared by both views. -/
theorem halt_only_axis_treeA :
    exactAxisTree cfg execA dummyRoot = MTree.halt := by
  norm_num [dummyRoot, exactAxisTree, ExactExecution.memoryTreeAt,
      Nock.RedTeam.Thm54P3Nonvacuity.execA, dummyTree, dummyLabel,
    AxisBridge.ofNTree, AxisBridge.MemWalk.toMTree, cfg]

theorem halt_root_no_responsesA : rootResponseRecords execA dummyRoot = [] := by
  simp [dummyRoot, rootResponseRecords, ExactExecution.memoryTreeAt,
      Nock.RedTeam.Thm54P3Nonvacuity.execA,
    dummyTree, dummyLabel, pDummy, MemoryTable.responseRecords, cfg, bfsForest]

def haltOnlyRootTraceA : RootTrace cfg execA dummyRoot where
  subject := .atom 0
  services := []
  recordPartition := by
    rw [halt_root_no_responsesA]
    simp
  readPartition := by
    rw [halt_only_axis_treeA]
    simp [readExps]
  verifyPartition := by
    rw [halt_only_axis_treeA]
    simp [verifyExps]
  traversal := by
    rw [halt_only_axis_treeA]
    exact ServiceWalk.halt

def readRoot : Fin cfg.kMem := ⟨1, by norm_num [cfg]⟩

/-- The two supplied roots exhaust the forest index. -/
theorem root_cases (i : Fin cfg.kMem) : i = readRoot ∨ i = dummyRoot := by
  rcases i with ⟨i, hi⟩
  have hi' : i < 2 := by simpa [cfg] using hi
  interval_cases i
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem forest_index_list : List.finRange cfg.kMem = [dummyRoot, readRoot] := rfl

/-- The exponent the exact carrier assigns to the shared record's timestamp `α^1 = 4`. -/
def sharedExponent : ℕ := timestampExp cfg.challenges.α sharedRecord.ts

theorem shared_timestamp_closed :
    sharedRecord.ts = cfg.challenges.α ^ sharedExponent :=
  timestampExp_spec
    (show TimestampClosedAt cfg.challenges.α sharedRecord.ts from
      ⟨1, by rw [shared_timestamp_is_alpha_one, semantic_exponent_one]⟩)

theorem shared_timestamp_value : cfg.challenges.α ^ sharedExponent = (4 : K17) := by
  rw [← shared_timestamp_closed]
  norm_num [sharedRecord]

/-- The serviced root's exact axis tree: one `read_root`, one `decompose`, and the matching
`verify_child` in the right branch with committed axis `3`. -/
theorem read_root_axis_tree :
    exactAxisTree cfg execA readRoot =
      .read sharedExponent
        (.decompose .halt (.verify sharedExponent (3 : K17) .halt)) := by
  norm_num [readRoot, sharedExponent, exactAxisTree, ExactExecution.memoryTreeAt,
    Nock.RedTeam.Thm54P3Nonvacuity.execA, readTreeP3A, decompTreeP3A, headTreeP3, verifyTreeA,
    tailTreeP3, readLabelP3A, decompLabelP3, headLabelP3, verifyLabelA, tailLabelP3,
    AxisBridge.ofNTree, AxisBridge.MemWalk.toMTree, timestampExpAt, pReadA, pVerifyA, pRead,
    pVerify, sharedRecord]

theorem read_root_exps :
    readExps (exactAxisTree cfg execA readRoot) = [sharedExponent] ∧
      verifyExps (exactAxisTree cfg execA readRoot) = [sharedExponent] := by
  rw [read_root_axis_tree]
  constructor <;> simp [readExps, verifyExps]

theorem halt_root_exps :
    readExps (exactAxisTree cfg execA dummyRoot) = [] ∧
      verifyExps (exactAxisTree cfg execA dummyRoot) = [] := by
  rw [halt_only_axis_treeA]
  constructor <;> simp [readExps, verifyExps]

/-- The record's root/child nouns: the shared record realizes the cell `(1, 2)` and its right
child `2`, so the Nock axis `3` genuinely serves it. -/
def serviceRootNoun : Noun := .cell (.atom 1) (.atom 2)

def serviceChildNoun : Noun := .atom 2

theorem service_realization :
    OpcodeSemantics.RealizesMemRec cfg.challenges.z sharedRecord
      serviceRootNoun serviceChildNoun 3 where
  root_realizes := by
    show sharedRecord.root = GlobalCarryRecognizer.enc cfg.challenges.z serviceRootNoun
    rw [show cfg.challenges.z = (1 : K17) from rfl, serviceRootNoun,
      GlobalCarryRecognizer.enc_cons (show (1 : K17) ≠ 0 by norm_num),
      GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_atom]
    ext <;>
      norm_num [sharedRecord, rootFP, headFP, tailFP, ComputeTable.FP.cons,
        ComputeTable.FP.atomFP]
  child_realizes := by
    show sharedRecord.child = GlobalCarryRecognizer.enc cfg.challenges.z serviceChildNoun
    rw [show cfg.challenges.z = (1 : K17) from rfl, serviceChildNoun,
      GlobalCarryRecognizer.enc_atom]
    ext <;> norm_num [sharedRecord, tailFP, ComputeTable.FP.atomFP]
  axis_realizes := by norm_num [sharedRecord]

/-- The compute-side service of the serviced root.  Nothing here is new evidence: the record, its
timestamp closure, its noun realization and its slot fact are all facts of the pre-existing
accepted execution. -/
noncomputable def readRootService : Service cfg execA where
  exponent := sharedExponent
  record := sharedRecord
  root := serviceRootNoun
  child := serviceChildNoun
  axis := 3
  request_mem := by
    change sharedRecord ∈ exec.rawRequests
    rw [ExactExecution.rawRequests, execution_rows.1]
    simp [cLabel, raw_requests_singleton]
  timestamp := shared_timestamp_closed
  realization := service_realization
  served := by norm_num [serviceRootNoun, serviceChildNoun, Noun.slot]

/-- The serviced root's `RootTrace`: one service, the computed right-descent route, and the
noun-indexed walk. -/
noncomputable def readRootTrace : RootTrace cfg execA readRoot where
  subject := serviceRootNoun
  services := [readRootService]
  recordPartition := by
    simp [rootResponseRecords, readRoot, ExactExecution.memoryTreeAt,
        Nock.RedTeam.Thm54P3Nonvacuity.execA, readTreeP3A,
      decompTreeP3A, headTreeP3, verifyTreeA, tailTreeP3, readLabelP3A, decompLabelP3,
      headLabelP3, verifyLabelA, tailLabelP3, bfsForest, MemoryTable.responseRecords,
      pReadA, pVerifyA, pRead, pDecomp, pHead, pVerify, pTail, readRootService] <;>
    (dsimp only [Fin.cast]; simp [rootResponseRecords, readRoot, ExactExecution.memoryTreeAt,
        Nock.RedTeam.Thm54P3Nonvacuity.execA, readTreeP3A,
      decompTreeP3A, headTreeP3, verifyTreeA, tailTreeP3, readLabelP3A, decompLabelP3,
      headLabelP3, verifyLabelA, tailLabelP3, bfsForest, MemoryTable.responseRecords,
      pReadA, pVerifyA, pRead, pDecomp, pHead, pVerify, pTail, readRootService])
  readPartition := by
    rw [read_root_exps.1]
    exact List.Perm.refl _
  verifyPartition := by
    rw [read_root_exps.2]
    exact List.Perm.refl _
  traversal := by
    rw [read_root_axis_tree]
    refine ServiceWalk.read readRootService (by simp) rfl rfl ?_ ?_
    · rw [show readRootService.axis = 3 from rfl,
        show axisPath 3 = [true] from Nock.NockVMROM.Thm54.BuildableConcrete.concreteAxisPath]
      exact VerifyRoute.right (by simp [readCount]) (by simp [verifyCount])
        (VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount]))
    · exact ServiceWalk.decompose ServiceWalk.halt (ServiceWalk.verify ServiceWalk.halt)

/-- The one global `intermediate` request multiset of the accepted two-root execution: the single
`z^i` of the serviced root, with the record-free root contributing nothing. -/
theorem accepted_forest_timestamps :
    forestReadTimestamps cfg execA = [(4 : K17)] ∧
      forestVerifyTimestamps cfg execA = [(4 : K17)] := by
  constructor
  · rw [forestReadTimestamps, forest_index_list, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_nil, read_root_exps.1, halt_root_exps.1]
    simp [shared_timestamp_value]
  · rw [forestVerifyTimestamps, forest_index_list, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_nil, read_root_exps.2, halt_root_exps.2]
    simp [shared_timestamp_value]

/-- **Flip of `accepted_two_root_execution_has_no_axisStructural`.**  The accepted two-root
execution whose second root is a legal halt-only noun now inhabits the released structural
refinement: its aggregate `intermediate` multiset is the single `z^i` of the serviced first root,
and the record-free root simply contributes nothing. -/
theorem accepted_two_root_execution_has_axisStructural :
    ExactAxisStructuralRefinement cfg execA := by
  refine
    { ancestry := ?_
      read_timestamps_nodup := ?_
      intermediate_matching := ?_ }
  · intro i
    rcases root_cases i with rfl | rfl
    · rw [read_root_axis_tree]
      norm_num [AxisBridge.ReadVerifyNested, verifyCount]
    · rw [halt_only_axis_treeA]
      trivial
  · intro i
    rcases root_cases i with rfl | rfl
    · rw [read_root_exps.1]
      simp
    · rw [halt_root_exps.1]
      simp
  · rw [IO.LmIO_iff, accepted_forest_timestamps.1, accepted_forest_timestamps.2]
    refine ⟨?_, le_refl _, by simp, rfl⟩
    norm_num [IO.InRange, cfg]

/-- **Flip of `accepted_halt_root_has_no_aggregate_trace`.**  Both roots inhabit `RootTrace` — the
halt-only one with an empty service partition — and the pair inhabits the aggregate
`ExactServedMemoryTrace` for *every* semantic-data witness, because the only compute row is a
terminal OP1 with no OP0/OP9 served lookup (`requiredServedLookups .s1 = 0`). -/
noncomputable def acceptedServedMemoryRoots : ∀ i : Fin cfg.kMem, RootTrace cfg execA i
  | ⟨0, _⟩ => haltOnlyRootTraceA
  | ⟨1, _⟩ => readRootTrace
  | ⟨_ + 2, h⟩ => by
      exfalso
      have hk : cfg.kMem = 2 := rfl
      omega

theorem accepted_roots_services :
    (acceptedServedMemoryRoots readRoot).services = [readRootService] ∧
      (acceptedServedMemoryRoots dummyRoot).services = [] :=
  ⟨rfl, rfl⟩

/-- The aggregate CORE on the accepted two-root execution, halt-only second root included. -/
noncomputable def acceptedServedMemoryTrace
    {q Λ : ℕ} (D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    ExactServedMemoryTrace q Λ cfg exec D execA where
  roots := acceptedServedMemoryRoots
  timestampPowersNodup := by
    rw [forest_index_list, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil]
    simp [RootTrace.timestampPowers, RootTrace.exponents, accepted_roots_services.1,
      accepted_roots_services.2, readRootService]
  forestIndexRange := by
    rw [forest_index_list, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil]
    simp [IO.InRange, RootTrace.timestampPowers, RootTrace.exponents,
      accepted_roots_services.1, accepted_roots_services.2, cfg] <;> exact ⟨Nat.le_refl _, by decide⟩
  semanticCoverage := by
    intro row lookup hlookup
    have hstate : (exec.computeRowAt row).1 = .s1 := by
      rcases row with ⟨row, hrow⟩
      have hrow0 : row = 0 := by
        have : row < 1 := by simpa [cfg] using hrow
        omega
      subst row
      norm_num [ExactExecution.computeRowAt, execution_rows.1, cLabel, cfg]
    have hlen : (D.rows row).needs.served.length = 0 := by
      rw [(D.rows row).needs.served_count]
      simp [SemanticTrace.requiredServedLookups, hstate]
    rw [List.eq_nil_of_length_eq_zero hlen] at hlookup
    simp at hlookup


theorem accepted_halt_root_has_aggregate_trace
    {q Λ : ℕ} (D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    Nonempty (RootTrace cfg execA dummyRoot) ∧
      Nonempty (ExactServedMemoryTrace q Λ cfg exec D execA) ∧
      (acceptedServedMemoryRoots dummyRoot).services = [] ∧
      rootResponseRecords execA dummyRoot = [] :=
  ⟨⟨haltOnlyRootTraceA⟩, ⟨acceptedServedMemoryTrace D⟩, rfl, halt_root_no_responsesA⟩

/-- **The halt-only root reaches the production axis fields.**  Both axis-side fields that
`buildableMemoryProductionAssignment` feeds to `MemoryProductionAssignment` are produced on the
accepted two-root execution: the released structural refinement and the identically-zero per-root
count polynomial for *every* root, halt-only root included. -/
theorem accepted_halt_root_reaches_memoryProduction_axis_fields
    {q Λ : ℕ} (D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    ExactAxisStructuralRefinement cfg execA ∧
      ExactMemoryAxisValidity cfg execA ∧
      ∀ i : Fin cfg.kMem, countsP_bin (exactAxisTree cfg execA i) = 0 := by
  have h2 : (2 : K17) ≠ 0 := by decide
  refine ⟨(acceptedServedMemoryTrace D).axisStructural,
    (acceptedServedMemoryTrace D).axisValidity, ?_⟩
  exact rootPolynomial_of_exactMemoryAxisValidity h2
    (acceptedServedMemoryTrace D).axisStructural
    (acceptedServedMemoryTrace D).axisValidity
    (acceptedServedMemoryTrace D).support

end AggregateHaltRoot

/-! ## D. Same-object threading and production load-bearingness -/

/-- Every generic subject remains in the dependent conclusion; the builder cannot choose a
detached configuration, execution, sampled assignment, or memory trace. -/
theorem generic_builder_threads_E_and_I
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros) :
    Nonempty (MemoryProductionAssignment (sampledAssignment E I) E.execA) ∧
      (buildableMemoryProductionAssignment E I hmore).axisStructural =
        E.memoryTrace.axisStructural ∧
      (buildableMemoryProductionAssignment E I hmore).axisRootPolynomial =
        rootPolynomial_of_exactMemoryAxisValidity E.two_ne_zero
          E.memoryTrace.axisStructural E.memoryTrace.axisValidity E.memoryTrace.support := by
  exact ⟨⟨buildableMemoryProductionAssignment E I hmore⟩, rfl, rfl⟩

/-- Both production-side fields are necessary on the same exact `E.cfg/E.exec`: failing either
actual-root ancestry or its root polynomial excludes the production assignment. -/
theorem production_axis_fields_are_load_bearing
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros) :
    (∀ root : Fin E.cfg.kMem,
      (¬ ReadVerifyNested (exactAxisTree E.cfg E.execA root)) →
        ¬ MemoryProductionAssignment (sampledAssignment E I) E.execA) ∧
      (∀ root : Fin E.cfg.kMem,
        countsP_bin (exactAxisTree E.cfg E.execA root) ≠ 0 →
          ¬ MemoryProductionAssignment (sampledAssignment E I) E.execA) := by
  exact ⟨fun root => no_memoryProduction_of_exact_ancestry_failure E I root,
    fun root => no_memoryProduction_of_exact_rootPolynomial_failure E I root⟩


theorem all_buildable_fields_are_explicit
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) :
    E = {
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
      memoryIOCapacity := E.memoryIOCapacity } :=
  E.eta_with_memoryTrace

/-! ## E. Released surface regression guards -/

theorem released_alias_and_forest_control_unchanged :
    @«Thm:NockVMROM» =
        @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch69.repaired_alias_and_forest_control

/-! ## F. -/

#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAddress
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAxis
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAxis_pos
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAddress_concat
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAxis_concat
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.axisPath
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.axisPath_of_lt_two
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.axisPath_of_two_le
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAxis_axisPath
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.nounChild
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.nounAt
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.nounAt_concat
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.slot_pathAxis
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.Service
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.Service.axis_pos
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.rootResponseRecords
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute.spec
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute.served
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.nounShape
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.readVerifyNested
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.support
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.nounShape
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.readVerifyNested
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.readTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.verifyTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.readExps_nodup
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.verifyExps_nodup
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.readTimestamps_perm
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.verifyTimestamps_perm
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.forestReadTimestamps_perm
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.forestVerifyTimestamps_perm
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.intermediateMatching
#print axioms Nock.NockVMROM.Thm54.forestReadTimestamps
#print axioms Nock.NockVMROM.Thm54.forestVerifyTimestamps
#print axioms Nock.NockVMROM.Thm54.readTimestamps_sublist_forest
#print axioms Nock.NockVMROM.Thm54.verifyTimestamps_sublist_forest
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.forestVerifyTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.verifyTimestamps_nodup
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.intermediate_closes
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.rootTimestampPowersNodup
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.axisStructural
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.support
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.honestReconstruction
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.eta_with_memoryTrace
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.language
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.rootPolynomial_of_exactMemoryAxisValidity
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.buildableMemoryProductionAssignment
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.buildableMemoryProductionAssignment_nonempty
#print axioms Nock.AxisBridge.countsP_zero_of_exactMemoryAxisValidity
#print axioms Nock.AxisBridge.countsP_zero_of_exactMemoryAxisValidity_single
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteMemoryService
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteAxisTree
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteAxisPath
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteServedMemoryRoots
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteServedMemoryTrace
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteExecution

#print axioms depth_two_slot_convention
#print axioms forcedDepthRoute
#print axioms forced_depth_route_rederives_slot
#print axioms wrong_depth_route_rejected
#print axioms terminal_route_forces_committed_axis
#print axioms concreteForcedRoute
#print axioms concreteForcedWalk
#print axioms concrete_walk_is_operational
#print axioms two_permutations_force_support
#print axioms read_partition_is_load_bearing
#print axioms verify_partition_is_load_bearing
#print axioms record_partition_is_emission_equality
#print axioms local_timestamp_nodup_does_not_imply_global
#print axioms timestamp_uniqueness_load_bearing
#print axioms permuted_matching_remains_accepted
#print axioms AggregateHaltRoot.empty_forest_lmio_rejected
#print axioms AggregateHaltRoot.forest_mismatch_lmio_rejected
#print axioms AggregateHaltRoot.forest_partition_is_load_bearing
#print axioms AggregateHaltRoot.record_free_forest_is_load_bearing
#print axioms AggregateHaltRoot.read_root_axis_tree
#print axioms AggregateHaltRoot.service_realization
#print axioms AggregateHaltRoot.readRootService
#print axioms AggregateHaltRoot.readRootTrace
#print axioms AggregateHaltRoot.accepted_forest_timestamps
#print axioms AggregateHaltRoot.accepted_two_root_execution_has_axisStructural
#print axioms AggregateHaltRoot.acceptedServedMemoryRoots
#print axioms AggregateHaltRoot.acceptedServedMemoryTrace
#print axioms AggregateHaltRoot.accepted_halt_root_has_aggregate_trace
#print axioms AggregateHaltRoot.accepted_halt_root_reaches_memoryProduction_axis_fields
#print axioms generic_builder_threads_E_and_I
#print axioms production_axis_fields_are_load_bearing
#print axioms all_buildable_fields_are_explicit
#print axioms released_alias_and_forest_control_unchanged

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

end
end Nock.RedTeam.Batch75
