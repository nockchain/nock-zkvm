import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.JointCoins
import Nock.AxisBridge

/-!
It
identifies the extra axis event that must be unioned into it.

There are two challenge coordinates that earlier axis statements conflate:

* `ChallengeVector.α` is the compute timestamp challenge.  Exact memory records have timestamps
  `α^e`.
* `ChallengeVector.z`, and hence `MemoryTable.Inputs.z`, is the noun-fingerprint (NPR) seed.

The production counterexamples `readVerifyNested_wall` and `nested_load_bearing` show
this.  We expose it in `ExactAxisRefinement`, rather than assuming it in an unconditional theorem.
-/

open scoped BigOperators Classical Polynomial

namespace Nock.NockVMROM.Thm54

open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

/-! ## The exact timestamp/axis view of an authoritative memory root -/

/-- A field timestamp is represented by a power of the exact timestamp challenge `α`. -/
def TimestampClosedAt (α ts : K) : Prop :=
  ∃ e : ℕ, ts = α ^ e

/-- Canonical exponent chosen from a timestamp and the exact timestamp challenge.

Unlike `AxisBridge.expOf inp`, this uses `ChallengeVector.α`; it deliberately does not use
`MemoryTable.Inputs.z`, which is the NPR seed in `ExactConfig`.
-/
noncomputable def timestampExp (α ts : K) : ℕ :=
  if h : TimestampClosedAt α ts then h.choose else 0

omit [Fintype K] [DecidableEq K] in
theorem timestampExp_spec {α ts : K} (h : TimestampClosedAt α ts) :
    ts = α ^ timestampExp α ts := by
  simp only [timestampExp, dif_pos h]
  exact h.choose_spec

/-- Timestamp exponent assigned to one exact memory-tree node.  It depends only on the committed
record timestamp, so equal read/verify timestamps receive definitionally the same exponent. -/
noncomputable def timestampExpAt (α : K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) : ℕ :=
  timestampExp α (NTree.label t).2.2.mem.ts

/-- Node-level timestamp closure, restricted to the two states that consume a memory record. -/
def TimestampNodeClosedAt (α : K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) : Prop :=
  match (NTree.label t).1 with
  | .read_root => TimestampClosedAt α (NTree.label t).2.2.mem.ts
  | .verify_child => TimestampClosedAt α (NTree.label t).2.2.mem.ts
  | _ => True

omit [Fintype K] [DecidableEq K] in
theorem timestampNodeClosedAt_spec (α : K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (h : TimestampNodeClosedAt α t) :
    Nock.AxisBridge.TsNode (timestampExpAt α) { z := α, β := 0, γ := 0 } t := by
  unfold TimestampNodeClosedAt at h
  unfold Nock.AxisBridge.TsNode
  generalize hs : (NTree.label t).1 = s at h ⊢
  cases s with
  | decompose => trivial
  | halt => trivial
  | read_root => exact timestampExp_spec h
  | verify_child => exact timestampExp_spec h

/-- The `AxisBatching.MTree` read from one authoritative exact memory root, with timestamp
exponents interpreted using the exact timestamp challenge `cfg.challenges.α`. -/
noncomputable def exactAxisTree
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (i : Fin cfg.kMem) :
    MTree K :=
  (Nock.AxisBridge.ofNTree
    (timestampExpAt cfg.challenges.α) (exec.memoryTreeAt i)).toMTree

/-! ## The one global `intermediate` accumulator of the whole memory forest

the paper stores `intermediate` "externally to the node labels", explicitly "a variable
`global' to the traversal", implements its constraints "in the exact same way as in
`RAP_mem-IO`, `RAP_comp-IO`", and checks its initial and
final values against zero *globally*.  `App:Memconstraints` writes the accumulator gate as the
single row recurrence `(RLC^γ(mem_record(i)) - β)·(intermediate(i) - intermediate(i-1)) =
op₃(i) - op₂(i)` over the whole memory table, and the paper seeds every
mutated `OP2`/`OP7`/`OP8`/`OP9` subject into that same table via `Corr:forest`, so the accumulator
necessarily ranges over all supplied roots at once.  Consequently the `L_mIO` index range `[K]` is a property of the one aggregate request/response multiset below, not of any
individual seeded root: a seeded atom subject is a legitimately record-free root. -/

/-- The one global `intermediate`/IO **request** multiset of the whole supplied memory forest: the
unique `z^i` timestamps added to `intermediate` at every `read_root` row of every seeded root. -/
noncomputable def forestReadTimestamps
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : List K :=
  (List.finRange cfg.kMem).flatMap fun i =>
    (readExps (exactAxisTree cfg exec i)).map (fun e => cfg.challenges.α ^ e)

/-- The matching global **response** multiset: the `z^i` timestamps removed from `intermediate` at
every `verify_child` row of the whole supplied memory forest. -/
noncomputable def forestVerifyTimestamps
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : List K :=
  (List.finRange cfg.kMem).flatMap fun i =>
    (verifyExps (exactAxisTree cfg exec i)).map (fun e => cfg.challenges.α ^ e)

/-- A member's image list is a sublist of a `flatMap`.  This is the localization handle that turns
the one global `intermediate` condition back into the per-root facts the axis derivation needs. -/
theorem sublist_flatMap_of_mem {α β : Type*} {l : List α} {f : α → List β} {a : α}
    (ha : a ∈ l) : (f a).Sublist (l.flatMap f) := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
      rw [List.flatMap_cons]
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact List.sublist_append_left _ _
      · exact (ih hmem).trans (List.sublist_append_right _ _)

omit [Fintype K] [DecidableEq K] in
theorem readTimestamps_sublist_forest
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (i : Fin cfg.kMem) :
    ((readExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Sublist (forestReadTimestamps cfg exec) :=
  sublist_flatMap_of_mem (l := List.finRange cfg.kMem)
    (f := fun j => (readExps (exactAxisTree cfg exec j)).map (fun e => cfg.challenges.α ^ e))
    (List.mem_finRange i)

omit [Fintype K] [DecidableEq K] in
theorem verifyTimestamps_sublist_forest
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (i : Fin cfg.kMem) :
    ((verifyExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Sublist (forestVerifyTimestamps cfg exec) :=
  sublist_flatMap_of_mem (l := List.finRange cfg.kMem)
    (f := fun j => (verifyExps (exactAxisTree cfg exec j)).map (fun e => cfg.challenges.α ^ e))
    (List.mem_finRange i)

/-- Exact cumulative ancestry on every authoritative memory root. -/
def ExactMemoryAncestry
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  ∀ i : Fin cfg.kMem, ReadVerifyNested (exactAxisTree cfg exec i)

/-- Exact axis validity on all records used on both sides of every authoritative memory root. -/
def ExactMemoryAxisValidity
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  ∀ (i : Fin cfg.kMem) (e : ℕ),
    e ∈ readExps (exactAxisTree cfg exec i) →
    e ∈ verifyExps (exactAxisTree cfg exec i) →
    vaxis e (exactAxisTree cfg exec i) = Relaxis e (exactAxisTree cfg exec i)

def ExactMemoryAxisSemantics
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  ExactMemoryAncestry cfg exec ∧ ExactMemoryAxisValidity cfg exec

structure AxisTraversableChainedSemanticExactLanguage
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  traversable : TraversableChainedSemanticExactLanguage cfg exec
  axis : ExactMemoryAxisSemantics cfg exec

/-- Proof-carrying members of the cumulative exact axis language. -/
abbrev AxisTraversableChainedAcceptedExecution (cfg : ExactConfig F K) :=
  { exec : ExactExecution cfg // AxisTraversableChainedSemanticExactLanguage cfg exec }


omit [Fintype K] [DecidableEq K] in
theorem ExactExecution.memoryTreeAt_mem
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) (i : Fin cfg.kMem) :
    exec.memoryTreeAt i ∈ exec.memoryForest := by
  unfold ExactExecution.memoryTreeAt
  exact List.get_mem _ _

structure ExactAxisBridgeLocal
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (i : Fin cfg.kMem) : Prop where
  rvt : RVT (MemoryTable.Fmem (K := K)) (exec.memoryTreeAt i)
  shared_inputs :
    ∀ t', InTree (exec.memoryTreeAt i) t' →
      (NTree.label t').2.1 = cfg.challenges.memoryInputs
  fanout :
    ∀ t', InTree (exec.memoryTreeAt i) t' →
      MemoryTable.fanoutMem (NTree.label t').1 = (NTree.children t').length

omit [Fintype K] [DecidableEq K] in
/-- It intentionally has no `ReadVerifyNested` conclusion. -/
theorem TraversableChainedSemanticExactLanguage.exactAxisBridgeLocal
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TraversableChainedSemanticExactLanguage cfg exec) (i : Fin cfg.kMem) :
    ExactAxisBridgeLocal cfg exec i := by
  have hroot : exec.memoryTreeAt i ∈ exec.memoryForest := exec.memoryTreeAt_mem i
  have hrvtA := h.memory_topology (exec.memoryTreeAt i) hroot
  refine ⟨hrvtA.1, ?_, ?_⟩
  · intro t' ht'
    have hglobal : t' ∈ bfsForest exec.memoryForest := by
      rw [mem_bfsForest]
      exact ⟨exec.memoryTreeAt i, hroot, ht'⟩
    have hrow : NTree.label t' ∈ exec.memoryRows := by
      rw [ExactExecution.memoryRows]
      exact List.mem_map.mpr ⟨t', hglobal, rfl⟩
    exact ((ExactExecution.memoryRowsAccepted_iff exec).1
      h.chained.semantic.2.1 (NTree.label t') hrow).2.1
  · intro t' ht'
    apply MemoryExactTopology.fanout_binding h.memory_topology
    rw [mem_bfsForest]
    exact ⟨exec.memoryTreeAt i, hroot, ht'⟩

/-! ## Explicit proof-carrying refinement for the irreducible ancestry seam -/

/-- Per-root honest noun reconstruction, parameterized by the public/virtual subject of each
authoritative memory root. -/
def ExactMemoryHonestReconstruction
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (subjects : Fin cfg.kMem → Noun) : Prop :=
  ∀ i, HonestRecon (subjects i) (exactAxisTree cfg exec i)

omit [Fintype K] [DecidableEq K] in
theorem exactMemoryAncestry_of_honestReconstruction
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {subjects : Fin cfg.kMem → Noun}
    (h : ExactMemoryHonestReconstruction cfg exec subjects) :
    ExactMemoryAncestry cfg exec :=
  fun i => (h i).2

/-- The exact proof-carrying refinement needed by the axis batching adapter.

`root_accepts` is the missing per-root axis boundary at the configured timestamp challenge.
The current chained exact language stores only the first aggregate memory-row boundary, so this
field is not claimed derivable for every root.
-/
structure ExactAxisRefinement
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  timestamp_closed :
    ∀ (i : Fin cfg.kMem) t', InTree (exec.memoryTreeAt i) t' →
      TimestampNodeClosedAt cfg.challenges.α t'
  ancestry : ExactMemoryAncestry cfg exec
  read_timestamps_nodup :
    ∀ i, ((readExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Nodup
  /-- The `L_mIO` matching of the one `intermediate` accumulator, applied once to the aggregate
  request/response multiset of the whole forest — the paper's variable "`global' to the traversal"
  with its global initial-zero and terminal-zero checks, whose formal shape is the
  `RAP_mem-IO`/`Thm:IO_result` argument it points at.  It is deliberately *not* imposed per seeded
  root: the paper seeds record-free atom subjects into the same forest. -/
  intermediate_matching :
    IO.LmIO cfg.Ksz (forestReadTimestamps cfg exec) (forestVerifyTimestamps cfg exec)
  root_accepts :
    ∀ i, (countsP (exactAxisTree cfg exec i)).eval cfg.challenges.α = 0
  /-- Identically-zero `countsP` is the λ-event (`pwAccountingWork'`), not
  `AxisFailureSet`.  Form R prices those zeros separately. -/
  root_nonzero :
    ∀ i, countsP (exactAxisTree cfg exec i) ≠ 0

namespace ExactAxisRefinement

omit [Fintype K] [DecidableEq K] in
theorem readExps_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisRefinement cfg exec) (i : Fin cfg.kMem) :
    (readExps (exactAxisTree cfg exec i)).Nodup :=
  Nock.AxisBridge.readExps_nodup_of_ts cfg.challenges.α _
    (R.read_timestamps_nodup i)

omit [Fintype K] in
/-- Unique response of the one global `intermediate` matching. -/
theorem forestVerifyTimestamps_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisRefinement cfg exec) :
    (forestVerifyTimestamps cfg exec).Nodup :=
  ((IO.LmIO_iff _ _ _).1 R.intermediate_matching).2.2.1

omit [Fintype K] in
theorem verifyTimestamps_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisRefinement cfg exec) (i : Fin cfg.kMem) :
    ((verifyExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Nodup :=
  (verifyTimestamps_sublist_forest cfg exec i).nodup R.forestVerifyTimestamps_nodup

omit [Fintype K] in
theorem verifyExps_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisRefinement cfg exec) (i : Fin cfg.kMem) :
    (verifyExps (exactAxisTree cfg exec i)).Nodup :=
  Nock.AxisBridge.verifyExps_nodup_of_ts cfg.challenges.α _
    (R.verifyTimestamps_nodup i)

/-- Build the refinement from a noun-realized reconstruction without separately assuming
`ReadVerifyNested`; ancestry is projected from `HonestRecon`. -/
def ofHonestReconstruction
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {subjects : Fin cfg.kMem → Noun}
    (hclosed :
      ∀ (i : Fin cfg.kMem) t', InTree (exec.memoryTreeAt i) t' →
        TimestampNodeClosedAt cfg.challenges.α t')
    (hhonest : ExactMemoryHonestReconstruction cfg exec subjects)
    (hread :
      ∀ i, ((readExps (exactAxisTree cfg exec i)).map
        (fun e => cfg.challenges.α ^ e)).Nodup)
    (hmatch :
      IO.LmIO cfg.Ksz (forestReadTimestamps cfg exec) (forestVerifyTimestamps cfg exec))
    (hroot :
      ∀ i, (countsP (exactAxisTree cfg exec i)).eval cfg.challenges.α = 0)
    (hnz :
      ∀ i, countsP (exactAxisTree cfg exec i) ≠ 0) :
    ExactAxisRefinement cfg exec where
  timestamp_closed := hclosed
  ancestry := exactMemoryAncestry_of_honestReconstruction hhonest
  read_timestamps_nodup := hread
  intermediate_matching := hmatch
  root_accepts := hroot
  root_nonzero := hnz

end ExactAxisRefinement

/-! ## The finite axis-batching event on the `αm` coordinate -/

/-- Lift a one-coordinate timestamp challenge event through the memory `αm` coordinate, leaving
`γ`, `αc`, and the NPR seed unrestricted. -/
noncomputable def liftAlphaM (B : Finset K) : Finset (JointCoins K) :=
  liftMemory (B ×ˢ (Finset.univ : Finset K))

omit [Field K] [DecidableEq K] in
@[simp]
theorem mem_liftAlphaM_iff (B : Finset K) (ω : JointCoins K) :
    ω ∈ liftAlphaM B ↔ alphaM ω ∈ B := by
  rw [liftAlphaM, mem_liftMemory_iff]
  simp [memoryCoins]

omit [Field K] [DecidableEq K] in
/-- Each bad timestamp challenge has exactly `|K|³` joint completions. -/
theorem card_liftAlphaM (B : Finset K) :
    (liftAlphaM B).card = B.card * Fintype.card K ^ 3 := by
  rw [liftAlphaM, card_liftMemory]
  simp only [Finset.card_product, Finset.card_univ]
  ring

/-- Bad timestamp challenges for one memory root.  If that root has any used record with a wrong
committed axis, this is exactly the root set of its axis-count polynomial; otherwise it is empty.
The polynomial is counted once per root, not once per record. -/
noncomputable def axisRootFailureAlphas
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (i : Fin cfg.kMem) : Finset K :=
  if (∃ e : ℕ,
        e ∈ readExps (exactAxisTree cfg exec i) ∧
        e ∈ verifyExps (exactAxisTree cfg exec i) ∧
        vaxis e (exactAxisTree cfg exec i) ≠ Relaxis e (exactAxisTree cfg exec i)) ∧
      countsP (exactAxisTree cfg exec i) ≠ 0
  then
    Finset.univ.filter
      (fun α : K => (countsP (exactAxisTree cfg exec i)).eval α = 0)
  else ∅

/-- Union of the axis-count polynomial bad sets over the exact ordered memory forest. -/
noncomputable def axisBadAlphas
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Finset K :=
  (Finset.univ : Finset (Fin cfg.kMem)).biUnion
    (axisRootFailureAlphas cfg exec)

/-- Polynomial workload of the exact memory forest: one axis-count degree per root. -/
noncomputable def exactAxisWorkload
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : ℕ :=
  ∑ i : Fin cfg.kMem, (countsP (exactAxisTree cfg exec i)).natDegree

@[simp]
theorem mem_axisRootFailureAlphas_iff
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (i : Fin cfg.kMem) (α : K) :
    α ∈ axisRootFailureAlphas cfg exec i ↔
      (∃ e : ℕ,
        e ∈ readExps (exactAxisTree cfg exec i) ∧
        e ∈ verifyExps (exactAxisTree cfg exec i) ∧
        vaxis e (exactAxisTree cfg exec i) ≠ Relaxis e (exactAxisTree cfg exec i)) ∧
      countsP (exactAxisTree cfg exec i) ≠ 0 ∧
      (countsP (exactAxisTree cfg exec i)).eval α = 0 := by
  by_cases h : (∃ e : ℕ,
        e ∈ readExps (exactAxisTree cfg exec i) ∧
        e ∈ verifyExps (exactAxisTree cfg exec i) ∧
        vaxis e (exactAxisTree cfg exec i) ≠ Relaxis e (exactAxisTree cfg exec i)) ∧
      countsP (exactAxisTree cfg exec i) ≠ 0
  · simp [axisRootFailureAlphas, h]
  · constructor
    · intro hα
      have : False := by simpa [axisRootFailureAlphas, h] using hα
      exact this.elim
    · intro hR
      exact (h ⟨hR.1, hR.2.1⟩).elim

@[simp]
theorem mem_axisBadAlphas_iff
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (α : K) :
    α ∈ axisBadAlphas cfg exec ↔
      ∃ i : Fin cfg.kMem, α ∈ axisRootFailureAlphas cfg exec i := by
  simp [axisBadAlphas]

/-- This event is separate from the memory `walkBadForest` event and from NPR collisions.  Its
arguments are the exact `cfg/exec`, so `JointSoundness.FailureUnion T` must add
`AxisFailureSet T.problem.cfg T.problem.exec`.
-/
noncomputable def AxisFailureSet
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Finset (JointCoins K) :=
  liftAlphaM (axisBadAlphas cfg exec)

@[simp]
theorem mem_AxisFailureSet_iff
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (ω : JointCoins K) :
    ω ∈ AxisFailureSet cfg exec ↔ alphaM ω ∈ axisBadAlphas cfg exec := by
  simp [AxisFailureSet]

/-- Form R zeros of a nonzero `countsP` are bounded by degree (`Walk.card_roots_le`).
    Identically-zero polynomials are the λ-event (`pwAccountingWork'`), not this set. -/
theorem axisRootFailureAlphas_card_le
    (_h2 : (2 : K) ≠ 0)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (_R : ExactAxisRefinement cfg exec) (i : Fin cfg.kMem) :
    (axisRootFailureAlphas cfg exec i).card ≤
      (countsP (exactAxisTree cfg exec i)).natDegree := by
  unfold axisRootFailureAlphas
  split
  · rename_i hbad
    have hp : countsP (exactAxisTree cfg exec i) ≠ 0 := hbad.2
    have hset :
        (Finset.univ.filter
            (fun α : K => (countsP (exactAxisTree cfg exec i)).eval α = 0))
          = (Finset.univ.filter
            (fun α : K => (countsP (exactAxisTree cfg exec i)).IsRoot α)) := rfl
    rw [hset]
    exact Nock.Walk.card_roots_le _ hp
  · simp

theorem axisBadAlphas_card_le
    (h2 : (2 : K) ≠ 0)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisRefinement cfg exec) :
    (axisBadAlphas cfg exec).card ≤ exactAxisWorkload cfg exec := by
  calc
    (axisBadAlphas cfg exec).card
        ≤ ∑ i : Fin cfg.kMem, (axisRootFailureAlphas cfg exec i).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ i : Fin cfg.kMem,
          (countsP (exactAxisTree cfg exec i)).natDegree :=
      Finset.sum_le_sum (fun i _ => axisRootFailureAlphas_card_le h2 R i)
    _ = exactAxisWorkload cfg exec := rfl

theorem card_AxisFailureSet
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    (AxisFailureSet cfg exec).card =
      (axisBadAlphas cfg exec).card * Fintype.card K ^ 3 := by
  exact card_liftAlphaM _

/-- Joint-space axis-event bound. -/
theorem AxisFailureSet_card_le
    (h2 : (2 : K) ≠ 0)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (R : ExactAxisRefinement cfg exec) :
    (AxisFailureSet cfg exec).card ≤
      exactAxisWorkload cfg exec * Fintype.card K ^ 3 := by
  rw [card_AxisFailureSet cfg exec]
  exact Nat.mul_le_mul_right _ (axisBadAlphas_card_le h2 R)

/-! ## The corrected failure union and bound -/

/-- For
`JointSoundness.FailureUnion T`, instantiate `base := FailureUnion T`,
`cfg := T.problem.cfg`, and `exec := T.problem.exec`. -/
noncomputable def FailureUnionWithAxis
    (base : Finset (JointCoins K))
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Finset (JointCoins K) :=
  base ∪ AxisFailureSet cfg exec

/-- Corrected workload numerator. -/
noncomputable def jointWorkloadWithAxis
    (baseWorkload : ℕ) (cfg : ExactConfig F K) (exec : ExactExecution cfg) : ℕ :=
  baseWorkload + exactAxisWorkload cfg exec

/-- Corrected finite union bound, conditional only on the explicit axis refinement needed to
justify the new polynomial term.  `hbase` is exactly the existing `failureUnion_card_le`. -/
theorem failureUnionWithAxis_card_le
    (h2 : (2 : K) ≠ 0)
    (base : Finset (JointCoins K)) (baseWorkload : ℕ)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (hbase : base.card ≤ baseWorkload * Fintype.card K ^ 3)
    (R : ExactAxisRefinement cfg exec) :
    (FailureUnionWithAxis base cfg exec).card ≤
      jointWorkloadWithAxis baseWorkload cfg exec * Fintype.card K ^ 3 := by
  calc
    (FailureUnionWithAxis base cfg exec).card
        ≤ base.card + (AxisFailureSet cfg exec).card :=
      Finset.card_union_le _ _
    _ ≤ baseWorkload * Fintype.card K ^ 3 +
          exactAxisWorkload cfg exec * Fintype.card K ^ 3 :=
      Nat.add_le_add hbase (AxisFailureSet_card_le h2 cfg exec R)
    _ = jointWorkloadWithAxis baseWorkload cfg exec * Fintype.card K ^ 3 := by
      simp only [jointWorkloadWithAxis]
      ring

/-! ## Axis-only containment, narrower than noun decoding -/

/-- Extend any existing exact field target by ancestry and axis validity on the same execution. -/
def AxisCumulativeFieldExecutionTarget
    (baseTarget : Prop) (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  baseTarget ∧ ExactMemoryAxisSemantics cfg exec

/-- Axis-only containment interface.  It assumes the old field target already holds and concerns
only failure of the added axis semantics; it performs no noun decoding.  The acceptance premise
contains only the exact-family diagonal fact needed here, `alphaM ω = cfg.challenges.α`. -/
def P8AxisContainment
    (accepts : JointCoins K → Prop) (baseTarget : Prop)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (_R : ExactAxisRefinement cfg exec) : Prop :=
  ∀ ω,
    accepts ω →
    alphaM ω = cfg.challenges.α →
    baseTarget →
    ¬ AxisCumulativeFieldExecutionTarget baseTarget cfg exec →
    ω ∈ AxisFailureSet cfg exec

/-- The proof-carrying refinement proves the narrow axis containment.  The configured root
boundary is transported to sampled `alphaM` by the exact-family diagonal premise. -/
theorem exactAxisRefinement_P8AxisContainment
    (accepts : JointCoins K → Prop) (baseTarget : Prop)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (R : ExactAxisRefinement cfg exec) :
    P8AxisContainment accepts baseTarget cfg exec R := by
  intro ω _hacc hα hfield hnotTarget
  have hnotValid :
      ¬ ExactMemoryAxisValidity cfg exec := by
    intro hvalid
    exact hnotTarget ⟨hfield, R.ancestry, hvalid⟩
  simp only [ExactMemoryAxisValidity] at hnotValid
  push Not at hnotValid
  obtain ⟨i, e, hre, hve, hwrong⟩ := hnotValid
  rw [mem_AxisFailureSet_iff, mem_axisBadAlphas_iff]
  refine ⟨i, ?_⟩
  rw [mem_axisRootFailureAlphas_iff]
  refine ⟨⟨e, hre, hve, hwrong⟩, R.root_nonzero i, ?_⟩
  rw [hα]
  exact R.root_accepts i

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.timestampExp_spec
#print axioms Nock.NockVMROM.Thm54.TraversableChainedSemanticExactLanguage.exactAxisBridgeLocal
#print axioms Nock.NockVMROM.Thm54.exactMemoryAncestry_of_honestReconstruction
#print axioms Nock.NockVMROM.Thm54.axisRootFailureAlphas_card_le
#print axioms Nock.NockVMROM.Thm54.AxisFailureSet_card_le
#print axioms Nock.NockVMROM.Thm54.failureUnionWithAxis_card_le
#print axioms Nock.NockVMROM.Thm54.exactAxisRefinement_P8AxisContainment
