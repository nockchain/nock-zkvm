/-
  Nock/NockVMROM/Thm54/TraceGen/BFSAssign.lean

  Relabel a compute tree so line-number exponents follow BFS order, matching
  `computeSkeletonRows` (`Walk.bfsForest`) and `SemanticTimestampSkeleton`.
  `assignExponents` in `Gen.lean` remains the DFS pass (`genTraceDFS`); this
  module does not edit it.  Production `genTrace` lives here: `BFSAssign`
  imports `Gen`, so `Gen.lean` cannot import this file.  Generic traces
  (`genTraceGeneric`) stamp with `bfsAssign` as well.

  The reconstruction is `buildTF` / `reconForest` of the original BFS fan-out
  column, with labels `stampOfAcc` at the prefix-sum of `recordCount` along
  BFS index (`accAt`).  That is the same reconstruction `computeForestOf`
  uses on an execution (`GenericHonestData.lean`).

  Fusion lifts the compute-only capstone over a memory forest via
  `genSemanticSkeleton`; T2–T6 transport by `computeSkeletonRows_genSemantic`
  (`rfl`).  Mem-join restamps live memory `recordExponent`s from BFS compute
  request slots by `MemRecSkeleton` value, not list index.
-/

import Nock.NockVMROM.Thm54.TraceGen.Gen

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

variable {K : Type} [Field K]

/-! ## BFS exponent assignment -/

/-- BFS flatten of a single compute tree, labels only -/
def bfsRows (t : NTree (GenComputeRow K)) : List (GenComputeRow K) :=
  (bfsForest [t]).map NTree.label

/-- Prefix-sum of `recordCount` along BFS index.  `accAt t k` is the exponent
    handed to the node at 0-based BFS position `k` -/
def accAt (t : NTree (GenComputeRow K)) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      accAt t k +
        match (bfsRows t)[k]? with
        | some g => Nock.Framework.recordCount g.skel.state
        | none => 0

/-- 1-indexed BFS label: overwrite only `stamp` via `stampOfAcc`.
    Out-of-range indices fall back to the root at accumulator `0`. -/
def bfsLabelAt (t : NTree (GenComputeRow K)) (i : ℕ) : GenComputeRow K :=
  match (bfsRows t)[i - 1]? with
  | some g => { g with stamp := stampOfAcc g.skel.state (accAt t (i - 1)) }
  | none => { t.label with stamp := stampOfAcc t.label.skel.state 0 }

/-- Relabel `t` by reconstructing its BFS shape with `bfsLabelAt`.
    Returns a tree, not a stamp list: `renderRows` reads stamps off nodes. -/
def bfsAssign (t : NTree (GenComputeRow K)) : NTree (GenComputeRow K) :=
  buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t) (bfsForest [t]).length 1

/-- BFS stamp list of an assigned tree -/
def bfsStamps (u : NTree (GenComputeRow K)) : List ComputeTimestampRow :=
  (bfsForest [u]).map (fun n => n.label.stamp)

/-! ## T1: reconstructed BFS labels -/

theorem bfsForest_singleton_ne_nil {α : Type} (t : NTree α) :
    bfsForest [t] ≠ [] := by
  rw [bfsForest_cons_eq [t] (List.cons_ne_nil _ _)]
  exact List.cons_ne_nil _ _

theorem bfsForest_singleton_length_pos {α : Type} (t : NTree α) :
    0 < (bfsForest [t]).length :=
  List.length_pos_iff.mpr (bfsForest_singleton_ne_nil t)

theorem reconForest_one {α : Type} (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    reconForest 1 fo lbl h = [buildTF 1 fo lbl h 1] := by
  simp [reconForest, List.range'_succ, List.range'_zero]

/-- T1.  BFS labels of `bfsAssign t` are `bfsLabelAt` on `range' 1 h`. -/
theorem bfsAssign_bfsForest_labels (t : NTree (GenComputeRow K)) :
    (bfsForest [bfsAssign t]).map NTree.label =
      (List.range' 1 (bfsForest [t]).length).map (bfsLabelAt t) := by
  have hne : [t] ≠ [] := List.cons_ne_nil _ _
  have hrecon :
      reconForest 1 (foCol (bfsForest [t])) (bfsLabelAt t)
          (bfsForest [t]).length =
        [bfsAssign t] := by
    rw [reconForest_one, bfsAssign]
  rw [← hrecon]
  exact reconForest_labels 1 _ _ _ (Nat.le_refl 1)
    (foCol_Sf_tilingF [t] hne) (foCol_BFSValidF [t] hne)

theorem bfsStamps_bfsAssign (t : NTree (GenComputeRow K)) :
    bfsStamps (bfsAssign t) =
      (List.range' 1 (bfsForest [t]).length).map
        (fun i => (bfsLabelAt t i).stamp) := by
  unfold bfsStamps
  have hmap :
      (bfsForest [bfsAssign t]).map (fun n => n.label.stamp) =
        ((bfsForest [bfsAssign t]).map NTree.label).map
          (fun g => g.stamp) := by
    rw [List.map_map]
    rfl
  rw [hmap, bfsAssign_bfsForest_labels, List.map_map]
  rfl

theorem bfsRows_length (t : NTree (GenComputeRow K)) :
    (bfsRows t).length = (bfsForest [t]).length := by
  simp [bfsRows]

theorem lt_bfsRows_of_mem_range' {t : NTree (GenComputeRow K)} {i : ℕ}
    (hi : i ∈ List.range' 1 (bfsForest [t]).length) :
    i - 1 < (bfsRows t).length := by
  have := (List.mem_range'.mp hi)
  rw [bfsRows_length]
  omega

theorem bfsLabelAt_eq (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    bfsLabelAt t i =
      let g := (bfsRows t)[i - 1]
      { g with stamp := stampOfAcc g.skel.state (accAt t (i - 1)) } := by
  simp [bfsLabelAt, List.getElem?_eq_getElem hi]

theorem bfsLabelAt_skel (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    (bfsLabelAt t i).skel = (bfsRows t)[i - 1].skel := by
  simp [bfsLabelAt_eq t i hi]

theorem bfsLabelAt_stamp (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    (bfsLabelAt t i).stamp =
      stampOfAcc (bfsRows t)[i - 1].skel.state (accAt t (i - 1)) := by
  simp [bfsLabelAt_eq t i hi]

theorem bfsLabelAt_lnPrev (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    (bfsLabelAt t i).stamp.lnPrevExponent = accAt t (i - 1) := by
  rw [bfsLabelAt_stamp t i hi, stampOfAcc_lnPrevExponent]

theorem bfsLabelAt_lnExponent (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    (bfsLabelAt t i).stamp.lnExponent =
      accAt t (i - 1) +
        Nock.Framework.recordCount (bfsLabelAt t i).skel.state := by
  rw [bfsLabelAt_stamp t i hi, stampOfAcc_lnExponent, bfsLabelAt_skel t i hi]

theorem bfsLabelAt_state (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    (bfsLabelAt t i).stamp.state = (bfsLabelAt t i).skel.state := by
  rw [bfsLabelAt_stamp t i hi, stampOfAcc_state, bfsLabelAt_skel t i hi]

theorem accAt_succ_of_lt (t : NTree (GenComputeRow K)) (k : ℕ)
    (hk : k < (bfsRows t).length) :
    accAt t (k + 1) =
      accAt t k + Nock.Framework.recordCount (bfsRows t)[k].skel.state := by
  simp [accAt, List.getElem?_eq_getElem hk]

/-! ## T2: compute topology -/

/-- T2.  Unconditional: BFS skeletons zip with BFS stamps of the same tree. -/
theorem bfsAssign_computeTopology (t : NTree (GenComputeRow K)) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows (genComputeSemanticSkeleton (bfsAssign t)))
      (bfsStamps (bfsAssign t)) := by
  rw [computeSkeletonRows_genCompute]
  unfold bfsStamps
  rw [forall2_map_map_iff]
  intro n hn
  have hmem : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hn, rfl⟩
  rw [bfsAssign_bfsForest_labels, List.mem_map] at hmem
  obtain ⟨i, hi, hni⟩ := hmem
  have hi' := lt_bfsRows_of_mem_range' hi
  rw [← hni]
  exact bfsLabelAt_state t i hi'

/-! ## T3: line-exponent chain -/

theorem computeLineExponentChain_map_range'
    (f : ℕ → ComputeTimestampRow) (a n : ℕ)
    (hsucc : ∀ k, k + 1 < n →
      (f (a + k)).lnExponent = (f (a + k + 1)).lnPrevExponent) :
    ComputeLineExponentChain ((List.range' a n).map f) := by
  induction n generalizing a with
  | zero =>
    simp [List.range'_zero, ComputeLineExponentChain]
  | succ n ih =>
    cases n with
    | zero =>
      simp [List.range'_succ, List.range'_zero, ComputeLineExponentChain]
    | succ m =>
      rw [List.range'_succ, List.map_cons, List.range'_succ, List.map_cons]
      refine ⟨?_, ?_⟩
      · simpa using hsucc 0 (by omega)
      · exact ih (a := a + 1) (fun k hk => by
          have := hsucc (k + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this)

/-- T3.  Consecutive BFS stamps hand the line exponent along `accAt`. -/
theorem bfsAssign_computeLineChain (t : NTree (GenComputeRow K)) :
    ComputeLineExponentChain (bfsStamps (bfsAssign t)) := by
  rw [bfsStamps_bfsAssign]
  refine computeLineExponentChain_map_range'
    (fun i => (bfsLabelAt t i).stamp) 1 (bfsForest [t]).length ?hsucc
  intro k hk
  have hi : 1 + k - 1 < (bfsRows t).length := by
    rw [bfsRows_length]; omega
  have hi' : 1 + k + 1 - 1 < (bfsRows t).length := by
    rw [bfsRows_length]; omega
  have hk_rows : k < (bfsRows t).length := by
    rw [bfsRows_length]; omega
  rw [bfsLabelAt_lnExponent t (1 + k) hi, bfsLabelAt_lnPrev t (1 + k + 1) hi']
  have hidx : 1 + k - 1 = k := by omega
  have hidx' : 1 + k + 1 - 1 = k + 1 := by omega
  rw [hidx, hidx', bfsLabelAt_skel t (1 + k) hi]
  have hacc := accAt_succ_of_lt t k hk_rows
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hacc.symm

/-! ## T4 / T5 / T6 -/

/-- T4.  The BFS forest of a single tree is nonempty, so the head stamp
    starts at `accAt t 0 = 0` -/
theorem bfsAssign_startsAtZero (t : NTree (GenComputeRow K)) :
    ComputeLineStartsAtZero (bfsStamps (bfsAssign t)) := by
  rw [bfsStamps_bfsAssign]
  obtain ⟨m, hm⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.pos_iff_ne_zero.mp (bfsForest_singleton_length_pos t))
  rw [hm, List.range'_succ, List.map_cons]
  change (bfsLabelAt t 1).stamp.lnPrevExponent = 0
  have hi : 1 - 1 < (bfsRows t).length := by
    rw [bfsRows_length, hm]; omega
  rw [bfsLabelAt_lnPrev t 1 hi]
  rfl

theorem mem_bfsStamps_bfsAssign {t : NTree (GenComputeRow K)}
    {stamp : ComputeTimestampRow} (hst : stamp ∈ bfsStamps (bfsAssign t)) :
    ∃ i, i ∈ List.range' 1 (bfsForest [t]).length ∧
      stamp = (bfsLabelAt t i).stamp := by
  rw [bfsStamps_bfsAssign, List.mem_map] at hst
  obtain ⟨i, hi, rfl⟩ := hst
  exact ⟨i, hi, rfl⟩

/-- T5 -/
theorem bfsAssign_computeLineAdvance (t : NTree (GenComputeRow K))
    {stamp : ComputeTimestampRow} (hst : stamp ∈ bfsStamps (bfsAssign t)) :
    stamp.lnExponent =
      stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state := by
  obtain ⟨i, hi, rfl⟩ := mem_bfsStamps_bfsAssign hst
  have hi' := lt_bfsRows_of_mem_range' hi
  rw [bfsLabelAt_stamp t i hi', stampOfAcc_computeLineAdvance]

/-- T6 -/
theorem bfsAssign_computeRecordOffsets (t : NTree (GenComputeRow K))
    {stamp : ComputeTimestampRow} (hst : stamp ∈ bfsStamps (bfsAssign t))
    (i : Fin 3) (hi : (i : ℕ) < Nock.Framework.recordCount stamp.state) :
    stamp.recordExponent i = stamp.lnPrevExponent + (i : ℕ) + 1 := by
  obtain ⟨j, hj, rfl⟩ := mem_bfsStamps_bfsAssign hst
  have hj' := lt_bfsRows_of_mem_range' hj
  have hst' :
      (bfsLabelAt t j).stamp =
        stampOfAcc (bfsRows t)[j - 1].skel.state (accAt t (j - 1)) :=
    bfsLabelAt_stamp t j hj'
  have hstate :
      (bfsLabelAt t j).stamp.state = (bfsRows t)[j - 1].skel.state := by
    rw [hst', stampOfAcc_state]
  have hi' : (i : ℕ) < Nock.Framework.recordCount (bfsRows t)[j - 1].skel.state := by
    rwa [hstate] at hi
  rw [hst', stampOfAcc_recordExponent _ _ i hi', stampOfAcc_lnPrevExponent]

/-! ## Capstone -/

/-- Unconditional `SemanticTimestampSkeleton` over the compute-only
    projection of a BFS-assigned tree, with empty memory.  No path-tree
    or star hypothesis.  `F`/`Algebra` are binders for later
    α-specialization; the fields themselves are Nat/noun topology. -/
noncomputable def genComputeTimestampSkeleton
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) :
    SemanticTimestampSkeleton F K (genComputeSemanticSkeleton (bfsAssign t)) where
  computeRows := bfsStamps (bfsAssign t)
  memoryRows := []
  semanticRequests :=
    genSemanticRequests (genComputeSemanticSkeleton (bfsAssign t))
      (bfsStamps (bfsAssign t))
  semanticResponses := []
  computeTopology := bfsAssign_computeTopology t
  memoryTopology := memoryTopology_genCompute (bfsAssign t)
  computeStartsAtZero := bfsAssign_startsAtZero t
  computeLineChain := bfsAssign_computeLineChain t
  computeLineAdvance := fun _ hst => bfsAssign_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    bfsAssign_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_nil _).symm

theorem genComputeTimestampSkeleton_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) :
    (genComputeTimestampSkeleton F t).computeRows =
      bfsStamps (bfsAssign t) :=
  rfl

/-! ## Fusion: compute + memory

T2–T6 live on the compute-only projection.  `computeSkeletonRows_genSemantic`
is `rfl`, so they transport to a served memory forest with no extra work.
Memory topology is `memoryTopology_genSemantic` from
`memoryStampsWellFormed` on each forest root.  No path-tree or star
hypothesis -/

theorem bfsAssign_computeTopology_genSemantic
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows (genSemanticSkeleton (bfsAssign t) mf))
      (bfsStamps (bfsAssign t)) := by
  rw [computeSkeletonRows_genSemantic]
  exact bfsAssign_computeTopology t

/-- Unconditional `SemanticTimestampSkeleton` over a BFS-assigned compute
    tree and a served memory forest.  `h` is stamp/state agreement on each
    memory root, not a shape gate -/
noncomputable def genTimestampSkeleton
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (bfsAssign t) mf) where
  computeRows := bfsStamps (bfsAssign t)
  memoryRows := genMemoryStamps mf
  semanticRequests :=
    genSemanticRequests (genSemanticSkeleton (bfsAssign t) mf)
      (bfsStamps (bfsAssign t))
  semanticResponses :=
    genSemanticResponses (genSemanticSkeleton (bfsAssign t) mf)
      (genMemoryStamps mf)
  computeTopology := bfsAssign_computeTopology_genSemantic t mf
  memoryTopology := memoryTopology_genSemantic (bfsAssign t) mf h
  computeStartsAtZero := bfsAssign_startsAtZero t
  computeLineChain := bfsAssign_computeLineChain t
  computeLineAdvance := fun _ hst => bfsAssign_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    bfsAssign_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_eq _ _).symm

theorem genTimestampSkeleton_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    (genTimestampSkeleton F t mf h).computeRows =
      bfsStamps (bfsAssign t) :=
  rfl

theorem genTimestampSkeleton_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    (genTimestampSkeleton F t mf h).memoryRows = genMemoryStamps mf :=
  rfl

/-! ## Mem-join

Live memory `recordExponent`s are restamped from BFS compute request slots
by `MemRecSkeleton` value (`root`, `child`, `axis`), not list index.  Padding
rows are left alone.  The rendered `row` is not rewritten: this pass is
α-free -/

def memRecEq (a b : MemRecSkeleton) : Bool :=
  decide (a.root = b.root) && decide (a.child = b.child) && decide (a.axis = b.axis)

def lookupRequestExp (slots : List CanonicalRecordSlot) (rec : MemRecSkeleton) :
    Option ℕ :=
  (slots.find? fun s => memRecEq s.record rec).map CanonicalRecordSlot.exponent

/-- Request slots of the BFS-assigned compute tree, independent of the
    memory forest -/
def bfsRequestSlots (t : NTree (GenComputeRow K)) : List CanonicalRecordSlot :=
  genSemanticRequests (genComputeSemanticSkeleton (bfsAssign t))
    (bfsStamps (bfsAssign t))

/-- Restamp one memory row's Nat exponent from a matching request slot.
    `none` leaves the original exponent -/
def restampMemoryRow (slots : List CanonicalRecordSlot) (g : GenMemoryRow K) :
    GenMemoryRow K :=
  if h : memoryMemRecKind g.skel.state = .active then
    match lookupRequestExp slots (g.skel.memoryRecord h) with
    | some e => { g with stamp := { g.stamp with recordExponent := e } }
    | none => g
  else g

@[simp] theorem restampMemoryRow_skel (slots : List CanonicalRecordSlot)
    (g : GenMemoryRow K) :
    (restampMemoryRow slots g).skel = g.skel := by
  unfold restampMemoryRow
  split
  · rename_i hact
    cases lookupRequestExp slots (g.skel.memoryRecord hact) <;> rfl
  · rfl

@[simp] theorem restampMemoryRow_state (slots : List CanonicalRecordSlot)
    (g : GenMemoryRow K) :
    (restampMemoryRow slots g).stamp.state = g.stamp.state := by
  unfold restampMemoryRow
  split
  · rename_i hact
    cases lookupRequestExp slots (g.skel.memoryRecord hact) <;> rfl
  · rfl

@[simp] theorem restampMemoryRow_row (slots : List CanonicalRecordSlot)
    (g : GenMemoryRow K) :
    (restampMemoryRow slots g).row = g.row := by
  unfold restampMemoryRow
  split
  · rename_i hact
    cases lookupRequestExp slots (g.skel.memoryRecord hact) <;> rfl
  · rfl

theorem restampMemoryRow_padding (slots : List CanonicalRecordSlot)
    (g : GenMemoryRow K)
    (hp : memoryMemRecKind g.skel.state ≠ .active) :
    restampMemoryRow slots g = g := by
  unfold restampMemoryRow
  split
  · next hact => exact (hp hact).elim
  · rfl

theorem restampMemoryRow_recordExponent (slots : List CanonicalRecordSlot)
    (g : GenMemoryRow K) :
    (restampMemoryRow slots g).stamp.recordExponent =
      if h : memoryMemRecKind g.skel.state = .active then
        (lookupRequestExp slots (g.skel.memoryRecord h)).getD
          g.stamp.recordExponent
      else g.stamp.recordExponent := by
  unfold restampMemoryRow
  split
  · rename_i hact
    cases lookupRequestExp slots (g.skel.memoryRecord hact) <;> simp [Option.getD]
  · rfl

def restampMemoryTree (slots : List CanonicalRecordSlot) :
    NTree (GenMemoryRow K) → NTree (GenMemoryRow K) :=
  mapNTree (restampMemoryRow slots)

theorem restampMemoryTree_skel (slots : List CanonicalRecordSlot)
    (t : NTree (GenMemoryRow K)) :
    mapNTree (fun g => g.skel) (restampMemoryTree slots t) =
      mapNTree (fun g => g.skel) t := by
  unfold restampMemoryTree
  let P := fun t : NTree (GenMemoryRow K) =>
    mapNTree (fun g => g.skel) (mapNTree (restampMemoryRow slots) t) =
      mapNTree (fun g => g.skel) t
  change P t
  apply NTree.rec (motive_1 := P)
    (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro g ch ih
    simp only [P, mapNTree, List.map_map, restampMemoryRow_skel]
    refine congrArg (NTree.node g.skel) ?_
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem memoryStampsWellFormed_restamp
    (slots : List CanonicalRecordSlot)
    {t : NTree (GenMemoryRow K)}
    (h : memoryStampsWellFormed t) :
    memoryStampsWellFormed (restampMemoryTree slots t) := by
  unfold restampMemoryTree
  let P := fun t : NTree (GenMemoryRow K) =>
    memoryStampsWellFormed t →
      memoryStampsWellFormed (mapNTree (restampMemoryRow slots) t)
  have : P t := by
    apply NTree.rec (motive_1 := P)
      (motive_2 := fun ts => ∀ c ∈ ts, P c)
    · intro g ch ih hwf
      rw [memoryStampsWellFormed_iff] at hwf
      simp only [mapNTree]
      rw [memoryStampsWellFormed_iff]
      constructor
      · rw [restampMemoryRow_state, restampMemoryRow_skel]
        exact hwf.1
      · intro s hs
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
        exact ih u hu (hwf.2 u hu)
    · intro c hc; simp at hc
    · intro head tail ihHead ihTail c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ihHead
      · exact ihTail c hc
  exact this h

def memJoinForest (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    List (NTree (GenMemoryRow K)) :=
  mf.map (restampMemoryTree (bfsRequestSlots t))

theorem memJoinForest_skel (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (memJoinForest t mf).map (mapNTree (fun g => g.skel)) =
      mf.map (mapNTree (fun g => g.skel)) := by
  simp only [memJoinForest, List.map_map]
  apply List.map_congr_left
  intro u _
  exact restampMemoryTree_skel (bfsRequestSlots t) u

theorem genSemanticSkeleton_memJoinForest
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    genSemanticSkeleton (bfsAssign t) (memJoinForest t mf) =
      genSemanticSkeleton (bfsAssign t) mf := by
  unfold genSemanticSkeleton
  congr 1
  exact memJoinForest_skel t mf

theorem memJoinForest_memoryStampsWellFormed
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    ∀ root ∈ memJoinForest t mf, memoryStampsWellFormed root := by
  intro root hr
  simp only [memJoinForest, List.mem_map] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact memoryStampsWellFormed_restamp (bfsRequestSlots t) (h u hu)

/-- Fused capstone over the restamped memory forest.  Compute stamps are
    BFS; live memory exponents are the matching request exponents when a
    `MemRecSkeleton` hits -/
noncomputable def genJoinedTimestampSkeleton
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (bfsAssign t) (memJoinForest t mf)) :=
  genTimestampSkeleton F t (memJoinForest t mf)
    (memJoinForest_memoryStampsWellFormed t mf h)

theorem genJoinedTimestampSkeleton_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    (genJoinedTimestampSkeleton F t mf h).computeRows =
      bfsStamps (bfsAssign t) :=
  rfl

theorem genJoinedTimestampSkeleton_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    (genJoinedTimestampSkeleton F t mf h).memoryRows =
      genMemoryStamps (memJoinForest t mf) :=
  rfl


/-! ## Production worker and DFS bridges -/

/-- Reconstruct a node from `buildTF` via `List.attach_map_val`. -/
theorem buildTF_eq_node (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → GenComputeRow K)
    (h i : ℕ) :
    buildTF kroots fo lbl h i =
      NTree.node (lbl i) ((childIdxsF kroots fo h i).map (buildTF kroots fo lbl h)) := by
  rw [buildTF, List.attach_map_val]

theorem bfsForest_node_nil {α : Type} (g : α) :
    bfsForest [NTree.node g []] = [NTree.node g []] := by
  rw [bfsForest_singleton, NTree.children_node, bfsForest_nil]

/-- Leaf BFS assign is `stampOfAcc` at accumulator `0` with empty children. -/
theorem bfsAssign_node_nil (g : GenComputeRow K) :
    bfsAssign (NTree.node g []) =
      NTree.node { g with stamp := stampOfAcc g.skel.state 0 } [] := by
  have hW := bfsForest_node_nil g
  have hlen : (bfsForest [NTree.node g []]).length = 1 := by simp [hW]
  have hch : childIdxsF 1 (foCol (bfsForest [NTree.node g []])) 1 1 = [] := by
    have hfo : foCol (bfsForest [NTree.node g []]) 1 = 0 := by
      simp [foCol, hW, NTree.children_node, List.getElem?_cons_zero]
    simp [childIdxsF, hfo, List.range'_zero]
  have hlbl : bfsLabelAt (NTree.node g []) 1 =
      { g with stamp := stampOfAcc g.skel.state 0 } := by
    unfold bfsLabelAt
    have hrows : bfsRows (NTree.node g []) = [g] := by
      simp [bfsRows, hW]
    simp [hrows, accAt, List.getElem?_cons_zero]
  have hnode :
      buildTF 1 (foCol (bfsForest [NTree.node g []]))
          (bfsLabelAt (NTree.node g [])) 1 1 =
        NTree.node (bfsLabelAt (NTree.node g []) 1) [] := by
    rw [buildTF_eq_node, hch, List.map_nil]
  rw [bfsAssign, hlen, hnode, hlbl]

theorem bfsAssign_node_nil_eq_assignExponents (g : GenComputeRow K) :
    bfsAssign (NTree.node g []) = assignExponents (NTree.node g []) := by
  rw [bfsAssign_node_nil, assignExponents, assignTree, assignList]

theorem bfsForest_two_leaves {α : Type} (g gl gr : α) :
    bfsForest [NTree.node g [NTree.node gl [], NTree.node gr []]] =
      [NTree.node g [NTree.node gl [], NTree.node gr []],
        NTree.node gl [], NTree.node gr []] := by
  rw [bfsForest_singleton]
  simp only [NTree.children_node]
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, List.flatMap_nil, NTree.children_node,
    List.append_nil, bfsForest_nil, List.cons_append, List.nil_append]

theorem bfsRows_two_leaves (g gl gr : GenComputeRow K) :
    bfsRows (NTree.node g [NTree.node gl [], NTree.node gr []]) = [g, gl, gr] := by
  simp [bfsRows, bfsForest_two_leaves]

theorem accAt_two_leaves_1 (g gl gr : GenComputeRow K) :
    accAt (NTree.node g [NTree.node gl [], NTree.node gr []]) 1 =
      Nock.Framework.recordCount g.skel.state := by
  simp [accAt, bfsRows_two_leaves, List.getElem?_cons_zero]

theorem accAt_two_leaves_2 (g gl gr : GenComputeRow K) :
    accAt (NTree.node g [NTree.node gl [], NTree.node gr []]) 2 =
      Nock.Framework.recordCount g.skel.state +
        Nock.Framework.recordCount gl.skel.state := by
  simp [accAt, bfsRows_two_leaves, List.getElem?_cons_zero, List.getElem?_cons_succ]

/-- Cons-over-two-leaf star: BFS stamps coincide with DFS `assignExponents`. -/
theorem bfsAssign_eq_assignExponents_two_leaves
    (g gl gr : GenComputeRow K) :
    bfsAssign (NTree.node g [NTree.node gl [], NTree.node gr []]) =
      assignExponents (NTree.node g [NTree.node gl [], NTree.node gr []]) := by
  set t := NTree.node g [NTree.node gl [], NTree.node gr []]
  have hW := bfsForest_two_leaves g gl gr
  have hlen : (bfsForest [t]).length = 3 := by simp [t, hW]
  have hfo1 : foCol (bfsForest [t]) 1 = 2 := by
    simp [foCol, t, hW, NTree.children_node, List.getElem?_cons_zero]
  have hfo2 : foCol (bfsForest [t]) 2 = 0 := by
    simp [foCol, t, hW, NTree.children_node, List.getElem?_cons_zero,
      List.getElem?_cons_succ]
  have hfo3 : foCol (bfsForest [t]) 3 = 0 := by
    simp [foCol, t, hW, NTree.children_node, List.getElem?_cons_zero,
      List.getElem?_cons_succ]
  have hch1 : childIdxsF 1 (foCol (bfsForest [t])) 3 1 = [2, 3] := by
    unfold childIdxsF firstCF
    simp [Sf_zero, hfo1, List.range'_succ, List.range'_zero, List.filter,
      decide_eq_true_eq]
  have hch2 : childIdxsF 1 (foCol (bfsForest [t])) 3 2 = [] := by
    unfold childIdxsF
    simp [hfo2, List.range'_zero]
  have hch3 : childIdxsF 1 (foCol (bfsForest [t])) 3 3 = [] := by
    unfold childIdxsF
    simp [hfo3, List.range'_zero]
  have hlbl1 : bfsLabelAt t 1 =
      { g with stamp := stampOfAcc g.skel.state 0 } := by
    unfold bfsLabelAt
    simp [t, bfsRows_two_leaves, accAt, List.getElem?_cons_zero]
  have hlbl2 : bfsLabelAt t 2 =
      { gl with stamp := stampOfAcc gl.skel.state (Nock.Framework.recordCount g.skel.state) } := by
    unfold bfsLabelAt
    simp [t, bfsRows_two_leaves, accAt_two_leaves_1, List.getElem?_cons_zero,
      List.getElem?_cons_succ]
  have hlbl3 : bfsLabelAt t 3 =
      { gr with stamp := stampOfAcc gr.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount gl.skel.state) } := by
    unfold bfsLabelAt
    simp [t, bfsRows_two_leaves, accAt_two_leaves_2, List.getElem?_cons_zero,
      List.getElem?_cons_succ]
  have hrhs :
      assignExponents t =
        NTree.node { g with stamp := stampOfAcc g.skel.state 0 }
          [NTree.node { gl with stamp := stampOfAcc gl.skel.state (Nock.Framework.recordCount g.skel.state) } [],
           NTree.node { gr with stamp := stampOfAcc gr.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount gl.skel.state) } []] := by
    simp only [t, assignExponents, assignTree, assignList, subtreeRecordCount,
      List.map_nil, List.map_cons, List.sum_nil, List.sum_cons, Nat.zero_add,
      Nat.add_zero]
  have hlhs :
      buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t) 3 1 =
        NTree.node { g with stamp := stampOfAcc g.skel.state 0 }
          [NTree.node { gl with stamp := stampOfAcc gl.skel.state (Nock.Framework.recordCount g.skel.state) } [],
           NTree.node { gr with stamp := stampOfAcc gr.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount gl.skel.state) } []] := by
    rw [buildTF_eq_node, hch1, List.map_cons, List.map_cons, List.map_nil]
    rw [buildTF_eq_node (i := 2), hch2, List.map_nil]
    rw [buildTF_eq_node (i := 3), hch3, List.map_nil]
    rw [hlbl1, hlbl2, hlbl3]
  rw [bfsAssign, hlen, hlhs, hrhs]

/-- **`genTrace`.**  Production three-pass worker: compute stamps follow BFS
    (`bfsAssign`), matching `computeSkeletonRows` / `Walk.bfsForest`.  Memory is
    the served reconstruction `genMemForest`.  The DFS worker remains
    `genTraceDFS` in `Gen.lean` for path/star timestamp-skeleton inhabitants. -/
def genTrace (_q _Λ : ℕ) (z α : K) (fuel : ℕ) (subject formula : Noun) :
    Except GenError (GenTrace K K) :=
  match genComputeSkeleton fuel subject formula with
  | .error e => .error e
  | .ok (ct, result) =>
    .ok
      { subject := subject, formula := formula, result := result, fuel := fuel
        computeNodes := renderRows z α (bfsAssign ct)
        memoryNodes := genMemForest z α formula subject }

#print axioms bfsAssign_bfsForest_labels
#print axioms bfsAssign_computeTopology
#print axioms bfsAssign_computeLineChain
#print axioms bfsAssign_startsAtZero
#print axioms bfsAssign_computeLineAdvance
#print axioms bfsAssign_computeRecordOffsets
#print axioms genComputeTimestampSkeleton
#print axioms bfsAssign_computeTopology_genSemantic
#print axioms genTimestampSkeleton
#print axioms restampMemoryRow_skel
#print axioms restampMemoryTree_skel
#print axioms memoryStampsWellFormed_restamp
#print axioms memJoinForest_memoryStampsWellFormed
#print axioms genJoinedTimestampSkeleton
#print axioms bfsAssign_node_nil
#print axioms bfsAssign_node_nil_eq_assignExponents
#print axioms bfsAssign_eq_assignExponents_two_leaves
#print axioms genTrace

end Nock.NockVMROM.Thm54.TraceGen
