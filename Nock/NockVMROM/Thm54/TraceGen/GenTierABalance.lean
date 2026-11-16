/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierABalance.lean

  Record-count balance of the generated assigned memory forest: each served
  record contributes one `read_root` wrapper and one `verify_child` wrapper,
  so `RowLayout.RecordCountBalanced` holds for `DotConfig257.exec` and
  `DotConfig769.exec`.

  Counts are taken on the generated `GenMemoryRow` forest.  Mapping through
  `GenMemoryRow.row` and BFS does not change them, so the 184-row readout
  is never unfolded.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig769
import Nock.NockVMROM.Thm54.MemoryMplus2L

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Fibre counting on generated memory trees -/

/-- Public memory state on a generated row (`Pub.st`, the same projection
    `memoryStateCount` reads). -/
def memPubSt (g : GenMemoryRow K) : MState := g.row.2.2.st

mutual
/-- Recursive per-tree fibre of the public state. -/
def treeFibre (s : MState) : NTree (GenMemoryRow K) → ℕ
  | .node g cs => (if memPubSt g = s then 1 else 0) + forestFibre s cs
/-- Recursive per-forest fibre of the public state. -/
def forestFibre (s : MState) : List (NTree (GenMemoryRow K)) → ℕ
  | [] => 0
  | t :: ts => treeFibre s t + forestFibre s ts
end

/-- `verify_child` and `read_root` fibres agree. -/
def ForestCountBalanced (forest : List (NTree (GenMemoryRow K))) : Prop :=
  forestFibre .verify_child forest = forestFibre .read_root forest

theorem memPubSt_gMemRow9 (sk : MemoryRowSkeleton) (e : ℕ) (z : K)
    (pub : Pub K) :
    memPubSt (gMemRow9 sk e z pub) = pub.st :=
  rfl

theorem treeFibre_node (s : MState) (g : GenMemoryRow K)
    (cs : List (NTree (GenMemoryRow K))) :
    treeFibre s (.node g cs) =
      (if memPubSt g = s then 1 else 0) + forestFibre s cs :=
  rfl

theorem forestFibre_nil (s : MState) :
    forestFibre s ([] : List (NTree (GenMemoryRow K))) = 0 :=
  rfl

theorem forestFibre_cons (s : MState) (t : NTree (GenMemoryRow K))
    (ts : List (NTree (GenMemoryRow K))) :
    forestFibre s (t :: ts) = treeFibre s t + forestFibre s ts :=
  rfl

theorem forestFibre_singleton (s : MState) (t : NTree (GenMemoryRow K)) :
    forestFibre s [t] = treeFibre s t := by
  rw [forestFibre_cons, forestFibre_nil, add_zero]

theorem forestFibre_append (s : MState) :
    ∀ l₁ l₂ : List (NTree (GenMemoryRow K)),
      forestFibre s (l₁ ++ l₂) = forestFibre s l₁ + forestFibre s l₂
  | [], l₂ => by
      rw [List.nil_append, forestFibre_nil, zero_add]
  | t :: ts, l₂ => by
      rw [List.cons_append, forestFibre_cons, forestFibre_cons,
        forestFibre_append s ts l₂]
      omega

theorem treeFibre_gMemRow9 (s : MState) (sk : MemoryRowSkeleton) (e : ℕ)
    (z : K) (pub : Pub K) (cs : List (NTree (GenMemoryRow K))) :
    treeFibre s (.node (gMemRow9 sk e z pub) cs) =
      (if pub.st = s then 1 else 0) + forestFibre s cs := by
  rw [treeFibre_node, memPubSt_gMemRow9]

theorem annotatedDecPub_st (E : Noun → ComputeTable.FP K) (parent hd tl : Noun)
    (lcCell rcCell : Cell K) (lcSt rcSt : MState) (ipre icur : K) :
    (annotatedDecPub E parent hd tl lcCell rcCell lcSt rcSt ipre icur lmb).st = .decompose :=
  rfl

theorem annotatedReadPub_st (E : Noun → ComputeTable.FP K) (root child : Noun)
    (ax : ℕ) (ts : K) (lcCell : Cell K) (ipre icur lmb : K) :
    (annotatedReadPub E root child ax ts lcCell ipre icur lmb).st = .read_root :=
  rfl

theorem annotatedVerifyPub_st (E : Noun → ComputeTable.FP K) (root child : Noun)
    (ax : ℕ) (ts : K) (lcCell : Cell K) (ipre icur : K) :
    (annotatedVerifyPub E root child ax ts lcCell ipre icur lmb).st = .verify_child :=
  rfl

theorem op9HaltPub_st (E : Noun → ComputeTable.FP K) (a : ℕ) :
    (op9HaltPub E a).st = .halt :=
  rfl

theorem fibreCount_append {α β : Type*} [DecidableEq β] (f : α → β)
    (l₁ l₂ : List α) (b : β) :
    fibreCount f (l₁ ++ l₂) b = fibreCount f l₁ b + fibreCount f l₂ b := by
  simp [fibreCount, List.countP_append]

theorem fibreCount_map {α β γ : Type*} [DecidableEq γ] (f : β → γ) (g : α → β)
    (l : List α) (c : γ) :
    fibreCount f (l.map g) c = fibreCount (fun a => f (g a)) l c := by
  simp only [fibreCount, List.countP_map]
  rfl

theorem forestFibre_eq_roots_add_children (s : MState) :
    ∀ l : List (NTree (GenMemoryRow K)),
      forestFibre s l =
        fibreCount memPubSt (l.map NTree.label) s +
          forestFibre s (l.flatMap NTree.children) := by
  intro l
  induction l with
  | nil => simp [forestFibre, fibreCount]
  | cons t ts ih =>
    cases t with
    | node g cs =>
      rw [forestFibre_cons, treeFibre_node, List.map_cons, fibreCount_cons,
        List.flatMap_cons, forestFibre_append, NTree.label_node, NTree.children_node,
        ih]
      omega

theorem fibreCount_bfsForest (s : MState) :
    ∀ l : List (NTree (GenMemoryRow K)),
      fibreCount memPubSt ((bfsForest l).map NTree.label) s = forestFibre s l := by
  intro l
  generalize hn : totalSize l = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl : l = []
    · subst l
      simp [bfsForest_nil, forestFibre, fibreCount]
    · rw [bfsForest_cons_eq l hl, List.map_append, fibreCount_append,
        forestFibre_eq_roots_add_children]
      have hsize := totalSize_flatMap_children l
      have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
      have hlt : totalSize (l.flatMap NTree.children) < n := by omega
      rw [ih _ hlt (l.flatMap NTree.children) rfl]

/-! ## Noun walks contribute no wrappers -/

theorem genAnnotatedNounWalk_fibre_read (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, treeFibre (.read_root : MState) (genAnnotatedNounWalk E z lmb n).1 = 0
  | .atom a => by
      simp only [genAnnotatedNounWalk]
      rw [treeFibre_gMemRow9, op9HaltPub_st, forestFibre_nil]
      simp
  | .cell h t => by
      simp only [genAnnotatedNounWalk]
      rw [treeFibre_gMemRow9, annotatedDecPub_st]
      rw [forestFibre_cons, forestFibre_cons, forestFibre_nil]
      rw [genAnnotatedNounWalk_fibre_read E z h,
        genAnnotatedNounWalk_fibre_read E z t]
      simp

theorem genAnnotatedNounWalk_fibre_verify (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, treeFibre (.verify_child : MState) (genAnnotatedNounWalk E z lmb n).1 = 0
  | .atom a => by
      simp only [genAnnotatedNounWalk]
      rw [treeFibre_gMemRow9, op9HaltPub_st, forestFibre_nil]
      simp
  | .cell h t => by
      simp only [genAnnotatedNounWalk]
      rw [treeFibre_gMemRow9, annotatedDecPub_st]
      rw [forestFibre_cons, forestFibre_cons, forestFibre_nil]
      rw [genAnnotatedNounWalk_fibre_verify E z h,
        genAnnotatedNounWalk_fibre_verify E z t]
      simp

theorem genAnnotatedVerify_fibre_read (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    treeFibre (.read_root : MState)
      (genAnnotatedVerify E z lmb root child ax ts recordExp).1 = 0 := by
  simp only [genAnnotatedVerify]
  rw [treeFibre_gMemRow9, annotatedVerifyPub_st]
  rw [forestFibre_cons, forestFibre_nil]
  rw [genAnnotatedNounWalk_fibre_read]
  simp

theorem genAnnotatedVerify_fibre_verify (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    treeFibre (.verify_child : MState)
      (genAnnotatedVerify E z lmb root child ax ts recordExp).1 = 1 := by
  simp only [genAnnotatedVerify]
  rw [treeFibre_gMemRow9, annotatedVerifyPub_st]
  rw [forestFibre_cons, forestFibre_nil]
  rw [genAnnotatedNounWalk_fibre_verify]
  simp

/-! ## Axis descent places exactly one verify -/

theorem genAnnotatedDescent_fibre (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    forestFibre (.read_root : MState)
        (genAnnotatedDescent E z lmb root child recAxis ts recordExp
          currentNoun remainingAxis).1 = 0 ∧
      forestFibre (.verify_child : MState)
        (genAnnotatedDescent E z lmb root child recAxis ts recordExp
          currentNoun remainingAxis).1 = 1 := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · simp [forestFibre_singleton, genAnnotatedVerify_fibre_read,
        genAnnotatedVerify_fibre_verify]
    · split
      · constructor
        · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedDecPub_st]
          rw [forestFibre_append, forestFibre_singleton]
          rw [genAnnotatedNounWalk_fibre_read]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
          simp [ihd.1]
        · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedDecPub_st]
          rw [forestFibre_append, forestFibre_singleton]
          rw [genAnnotatedNounWalk_fibre_verify]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
          simp [ihd.2]
      · constructor
        · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedDecPub_st]
          rw [forestFibre_append, forestFibre_singleton]
          rw [genAnnotatedNounWalk_fibre_read]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
          simp [ihd.1]
        · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedDecPub_st]
          rw [forestFibre_append, forestFibre_singleton]
          rw [genAnnotatedNounWalk_fibre_verify]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
          simp [ihd.2]

theorem genAnnotatedRecordTree_fibre (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    treeFibre (.read_root : MState)
        (genAnnotatedRecordTree E z α lmb root child axis recordExp) = 1 ∧
      treeFibre (.verify_child : MState)
        (genAnnotatedRecordTree E z α lmb root child axis recordExp) = 1 := by
  simp only [genAnnotatedRecordTree]
  constructor
  · rw [treeFibre_gMemRow9, annotatedReadPub_st]
    have h := genAnnotatedDescent_fibre (lmb := lmb) E z root child axis (α ^ recordExp)
      recordExp root axis
    simp [h.1]
  · rw [treeFibre_gMemRow9, annotatedReadPub_st]
    have h := genAnnotatedDescent_fibre (lmb := lmb) E z root child axis (α ^ recordExp)
      recordExp root axis
    simp [h.2]

/-! ## Continuation descent preserves wrapper fibres -/

theorem genAnnotatedDescentCont_fibre (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : Cell K)
    (contState : MState) (currentNoun : Noun) (remainingAxis : ℕ) :
    forestFibre (.read_root : MState)
        (genAnnotatedDescentCont E z lmb cont contCell contState
          currentNoun remainingAxis).1 =
      forestFibre .read_root cont ∧
      forestFibre (.verify_child : MState)
        (genAnnotatedDescentCont E z lmb cont contCell contState
          currentNoun remainingAxis).1 =
      forestFibre .verify_child cont := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · simp
    · split
      · constructor
        · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedDecPub_st]
          rw [forestFibre_append, forestFibre_singleton]
          rw [genAnnotatedNounWalk_fibre_read]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
          simp [ihd.1]
        · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedDecPub_st]
          rw [forestFibre_append, forestFibre_singleton]
          rw [genAnnotatedNounWalk_fibre_verify]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
          simp [ihd.2]
      · constructor
        · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedDecPub_st]
          rw [forestFibre_append, forestFibre_singleton]
          rw [genAnnotatedNounWalk_fibre_read]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
          simp [ihd.1]
        · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedDecPub_st]
          rw [forestFibre_append, forestFibre_singleton]
          rw [genAnnotatedNounWalk_fibre_verify]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
          simp [ihd.2]

/-! ## Chained trees: one read and one verify per request -/

theorem genAnnotatedChainedInner_fibre (E : Noun → ComputeTable.FP K) (z α : K)
    (prev : MemRecordReq) :
    ∀ more,
      forestFibre (.read_root : MState)
          (genAnnotatedChainedInner E z α lmb prev more).1 = more.length ∧
        forestFibre (.verify_child : MState)
          (genAnnotatedChainedInner E z α lmb prev more).1 = more.length + 1
  | [] => by
      simp [genAnnotatedChainedInner_nil, forestFibre_singleton,
        genAnnotatedVerify_fibre_read, genAnnotatedVerify_fibre_verify]
  | r :: more => by
      unfold genAnnotatedChainedInner
      constructor
      · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedReadPub_st]
        rw [forestFibre_cons, forestFibre_nil]
        rw [treeFibre_gMemRow9, annotatedVerifyPub_st]
        have ih := genAnnotatedChainedInner_fibre E z α r more
        have hd := genAnnotatedDescentCont_fibre (lmb := lmb) E z
          (genAnnotatedChainedInner E z α lmb r more).1
          (genAnnotatedChainedInner E z α lmb r more).2
          (chainedInnerRootState more) r.root r.axis
        simp [hd.1, ih.1]
        omega
      · rw [forestFibre_singleton, treeFibre_gMemRow9, annotatedReadPub_st]
        rw [forestFibre_cons, forestFibre_nil]
        rw [treeFibre_gMemRow9, annotatedVerifyPub_st]
        have ih := genAnnotatedChainedInner_fibre E z α r more
        have hd := genAnnotatedDescentCont_fibre (lmb := lmb) E z
          (genAnnotatedChainedInner E z α lmb r more).1
          (genAnnotatedChainedInner E z α lmb r more).2
          (chainedInnerRootState more) r.root r.axis
        simp [hd.2, ih.2]
        omega

theorem genAnnotatedChainedTree_fibre (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb reqs = some t) :
    treeFibre (.read_root : MState) t = reqs.length ∧
      treeFibre (.verify_child : MState) t = reqs.length := by
  cases reqs with
  | nil => simp [genAnnotatedChainedTree] at ht
  | cons r rest =>
    cases rest with
    | nil =>
      simp only [genAnnotatedChainedTree] at ht
      injection ht with ht
      subst t
      simpa using
        genAnnotatedRecordTree_fibre (lmb := lmb) E z α r.root r.child r.axis r.recordExp
    | cons r2 more =>
      simp only [genAnnotatedChainedTree] at ht
      injection ht with ht
      subst t
      constructor
      · rw [treeFibre_gMemRow9, annotatedReadPub_st]
        have hi := genAnnotatedChainedInner_fibre (lmb := lmb) E z α r (r2 :: more)
        have hd := genAnnotatedDescentCont_fibre (lmb := lmb) E z
          (genAnnotatedChainedInner E z α lmb r (r2 :: more)).1
          (genAnnotatedChainedInner E z α lmb r (r2 :: more)).2
          (chainedInnerRootState (r2 :: more)) r.root r.axis
        simp [hd.1, hi.1]
        omega
      · rw [treeFibre_gMemRow9, annotatedReadPub_st]
        have hi := genAnnotatedChainedInner_fibre (lmb := lmb) E z α r (r2 :: more)
        have hd := genAnnotatedDescentCont_fibre (lmb := lmb) E z
          (genAnnotatedChainedInner E z α lmb r (r2 :: more)).1
          (genAnnotatedChainedInner E z α lmb r (r2 :: more)).2
          (chainedInnerRootState (r2 :: more)) r.root r.axis
        simp [hd.2, hi.2]

/-! ## Row forests preserve balance -/

theorem forestFibre_map_recordTrees (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ reqs : List MemRecordReq,
      forestFibre (.read_root : MState)
          (reqs.map fun r =>
            genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
        reqs.length ∧
        forestFibre (.verify_child : MState)
          (reqs.map fun r =>
            genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
        reqs.length
  | [] => by simp [forestFibre]
  | r :: rs => by
      rw [List.map_cons, forestFibre_cons, forestFibre_cons]
      have ⟨hr, hv⟩ := genAnnotatedRecordTree_fibre (lmb := lmb) E z α r.root r.child
        r.axis r.recordExp
      have ⟨ih1, ih2⟩ := forestFibre_map_recordTrees E z α rs
      exact ⟨by simp [hr, ih1]; omega, by simp [hv, ih2]; omega⟩

theorem genRowMemForest_pair_eq (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) :
    genRowMemForest E z α lmb [r1, r2] =
      if r1.child = r2.root then
        match genAnnotatedChainedTree E z α lmb [r1, r2] with
        | some t => [t]
        | none =>
          [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
           genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
      else
        [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
         genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp] :=
  rfl

theorem genRowMemForest_three_eq (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 r3 : MemRecordReq) :
    genRowMemForest E z α lmb [r1, r2, r3] =
      genRowMemForest E z α lmb [r1, r2] ++
        [genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp] :=
  rfl

theorem genRowMemForest_pair_balanced (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) :
    ForestCountBalanced (genRowMemForest E z α lmb [r1, r2]) := by
  unfold ForestCountBalanced
  rw [genRowMemForest_pair_eq]
  split
  · cases h : genAnnotatedChainedTree E z α lmb [r1, r2] with
    | none =>
      simp [genAnnotatedChainedTree] at h
    | some t =>
      rw [forestFibre_singleton, forestFibre_singleton]
      have ⟨htr, htv⟩ := genAnnotatedChainedTree_fibre E z α [r1, r2] t h
      omega
  · rw [forestFibre_cons, forestFibre_cons, forestFibre_nil,
      forestFibre_cons, forestFibre_cons, forestFibre_nil]
    have ⟨h1r, h1v⟩ := genAnnotatedRecordTree_fibre (lmb := lmb) E z α r1.root r1.child
      r1.axis r1.recordExp
    have ⟨h2r, h2v⟩ := genAnnotatedRecordTree_fibre (lmb := lmb) E z α r2.root r2.child
      r2.axis r2.recordExp
    omega

theorem genRowMemForest_balanced (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ reqs, ForestCountBalanced (genRowMemForest E z α lmb reqs)
  | [] => by
      simp [ForestCountBalanced, genRowMemForest, forestFibre]
  | [r] => by
      unfold ForestCountBalanced
      rw [genRowMemForest_singleton, forestFibre_singleton, forestFibre_singleton]
      have ⟨hr, hv⟩ := genAnnotatedRecordTree_fibre (lmb := lmb) E z α r.root r.child
        r.axis r.recordExp
      omega
  | [r1, r2] =>
      genRowMemForest_pair_balanced E z α r1 r2
  | [r1, r2, r3] => by
      unfold ForestCountBalanced
      rw [genRowMemForest_three_eq, forestFibre_append, forestFibre_append,
        forestFibre_singleton, forestFibre_singleton]
      have h12 := genRowMemForest_pair_balanced (lmb := lmb) E z α r1 r2
      have ⟨h3r, h3v⟩ := genAnnotatedRecordTree_fibre (lmb := lmb) E z α r3.root r3.child
        r3.axis r3.recordExp
      unfold ForestCountBalanced at h12
      omega
  | r1 :: r2 :: r3 :: r4 :: rest => by
      unfold ForestCountBalanced
      change forestFibre .verify_child
          ((r1 :: r2 :: r3 :: r4 :: rest).map fun r =>
            genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
        forestFibre .read_root
          ((r1 :: r2 :: r3 :: r4 :: rest).map fun r =>
            genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)
      have ⟨hr, hv⟩ := forestFibre_map_recordTrees (lmb := lmb) E z α
        (r1 :: r2 :: r3 :: r4 :: rest)
      omega

/-! ## The full generated forest is balanced -/

theorem genMemForestFromList_balanced (E : Noun → ComputeTable.FP K) (z α : K)
    (ts : List (NTree (GenComputeRow K)))
    (hs : ∀ t ∈ ts, ForestCountBalanced (genMemForestFromTree E z α lmb t)) :
    ForestCountBalanced (genMemForestFromList E z α lmb ts) := by
  induction ts with
  | nil =>
    simp [ForestCountBalanced, genMemForestFromList_nil, forestFibre]
  | cons t rest ih =>
    rw [genMemForestFromList_cons]
    unfold ForestCountBalanced
    rw [forestFibre_append, forestFibre_append]
    have ht : ForestCountBalanced (genMemForestFromTree E z α lmb t) :=
      hs t (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ForestCountBalanced (genMemForestFromList E z α lmb rest) :=
      ih (fun u hu => hs u (List.mem_cons.mpr (Or.inr hu)))
    unfold ForestCountBalanced at ht hrest
    omega

theorem genMemForestFromTree_balanced (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    ForestCountBalanced (genMemForestFromTree E z α lmb t) := by
  induction hn : t.size using Nat.strongRecOn generalizing t with
  | _ n ih =>
    cases t with
    | node g cs =>
      rw [genMemForestFromTree_node]
      unfold ForestCountBalanced
      rw [forestFibre_append, forestFibre_append]
      have hrow := genRowMemForest_balanced (lmb := lmb) E z α (extractNodeReqs g)
      have hcs : ∀ c ∈ cs, ForestCountBalanced (genMemForestFromTree E z α lmb c) := by
        intro c hc
        have hin : c.size ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hle : c.size ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        have hsz : n = 1 + (cs.map NTree.size).sum := by
          simpa [NTree.size] using hn.symm
        exact ih c.size (by omega) c rfl
      have hlist := genMemForestFromList_balanced E z α cs hcs
      unfold ForestCountBalanced at hrow hlist
      omega

/-! ## Mapping through `GenMemoryRow.row` preserves fibres -/

theorem fibreCount_bfsForest_mapNTree_row
    (forest : List (NTree (GenMemoryRow K))) (s : MState) :
    fibreCount (fun row : MState × DTmem K => row.2.2.st)
        ((bfsForest (forest.map (mapNTree GenMemoryRow.row))).map NTree.label) s =
      fibreCount memPubSt ((bfsForest forest).map NTree.label) s := by
  rw [bfsForest_mapNTree, List.map_map]
  simp [fibreCount_map, mapNTree_label, memPubSt]

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig257

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable

theorem memoryStateCount_eq_forestFibre (z α : K) (s : MState) :
    memoryStateCount (exec z α) s =
      forestFibre s
        (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (dotTree (K := K)))) := by
  unfold memoryStateCount ExactExecution.memoryRows
  have hmf : (exec z α).memoryForest = memoryForest z α := rfl
  rw [hmf, memoryForest, fibreCount_bfsForest_mapNTree_row, fibreCount_bfsForest]

/-- Wrapper counts agree on the assigned generated forest. -/
theorem recordCountBalance (z α : K) :
    RecordCountBalanced (exec z α) := by
  unfold RecordCountBalanced
  rw [memoryStateCount_eq_forestFibre, memoryStateCount_eq_forestFibre]
  exact genMemForestFromTree_balanced (encC z) z α
    (bfsAssign (dotTree (K := K)))

end Nock.NockVMROM.Thm54.TraceGen.DotConfig257

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable

theorem memoryStateCount_eq_forestFibre (z α : K) (s : MState) :
    memoryStateCount (exec z α) s =
      forestFibre s
        (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (dotTreeAir (K := K)))) := by
  unfold memoryStateCount ExactExecution.memoryRows
  have hmf : (exec z α).memoryForest = memoryForest z α := rfl
  rw [hmf, memoryForest, fibreCount_bfsForest_mapNTree_row, fibreCount_bfsForest]

/-- Wrapper counts agree on the assigned generated forest. -/
theorem recordCountBalance (z α : K) :
    RecordCountBalanced (exec z α) := by
  unfold RecordCountBalanced
  rw [memoryStateCount_eq_forestFibre, memoryStateCount_eq_forestFibre]
  exact genMemForestFromTree_balanced (encC z) z α
    (bfsAssign (dotTreeAir (K := K)))

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedRecordTree_fibre
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_balanced
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.recordCountBalance
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.recordCountBalance
