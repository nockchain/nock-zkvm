/-
  Nock/NockVMROM/Thm54/TraceGen/GenPairedRecordLayout.lean

  Additive downstream lemmas: `PairedRecordLayout` of the *canonical generated*
  memory trace.  Honest-side completeness only.

  This is a theorem about `genMemForestFromTree` / `genMemoryForest` /
  `genExactExecution` / `genBuildableOfProgram`, derived from the generator's
  definitions.  The §J ledger stays
  untouched — F97 remains the written tick; this module widens the *available*
  scope to every generated forest.

  `Gen.lean` is not edited.  Lemma 6 (pole retarget / `interResidentAcc` completeness) is out of
  scope here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierABalance
import Nock.NockVMROM.Thm54.TraceGen.GenTierASemantic
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenBuildableAssembly
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig769
import Nock.NockVMROM.Thm54.ExactTraversal

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Record lists of a generated forest — DFS pre-order

Same mutual shape as `treeFibre` / `forestFibre` (`GenTierABalance`), reading
the consumed `MemRec` lists instead of the wrapper counts. -/

/-- The record a request constructor writes on both the `read_root` and
`verify_child` wrappers (`annotatedReadPub` / `annotatedVerifyPub`). -/
def reqMem (E : Noun → ComputeTable.FP K) (α : K) (r : MemRecordReq) : ComputeTable.MemRec K :=
  ⟨E r.root, E r.child, (r.axis : K), α ^ r.recordExp⟩

def reqMems (E : Noun → ComputeTable.FP K) (α : K) (reqs : List MemRecordReq) :
    List (ComputeTable.MemRec K) :=
  reqs.map (reqMem E α)

mutual
/-- Added (`read_root`) records of one generated memory tree, DFS pre-order. -/
def treeAdded : NTree (GenMemoryRow K) → List (ComputeTable.MemRec K)
  | .node g cs => responseRecords g.row.2.2 ++ forestAdded cs
/-- Added records of a generated memory forest. -/
def forestAdded : List (NTree (GenMemoryRow K)) → List (ComputeTable.MemRec K)
  | [] => []
  | t :: ts => treeAdded t ++ forestAdded ts
end

mutual
/-- Consumed (`verify_child`) records of one generated memory tree, DFS pre-order. -/
def treeConsumed : NTree (GenMemoryRow K) → List (ComputeTable.MemRec K)
  | .node g cs => consumedRecords g.row.2.2 ++ forestConsumed cs
/-- Consumed records of a generated memory forest. -/
def forestConsumed : List (NTree (GenMemoryRow K)) → List (ComputeTable.MemRec K)
  | [] => []
  | t :: ts => treeConsumed t ++ forestConsumed ts
end

theorem treeAdded_node (g : GenMemoryRow K) (cs : List (NTree (GenMemoryRow K))) :
    treeAdded (.node g cs) = responseRecords g.row.2.2 ++ forestAdded cs :=
  rfl

theorem treeConsumed_node (g : GenMemoryRow K) (cs : List (NTree (GenMemoryRow K))) :
    treeConsumed (.node g cs) = consumedRecords g.row.2.2 ++ forestConsumed cs :=
  rfl

theorem forestAdded_nil : forestAdded ([] : List (NTree (GenMemoryRow K))) = [] := rfl
theorem forestConsumed_nil : forestConsumed ([] : List (NTree (GenMemoryRow K))) = [] :=
  rfl

theorem forestAdded_cons (t : NTree (GenMemoryRow K))
    (ts : List (NTree (GenMemoryRow K))) :
    forestAdded (t :: ts) = treeAdded t ++ forestAdded ts :=
  rfl

theorem forestConsumed_cons (t : NTree (GenMemoryRow K))
    (ts : List (NTree (GenMemoryRow K))) :
    forestConsumed (t :: ts) = treeConsumed t ++ forestConsumed ts :=
  rfl

theorem forestAdded_singleton (t : NTree (GenMemoryRow K)) :
    forestAdded [t] = treeAdded t := by
  rw [forestAdded_cons, forestAdded_nil, List.append_nil]

theorem forestConsumed_singleton (t : NTree (GenMemoryRow K)) :
    forestConsumed [t] = treeConsumed t := by
  rw [forestConsumed_cons, forestConsumed_nil, List.append_nil]

theorem forestAdded_append :
    ∀ l₁ l₂ : List (NTree (GenMemoryRow K)),
      forestAdded (l₁ ++ l₂) = forestAdded l₁ ++ forestAdded l₂
  | [], l₂ => by rw [List.nil_append, forestAdded_nil, List.nil_append]
  | t :: ts, l₂ => by
      rw [List.cons_append, forestAdded_cons, forestAdded_cons, forestAdded_append ts l₂,
        List.append_assoc]

theorem forestConsumed_append :
    ∀ l₁ l₂ : List (NTree (GenMemoryRow K)),
      forestConsumed (l₁ ++ l₂) = forestConsumed l₁ ++ forestConsumed l₂
  | [], l₂ => by rw [List.nil_append, forestConsumed_nil, List.nil_append]
  | t :: ts, l₂ => by
      rw [List.cons_append, forestConsumed_cons, forestConsumed_cons,
        forestConsumed_append ts l₂, List.append_assoc]

theorem treeAdded_gMemRow9 (sk : MemoryRowSkeleton) (e : ℕ) (z : K) (pub : Pub K)
    (cs : List (NTree (GenMemoryRow K))) :
    treeAdded (.node (gMemRow9 sk e z pub) cs) =
      responseRecords pub ++ forestAdded cs :=
  rfl

theorem treeConsumed_gMemRow9 (sk : MemoryRowSkeleton) (e : ℕ) (z : K) (pub : Pub K)
    (cs : List (NTree (GenMemoryRow K))) :
    treeConsumed (.node (gMemRow9 sk e z pub) cs) =
      consumedRecords pub ++ forestConsumed cs :=
  rfl

/-! ## Constructor pairing — the paper -/

theorem annotatedVerifyPub_mem' (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lc : Cell K) (ipre icur : K) :
    (annotatedVerifyPub E root child ax ts lc ipre icur lmb).mem =
      ⟨E root, E child, (ax : K), ts⟩ :=
  rfl

theorem added_of_annotatedRead (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lc : Cell K) (ipre icur : K) :
    responseRecords (annotatedReadPub E root child ax ts lc ipre icur lmb) =
      [⟨E root, E child, (ax : K), ts⟩] := by
  simp [responseRecords, annotatedReadPub_ver, annotatedReadPub_mem]

theorem consumed_of_annotatedVerify (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lc : Cell K) (ipre icur : K) :
    consumedRecords (annotatedVerifyPub E root child ax ts lc ipre icur lmb) =
      [⟨E root, E child, (ax : K), ts⟩] := by
  simp [consumedRecords, annotatedVerifyPub_st, annotatedVerifyPub_mem']

theorem consumed_of_annotatedRead (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lc : Cell K) (ipre icur : K) :
    consumedRecords (annotatedReadPub E root child ax ts lc ipre icur lmb) = [] := by
  simp [consumedRecords, annotatedReadPub_st]

theorem added_of_annotatedVerify (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lc : Cell K) (ipre icur : K) :
    responseRecords (annotatedVerifyPub E root child ax ts lc ipre icur lmb) = [] := by
  simp [responseRecords, annotatedVerifyPub_ver]

theorem added_of_annotatedDec (E : Noun → ComputeTable.FP K)
    (parent hd tl : Noun) (lc rc : Cell K) (lcSt rcSt : MState) (ipre icur : K) :
    responseRecords (annotatedDecPub E parent hd tl lc rc lcSt rcSt ipre icur lmb) = [] := by
  simp [responseRecords, annotatedDecPub_ver]

theorem consumed_of_annotatedDec (E : Noun → ComputeTable.FP K)
    (parent hd tl : Noun) (lc rc : Cell K) (lcSt rcSt : MState) (ipre icur : K) :
    consumedRecords (annotatedDecPub E parent hd tl lc rc lcSt rcSt ipre icur lmb) = [] := by
  simp [consumedRecords, annotatedDecPub_st]

theorem added_of_op9Halt (E : Noun → ComputeTable.FP K) (a : ℕ) :
    responseRecords (op9HaltPub E a) = [] := by
  -- `op9HaltPub` leaves `ver` at the structure default `decide (st = read_root)`,
  -- and `st =.halt`, so `ver = false`.
  simp [responseRecords, op9HaltPub]

theorem consumed_of_op9Halt (E : Noun → ComputeTable.FP K) (a : ℕ) :
    consumedRecords (op9HaltPub E a) = [] := by
  simp [consumedRecords, op9HaltPub_st]

/-! ## Lemma 3 load-bearing: noun walks contribute nothing — the paper -/

/-- Off-path siblings and `verify_child`'s unique child emit no `read_root` and
no `verify_child` wrappers, so they add and remove nothing from `intermediate`. -/
theorem genAnnotatedNounWalk_treeAdded (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, treeAdded (genAnnotatedNounWalk E z lmb n).1 = []
  | .atom a => by
      simp only [genAnnotatedNounWalk]
      rw [treeAdded_gMemRow9, added_of_op9Halt, forestAdded_nil, List.nil_append]
  | .cell h t => by
      simp only [genAnnotatedNounWalk]
      rw [treeAdded_gMemRow9, added_of_annotatedDec]
      rw [forestAdded_cons, forestAdded_cons, forestAdded_nil]
      rw [genAnnotatedNounWalk_treeAdded E z h, genAnnotatedNounWalk_treeAdded E z t]
      simp

theorem genAnnotatedNounWalk_treeConsumed (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, treeConsumed (genAnnotatedNounWalk E z lmb n).1 = []
  | .atom a => by
      simp only [genAnnotatedNounWalk]
      rw [treeConsumed_gMemRow9, consumed_of_op9Halt, forestConsumed_nil, List.nil_append]
  | .cell h t => by
      simp only [genAnnotatedNounWalk]
      rw [treeConsumed_gMemRow9, consumed_of_annotatedDec]
      rw [forestConsumed_cons, forestConsumed_cons, forestConsumed_nil]
      rw [genAnnotatedNounWalk_treeConsumed E z h,
        genAnnotatedNounWalk_treeConsumed E z t]
      simp

/-! ## Verify subtree: add nothing, consume the constructor record -/

theorem genAnnotatedVerify_treeAdded (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    treeAdded (genAnnotatedVerify E z lmb root child ax ts recordExp).1 = [] := by
  simp only [genAnnotatedVerify]
  rw [treeAdded_gMemRow9, added_of_annotatedVerify, forestAdded_singleton,
    genAnnotatedNounWalk_treeAdded]
  rfl

theorem genAnnotatedVerify_treeConsumed (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    treeConsumed (genAnnotatedVerify E z lmb root child ax ts recordExp).1 =
      [⟨E root, E child, (ax : K), ts⟩] := by
  simp only [genAnnotatedVerify]
  rw [treeConsumed_gMemRow9, consumed_of_annotatedVerify, forestConsumed_singleton,
    genAnnotatedNounWalk_treeConsumed, List.append_nil]

/-! ## Axis descent: add nothing, consume the one verify — the paper -/

theorem genAnnotatedDescent_lists (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    forestAdded (genAnnotatedDescent E z lmb root child recAxis ts recordExp
        currentNoun remainingAxis).1 = [] ∧
      forestConsumed (genAnnotatedDescent E z lmb root child recAxis ts recordExp
        currentNoun remainingAxis).1 =
        [⟨E root, E child, (recAxis : K), ts⟩] := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · simp [forestAdded_singleton, forestConsumed_singleton,
        genAnnotatedVerify_treeAdded, genAnnotatedVerify_treeConsumed]
    · split
      · constructor
        · rw [forestAdded_singleton, treeAdded_gMemRow9, added_of_annotatedDec]
          rw [forestAdded_append, forestAdded_singleton]
          rw [genAnnotatedNounWalk_treeAdded]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
          simp [ihd.1]
        · rw [forestConsumed_singleton, treeConsumed_gMemRow9, consumed_of_annotatedDec]
          rw [forestConsumed_append, forestConsumed_singleton]
          rw [genAnnotatedNounWalk_treeConsumed]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
          simp [ihd.2]
      · constructor
        · rw [forestAdded_singleton, treeAdded_gMemRow9, added_of_annotatedDec]
          rw [forestAdded_append, forestAdded_singleton]
          rw [genAnnotatedNounWalk_treeAdded]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
          simp [ihd.1]
        · rw [forestConsumed_singleton, treeConsumed_gMemRow9, consumed_of_annotatedDec]
          rw [forestConsumed_append, forestConsumed_singleton]
          rw [genAnnotatedNounWalk_treeConsumed]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
          simp [ihd.2]

/-! ## Lemma 1: independent record tree — both sides `[⟨E root, E child, axis, α^e⟩]` -/

theorem genAnnotatedRecordTree_added (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    treeAdded (genAnnotatedRecordTree E z α lmb root child axis recordExp) =
      [⟨E root, E child, (axis : K), α ^ recordExp⟩] := by
  simp only [genAnnotatedRecordTree]
  rw [treeAdded_gMemRow9, added_of_annotatedRead]
  have h := genAnnotatedDescent_lists (lmb := lmb) E z root child axis (α ^ recordExp)
    recordExp root axis
  simp [h.1]

theorem genAnnotatedRecordTree_consumed (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    treeConsumed (genAnnotatedRecordTree E z α lmb root child axis recordExp) =
      [⟨E root, E child, (axis : K), α ^ recordExp⟩] := by
  simp only [genAnnotatedRecordTree]
  rw [treeConsumed_gMemRow9, consumed_of_annotatedRead]
  have h := genAnnotatedDescent_lists (lmb := lmb) E z root child axis (α ^ recordExp)
    recordExp root axis
  simp [h.2]

theorem genAnnotatedRecordTree_lists (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    treeAdded (genAnnotatedRecordTree E z α lmb root child axis recordExp) =
      treeConsumed (genAnnotatedRecordTree E z α lmb root child axis recordExp) :=
  (genAnnotatedRecordTree_added E z α root child axis recordExp).trans
    (genAnnotatedRecordTree_consumed E z α root child axis recordExp).symm

theorem genAnnotatedRecordTree_eq_reqMem (E : Noun → ComputeTable.FP K) (z α : K)
    (r : MemRecordReq) :
    treeAdded (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
      [reqMem E α r] ∧
      treeConsumed (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
        [reqMem E α r] :=
  ⟨genAnnotatedRecordTree_added E z α r.root r.child r.axis r.recordExp,
    genAnnotatedRecordTree_consumed E z α r.root r.child r.axis r.recordExp⟩

/-! ## Continuation descent preserves record lists — the paper -/

theorem genAnnotatedDescentCont_lists (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : Cell K)
    (contState : MState) (currentNoun : Noun) (remainingAxis : ℕ) :
    forestAdded (genAnnotatedDescentCont E z lmb cont contCell contState
        currentNoun remainingAxis).1 =
      forestAdded cont ∧
      forestConsumed (genAnnotatedDescentCont E z lmb cont contCell contState
        currentNoun remainingAxis).1 =
      forestConsumed cont := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · simp
    · split
      · constructor
        · rw [forestAdded_singleton, treeAdded_gMemRow9, added_of_annotatedDec]
          rw [forestAdded_append, forestAdded_singleton]
          rw [genAnnotatedNounWalk_treeAdded]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
          simp [ihd.1]
        · rw [forestConsumed_singleton, treeConsumed_gMemRow9, consumed_of_annotatedDec]
          rw [forestConsumed_append, forestConsumed_singleton]
          rw [genAnnotatedNounWalk_treeConsumed]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
          simp [ihd.2]
      · constructor
        · rw [forestAdded_singleton, treeAdded_gMemRow9, added_of_annotatedDec]
          rw [forestAdded_append, forestAdded_singleton]
          rw [genAnnotatedNounWalk_treeAdded]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
          simp [ihd.1]
        · rw [forestConsumed_singleton, treeConsumed_gMemRow9, consumed_of_annotatedDec]
          rw [forestConsumed_append, forestConsumed_singleton]
          rw [genAnnotatedNounWalk_treeConsumed]
          have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
          simp [ihd.2]

/-! ## Lemma 2: chained tree — one add and one remove per request -/

theorem genAnnotatedChainedInner_lists (E : Noun → ComputeTable.FP K) (z α : K)
    (prev : MemRecordReq) :
    ∀ more,
      forestAdded (genAnnotatedChainedInner E z α lmb prev more).1 = reqMems E α more ∧
        forestConsumed (genAnnotatedChainedInner E z α lmb prev more).1 =
          reqMem E α prev :: reqMems E α more
  | [] => by
      simp [genAnnotatedChainedInner_nil, forestAdded_singleton, forestConsumed_singleton,
        genAnnotatedVerify_treeAdded, genAnnotatedVerify_treeConsumed, reqMems, reqMem]
  | r :: more => by
      unfold genAnnotatedChainedInner
      constructor
      · rw [forestAdded_singleton, treeAdded_gMemRow9, added_of_annotatedRead]
        rw [forestAdded_cons, forestAdded_nil, List.append_nil]
        rw [treeAdded_gMemRow9, added_of_annotatedVerify]
        have ih := genAnnotatedChainedInner_lists E z α r more
        have hd := genAnnotatedDescentCont_lists (lmb := lmb) E z
          (genAnnotatedChainedInner E z α lmb r more).1
          (genAnnotatedChainedInner E z α lmb r more).2
          (chainedInnerRootState more) r.root r.axis
        simp [reqMems, reqMem, hd.1, ih.1]
      · rw [forestConsumed_singleton, treeConsumed_gMemRow9, consumed_of_annotatedRead]
        rw [forestConsumed_cons, forestConsumed_nil, List.append_nil]
        rw [treeConsumed_gMemRow9, consumed_of_annotatedVerify]
        have ih := genAnnotatedChainedInner_lists E z α r more
        have hd := genAnnotatedDescentCont_lists (lmb := lmb) E z
          (genAnnotatedChainedInner E z α lmb r more).1
          (genAnnotatedChainedInner E z α lmb r more).2
          (chainedInnerRootState more) r.root r.axis
        simp [reqMems, reqMem, hd.2, ih.2]

theorem genAnnotatedChainedTree_lists (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb reqs = some t) :
    treeAdded t = reqMems E α reqs ∧ treeConsumed t = reqMems E α reqs := by
  cases reqs with
  | nil => simp [genAnnotatedChainedTree] at ht
  | cons r rest =>
    cases rest with
    | nil =>
      simp only [genAnnotatedChainedTree] at ht
      injection ht with ht
      subst t
      simpa [reqMems] using
        genAnnotatedRecordTree_eq_reqMem (lmb := lmb) E z α r
    | cons r2 more =>
      simp only [genAnnotatedChainedTree] at ht
      injection ht with ht
      subst t
      constructor
      · rw [treeAdded_gMemRow9, added_of_annotatedRead]
        have hi := genAnnotatedChainedInner_lists (lmb := lmb) E z α r (r2 :: more)
        have hd := genAnnotatedDescentCont_lists (lmb := lmb) E z
          (genAnnotatedChainedInner E z α lmb r (r2 :: more)).1
          (genAnnotatedChainedInner E z α lmb r (r2 :: more)).2
          (chainedInnerRootState (r2 :: more)) r.root r.axis
        simp [reqMems, reqMem, hd.1, hi.1]
      · rw [treeConsumed_gMemRow9, consumed_of_annotatedRead]
        have hi := genAnnotatedChainedInner_lists (lmb := lmb) E z α r (r2 :: more)
        have hd := genAnnotatedDescentCont_lists (lmb := lmb) E z
          (genAnnotatedChainedInner E z α lmb r (r2 :: more)).1
          (genAnnotatedChainedInner E z α lmb r (r2 :: more)).2
          (chainedInnerRootState (r2 :: more)) r.root r.axis
        simp [reqMems, reqMem, hd.2, hi.2]

/-! ## Lemma 3: row forest / compute-tree forest concatenate; walks contribute nothing -/

theorem forestAdded_map_recordTrees (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ reqs : List MemRecordReq,
      forestAdded (reqs.map fun r =>
          genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
        reqMems E α reqs ∧
        forestConsumed (reqs.map fun r =>
          genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
        reqMems E α reqs
  | [] => by simp [forestAdded, forestConsumed, reqMems]
  | r :: rs => by
      rw [List.map_cons, forestAdded_cons, forestConsumed_cons]
      have ⟨ha, hc⟩ := genAnnotatedRecordTree_eq_reqMem (lmb := lmb) E z α r
      have ⟨ih1, ih2⟩ := forestAdded_map_recordTrees E z α rs
      refine ⟨?_, ?_⟩
      · simp [reqMems]; rw [ha, ih1]; rfl
      · simp [reqMems]; rw [hc, ih2]; rfl

theorem genRowMemForest_pair_lists (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) :
    forestAdded (genRowMemForest E z α lmb [r1, r2]) = reqMems E α [r1, r2] ∧
      forestConsumed (genRowMemForest E z α lmb [r1, r2]) = reqMems E α [r1, r2] := by
  rw [genRowMemForest_pair_eq]
  split
  · cases h : genAnnotatedChainedTree E z α lmb [r1, r2] with
    | none =>
      simp [genAnnotatedChainedTree] at h
    | some t =>
      rw [forestAdded_singleton, forestConsumed_singleton]
      exact genAnnotatedChainedTree_lists E z α [r1, r2] t h
  · rw [forestAdded_cons, forestAdded_cons, forestAdded_nil, List.append_nil]
    rw [forestConsumed_cons, forestConsumed_cons, forestConsumed_nil, List.append_nil]
    have ⟨h1a, h1c⟩ := genAnnotatedRecordTree_eq_reqMem (lmb := lmb) E z α r1
    have ⟨h2a, h2c⟩ := genAnnotatedRecordTree_eq_reqMem (lmb := lmb) E z α r2
    simp [reqMems]; rw [h1a, h1c, h2a, h2c]; simp

theorem genRowMemForest_lists (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ reqs,
      forestAdded (genRowMemForest E z α lmb reqs) = reqMems E α reqs ∧
        forestConsumed (genRowMemForest E z α lmb reqs) = reqMems E α reqs
  | [] => by
      simp [genRowMemForest, forestAdded, forestConsumed, reqMems]
  | [r] => by
      rw [genRowMemForest_singleton, forestAdded_singleton, forestConsumed_singleton]
      simpa [reqMems] using genAnnotatedRecordTree_eq_reqMem (lmb := lmb) E z α r
  | [r1, r2] =>
      genRowMemForest_pair_lists E z α r1 r2
  | [r1, r2, r3] => by
      rw [genRowMemForest_three_eq, forestAdded_append, forestConsumed_append,
        forestAdded_singleton, forestConsumed_singleton]
      have ⟨h12a, h12c⟩ := genRowMemForest_pair_lists (lmb := lmb) E z α r1 r2
      have ⟨h3a, h3c⟩ := genAnnotatedRecordTree_eq_reqMem (lmb := lmb) E z α r3
      simp [reqMems]; rw [h12a, h12c, h3a, h3c]; simp [reqMems]
  | r1 :: r2 :: r3 :: r4 :: rest => by
      change
        forestAdded ((r1 :: r2 :: r3 :: r4 :: rest).map fun r =>
            genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
          reqMems E α (r1 :: r2 :: r3 :: r4 :: rest) ∧
          forestConsumed ((r1 :: r2 :: r3 :: r4 :: rest).map fun r =>
            genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) =
          reqMems E α (r1 :: r2 :: r3 :: r4 :: rest)
      exact forestAdded_map_recordTrees E z α (r1 :: r2 :: r3 :: r4 :: rest)

/-- Each compute-row request contributes one added record and one consumed
record; noun-walk and decompose nodes contribute nothing. -/
theorem genRowMemForest_added_eq_consumed (E : Noun → ComputeTable.FP K)
    (z α : K) (reqs : List MemRecordReq) :
    forestAdded (genRowMemForest E z α lmb reqs) =
      forestConsumed (genRowMemForest E z α lmb reqs) :=
  (genRowMemForest_lists E z α reqs).1.trans
    (genRowMemForest_lists E z α reqs).2.symm

theorem genMemForestFromList_lists (E : Noun → ComputeTable.FP K) (z α : K)
    (ts : List (NTree (GenComputeRow K)))
    (hs : ∀ t ∈ ts,
      forestAdded (genMemForestFromTree E z α lmb t) =
        forestConsumed (genMemForestFromTree E z α lmb t)) :
    forestAdded (genMemForestFromList E z α lmb ts) =
      forestConsumed (genMemForestFromList E z α lmb ts) := by
  induction ts with
  | nil =>
    simp [genMemForestFromList_nil, forestAdded, forestConsumed]
  | cons t rest ih =>
    rw [genMemForestFromList_cons, forestAdded_append, forestConsumed_append]
    have ht := hs t (List.mem_cons.mpr (Or.inl rfl))
    have hrest := ih (fun u hu => hs u (List.mem_cons.mpr (Or.inr hu)))
    rw [ht, hrest]

/-- Concatenation through `genMemForestFromTree`: the consumed list equals the
added list because each request contributes one of each and walks contribute
nothing. -/
theorem genMemForestFromTree_added_eq_consumed (E : Noun → ComputeTable.FP K)
    (z α : K) (t : NTree (GenComputeRow K)) :
    forestAdded (genMemForestFromTree E z α lmb t) =
      forestConsumed (genMemForestFromTree E z α lmb t) := by
  induction hn : t.size using Nat.strongRecOn generalizing t with
  | _ n ih =>
    cases t with
    | node g cs =>
      rw [genMemForestFromTree_node, forestAdded_append, forestConsumed_append]
      have hrow := genRowMemForest_added_eq_consumed (lmb := lmb) E z α (extractNodeReqs g)
      have hcs : ∀ c ∈ cs,
          forestAdded (genMemForestFromTree E z α lmb c) =
            forestConsumed (genMemForestFromTree E z α lmb c) := by
        intro c hc
        have hin : c.size ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hle : c.size ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        have hsz : n = 1 + (cs.map NTree.size).sum := by
          simpa [NTree.size] using hn.symm
        exact ih c.size (by omega) c rfl
      have hlist := genMemForestFromList_lists E z α cs hcs
      rw [hrow, hlist]

/-! ## DFS flatten agrees with the structural lists -/

theorem forest_lists_eq_dfs (l : List (NTree (GenMemoryRow K))) :
    forestAdded l =
        (dfsForest l).flatMap (fun u => responseRecords u.label.row.2.2) ∧
      forestConsumed l =
        (dfsForest l).flatMap (fun u => consumedRecords u.label.row.2.2) := by
  induction hn : totalSize l using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l with
    | [] => simp [forestAdded, forestConsumed, dfsForest]
    | t :: ts =>
      cases t with
      | node g cs =>
        have hsz : n = 1 + totalSize cs + totalSize ts := by
          rw [totalSize, List.map_cons, List.sum_cons, NTree.size] at hn
          simp [totalSize] at hn ⊢
          omega
        have hcs : totalSize cs < n := by omega
        have hts : totalSize ts < n := by omega
        have ihcs := ih (totalSize cs) hcs cs rfl
        have ihts := ih (totalSize ts) hts ts rfl
        constructor
        · rw [forestAdded_cons, treeAdded_node, dfsForest_cons, dfsTree_eq,
            NTree.children_node, List.cons_append, List.flatMap_cons,
            List.flatMap_append, NTree.label_node, ihcs.1, ihts.1,
            List.append_assoc]
        · rw [forestConsumed_cons, treeConsumed_node, dfsForest_cons, dfsTree_eq,
            NTree.children_node, List.cons_append, List.flatMap_cons,
            List.flatMap_append, NTree.label_node, ihcs.2, ihts.2,
            List.append_assoc]

theorem forestAdded_eq_dfsForest (l : List (NTree (GenMemoryRow K))) :
    forestAdded l =
      (dfsForest l).flatMap (fun u => responseRecords u.label.row.2.2) :=
  (forest_lists_eq_dfs l).1

theorem forestConsumed_eq_dfsForest (l : List (NTree (GenMemoryRow K))) :
    forestConsumed l =
      (dfsForest l).flatMap (fun u => consumedRecords u.label.row.2.2) :=
  (forest_lists_eq_dfs l).2

/-! ## Lemma 4: BFS permutation and threading preserve `List.Perm` -/

/-- BFS-order consumed records — the `consumedRecords` twin of `servedGen`. -/
def consumedGen (forest : List (NTree (GenMemoryRow K))) : List (ComputeTable.MemRec K) :=
  (bfsForest forest).flatMap (fun t => consumedRecords t.label.row.2.2)

theorem servedGen_perm_forestAdded (forest : List (NTree (GenMemoryRow K))) :
    (servedGen forest).Perm (forestAdded forest) := by
  rw [servedGen, forestAdded_eq_dfsForest]
  exact (bfsForest_perm_dfsForest forest).flatMap (fun _ _ => List.Perm.refl _)

theorem consumedGen_perm_forestConsumed (forest : List (NTree (GenMemoryRow K))) :
    (consumedGen forest).Perm (forestConsumed forest) := by
  rw [consumedGen, forestConsumed_eq_dfsForest]
  exact (bfsForest_perm_dfsForest forest).flatMap (fun _ _ => List.Perm.refl _)

theorem servedGen_perm_consumedGen_of_eq (forest : List (NTree (GenMemoryRow K)))
    (h : forestAdded forest = forestConsumed forest) :
    (servedGen forest).Perm (consumedGen forest) :=
  (servedGen_perm_forestAdded forest).trans <|
    h ▸ (consumedGen_perm_forestConsumed forest).symm

omit [Field K] in
theorem consumedRecords_setAcc (p : Pub K) (a b : K) :
    consumedRecords (setAcc p a b) = consumedRecords p := by
  cases p.st <;> rfl

theorem threadGenRow_consumedRecords (inp : Inputs K) (acc : K)
    (g : GenMemoryRow K) :
    consumedRecords (threadGenRow inp acc g).2.row.2.2 =
      consumedRecords g.row.2.2 := by
  rw [threadGenRow_snd]
  simp [setGenAcc, consumedRecords_setAcc]

theorem threadGenRows_flatMap_consumedRecords (inp : Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).flatMap
          (fun g : GenMemoryRow K => consumedRecords g.row.2.2) =
        gs.flatMap (fun g => consumedRecords g.row.2.2)
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows, threadGenRow_consumedRecords]
      exact threadGenRows_flatMap_consumedRecords inp
        (threadGenRow inp acc g).1 gs

theorem servedGen_threadGenForest' (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    servedGen (threadGenForest inp acc forest) = servedGen forest := by
  rw [servedGen_eq_labels, threadGenForest_bfs_labels,
    threadGenRows_flatMap_responseRecords, servedGen_eq_labels]

theorem consumedGen_eq_labels (forest : List (NTree (GenMemoryRow K))) :
    consumedGen forest =
      ((bfsForest forest).map NTree.label).flatMap
        (fun g : GenMemoryRow K => consumedRecords g.row.2.2) := by
  simp [consumedGen, List.flatMap_map]

theorem consumedGen_threadGenForest (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    consumedGen (threadGenForest inp acc forest) = consumedGen forest := by
  rw [consumedGen_eq_labels, threadGenForest_bfs_labels,
    threadGenRows_flatMap_consumedRecords, consumedGen_eq_labels]

theorem servedGen_perm_consumedGen_thread (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (h : forestAdded forest = forestConsumed forest) :
    (servedGen (threadGenForest inp acc forest)).Perm
      (consumedGen (threadGenForest inp acc forest)) := by
  rw [servedGen_threadGenForest', consumedGen_threadGenForest]
  exact servedGen_perm_consumedGen_of_eq forest h

/-! ## Execution-level transport

`addedRecordList` / `consumedRecordList` are BFS flats of the *mapped* row
forest.  Mapping `GenMemoryRow.row` does not move `mem` or `st`. -/

variable {F : Type} [Field F] [Algebra F K]

theorem addedRecordList_eq_servedGen {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (mf : List (NTree (GenMemoryRow K)))
    (h : exec.memoryForest = mf.map (mapNTree GenMemoryRow.row))
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    addedRecordList exec = servedGen mf := by
  have hraw : ExactExecution.rawResponses exec = servedGen mf := by
    unfold ExactExecution.rawResponses ExactExecution.memoryRows servedGen
    rw [h, bfsForest_mapNTree, List.map_map, List.flatMap_map]
    simp [Function.comp, mapNTree_label]
  exact (rawResponses_eq_addedRecordList exec hhon).symm.trans hraw

theorem consumedRecordList_eq_consumedGen {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (mf : List (NTree (GenMemoryRow K)))
    (h : exec.memoryForest = mf.map (mapNTree GenMemoryRow.row)) :
    consumedRecordList exec = consumedGen mf := by
  unfold consumedRecordList ExactExecution.memoryRows consumedGen
  rw [h, bfsForest_mapNTree, List.map_map, List.flatMap_map]
  simp [Function.comp, mapNTree_label]

/-- `PairedRecordLayout` of any carrier whose memory forest is a mapped
generated forest whose added and consumed DFS lists agree. -/
theorem pairedRecordLayout_of_mapped_lists {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (mf : List (NTree (GenMemoryRow K)))
    (hfor : exec.memoryForest = mf.map (mapNTree GenMemoryRow.row))
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hperm : (servedGen mf).Perm (consumedGen mf)) :
    PairedRecordLayout exec := by
  unfold PairedRecordLayout
  rw [consumedRecordList_eq_consumedGen exec mf hfor,
    addedRecordList_eq_servedGen exec mf hfor hhon]
  exact hperm.symm

theorem pairedRecordLayout_of_genMemForestFromTree {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (E : Noun → ComputeTable.FP K) (z α : K) (t : NTree (GenComputeRow K))
    (h : exec.memoryForest =
      (genMemForestFromTree E z α lmb t).map (mapNTree GenMemoryRow.row))
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    PairedRecordLayout exec :=
  pairedRecordLayout_of_mapped_lists exec (genMemForestFromTree E z α lmb t) h hhon
    (servedGen_perm_consumedGen_of_eq _
      (genMemForestFromTree_added_eq_consumed (lmb := lmb) E z α t))

theorem pairedRecordLayout_of_threadGenForest {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (E : Noun → ComputeTable.FP K) (z α : K) (inp : MemoryTable.Inputs K) (acc : K)
    (t : NTree (GenComputeRow K))
    (h : exec.memoryForest =
      (threadGenForest inp acc (genMemForestFromTree E z α lmb t)).map
        (mapNTree GenMemoryRow.row))
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    PairedRecordLayout exec :=
  pairedRecordLayout_of_mapped_lists exec
    (threadGenForest inp acc (genMemForestFromTree E z α lmb t)) h hhon
    (servedGen_perm_consumedGen_thread inp acc _
      (genMemForestFromTree_added_eq_consumed (lmb := lmb) E z α t))

/-- Honest `ver` of an a-bearing bound row. -/
theorem bindMemoryRowA_honest_ver (z : K) {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRowA z s row) :
    row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  rw [h.2.2.1]; exact h.2.2.2.2.2.2

/-! ## Row encode transport and honest `C'` coherence

The
two record columns transport through the Form R record encode, and on the executed rows `C'` is a
function of the stored record whenever the a-bearing active records are determined by their
timestamps — the replacement of the retired `C' = 1`. -/

section Coherence

theorem consumedRecords_encPub (p : MemoryTable.Pub K) :
    consumedRecords (encPub lmb p) =
      (consumedRecords p).map (fun m => NockVM.formRRow m lmb) := by
  unfold consumedRecords
  rw [encPub_st]
  cases h : p.st with
  | verify_child =>
      simp [encPub_mem_active p (by simp [h, memoryMemRecKind])]
  | read_root => rfl
  | decompose => rfl
  | halt => rfl

theorem addedRecords_encPub (p : MemoryTable.Pub K) :
    (match (encPub lmb p).st with
      | .read_root => [(encPub lmb p).mem]
      | .decompose | .halt | .verify_child => []) =
      (match p.st with
        | .read_root => [p.mem]
        | .decompose | .halt | .verify_child => []).map
        (fun m => NockVM.formRRow m lmb) := by
  rw [encPub_st]
  cases h : p.st with
  | read_root =>
      simp [encPub_mem_active p (by simp [h, memoryMemRecKind])]
  | verify_child => rfl
  | decompose => rfl
  | halt => rfl

/-- On rows whose outer state is their pub's state, the row encode maps the two record columns
through the Form R record encode. -/
theorem consumedRecordList_encodeMem {cfg : ExactConfig F K} (E : ExactExecution cfg)
    (hst : ∀ row ∈ E.memoryRows, row.1 = row.2.2.st) :
    consumedRecordList E.encodeMem =
      (consumedRecordList E).map (fun m => NockVM.formRRow m cfg.challenges.lam) := by
  unfold consumedRecordList
  rw [ExactExecution.encodeMem_memoryRows, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun row hrow => ?_
  rw [encodeRow_pub row (hst row hrow), consumedRecords_encPub]

theorem addedRecordList_encodeMem {cfg : ExactConfig F K} (E : ExactExecution cfg)
    (hst : ∀ row ∈ E.memoryRows, row.1 = row.2.2.st) :
    addedRecordList E.encodeMem =
      (addedRecordList E).map (fun m => NockVM.formRRow m cfg.challenges.lam) := by
  unfold addedRecordList
  rw [ExactExecution.encodeMem_memoryRows, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun row hrow => ?_
  rw [encodeRow_pub row (hst row hrow)]
  exact addedRecords_encPub _

theorem pairedRecordLayout_encodeMem {cfg : ExactConfig F K} (E : ExactExecution cfg)
    (hst : ∀ row ∈ E.memoryRows, row.1 = row.2.2.st) (h : PairedRecordLayout E) :
    PairedRecordLayout E.encodeMem := by
  unfold PairedRecordLayout
  rw [consumedRecordList_encodeMem E hst, addedRecordList_encodeMem E hst]
  exact h.map _

/-- **Active records are determined by their timestamps** on a paired execution whose added column
has distinct timestamps. -/
theorem mem_eq_of_ts_eq_of_paired {cfg : ExactConfig F K} (E : ExactExecution cfg)
    (h : PairedRecordLayout E)
    (hnd : ((addedRecordList E).map ComputeTable.MemRec.ts).Nodup)
    {x y : MemoryTable.MState × MemoryTable.DTmem K} (hx : x ∈ E.memoryRows)
    (hy : y ∈ E.memoryRows)
    (hxa : memoryMemRecKind x.2.2.st = .active) (hya : memoryMemRecKind y.2.2.st = .active)
    (hts : x.2.2.mem.ts = y.2.2.mem.ts) : x.2.2.mem = y.2.2.mem := by
  have hin : ∀ w ∈ E.memoryRows, memoryMemRecKind w.2.2.st = .active →
      w.2.2.mem ∈ addedRecordList E := by
    intro w hw ha
    cases hs : w.2.2.st with
    | read_root =>
        unfold addedRecordList
        exact List.mem_flatMap.mpr ⟨w, hw, by simp [hs]⟩
    | verify_child =>
        refine h.subset ?_
        unfold consumedRecordList
        exact List.mem_flatMap.mpr ⟨w, hw, by simp [consumedRecords, hs]⟩
    | decompose => simp [hs, memoryMemRecKind] at ha
    | halt => simp [hs, memoryMemRecKind] at ha
  exact List.inj_on_of_nodup_map hnd (hin x hx hxa) (hin y hy hya) hts

/-- **Honest `C'` coherence of a row encode.** -/
theorem cprimeCoherent_encodeMem {cfg : ExactConfig F K} (E : ExactExecution cfg)
    (hst : ∀ row ∈ E.memoryRows, row.1 = row.2.2.st)
    (hactTs : ∀ row ∈ E.memoryRows, memoryMemRecKind row.2.2.st = .active →
      row.2.2.mem.ts ≠ 0)
    (hpad : ∀ row ∈ E.memoryRows, memoryMemRecKind row.2.2.st ≠ .active →
      row.2.2.mem = ComputeTable.MemRec.zero ∧ row.2.2.cprime? = none)
    (hts : ∀ x ∈ E.memoryRows, ∀ y ∈ E.memoryRows,
      memoryMemRecKind x.2.2.st = .active → memoryMemRecKind y.2.2.st = .active →
      x.2.2.mem.ts = y.2.2.mem.ts → x.2.2.mem = y.2.2.mem) :
    E.encodeMem.CprimeCoherent := by
  intro r hr r' hr' hm
  rw [ExactExecution.encodeMem_memoryRows] at hr hr'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr'
  rw [encodeRow_pub x (hst x hx), encodeRow_pub y (hst y hy)] at hm ⊢
  by_cases hxa : memoryMemRecKind x.2.2.st = .active <;>
    by_cases hya : memoryMemRecKind y.2.2.st = .active
  · rw [encPub_mem_active _ hxa, encPub_mem_active _ hya] at hm
    have hts' : x.2.2.mem.ts = y.2.2.mem.ts := by
      have := congrArg ComputeTable.MemRec.ts hm
      simpa [NockVM.formRRow] using this
    rw [encPub_cprime_active _ hxa, encPub_cprime_active _ hya,
      hts x hx y hy hxa hya hts']
  · rw [encPub_mem_active _ hxa, encPub_mem_padding _ hya, (hpad y hy hya).1] at hm
    have := congrArg ComputeTable.MemRec.ts hm
    exact absurd (by simpa [NockVM.formRRow, ComputeTable.MemRec.zero] using this)
      (hactTs x hx hxa)
  · rw [encPub_mem_padding _ hxa, (hpad x hx hxa).1, encPub_mem_active _ hya] at hm
    have := congrArg ComputeTable.MemRec.ts hm
    exact absurd (by simpa [NockVM.formRRow, ComputeTable.MemRec.zero] using this.symm)
      (hactTs y hy hya)
  · simp [MemoryTable.Pub.cprime, encPub_cprime?_padding _ hxa, encPub_cprime?_padding _ hya,
      (hpad x hx hxa).2, (hpad y hy hya).2]

end Coherence

/-! ## Lemma 5: `PairedRecordLayout` of `genExactExecution` / `genBuildableOfProgram`

Scope: any compute tree fed to `genMemoryForest` (hence any program
`genComputeSkeleton` accepts).  Not `∀ E`.  Not a field of `E`. -/

/-- **`PairedRecordLayout` of `genExactExecution` at `genMemoryForest`.**

Any compute tree, any field, any threading inputs. -/
theorem genExactExecution_pairedRecordLayout
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (hst : ∀ row ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) (genMemoryForest z α chal.lam inp t)
        hmempos hcomp hmem).memoryRows, row.1 = row.2.2.st)
    (hhon : ∀ row ∈ (genExactExecution (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) (genMemoryForest z α chal.lam inp t)
        hmempos hcomp hmem).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    PairedRecordLayout
      (genExactExecution (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) (genMemoryForest z α chal.lam inp t)
        hmempos hcomp hmem) := by
  set A := genExactExecutionA (F := F) chal Ksz orbit horb a b c
    (genComputeRows z α t) (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem with hA
  have hhonA : ∀ row ∈ A.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
    intro row hrow
    have := hhon (MemoryRowTemplate.encodeRow chal.lam row) (by
      rw [genExactExecution_eq_encodeMem, ExactExecution.encodeMem_memoryRows]
      exact List.mem_map_of_mem hrow)
    rwa [encodeRow_pub row (hst row hrow), encPub_ver, encPub_st] at this
  rw [genExactExecution_eq_encodeMem]
  exact pairedRecordLayout_encodeMem A hst
    (pairedRecordLayout_of_threadGenForest A (encC z) z α inp 0 (bfsAssign (airReorder t)) rfl
      hhonA)

section Program
variable [Fintype K] [DecidableEq K]

private theorem forall₂_exists_of_mem_right {α β} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => cases hb
  | cons hab _ ih =>
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

omit [Fintype K] [DecidableEq K] in
/-- Honest `ver` on any execution witnessing `BindsAt`. -/
theorem honestVer_of_bindsAt {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z S cfg exec) :
    ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  intro row hr
  obtain ⟨s, -, hb⟩ := forall₂_exists_of_mem_right h.derived_memoryRows hr
  exact BindMemoryRow.honest_ver z hb

/-- **Honest `ver` of `genBuildableOfProgram.exec`.** Same hypothesis list as the assembly. -/
theorem genBuildableOfProgram_honestVer {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    ∀ row ∈ (genBuildableOfProgram (F := F) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  have hzchal : chal.z = z := by
    have := congrArg (fun i : ComputeTable.Inputs K => i.z) hinp
    simpa [ChallengeVector.computeInputs] using this
  have hBinds := genBindsAt_threaded (F := F) z α (memInputs z) chal hzchal Ksz orbit horb a b c
    h hmempos hcomp hmem
  exact honestVer_of_bindsAt hBinds

/-- **`PairedRecordLayout` of `genBuildableOfProgram.exec`.**  Same hypothesis
list as the assembly; the conclusion is about the generated carrier, not a
new field of `E`. -/
theorem genBuildableOfProgram_pairedRecordLayout {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    PairedRecordLayout
      (genBuildableOfProgram (F := F) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec := by
  change PairedRecordLayout
    (genExactExecution (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t)
      hmempos hcomp hmem)
  refine genExactExecution_pairedRecordLayout chal Ksz orbit horb z α a b c
    (memInputs z) t hmempos hcomp hmem ?_ ?_
  · intro row hrow
    rw [genExactExecutionA_memoryRows] at hrow
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hrow
    exact genThreadedMemory_state z α (memInputs z) h n hn
  exact genBuildableOfProgram_honestVer (F := F) z α hz htwo a b c chal hinp hmi
    Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
    hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst

/-! ## Honest `C'` coherence of the generated execution (the unique-timestamp premise)

`C' = 1` is gone; the executed rows carry `C' = formRC λ a` of the a-bearing record.  Coherence holds because the a-bearing active records
are determined by their timestamps: verify records are a permutation of read records
(`PairedRecordLayout`), and the read records have distinct timestamps
(`genMemForest_servedTs_nodup`, under the orbit window). -/

omit [Fintype K] [DecidableEq K] in
theorem forestAdded_eq_flatMap (l : List (NTree (GenMemoryRow K))) :
    forestAdded l = l.flatMap (fun u => forestAdded [u]) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
      rw [forestAdded_cons, List.flatMap_cons, ih, forestAdded_singleton]

omit [Fintype K] [DecidableEq K] in
/-- Read timestamps of the generated forest are distinct (orbit window). -/
theorem genMemForest_servedGen_ts_nodup (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) (hmatch : treeRequestsMatch (bfsAssign t))
    (horb : accAt t (bfsRows t).length < orderOf α) :
    ((servedGen (genMemForestFromTree E z α lmb (bfsAssign t))).map
      ComputeTable.MemRec.ts).Nodup := by
  set l := genMemForestFromTree E z α lmb (bfsAssign t)
  have hperm : (servedGen l).Perm (l.flatMap (fun u => servedGen [u])) := by
    refine (servedGen_perm_forestAdded l).trans ?_
    rw [forestAdded_eq_flatMap]
    exact (List.Perm.refl l).flatMap (fun u _ => (servedGen_perm_forestAdded [u]).symm)
  have hnd := genMemForest_servedTs_nodup (lmb := lmb) E z α t hmatch horb
  have heq : (l.flatMap (fun u => servedGen [u])).map ComputeTable.MemRec.ts =
      l.flatMap servedTs := by
    rw [List.map_flatMap]; rfl
  rw [← heq] at hnd
  exact ((hperm.map _).nodup_iff).mpr hnd

omit [Fintype K] [DecidableEq K] in
/-- **Honest `CprimeCoherent` of the generated execution** — the generator discharges the
unique-timestamp premise. -/
theorem genExactExecution_cprimeCoherent (z α : K)
    (chal : ChallengeVector K) (hzc : chal.z = z) (Ksz : ℕ) (orbit : OrbitDomain K)
    (horb : 1 ≤ orbit.h) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).CprimeCoherent := by
  set A := genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem with hA
  have hrowsA := genExactExecutionA_memoryRows (F := F) chal Ksz orbit horb a b c
    (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem
  have hst : ∀ row ∈ A.memoryRows, row.1 = row.2.2.st := by
    intro row hrow
    rw [hrowsA] at hrow
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hrow
    exact genThreadedMemory_state z α (memInputs z) h n hn
  -- honest `ver` on the a-bearing rows, from the executed rows' binding
  have hhonE := honestVer_of_bindsAt
    (genBindsAt_threaded (F := F) z α (memInputs z) chal hzc Ksz orbit horb a b c h
      hmempos hcomp hmem)
  have hhonA : ∀ row ∈ A.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
    intro row hrow
    have := hhonE (MemoryRowTemplate.encodeRow chal.lam row) (by
      rw [genExactExecution_eq_encodeMem, ExactExecution.encodeMem_memoryRows]
      exact List.mem_map_of_mem hrow)
    simpa using this
  have hpaired : PairedRecordLayout A :=
    pairedRecordLayout_of_threadGenForest A (encC z) z α (memInputs z) 0
      (bfsAssign (airReorder t)) rfl hhonA
  have hnd : ((addedRecordList A).map ComputeTable.MemRec.ts).Nodup := by
    rw [addedRecordList_eq_servedGen A _ rfl hhonA]
    unfold genMemoryForest
    rw [servedGen_threadGenForest']
    exact genMemForest_servedGen_ts_nodup (encC z) z α (airReorder t)
      (genComputeSkeleton_air_requestsMatch h) horbα
  have hpad : ∀ row ∈ A.memoryRows, memoryMemRecKind row.2.2.st ≠ .active →
      row.2.2.mem = ComputeTable.MemRec.zero ∧ row.2.2.cprime? = none := by
    intro row hrow hpadst
    rw [hrowsA] at hrow
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hrow
    refine ⟨?_, (genMemoryForest_bfs_aBearing z α (memInputs z) t n hn).1⟩
    obtain ⟨w, hw, hin⟩ := (mem_bfsForest _ n).mp hn
    have hOK := genThreadedMemoryNodesOK z α (memInputs z) h w hw
      (mapNTree GenMemoryRow.node n) (mapNTree_inTree _ hin)
    obtain ⟨-, -, -, htime⟩ := hOK
    simp only [mapNTree_label, GenMemoryRow.node_row, GenMemoryRow.node_stamp] at htime
    have hs1 := hst _ (by rw [hrowsA]; exact List.mem_map_of_mem hn)
    have hkind : memoryMemRecKind n.label.stamp.state = .padding := by
      rw [← htime.1, hs1]
      revert hpadst
      cases n.label.row.2.2.st <;> simp [memoryMemRecKind]
    exact htime.2.2.2 hkind
  -- active rows: `ts = α^e ≠ 0` (`α` has positive order by the orbit window)
  have hα0 : α ≠ 0 := by
    rintro rfl
    have hpos : 0 < orderOf (0 : K) := lt_of_le_of_lt (Nat.zero_le _) horbα
    obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.mp (orderOf_pos_iff.mp hpos)
    simp [zero_pow hn.ne'] at h1
  have hactTs : ∀ row ∈ A.memoryRows, memoryMemRecKind row.2.2.st = .active →
      row.2.2.mem.ts ≠ 0 := by
    intro row hrow hact
    rw [hrowsA] at hrow
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨w, hw, hin⟩ := (mem_bfsForest _ n).mp hn
    have hOK := genThreadedMemoryNodesOK z α (memInputs z) h w hw
      (mapNTree GenMemoryRow.node n) (mapNTree_inTree _ hin)
    obtain ⟨-, -, -, htime⟩ := hOK
    simp only [mapNTree_label, GenMemoryRow.node_row, GenMemoryRow.node_stamp] at htime
    have hk : memoryMemRecKind n.label.stamp.state = .active := by
      rw [← htime.2.1]; exact hact
    rw [htime.2.2.1, if_pos hk]
    exact pow_ne_zero _ hα0
  rw [genExactExecution_eq_encodeMem]
  exact cprimeCoherent_encodeMem A hst hactTs hpad
    (fun x hx y hy hxa hya hts => mem_eq_of_ts_eq_of_paired A hpaired hnd hx hy hxa hya hts)

end Program

/-! ## Non-vacuity at the generated Tier-A carriers

`DotConfig257.exec` / `DotConfig769.exec` commit `genMemForestFromTree` of the
assigned compute tree (unthreaded).  Hand-written F73 / `multiRoot` are *not*
this generator — they already inhabit `PairedRecordLayout` by fixture listing
(`Batch135`, F97 C1); that is a different proof, not an instance of lemma 5. -/

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig257

open Nock.Walk
open Nock.NockVMROM.Thm54.RowLayout
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen

theorem exec_honestVer (z α : K) :
    ∀ row ∈ (exec z α).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  intro row hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (show row ∈
      (bfsForest (memoryForest z α)).map NTree.label from hr)
  unfold memoryForest at ht
  rw [bfsForest_mapNTree, List.mem_map] at ht
  obtain ⟨g, hg, rfl⟩ := ht
  simpa [mapNTree_label] using
    bindMemoryRowA_honest_ver z (assigned_bfs_bindMemoryRow z α g hg)

theorem exec_pairedRecordLayout (z α : K) :
    PairedRecordLayout (exec z α) :=
  pairedRecordLayout_of_genMemForestFromTree (F := F) (exec z α)
    (encC z) z α (bfsAssign (dotTree (K := K))) rfl (exec_honestVer z α)

end Nock.NockVMROM.Thm54.TraceGen.DotConfig257

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock.Walk
open Nock.NockVMROM.Thm54.RowLayout
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen

theorem exec_honestVer (z α : K) :
    ∀ row ∈ (exec z α).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  intro row hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (show row ∈
      (bfsForest (memoryForest z α)).map NTree.label from hr)
  unfold memoryForest at ht
  rw [bfsForest_mapNTree, List.mem_map] at ht
  obtain ⟨g, hg, rfl⟩ := ht
  simpa [mapNTree_label] using
    bindMemoryRowA_honest_ver z (assigned_bfs_bindMemoryRow_air z α g hg)

theorem exec_pairedRecordLayout (z α : K) :
    PairedRecordLayout (exec z α) :=
  pairedRecordLayout_of_genMemForestFromTree (F := F) (exec z α)
    (encC z) z α (bfsAssign (dotTreeAir (K := K))) rfl (exec_honestVer z α)

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedNounWalk_treeAdded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedRecordTree_lists
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedChainedTree_lists
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_added_eq_consumed
#print axioms Nock.NockVMROM.Thm54.TraceGen.consumedGen_threadGenForest
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_pairedRecordLayout
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBuildableOfProgram_pairedRecordLayout
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.exec_pairedRecordLayout
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.exec_pairedRecordLayout
