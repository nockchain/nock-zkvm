/-
  Nock/NockVMROM/Thm54/TraceGen/GenMemAtomFill.lean

  Every `halt` row the honest memory generator emits is an atom of
  the noun it represents: its `pt.noun` is `E (.atom a)` for the atom `a` (`op9HaltPub`).  At the
  generator's encoder `encC z` (and the carrier's `enc z`) the leaf is `(a : K)`, the image of the base-field value `(a : F)`; the pre-seed `atom` column's
  honest value is that `(a : F)` (`honestAtomOf_op9HaltPub`), it is `z`- and `λ`-free, and the
  row encode (`encPub` / `MemoryRowTemplate.encodeRow`) leaves `st` and `pt` untouched
  (`encPub_st`, `encPub_pt`).  So the honest `halt` rows satisfy the `halt`-row atom gate
  (`honest_halt_gate`, the `Batch579.honest_atom_fill` shape).  `TraceGen/Gen.lean` is unedited;
  the invariant `AllH` mirrors `AllC` (`GenMem.lean`) builder by builder.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMem
import Nock.NockVMROM.Thm54.TraceGen.Encode
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

section AtomFill

variable {K : Type} [Field K]

mutual
/-- Every `halt` node of a generated tree is an atom of `E`: `pt.noun = E (.atom a)`. -/
def AllH (E : Noun → ComputeTable.FP K) : NTree (GenMemoryRow K) → Prop
  | .node g cs =>
      (g.row.2.2.st = MemoryTable.MState.halt → ∃ a : ℕ, g.row.2.2.pt.noun = E (.atom a)) ∧
        AllHL E cs

def AllHL (E : Noun → ComputeTable.FP K) : List (NTree (GenMemoryRow K)) → Prop
  | [] => True
  | c :: cs => AllH E c ∧ AllHL E cs
end

theorem allHL_of_forall {E : Noun → ComputeTable.FP K} {cs : List (NTree (GenMemoryRow K))}
    (h : ∀ c ∈ cs, AllH E c) : AllHL E cs := by
  induction cs with
  | nil => trivial
  | cons a cs ih =>
      exact ⟨h a (by simp), ih (fun c hc => h c (List.mem_cons_of_mem _ hc))⟩

theorem allH_halt {E : Noun → ComputeTable.FP K} {t : NTree (GenMemoryRow K)} (h : AllH E t) :
    t.label.row.2.2.st = MemoryTable.MState.halt → ∃ a : ℕ, t.label.row.2.2.pt.noun = E (.atom a) := by
  cases t with
  | node g cs => simpa [AllH, NTree.label] using h.1

theorem allHL_mem {E : Noun → ComputeTable.FP K} : ∀ {cs : List (NTree (GenMemoryRow K))} {c},
    AllHL E cs → c ∈ cs → AllH E c
  | [], _, _, h => by simp at h
  | _ :: _, _, h, hc => by
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact h.1
      · exact allHL_mem h.2 hc

theorem allH_child {E : Noun → ComputeTable.FP K} {t c : NTree (GenMemoryRow K)} (h : AllH E t)
    (hc : c ∈ t.children) : AllH E c := by
  cases t with
  | node g cs =>
      exact allHL_mem (by simpa [AllH] using h.2) hc

theorem genAnnotatedNounWalk_allH (E : Noun → ComputeTable.FP K) (z lmb : K) :
    ∀ n, AllH E (genAnnotatedNounWalk E z lmb n).1
  | .atom _ => by
      unfold genAnnotatedNounWalk
      refine ⟨?_, ?_⟩
      · intro _
        exact ⟨_, rfl⟩
      · exact trivial
  | .cell h t => by
      unfold genAnnotatedNounWalk
      refine ⟨?_, allHL_of_forall ?_⟩
      · simp [gMemRow9, annotatedDecPub]
      · intro c hc
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · exact genAnnotatedNounWalk_allH E z lmb h
        · exact genAnnotatedNounWalk_allH E z lmb t

theorem genAnnotatedVerify_allH (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    AllH E (genAnnotatedVerify E z lmb root child ax ts recordExp).1 := by
  unfold genAnnotatedVerify
  refine ⟨?_, allHL_of_forall ?_⟩
  · simp [gMemRow9, annotatedVerifyPub]
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    subst hc
    exact genAnnotatedNounWalk_allH E z lmb child

theorem genAnnotatedDescent_allH (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    ∀ t ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
      currentNoun remainingAxis).1, AllH E t := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact genAnnotatedVerify_allH E z lmb root child recAxis ts recordExp
    · split
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine ⟨?_, allHL_of_forall ?_⟩
        · simp [gMemRow9, annotatedDecPub]
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | hc
          · exact genAnnotatedNounWalk_allH E z lmb (formulaHead currentNoun)
          · exact ih (axisRest n) (axisRest_lt (by omega))
              (formulaTail currentNoun) c hc
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine ⟨?_, allHL_of_forall ?_⟩
        · simp [gMemRow9, annotatedDecPub]
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with hc | rfl
          · exact ih (axisRest n) (axisRest_lt (by omega))
              (formulaHead currentNoun) c hc
          · exact genAnnotatedNounWalk_allH E z lmb (formulaTail currentNoun)

theorem genAnnotatedRecordTree_allH (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    AllH E (genAnnotatedRecordTree E z α lmb root child axis recordExp) := by
  unfold genAnnotatedRecordTree
  refine ⟨?_, allHL_of_forall ?_⟩
  · simp [gMemRow9, annotatedReadPub]
  · intro c hc
    exact genAnnotatedDescent_allH E z lmb root child axis (α ^ recordExp) recordExp
      root axis c hc

theorem genAnnotatedDescentCont_allH (E : Noun → ComputeTable.FP K) (z lmb : K)
    (cont : List (NTree (GenMemoryRow K)))
    (contCell : MemoryTable.Cell K) (contState : MemoryTable.MState)
    (currentNoun : Noun) (remainingAxis : ℕ)
    (hcont : ∀ t ∈ cont, AllH E t) :
    ∀ t ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
      currentNoun remainingAxis).1, AllH E t := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · exact hcont
    · split
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine ⟨?_, allHL_of_forall ?_⟩
        · simp [gMemRow9, annotatedDecPub]
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | hc
          · exact genAnnotatedNounWalk_allH E z lmb (formulaHead currentNoun)
          · exact ih (axisRest n) (axisRest_lt (by omega))
              (formulaTail currentNoun) c hc
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine ⟨?_, allHL_of_forall ?_⟩
        · simp [gMemRow9, annotatedDecPub]
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with hc | rfl
          · exact ih (axisRest n) (axisRest_lt (by omega))
              (formulaHead currentNoun) c hc
          · exact genAnnotatedNounWalk_allH E z lmb (formulaTail currentNoun)

theorem genAnnotatedChainedInner_allH (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (prev : MemRecordReq) :
    ∀ reqs, ∀ t ∈ (genAnnotatedChainedInner E z α lmb prev reqs).1, AllH E t
  | [] => by
      intro t ht
      simp only [genAnnotatedChainedInner, List.mem_singleton] at ht
      subst ht
      exact genAnnotatedVerify_allH E z lmb prev.root prev.child prev.axis
        (α ^ prev.recordExp) prev.recordExp
  | r :: more => by
      intro t ht
      simp only [genAnnotatedChainedInner, List.mem_singleton] at ht
      subst ht
      refine ⟨?_, allHL_of_forall ?_⟩
      · simp [gMemRow9, annotatedReadPub]
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        refine ⟨?_, allHL_of_forall ?_⟩
        · simp [gMemRow9, annotatedVerifyPub]
        · intro d hd
          exact genAnnotatedDescentCont_allH E z lmb
            (genAnnotatedChainedInner E z α lmb r more).1
            (genAnnotatedChainedInner E z α lmb r more).2
            (chainedInnerRootState more) r.root r.axis
            (genAnnotatedChainedInner_allH E z α lmb r more) d hd

theorem genAnnotatedChainedTree_allH (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) (t : NTree (GenMemoryRow K))
    (h : genAnnotatedChainedTree E z α lmb reqs = some t) : AllH E t := by
  match reqs with
  | [] => simp [genAnnotatedChainedTree] at h
  | [r] =>
      simp only [genAnnotatedChainedTree] at h
      injection h with ht
      rw [← ht]
      exact genAnnotatedRecordTree_allH E z α lmb r.root r.child r.axis r.recordExp
  | r :: r2 :: rest =>
      simp only [genAnnotatedChainedTree] at h
      injection h with ht
      subst ht
      refine ⟨?_, allHL_of_forall ?_⟩
      · simp [gMemRow9, annotatedReadPub]
      · intro c hc
        exact genAnnotatedDescentCont_allH E z lmb
          (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
          (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
          (chainedInnerRootState (r2 :: rest)) r.root r.axis
          (genAnnotatedChainedInner_allH E z α lmb r (r2 :: rest)) c hc

theorem genRowMemForest_allH (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) :
    ∀ t ∈ genRowMemForest E z α lmb reqs, AllH E t := by
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] =>
      intro t ht
      simp only [genRowMemForest, List.mem_singleton] at ht
      subst ht
      exact genAnnotatedRecordTree_allH E z α lmb r.root r.child r.axis r.recordExp
  | [r1, r2] =>
      intro t ht
      simp only [genRowMemForest] at ht
      by_cases hch : r1.child = r2.root
      · rw [if_pos hch] at ht
        generalize hchain : genAnnotatedChainedTree E z α lmb [r1, r2] = o
        cases o
        · rw [hchain] at ht
          simp [List.mem_cons, List.mem_singleton, or_false] at ht
          rcases ht with h | h
          · exact h ▸ genAnnotatedRecordTree_allH E z α lmb r1.root r1.child r1.axis r1.recordExp
          · exact h ▸ genAnnotatedRecordTree_allH E z α lmb r2.root r2.child r2.axis r2.recordExp
        · rename_i t'
          rw [hchain] at ht
          simp [List.mem_singleton] at ht
          exact ht ▸ genAnnotatedChainedTree_allH E z α lmb [r1, r2] t' hchain
      · rw [if_neg hch] at ht
        simp [List.mem_cons, List.mem_singleton, or_false] at ht
        rcases ht with h | h
        · exact h ▸ genAnnotatedRecordTree_allH E z α lmb r1.root r1.child r1.axis r1.recordExp
        · exact h ▸ genAnnotatedRecordTree_allH E z α lmb r2.root r2.child r2.axis r2.recordExp
  | [r1, r2, r3] =>
      intro t ht
      have hpair :
          genRowMemForest E z α lmb [r1, r2, r3] =
            genRowMemForest E z α lmb [r1, r2] ++
              [genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp] := by
        simp [genRowMemForest]
      rw [hpair] at ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact genRowMemForest_allH E z α lmb [r1, r2] t ht
      · exact genAnnotatedRecordTree_allH E z α lmb r3.root r3.child r3.axis r3.recordExp
  | r1 :: r2 :: r3 :: r4 :: rest =>
      intro t ht
      simp only [genRowMemForest, List.mem_map] at ht
      obtain ⟨r, _, rfl⟩ := ht
      exact genAnnotatedRecordTree_allH E z α lmb r.root r.child r.axis r.recordExp
termination_by reqs.length

mutual
theorem genMemForestFromTree_allH (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ∀ t, ∀ u ∈ genMemForestFromTree E z α lmb t, AllH E u
  | .node g cs => by
      intro u hu
      simp only [genMemForestFromTree, List.mem_append] at hu
      rcases hu with hu | hu
      · exact genRowMemForest_allH E z α lmb _ u hu
      · exact genMemForestFromList_allH E z α lmb cs u hu

theorem genMemForestFromList_allH (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ∀ ts, ∀ u ∈ genMemForestFromList E z α lmb ts, AllH E u
  | [] => by simp [genMemForestFromList]
  | t :: ts => by
      intro u hu
      simp only [genMemForestFromList, List.mem_append] at hu
      rcases hu with hu | hu
      · exact genMemForestFromTree_allH E z α lmb t u hu
      · exact genMemForestFromList_allH E z α lmb ts u hu
end


theorem forest_bfs_halt (E : Noun → ComputeTable.FP K) :
    ∀ (l : List (NTree (GenMemoryRow K))),
      (∀ t ∈ l, AllH E t) →
      ∀ n ∈ bfsForest l, n.label.row.2.2.st = MemoryTable.MState.halt →
        ∃ a : ℕ, n.label.row.2.2.pt.noun = E (.atom a)
  | [], _, n, hn => by simp [bfsForest_nil] at hn
  | t :: rest, h, n, hn => by
      rw [bfsForest_cons_eq (t :: rest) (by simp)] at hn
      simp only [List.mem_append] at hn
      rcases hn with hn | hn
      · simp only [List.mem_cons] at hn
        rcases hn with hnt | hn
        · subst hnt
          exact allH_halt (h _ (List.mem_cons_self ..))
        · exact allH_halt (h n (List.mem_cons_of_mem _ hn))
      · have hall : ∀ c ∈ (t :: rest).flatMap NTree.children, AllH E c := by
          intro c hc
          simp only [List.mem_flatMap] at hc
          obtain ⟨s, hs, hc⟩ := hc
          exact allH_child (h s hs) hc
        exact forest_bfs_halt E ((t :: rest).flatMap NTree.children) hall n hn
termination_by l => totalSize l
decreasing_by
  have hsz := totalSize_flatMap_children (t :: rest)
  simp only [List.length_cons] at hsz
  omega

/-- Every `halt` row of the honest generated forest (BFS order), at every encoder, is an atom. -/
theorem genMemForestFromTree_bfs_halt (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (t : NTree (GenComputeRow K)) :
    ∀ n ∈ bfsForest (genMemForestFromTree E z α lmb t),
      n.label.row.2.2.st = MemoryTable.MState.halt →
        ∃ a : ℕ, n.label.row.2.2.pt.noun = E (.atom a) :=
  forest_bfs_halt E _ (genMemForestFromTree_allH E z α lmb t)

/-! ### The honest atom value -/

/-- The generator's encoder gives an atom leaf `(a : K)`. -/
theorem encC_atom_leaf (z : K) (a : ℕ) : (encC z (.atom a)).leaf = (a : K) := by
  rw [encC_eq, GlobalCarryRecognizer.enc_atom]
  rfl

variable {F : Type} [Field F] [Algebra F K]

/-- The leaf of an honest `halt` row is the image of the base-field atom `(a : F)`. -/
theorem halt_leaf_algebraMap (z : K) (a : ℕ) :
    (encC z (.atom a)).leaf = algebraMap F K (a : F) := by
  rw [encC_atom_leaf, map_natCast]

/-- **Honest pre-seed atom of a generated `halt` row** is `(a : F)`; it reads no `z`, no `λ`. -/
theorem honestAtomOf_op9HaltPub (z : K) (a : ℕ) :
    OptimizedMemoryCanonicalTrace.honestAtomOf (F := F) (op9HaltPub (encC z) a) = (a : F) := by
  have hex : (op9HaltPub (encC z) a).st = .halt ∧
      ∃ b : F, algebraMap F K b = (op9HaltPub (encC z) a).pt.noun.leaf :=
    ⟨rfl, ⟨(a : F), (halt_leaf_algebraMap (F := F) z a).symm⟩⟩
  apply (algebraMap F K).injective
  rw [OptimizedMemoryCanonicalTrace.honestAtomOf_spec (F := F) _ hex]
  exact halt_leaf_algebraMap (F := F) z a

/-- **Completeness at the gate** (`Batch579.honest_atom_fill` shape): on a generated `halt` row,
the leaf is the lifted honest atom, so `sel_halt · (leaf − algebraMap atom) = 0`. -/
theorem honest_halt_gate (z : K) (a : ℕ) :
    (op9HaltPub (encC z) a).pt.noun.leaf =
      algebraMap F K (OptimizedMemoryCanonicalTrace.honestAtomOf (F := F)
        (op9HaltPub (encC z) a)) := by
  rw [honestAtomOf_op9HaltPub]
  exact halt_leaf_algebraMap (F := F) z a

/-- The row encode leaves state and parent cell untouched, so the executed `halt` row keeps the
honest atom leaf. -/
theorem encPub_halt_leaf (lmb : K) (p : MemoryTable.Pub K) :
    (encPub lmb p).st = p.st ∧ (encPub lmb p).pt.noun.leaf = p.pt.noun.leaf := by
  simp

/-- Generated forest rows at `encC z`: every `halt` row's leaf is in the image of `𝔽` —
the `HaltLeavesBase` side condition of canonical memory completeness, row by row. -/
theorem genMemForestFromTree_halt_leaf_base (z α lmb : K) (t : NTree (GenComputeRow K)) :
    ∀ n ∈ bfsForest (genMemForestFromTree (encC z) z α lmb t),
      n.label.row.2.2.st = MemoryTable.MState.halt →
        ∃ b : F, algebraMap F K b = (encPub lmb n.label.row.2.2).pt.noun.leaf := by
  intro n hn hst
  obtain ⟨a, ha⟩ := genMemForestFromTree_bfs_halt (encC z) z α lmb t n hn hst
  exact ⟨(a : F), by rw [(encPub_halt_leaf lmb _).2, ha, halt_leaf_algebraMap (F := F)]⟩

end AtomFill

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_bfs_halt
#print axioms Nock.NockVMROM.Thm54.TraceGen.honestAtomOf_op9HaltPub
#print axioms Nock.NockVMROM.Thm54.TraceGen.honest_halt_gate
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_halt_leaf_base
