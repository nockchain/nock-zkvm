/-
  Nock/NockVMROM/Thm54/TraceGen/GenRequestTargets.lean

  * §A — a generic ordering lemma on any compute timestamp skeleton: the request list
    `PreSeedCensus.requestList S` read at `lnPrevExponent + k` is the `k`-th memory record of the
    row (`requestList_getElem_slot`).  So `requestTargets S st (e)` at the exponent
    `e = lnPrevExponent + k + 1` is the root (`read_root`) / child (`verify_child`) of that record.
  * §B — the generator's per-node statement: every live (`read_root` / `verify_child`) node of
    `genMemForestFromTree` carries `requestTargets S st (stamp.recordExponent) = skel.parent`
    (`genMemForestFromTree_requestTargets`), for the BFS-assigned compute tree.
  * §C — threading and the `genMemoryForest` form (`genMemoryForest_requestTargets`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedSemanticCoverage
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.PreZCensusCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.PreSeedCensus

/-! ## §A  The request list read by exponent -/

section Ordering

theorem chain_getElem :
    ∀ (l : List ComputeTimestampRow), ComputeLineExponentChain l →
      ∀ (j : ℕ) (hj : j + 1 < l.length),
        (l[j]'(by omega)).lnExponent = (l[j + 1]'hj).lnPrevExponent
  | [], _, j, hj => by simp at hj
  | [_], _, j, hj => by simp at hj
  | a :: b :: rest, hc, 0, _ => by simpa using hc.1
  | a :: b :: rest, hc, j + 1, hj => by
      have := chain_getElem (b :: rest) hc.2 j (by simpa using hj)
      simpa using this

/-- Generic filterMap over `Fin 3` with a downward-closed guard `i < c`. -/
theorem finRange3_filterMap {α : Type*} (c : ℕ) (hc : c ≤ 3)
    (g : ∀ i : Fin 3, (i : ℕ) < c → α) :
    ((List.finRange 3).filterMap fun (i : Fin 3) =>
      if h : (i : ℕ) < c then some (g i h) else none).length = c ∧
    ∀ (k : ℕ) (hk : k < c),
      ((List.finRange 3).filterMap fun (i : Fin 3) =>
        if h : (i : ℕ) < c then some (g i h) else none)[k]? =
          some (g ⟨k, by omega⟩ hk) := by
  interval_cases c
  · refine ⟨by simp, fun k hk => by omega⟩
  · refine ⟨by simp [List.finRange], fun k hk => ?_⟩
    obtain rfl : k = 0 := by omega
    simp [List.finRange]
  · refine ⟨by simp [List.finRange], fun k hk => ?_⟩
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · simp [List.finRange]
    · simp [List.finRange]
  · refine ⟨by simp [List.finRange], fun k hk => ?_⟩
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    · simp [List.finRange]
    · simp [List.finRange]
    · simp [List.finRange]

/-- The request slots of one row, in slot order. -/
def rowRecords (r : ComputeRowSkeleton) : List MemRecSkeleton :=
  (List.finRange 3).filterMap fun (i : Fin 3) =>
    if h : (i : ℕ) < Nock.Framework.recordCount r.state then some (r.memoryRecord i h) else none

theorem rowRecords_length (r : ComputeRowSkeleton) :
    (rowRecords r).length = Nock.Framework.recordCount r.state :=
  (finRange3_filterMap _ (Nock.Framework.recordCount_le r.state)
    (fun i h => r.memoryRecord i h)).1

theorem rowRecords_getElem (r : ComputeRowSkeleton) (k : ℕ)
    (hk : k < Nock.Framework.recordCount r.state) :
    (rowRecords r)[k]? = some (r.memoryRecord ⟨k, lt_of_lt_of_le hk
      (Nock.Framework.recordCount_le r.state)⟩ hk) :=
  (finRange3_filterMap _ (Nock.Framework.recordCount_le r.state)
    (fun i h => r.memoryRecord i h)).2 k hk

theorem requestList_eq (S : SemanticSkeleton) :
    requestList S = (computeSkeletonRows S).flatMap rowRecords := rfl

/-- The records of the first `j` rows number exactly the line exponent handed to row `j`. -/
theorem prefix_records_length (rows : List ComputeRowSkeleton) (stamps : List ComputeTimestampRow)
    (htop : List.Forall₂ (fun row stamp => stamp.state = row.state) rows stamps)
    (h0 : ComputeLineStartsAtZero stamps) (hch : ComputeLineExponentChain stamps)
    (hadv : ∀ s ∈ stamps, s.lnExponent = s.lnPrevExponent + Nock.Framework.recordCount s.state) :
    ∀ (j : ℕ) (hj : j < rows.length),
      ((rows.take j).flatMap rowRecords).length =
        (stamps[j]'(by rw [← htop.length_eq]; exact hj)).lnPrevExponent := by
  have hlen := htop.length_eq
  have hpt := (List.forall₂_iff_get.mp htop).2
  intro j
  induction j with
  | zero =>
    intro hj
    obtain ⟨s, rest, hs⟩ : ∃ s rest, stamps = s :: rest := by
      cases stamps with
      | nil =>
        exfalso
        have : rows.length = 0 := by simpa using hlen
        omega
      | cons s rest => exact ⟨s, rest, rfl⟩
    subst hs
    simpa using h0.symm
  | succ j ih =>
    intro hj
    have hj' : j < rows.length := by omega
    have hjs : j < stamps.length := by omega
    have hstate : (stamps[j]'hjs).state = (rows[j]'hj').state := hpt j hj' hjs
    have hc := chain_getElem stamps hch j (by omega)
    have hadvj := hadv _ (List.getElem_mem hjs)
    rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.flatMap_append,
      List.length_append, ih hj', List.flatMap_singleton, rowRecords_length]
    rw [← hc, hadvj, hstate]

/-- **The request list read by exponent.**  Row `j`'s `k`-th memory record sits at index
`lnPrevExponent_j + k` of `requestList S`: compute-BFS order, slot order, `0`-based; so the
`1`-based exponent of the slot is `lnPrevExponent_j + k + 1`. -/
theorem requestList_getElem_slot (S : SemanticSkeleton) (stamps : List ComputeTimestampRow)
    (htop : List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows S) stamps)
    (h0 : ComputeLineStartsAtZero stamps) (hch : ComputeLineExponentChain stamps)
    (hadv : ∀ s ∈ stamps, s.lnExponent = s.lnPrevExponent + Nock.Framework.recordCount s.state)
    (j : ℕ) (hj : j < (computeSkeletonRows S).length) (k : ℕ)
    (hk : k < Nock.Framework.recordCount ((computeSkeletonRows S)[j]'hj).state) :
    (requestList S)[(stamps[j]'(by rw [← htop.length_eq]; exact hj)).lnPrevExponent + k]? =
      some (((computeSkeletonRows S)[j]'hj).memoryRecord ⟨k, lt_of_lt_of_le hk
        (Nock.Framework.recordCount_le _)⟩ hk) := by
  rw [requestList_eq, ← prefix_records_length _ stamps htop h0 hch hadv j hj]
  generalize hrows : computeSkeletonRows S = rows at hj hk ⊢
  have hsplit : rows.flatMap rowRecords =
      (rows.take j).flatMap rowRecords ++ (rowRecords rows[j] ++ (rows.drop (j + 1)).flatMap rowRecords) := by
    conv_lhs => rw [← List.take_append_drop j rows]
    rw [List.flatMap_append, List.drop_eq_getElem_cons hj, List.flatMap_cons]
  rw [hsplit, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [rowRecords_length]; exact hk)]
  exact rowRecords_getElem _ k hk

end Ordering

/-! ## §B  Every live node of the generated forest carries its request's target -/

section Forest

variable {K : Type} [Field K]

/-- `P` holds at every node of the tree. -/
def AllTree (P : GenMemoryRow K → Prop) (t : NTree (GenMemoryRow K)) : Prop :=
  ∀ n, InTree t n → P n.label

theorem allTree_node {P : GenMemoryRow K → Prop} {g : GenMemoryRow K}
    {cs : List (NTree (GenMemoryRow K))} (hg : P g) (hcs : ∀ c ∈ cs, AllTree P c) :
    AllTree P (.node g cs) := by
  intro n hn
  cases hn with
  | here => exact hg
  | sub hs h => exact hcs _ hs n h

/-- The live-node target statement: a `read_root` / `verify_child` node's exponent indexes the
request whose root / child is the node's parent noun. -/
def Tgt (T : MemoryTable.MState → ℕ → Noun) (g : GenMemoryRow K) : Prop :=
  (g.skel.state = .read_root ∨ g.skel.state = .verify_child) →
    T g.skel.state g.stamp.recordExponent = g.skel.parent

/-- The request's two nouns sit at its exponent in `T`. -/
def GoodReq (T : MemoryTable.MState → ℕ → Noun) (r : MemRecordReq) : Prop :=
  T .read_root r.recordExp = r.root ∧ T .verify_child r.recordExp = r.child

variable (T : MemoryTable.MState → ℕ → Noun)

theorem tgt_decompose (formula head result : Noun) (e : ℕ) (z : K) (pub : MemoryTable.Pub K) :
    Tgt T (gMemRow9 (memDecomposeSkel formula head result) e z pub) := by
  intro h
  simp [gMemRow9, memDecomposeSkel] at h

theorem tgt_halt (a : ℕ) (e : ℕ) (z : K) (pub : MemoryTable.Pub K) :
    Tgt T (gMemRow9 (memHaltSkel a) e z pub) := by
  intro h
  simp [gMemRow9, memHaltSkel] at h

theorem tgt_read (root child : Noun) (ax e : ℕ) (z : K) (pub : MemoryTable.Pub K)
    (h : T .read_root e = root) : Tgt T (gMemRow9 (memReadSkelAx root child ax) e z pub) := by
  intro _
  exact h

theorem tgt_verify (root child : Noun) (ax e : ℕ) (z : K) (pub : MemoryTable.Pub K)
    (h : T .verify_child e = child) :
    Tgt T (gMemRow9 (memVerifySkelAx root child ax) e z pub) := by
  intro _
  exact h

theorem nounWalk_allTree (E : Noun → ComputeTable.FP K) (z lmb : K) :
    ∀ n, AllTree (Tgt T) (genAnnotatedNounWalk E z lmb n).1
  | .atom a => by
      unfold genAnnotatedNounWalk
      exact allTree_node (tgt_halt T _ _ _ _) (by simp)
  | .cell h t => by
      unfold genAnnotatedNounWalk
      refine allTree_node (tgt_decompose T _ _ _ _ _ _) ?_
      intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact nounWalk_allTree E z lmb h
      · exact nounWalk_allTree E z lmb t

theorem verify_allTree (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    (hv : T .verify_child recordExp = child) :
    AllTree (Tgt T) (genAnnotatedVerify E z lmb root child ax ts recordExp).1 := by
  unfold genAnnotatedVerify
  refine allTree_node (tgt_verify T _ _ _ _ _ _ hv) ?_
  intro c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  subst hc
  exact nounWalk_allTree T E z lmb child

theorem descent_allTree (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (hv : T .verify_child recordExp = child)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    ∀ t ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
      currentNoun remainingAxis).1, AllTree (Tgt T) t := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact verify_allTree T E z lmb root child recAxis ts recordExp hv
    · split
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine allTree_node (tgt_decompose T _ _ _ _ _ _) ?_
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | hc
        · exact nounWalk_allTree T E z lmb (formulaHead currentNoun)
        · exact ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun) c hc
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine allTree_node (tgt_decompose T _ _ _ _ _ _) ?_
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with hc | rfl
        · exact ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun) c hc
        · exact nounWalk_allTree T E z lmb (formulaTail currentNoun)

theorem recordTree_allTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ)
    (hg : T .read_root recordExp = root ∧ T .verify_child recordExp = child) :
    AllTree (Tgt T) (genAnnotatedRecordTree E z α lmb root child axis recordExp) := by
  unfold genAnnotatedRecordTree
  refine allTree_node (tgt_read T _ _ _ _ _ _ hg.1) ?_
  intro c hc
  exact descent_allTree T E z lmb root child axis (α ^ recordExp) recordExp hg.2 root axis c hc

theorem descentCont_allTree (E : Noun → ComputeTable.FP K) (z lmb : K)
    (cont : List (NTree (GenMemoryRow K)))
    (contCell : MemoryTable.Cell K) (contState : MemoryTable.MState)
    (currentNoun : Noun) (remainingAxis : ℕ)
    (hcont : ∀ t ∈ cont, AllTree (Tgt T) t) :
    ∀ t ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
      currentNoun remainingAxis).1, AllTree (Tgt T) t := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · exact hcont
    · split
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine allTree_node (tgt_decompose T _ _ _ _ _ _) ?_
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | hc
        · exact nounWalk_allTree T E z lmb (formulaHead currentNoun)
        · exact ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun) c hc
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine allTree_node (tgt_decompose T _ _ _ _ _ _) ?_
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with hc | rfl
        · exact ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun) c hc
        · exact nounWalk_allTree T E z lmb (formulaTail currentNoun)

theorem chainedInner_allTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (prev : MemRecordReq) (hprev : GoodReq T prev) :
    ∀ reqs : List MemRecordReq, (∀ r ∈ reqs, GoodReq T r) →
      ∀ t ∈ (genAnnotatedChainedInner E z α lmb prev reqs).1, AllTree (Tgt T) t
  | [], _ => by
      intro t ht
      simp only [genAnnotatedChainedInner, List.mem_singleton] at ht
      subst ht
      exact verify_allTree T E z lmb prev.root prev.child prev.axis (α ^ prev.recordExp)
        prev.recordExp hprev.2
  | r :: more, hall => by
      intro t ht
      simp only [genAnnotatedChainedInner, List.mem_singleton] at ht
      subst ht
      have hr : GoodReq T r := hall r List.mem_cons_self
      refine allTree_node (tgt_read T _ _ _ _ _ _ hr.1) ?_
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      refine allTree_node (tgt_verify T _ _ _ _ _ _ hprev.2) ?_
      intro d hd
      exact descentCont_allTree T E z lmb
        (genAnnotatedChainedInner E z α lmb r more).1
        (genAnnotatedChainedInner E z α lmb r more).2
        (chainedInnerRootState more) r.root r.axis
        (chainedInner_allTree E z α lmb r hr more
          (fun x hx => hall x (List.mem_cons_of_mem _ hx))) d hd

theorem chainedTree_allTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) (hall : ∀ r ∈ reqs, GoodReq T r)
    (t : NTree (GenMemoryRow K))
    (h : genAnnotatedChainedTree E z α lmb reqs = some t) : AllTree (Tgt T) t := by
  match reqs with
  | [] => simp [genAnnotatedChainedTree] at h
  | [r] =>
      simp only [genAnnotatedChainedTree] at h
      injection h with ht
      rw [← ht]
      exact recordTree_allTree T E z α lmb r.root r.child r.axis r.recordExp
        (hall r List.mem_cons_self)
  | r :: r2 :: rest =>
      simp only [genAnnotatedChainedTree] at h
      injection h with ht
      subst ht
      refine allTree_node (tgt_read T _ _ _ _ _ _ (hall r List.mem_cons_self).1) ?_
      intro c hc
      exact descentCont_allTree T E z lmb
        (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
        (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
        (chainedInnerRootState (r2 :: rest)) r.root r.axis
        (chainedInner_allTree T E z α lmb r (hall r List.mem_cons_self) (r2 :: rest)
          (fun x hx => hall x (List.mem_cons_of_mem _ hx))) c hc

theorem rowMemForest_allTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) (hall : ∀ r ∈ reqs, GoodReq T r) :
    ∀ t ∈ genRowMemForest E z α lmb reqs, AllTree (Tgt T) t := by
  have hrec : ∀ r ∈ reqs, AllTree (Tgt T)
      (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) :=
    fun r hr => recordTree_allTree T E z α lmb r.root r.child r.axis r.recordExp (hall r hr)
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] =>
      intro t ht
      simp only [genRowMemForest, List.mem_singleton] at ht
      subst ht
      exact hrec r List.mem_cons_self
  | [r1, r2] =>
      intro t ht
      simp only [genRowMemForest] at ht
      have h1 := hrec r1 (by simp)
      have h2 := hrec r2 (by simp)
      by_cases hch : r1.child = r2.root
      · rw [if_pos hch] at ht
        generalize hchain : genAnnotatedChainedTree E z α lmb [r1, r2] = o
        cases o
        · rw [hchain] at ht
          simp [List.mem_cons, or_false] at ht
          rcases ht with h | h
          · exact h ▸ h1
          · exact h ▸ h2
        · rename_i t'
          rw [hchain] at ht
          simp at ht
          exact ht ▸ chainedTree_allTree T E z α lmb [r1, r2] hall t' hchain
      · rw [if_neg hch] at ht
        simp [List.mem_cons, or_false] at ht
        rcases ht with h | h
        · exact h ▸ h1
        · exact h ▸ h2
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
      · exact rowMemForest_allTree E z α lmb [r1, r2]
          (fun r hr => hall r (by simp at hr ⊢; tauto)) t ht
      · exact hrec r3 (by simp)
  | r1 :: r2 :: r3 :: r4 :: rest =>
      intro t ht
      simp only [genRowMemForest, List.mem_map] at ht
      obtain ⟨r, hr, rfl⟩ := ht
      exact hrec r hr
termination_by reqs.length

mutual
theorem memForestFromTree_allTree (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ∀ t : NTree (GenComputeRow K),
      (∀ n, InTree t n → ∀ r ∈ extractNodeReqs n.label, GoodReq T r) →
      ∀ u ∈ genMemForestFromTree E z α lmb t, AllTree (Tgt T) u
  | .node g cs => by
      intro hT u hu
      simp only [genMemForestFromTree, List.mem_append] at hu
      rcases hu with hu | hu
      · exact rowMemForest_allTree T E z α lmb _ (hT _ (InTree.here _)) u hu
      · exact memForestFromList_allTree E z α lmb cs
          (fun c hc n hn => hT n (InTree.sub hc hn)) u hu

theorem memForestFromList_allTree (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ∀ ts : List (NTree (GenComputeRow K)),
      (∀ c ∈ ts, ∀ n, InTree c n → ∀ r ∈ extractNodeReqs n.label, GoodReq T r) →
      ∀ u ∈ genMemForestFromList E z α lmb ts, AllTree (Tgt T) u
  | [] => by simp [genMemForestFromList]
  | t :: ts => by
      intro hT u hu
      simp only [genMemForestFromList, List.mem_append] at hu
      rcases hu with hu | hu
      · exact memForestFromTree_allTree E z α lmb t (hT t List.mem_cons_self) u hu
      · exact memForestFromList_allTree E z α lmb ts
          (fun c hc => hT c (List.mem_cons_of_mem _ hc)) u hu
end

end Forest

/-! ## §C  The compute side: every extracted request is at its exponent in `requestTargets` -/

section ComputeSide

variable {K : Type} [Field K]

/-- `requestTargets` reads only the compute skeleton rows. -/
theorem requestTargets_congr {S S' : SemanticSkeleton}
    (h : computeSkeletonRows S = computeSkeletonRows S') : requestTargets S = requestTargets S' := by
  have : requestList S = requestList S' := by rw [requestList_eq, requestList_eq, h]
  funext st k
  cases k with
  | zero => cases st <;> rfl
  | succ k => cases st <;> simp [requestTargets, this]

/-- **The extracted requests of the BFS-assigned tree are at their exponents.**  For every node
`n` of `bfsAssign t0` and every request `r` of `extractNodeReqs n.label`, the skeleton's
`requestTargets` at `r.recordExp` is `r`'s root (`read_root`) and child (`verify_child`):
`requestTargets` is ordered compute-BFS x slot, `1`-indexed, exactly as the generator stamps. -/
theorem goodReq_extractNodeReqs (t0 : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t0)) {n : NTree (GenComputeRow K)}
    (hn : InTree (bfsAssign t0) n) :
    ∀ r ∈ extractNodeReqs n.label,
      GoodReq (requestTargets (genComputeSemanticSkeleton (bfsAssign t0))) r := by
  intro r hr
  set S0 := genComputeSemanticSkeleton (bfsAssign t0) with hS0
  have hmat : requestsMatchMemory n.label := hmatch n hn
  have hlen := requestsMatch_length n.label hmat
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
  have hkq : k < n.label.requests.length := by rw [← extractNodeReqs_length]; exact hk
  have hc : k < Nock.Framework.recordCount n.label.skel.state := by rw [← hlen]; exact hkq
  have h3 : k < 3 := lt_of_lt_of_le hc (Nock.Framework.recordCount_le _)
  obtain ⟨hk', hreq⟩ := extractNodeReqs_getElem_skel n.label hmat k h3 hc
  -- locate `n` in the BFS list
  have hnb : n ∈ bfsForest [bfsAssign t0] := (mem_bfsForest _ _).mpr ⟨_, List.mem_singleton_self _, hn⟩
  obtain ⟨j, hj, hjn⟩ := List.mem_iff_getElem.mp hnb
  have hrows : computeSkeletonRows S0 = (bfsForest [bfsAssign t0]).map (fun n => n.label.skel) :=
    computeSkeletonRows_genCompute _
  have hjr : j < (computeSkeletonRows S0).length := by rw [hrows]; simpa using hj
  have hstamps : bfsStamps (bfsAssign t0) = (bfsForest [bfsAssign t0]).map (fun n => n.label.stamp) :=
    rfl
  have hjs : j < (bfsStamps (bfsAssign t0)).length := by rw [hstamps]; simpa using hj
  have hrow : (computeSkeletonRows S0)[j]'hjr = n.label.skel := by
    simp only [hrows, List.getElem_map, hjn]
  have hstamp : (bfsStamps (bfsAssign t0))[j]'hjs = n.label.stamp := by
    simp only [hstamps, List.getElem_map, hjn]
  have hkr : k < Nock.Framework.recordCount ((computeSkeletonRows S0)[j]'hjr).state := by
    rw [hrow]; exact hc
  have hslot := requestList_getElem_slot S0 (bfsStamps (bfsAssign t0))
    (bfsAssign_computeTopology t0) (bfsAssign_startsAtZero t0) (bfsAssign_computeLineChain t0)
    (fun s hs => bfsAssign_computeLineAdvance t0 hs) j hjr k hkr
  have hstm : n.label.stamp ∈ bfsStamps (bfsAssign t0) := by
    rw [← hstamp]; exact List.getElem_mem hjs
  have hstate : n.label.stamp.state = n.label.skel.state := by
    have := (List.forall₂_iff_get.mp (bfsAssign_computeTopology t0)).2 j hjr hjs
    simp only [List.get_eq_getElem] at this
    rw [hstamp, hrow] at this
    exact this
  have hexp := bfsAssign_computeRecordOffsets t0 hstm ⟨k, h3⟩ (by rw [hstate]; exact hc)
  -- the extracted request
  have hrk : (extractNodeReqs n.label)[k] =
      { root := (n.label.skel.memoryRecord ⟨k, h3⟩ hc).root,
        child := (n.label.skel.memoryRecord ⟨k, h3⟩ hc).child,
        axis := (n.label.skel.memoryRecord ⟨k, h3⟩ hc).axis,
        recordExp := getRecordExp n.label.stamp k } := hreq
  rw [hrk]
  have hge : getRecordExp n.label.stamp k = n.label.stamp.lnPrevExponent + k + 1 := by
    unfold getRecordExp
    rw [dif_pos h3]
    exact hexp
  have hslot' : (requestList S0)[n.label.stamp.lnPrevExponent + k]? =
      some (n.label.skel.memoryRecord ⟨k, h3⟩ hc) := by
    have := hslot
    simp only [hstamp] at this
    rw [this]
    simp only [hrow]
  refine ⟨?_, ?_⟩
  · show requestTargets S0 .read_root (getRecordExp n.label.stamp k) = _
    rw [hge]
    simp [requestTargets, hslot']
  · show requestTargets S0 .verify_child (getRecordExp n.label.stamp k) = _
    rw [hge]
    simp [requestTargets, hslot']

end ComputeSide

/-! ## §D  The generated forest (unthreaded and threaded) -/

section Generated

variable {K : Type} [Field K]

/-- **N3 on `genMemForestFromTree`.**  Every live node of the generator's own forest over the
BFS-assigned tree carries `requestTargets` at its exponent equal to its parent noun. -/
theorem genMemForestFromTree_requestTargets (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (t0 : NTree (GenComputeRow K)) (hmatch : treeRequestsMatch (bfsAssign t0)) :
    ∀ n ∈ bfsForest (genMemForestFromTree E z α lmb (bfsAssign t0)),
      Tgt (requestTargets (genComputeSemanticSkeleton (bfsAssign t0))) n.label := by
  intro n hn
  obtain ⟨c, hc, hcn⟩ := (mem_bfsForest _ _).mp hn
  exact memForestFromTree_allTree (requestTargets (genComputeSemanticSkeleton (bfsAssign t0)))
    E z α lmb (bfsAssign t0)
    (fun m hm r hr => goodReq_extractNodeReqs t0 hmatch hm r hr) c hc n hcn



/-- Threading changes only the accumulator columns: every threaded row has the skeleton and the
stamp of a generated row. -/
theorem threadGenRows_skel_stamp (inp : MemoryTable.Inputs K) :
    ∀ (acc : K) (gs : List (GenMemoryRow K)), ∀ g' ∈ threadGenRows inp acc gs,
      ∃ g ∈ gs, g'.skel = g.skel ∧ g'.stamp = g.stamp
  | _, [], g', hg => by cases hg
  | acc, q :: qs, g', hg => by
      rw [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨q, List.mem_cons_self, rfl, rfl⟩
      · obtain ⟨g, hg1, h1, h2⟩ := threadGenRows_skel_stamp inp (threadGenRow inp acc q).1 qs g' hg
        exact ⟨g, List.mem_cons_of_mem _ hg1, h1, h2⟩

/-- **N3 on the committed (threaded) memory forest of an accepted program.**  At the generated
carrier's skeleton `S`, every live memory node's exponent indexes, in `requestTargets S`, exactly
the noun the node's skeleton row names as its parent: the root of the request (`read_root`) /
the child of the request (`verify_child`).  The only hypothesis is acceptance. -/
theorem genMemoryForest_requestTargets (z α lmb : K) (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ n ∈ bfsForest (genMemoryForest z α lmb inp t),
      (n.label.skel.state = .read_root ∨ n.label.skel.state = .verify_child) →
        requestTargets
            (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t))
            n.label.skel.state n.label.stamp.recordExponent = n.label.skel.parent := by
  intro n hn hlive
  have hlab : n.label ∈ (bfsForest (genMemoryForest z α lmb inp t)).map NTree.label :=
    List.mem_map.mpr ⟨n, hn, rfl⟩
  unfold genMemoryForest at hlab hn ⊢
  rw [threadGenForest_bfs_labels] at hlab
  obtain ⟨g, hg, hskel, hstamp⟩ := threadGenRows_skel_stamp inp 0 _ _ hlab
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
  have hmatch : treeRequestsMatch (bfsAssign (airReorder t)) :=
    genComputeSkeleton_air_requestsMatch h
  have hT := genMemForestFromTree_requestTargets (encC z) z α lmb (airReorder t) hmatch m hm
  rw [requestTargets_congr (S' := genComputeSemanticSkeleton (bfsAssign (airReorder t)))
    (computeSkeletonRows_genSemantic _ _)]
  rw [hskel] at hlive ⊢
  rw [hstamp]
  exact hT hlive

/-- **The same, row-indexed** (`memorySkeletonRows` / `genMemoryStamps`, the two lists the
generated `SemanticTimestampSkeleton` pairs up).  Composed with
`GenRecordExponentBridge.production_reqIdxNat_eq_recordExponent` (whose right-hand side is
`(genMemoryStamps mf)[i].recordExponent`), this puts `requestTargets` at the committed `reqIdx`. -/
theorem genMemoryForest_requestTargets_row (z α lmb : K) (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (i : ℕ)
    (hi : i < (memorySkeletonRows
      (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t))).length)
    (hi' : i < (genMemoryStamps (genMemoryForest z α lmb inp t)).length)
    (hlive : ((memorySkeletonRows
        (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t)))[i]).state
          = .read_root ∨
      ((memorySkeletonRows
        (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t)))[i]).state
          = .verify_child) :
    requestTargets
        (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t))
        ((memorySkeletonRows
          (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t)))[i]).state
        ((genMemoryStamps (genMemoryForest z α lmb inp t))[i]).recordExponent =
      ((memorySkeletonRows
        (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t)))[i]).parent := by
  have hrows := memorySkeletonRows_genSemantic (bfsAssign (airReorder t))
    (genMemoryForest z α lmb inp t)
  have hlen : i < (bfsForest (genMemoryForest z α lmb inp t)).length := by
    rw [hrows] at hi; simpa using hi
  have hn := List.getElem_mem hlen
  have key := genMemoryForest_requestTargets z α lmb inp h _ hn
  have e1 : ((memorySkeletonRows
        (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t)))[i]) =
      ((bfsForest (genMemoryForest z α lmb inp t))[i]).label.skel := by
    simp only [hrows, List.getElem_map]
  have e2 : ((genMemoryStamps (genMemoryForest z α lmb inp t))[i]) =
      ((bfsForest (genMemoryForest z α lmb inp t))[i]).label.stamp := by
    simp only [genMemoryStamps, List.getElem_map]
  rw [e1] at hlive ⊢
  rw [e2]
  exact key hlive

end Generated

end Nock.NockVMROM.Thm54.TraceGen
