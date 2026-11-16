/-
  Nock/RedTeam/Batch771Thm54BfsRoundTrip.lean

  `StrategyOfTraces.rebuildForest` is the deployed BFS inverse (`unbfs`).  The route-B built
  skeleton reads its compute tree off it (`typedComputeTree`).  Two directions, both generic in the
  label type and the fanout:

  * `rebuildForest_bfs` (tree → rows → tree): a forest whose BFS nodes all have `fanout label`
    children is recovered by `rebuildForest` from its own BFS labels.
  * `bfs_rebuildForest` (rows → tree → rows): rows that tile (`kRoots + Σ fanout = length`) and are
    queued (row `i` is queued by the rows before it) satisfy `(bfsForest (rebuildForest …)).map
    label = rows`.  Through `Walk.reconForest`; the tiling / queue hypotheses are exactly
    `BFSValidF` / the terminal-gate tiling in rows form (`Sf_foRows`).
-/
import Nock.NockVMROM.Thm54.StrategyOfTraces

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch771

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54.StrategyOfTraces

variable {α : Type}

/-! ## §A  `groupChildren` undoes `flatten` -/

theorem groupChildren_flatten (ls : List (List (NTree α))) :
    groupChildren (ls.map List.length) ls.flatten = (ls, []) := by
  induction ls with
  | nil => simp [groupChildren]
  | cons l rest ih =>
      simp only [List.map_cons, List.flatten_cons, groupChildren]
      rw [List.take_left, List.drop_left, ih]

/-! ## §B  tree → rows → tree -/

/-- Every node of the BFS list of `l` has exactly `fo label` children. -/
def FanoutWF (fo : α → ℕ) (l : List (NTree α)) : Prop :=
  ∀ t ∈ bfsForest l, t.children.length = fo t.label

theorem FanoutWF.level {fo : α → ℕ} {l : List (NTree α)} (h : FanoutWF fo l) :
    ∀ t ∈ l, t.children.length = fo t.label := by
  intro t ht
  by_cases hl : l = []
  · subst hl; simp at ht
  · exact h t (by rw [bfsForest_cons_eq l hl]; exact List.mem_append_left _ ht)

theorem FanoutWF.next {fo : α → ℕ} {l : List (NTree α)} (h : FanoutWF fo l) :
    FanoutWF fo (l.flatMap NTree.children) := by
  intro t ht
  by_cases hl : l = []
  · subst hl; simp [bfsForest_nil] at ht
  · exact h t (by rw [bfsForest_cons_eq l hl]; exact List.mem_append_right _ ht)

theorem node_eta (t : NTree α) : NTree.node t.label t.children = t := by
  cases t; rfl

theorem zip_label_children (l : List (NTree α)) :
    ((l.map NTree.label).zip (l.map NTree.children)).map
        (fun p : α × List (NTree α) => NTree.node p.1 p.2) = l := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp only [List.map_cons, List.zip_cons_cons, ih, node_eta]

theorem unbfs_bfs_aux (fo : α → ℕ) :
    ∀ (fuel : ℕ) (l : List (NTree α)), totalSize l ≤ fuel → FanoutWF fo l →
      unbfs fo fuel (l.map NTree.label)
          ((bfsForest (l.flatMap NTree.children)).map NTree.label) = l := by
  intro fuel
  induction fuel with
  | zero =>
      intro l hsz _
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons t rest =>
            exfalso
            have : 1 ≤ t.size := by cases t with | node _ _ => simp [NTree.size]
            rw [totalSize_cons] at hsz; omega
      subst hl; simp [unbfs]
  | succ f ih =>
      intro l hsz hwf
      by_cases hl : l = []
      · subst hl; simp [unbfs]
      · set C := l.flatMap NTree.children with hC
        have hlen : 1 ≤ l.length := List.length_pos_of_ne_nil hl
        have hts := totalSize_flatMap_children l
        rw [← hC] at hts
        have hCsz : totalSize C ≤ f := by omega
        have hlev := hwf.level
        have hCflat : C = (l.map NTree.children).flatten := by
          rw [hC, List.flatMap_def]
        have hmap : (l.map NTree.label).map fo = (l.map NTree.children).map List.length := by
          rw [List.map_map, List.map_map]
          exact List.map_congr_left (fun t ht => (hlev t ht).symm)
        have hnCh : ((l.map NTree.label).map fo).sum = C.length := by
          rw [hmap, hCflat, List.length_flatten]
        have hCbfs : bfsForest C = (if C = [] then [] else C ++ bfsForest (C.flatMap NTree.children)) := by
          by_cases hc : C = []
          · simp [hc, bfsForest_nil]
          · simp [hc, bfsForest_cons_eq C hc]
        have hchildLabels :
            ((bfsForest C).map NTree.label).take (((l.map NTree.label).map fo).sum)
              = C.map NTree.label := by
          rw [hnCh]
          by_cases hc : C = []
          · simp [hc, bfsForest_nil]
          · rw [bfsForest_cons_eq C hc, List.map_append]
            exact List.take_left' (by simp)
        have hrest :
            ((bfsForest C).map NTree.label).drop (((l.map NTree.label).map fo).sum)
              = (bfsForest (C.flatMap NTree.children)).map NTree.label := by
          rw [hnCh]
          by_cases hc : C = []
          · simp [hc, bfsForest_nil]
          · rw [bfsForest_cons_eq C hc, List.map_append]
            exact List.drop_left' (by simp)
        have hgrp : (groupChildren ((l.map NTree.label).map fo) C).1 = l.map NTree.children := by
          rw [hmap, hCflat, groupChildren_flatten]
        show unbfs fo (f + 1) (l.map NTree.label)
            ((bfsForest C).map NTree.label) = l
        have hne : l.map NTree.label ≠ [] := by simpa using hl
        rw [unbfs]
        · simp only [hchildLabels, hrest]
          rw [ih C hCsz hwf.next, hgrp]
          exact zip_label_children l
        · exact hne

theorem rebuildForest_bfs (fo : α → ℕ) (l : List (NTree α)) (hwf : FanoutWF fo l) :
    rebuildForest fo l.length ((bfsForest l).map NTree.label) = l := by
  by_cases hl : l = []
  · subst hl; simp [rebuildForest_zero_roots, bfsForest_nil]
  · have hbfs := bfsForest_cons_eq l hl
    have hlen : (bfsForest l).length = totalSize l := bfsForest_length l
    unfold rebuildForest
    rw [hbfs, List.map_append]
    have h1 : ((l.map NTree.label) ++ (bfsForest (l.flatMap NTree.children)).map NTree.label).take
        l.length = l.map NTree.label :=
      List.take_left' (by simp)
    have h2 : ((l.map NTree.label) ++ (bfsForest (l.flatMap NTree.children)).map NTree.label).drop
        l.length = (bfsForest (l.flatMap NTree.children)).map NTree.label :=
      List.drop_left' (by simp)
    rw [h1, h2]
    have hfuel : totalSize l ≤ ((l.map NTree.label) ++
        (bfsForest (l.flatMap NTree.children)).map NTree.label).length + 1 := by
      rw [← List.map_append, List.length_map, ← hbfs]; omega
    -- monotonicity of `unbfs` in the fuel is not needed: `unbfs_bfs_aux` holds at every fuel ≥ size
    exact unbfs_bfs_aux fo _ l hfuel hwf

/-! ## §C  rows → tree → rows, under the tiling -/

/-- The fanout column of a row list, 1-indexed (`Walk.foCol`'s shape). -/
def foRows (fanout : α → ℕ) (rows : List α) : ℕ → ℕ :=
  fun i => ((rows[i - 1]?).map fanout).getD 0

/-- The label column of a row list, 1-indexed, with a default off the end. -/
def lblRows (d : α) (rows : List α) : ℕ → α :=
  fun i => rows.getD (i - 1) d

theorem Sf_foRows (fanout : α → ℕ) (rows : List α) (m : ℕ) (hm : m ≤ rows.length) :
    Sf (foRows fanout rows) m = ((rows.take m).map fanout).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hlt : m < rows.length := by omega
      rw [Sf_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hlt]
      simp only [foRows, Nat.add_sub_cancel, List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some,
        Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]

/-- **The tiling** of a row list: `kRoots` roots plus all the fanouts account for every row
(`Walk.SfF_tiling_of_qgate`, in rows form). -/
def Tiles (fanout : α → ℕ) (kRoots : ℕ) (rows : List α) : Prop :=
  kRoots + (rows.map fanout).sum = rows.length

/-- **Queue validity** of a row list (`Walk.BFSValidF`, in rows form): row `i` has been queued by the
rows before it. -/
def Queued (fanout : α → ℕ) (kRoots : ℕ) (rows : List α) : Prop :=
  ∀ i, i < rows.length → i + 1 ≤ kRoots + ((rows.take i).map fanout).sum

theorem Tiles.sf {fanout : α → ℕ} {k : ℕ} {rows : List α} (h : Tiles fanout k rows) :
    k + Sf (foRows fanout rows) rows.length = rows.length := by
  rw [Sf_foRows fanout rows _ le_rfl, List.take_length]; exact h

theorem Queued.valid {fanout : α → ℕ} {k : ℕ} {rows : List α} (h : Queued fanout k rows) :
    BFSValidF k (foRows fanout rows) rows.length := by
  intro i hi1 hih
  rw [Sf_foRows fanout rows _ (by omega)]
  have := h (i - 1) (by omega)
  omega

theorem lblRows_range (d : α) (rows : List α) :
    (List.range' 1 rows.length).map (lblRows d rows) = rows := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [lblRows, List.getElem_range']
    simp [List.getElem?_eq_getElem h2]

theorem reconForest_wf (fanout : α → ℕ) (d : α) {k : ℕ} {rows : List α}
    (hk : 1 ≤ k) (ht : Tiles fanout k rows) (hq : Queued fanout k rows) :
    FanoutWF fanout (reconForest k (foRows fanout rows) (lblRows d rows) rows.length) := by
  intro t htm
  rw [bfsForest_reconForest k (foRows fanout rows) (lblRows d rows) rows.length hk ht.sf hq.valid]
    at htm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp htm
  rw [List.mem_range'_1] at hi
  have hi1 : 1 ≤ i := by omega
  have hih : i ≤ rows.length := by omega
  rw [buildTF_label, buildTF_children,
    childIdxsF_eq k (foRows fanout rows) rows.length ht.sf hq.valid hi1 hih]
  simp only [List.length_map, List.length_range']
  have hlt : i - 1 < rows.length := by omega
  simp [foRows, lblRows, List.getElem?_eq_getElem hlt, List.getD_eq_getElem?_getD]

/-- **The rebuilt forest is the Walk reconstruction** (hence the forest `execOfTraces` reads). -/
theorem rebuildForest_eq_reconForest (fanout : α → ℕ) (d : α) {k : ℕ} {rows : List α}
    (hk : 1 ≤ k) (ht : Tiles fanout k rows) (hq : Queued fanout k rows) :
    rebuildForest fanout k rows =
      reconForest k (foRows fanout rows) (lblRows d rows) rows.length := by
  set recon := reconForest k (foRows fanout rows) (lblRows d rows) rows.length with hrecon
  have hbfs : (bfsForest recon).map NTree.label = rows := by
    rw [hrecon, reconForest_labels k (foRows fanout rows) (lblRows d rows) rows.length hk ht.sf
      hq.valid]
    exact lblRows_range d rows
  have hlen : recon.length = k := by simp [hrecon, reconForest]
  have := rebuildForest_bfs fanout recon (reconForest_wf fanout d hk ht hq)
  rwa [hlen, hbfs] at this

/-- **`bfs ∘ rebuildForest` is the identity on tiled, queued rows** (S5, the round trip). -/
theorem bfs_rebuildForest (fanout : α → ℕ) {k : ℕ} {rows : List α}
    (hk : 1 ≤ k) (ht : Tiles fanout k rows) (hq : Queued fanout k rows) :
    ((bfsForest (rebuildForest fanout k rows)).map NTree.label) = rows := by
  have hd : rows ≠ [] := by
    intro h; subst h; simp [Tiles] at ht; omega
  rw [rebuildForest_eq_reconForest fanout (rows.head hd) hk ht hq,
    reconForest_labels k (foRows fanout rows) _ rows.length hk ht.sf hq.valid]
  exact lblRows_range _ rows

end Nock.RedTeam.Batch771

#print axioms Nock.RedTeam.Batch771.groupChildren_flatten
#print axioms Nock.RedTeam.Batch771.unbfs_bfs_aux
#print axioms Nock.RedTeam.Batch771.rebuildForest_bfs
#print axioms Nock.RedTeam.Batch771.Sf_foRows
#print axioms Nock.RedTeam.Batch771.Tiles.sf
#print axioms Nock.RedTeam.Batch771.Queued.valid
#print axioms Nock.RedTeam.Batch771.reconForest_wf
#print axioms Nock.RedTeam.Batch771.rebuildForest_eq_reconForest
#print axioms Nock.RedTeam.Batch771.bfs_rebuildForest
