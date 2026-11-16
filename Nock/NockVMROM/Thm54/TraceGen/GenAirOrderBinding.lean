/-
  Nock/NockVMROM/Thm54/TraceGen/GenAirOrderBinding.lean

  `RawComputeTopologyBinding` on the BFS-assigned, rendered AIR-ordered
  tree of any successful `genComputeSkeleton` run.  Fan-out is
  `bfsAssign_children_len_of_fanout`; `childLinkComp` is
  `childLinkComp_of_match` after transporting `childrenMatchSf` through
  the BFS reconstruction.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink
import Nock.NockVMROM.Thm54.TraceGen.GenWF
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonSpecialize

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open ComputeTable

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! ## List / BFS child identity -/

omit [Field K] in
theorem flatMap_index_lt {α β : Type*} (l : List α) (f : α → List β)
    {k j : ℕ} (hk : k < l.length) (hj : j < (f l[k]).length) :
    ((l.take k).flatMap f).length + j < (l.flatMap f).length := by
  have hsplit : l.flatMap f =
      (l.take k).flatMap f ++ (l.drop k).flatMap f := by
    conv_lhs => rw [← List.take_append_drop k l]
    rw [List.flatMap_append]
  have hdrop : l.drop k = l[k] :: l.drop (k + 1) :=
    List.drop_eq_getElem_cons hk
  rw [hsplit, List.length_append, hdrop, List.flatMap_cons, List.length_append]
  omega

omit [Field K] in
theorem getElem?_flatMap_at {α β : Type*} (l : List α) (f : α → List β)
    {k j : ℕ} (hk : k < l.length) (hj : j < (f l[k]).length) :
    (l.flatMap f)[((l.take k).flatMap f).length + j]? = some (f l[k])[j] := by
  have hsplit : l.flatMap f =
      (l.take k).flatMap f ++ (l.drop k).flatMap f := by
    conv_lhs => rw [← List.take_append_drop k l]
    rw [List.flatMap_append]
  have hdrop : l.drop k = l[k] :: l.drop (k + 1) :=
    List.drop_eq_getElem_cons hk
  rw [hsplit, hdrop, List.flatMap_cons,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (i := j) (hn := hj),
    List.getElem?_eq_getElem hj]

omit [Field K] in
theorem foCol_get {α : Type*} (W : List (NTree α)) {i : ℕ}
    (hi : i - 1 < W.length) :
    foCol W i = W[i - 1].children.length := by
  simp [foCol, List.getElem?_eq_getElem hi]

omit [Field K] in
theorem firstCF_child_lt {α : Type*} (t : NTree α) {i j : ℕ}
    (hi1 : 1 ≤ i) (hih : i ≤ (bfsForest [t]).length)
    (hj : j < foCol (bfsForest [t]) i) :
    firstCF 1 (foCol (bfsForest [t])) i + j - 1 < (bfsForest [t]).length := by
  set W := bfsForest [t]
  have htile : 1 + Sf (foCol W) W.length = W.length := by
    simpa using foCol_Sf_tilingF [t] (List.cons_ne_nil _ _)
  have hmono : Sf (foCol W) i ≤ Sf (foCol W) W.length := Sf_mono (foCol W) hih
  have hsucc : Sf (foCol W) i = Sf (foCol W) (i - 1) + foCol W i := by
    have hi : i - 1 + 1 = i := by omega
    conv_lhs => rw [← hi]
    rw [Sf_succ, hi]
  change 1 + 1 + Sf (foCol W) (i - 1) + j - 1 < W.length
  omega

omit [Field K] in
theorem bfs_child_get {α : Type*} (t : NTree α) {i j : ℕ}
    (hk : i - 1 < (bfsForest [t]).length)
    (hidx : firstCF 1 (foCol (bfsForest [t])) i + j - 1 < (bfsForest [t]).length)
    (hj : j < (bfsForest [t])[i - 1].children.length) :
    (bfsForest [t])[i - 1].children[j] =
      (bfsForest [t])[firstCF 1 (foCol (bfsForest [t])) i + j - 1] := by
  set W := bfsForest [t]
  set pref := (W.take (i - 1)).flatMap NTree.children
  have hflat := getElem?_flatMap_at W NTree.children hk hj
  have hW : W = t :: W.flatMap NTree.children := walk_tail_eq t
  have hfirst : firstCF 1 (foCol W) i + j - 1 = 1 + pref.length + j := by
    change 1 + 1 + Sf (foCol W) (i - 1) + j - 1 = 1 + pref.length + j
    have hSf : pref.length = Sf (foCol W) (i - 1) := (Sf_foCol W (i - 1)).symm
    omega
  have hcons : W[1 + pref.length + j]? =
      (W.flatMap NTree.children)[pref.length + j]? := by
    have hsucc : 1 + pref.length + j = pref.length + j + 1 := by omega
    have hlhs : W[1 + pref.length + j]? =
        (t :: W.flatMap NTree.children)[1 + pref.length + j]? := by
      conv => lhs; rw [hW]
    rw [hlhs, hsucc, List.getElem?_cons_succ]
  have hopt : (bfsForest [t])[firstCF 1 (foCol (bfsForest [t])) i + j - 1]? =
      some ((bfsForest [t])[i - 1].children[j]) := by
    simp only [W] at hfirst hcons hflat ⊢
    rw [hfirst, hcons]
    simpa [pref] using hflat
  have hR : (bfsForest [t])[firstCF 1 (foCol (bfsForest [t])) i + j - 1]? =
      some ((bfsForest [t])[firstCF 1 (foCol (bfsForest [t])) i + j - 1]) :=
    List.getElem?_eq_getElem hidx
  exact Option.some.inj (hopt.symm.trans hR)

/-! ## Assigned children match original `sf` slots -/

omit [Field K] in
theorem inTree_of_mem_bfsForest_singleton {α : Type*}
    {t u : NTree α} (h : u ∈ bfsForest [t]) : InTree t u := by
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest [t] u).mp h
  simp at hr
  subst r
  exact hin

theorem childrenMatchSf_bfs_of_AirLinked {t : NTree (GenComputeRow K)}
    (h : AirLinked t) {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [t]) : childrenMatchSf n :=
  childrenMatchSf_of_AirLinked (AirLinked_of_inTree h (inTree_of_mem_bfsForest_singleton hn))

theorem bfsAssign_build {t : NTree (GenComputeRow K)}
    {n : NTree (GenComputeRow K)} (hn : n ∈ bfsForest [bfsAssign t]) :
    ∃ i, i ∈ List.range' 1 (bfsForest [t]).length ∧
      n = buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
        (bfsForest [t]).length i := by
  rw [bfsForest_bfsAssign, List.mem_map] at hn
  obtain ⟨i, hi, heq⟩ := hn
  exact ⟨i, hi, heq.symm⟩

theorem childrenMatchSf_bfsAssign {t : NTree (GenComputeRow K)}
    (hmatch : ∀ n ∈ bfsForest [t], childrenMatchSf n)
    {n : NTree (GenComputeRow K)} (hn : n ∈ bfsForest [bfsAssign t]) :
    childrenMatchSf n := by
  obtain ⟨i, hi, rfl⟩ := bfsAssign_build hn
  obtain ⟨_, _, _⟩ := List.mem_range'.mp hi
  have hi1 : 1 ≤ i := by omega
  have hih : i ≤ (bfsForest [t]).length := by omega
  have hk : i - 1 < (bfsForest [t]).length := by omega
  have hne : [t] ≠ [] := List.cons_ne_nil _ _
  have hSf := foCol_Sf_tilingF [t] hne
  have hvalid := foCol_BFSValidF [t] hne
  intro j hj
  have hch := buildTF_children 1 (foCol (bfsForest [t])) (bfsLabelAt t)
    (bfsForest [t]).length i
  have hidx := childIdxsF_eq (kroots := 1) (fo := foCol (bfsForest [t]))
    (h := (bfsForest [t]).length) hSf hvalid hi1 hih
  have hjfo : (j : ℕ) < foCol (bfsForest [t]) i := by
    have := hj
    rw [hch, hidx] at this
    simpa [List.length_map, List.length_range'] using this
  have horigMem : (bfsForest [t])[i - 1] ∈ bfsForest [t] := List.getElem_mem hk
  have hjorig : (j : ℕ) < (bfsForest [t])[i - 1].children.length := by
    have hfo := foCol_get (bfsForest [t]) hk
    simpa [hfo] using hjfo
  have hm := hmatch _ horigMem j hjorig
  have hget :
      (buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
          (bfsForest [t]).length i).children[(j : ℕ)] =
        buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
          (bfsForest [t]).length
          (firstCF 1 (foCol (bfsForest [t])) i + j) := by
    simp_rw [hch, hidx]
    rw [List.getElem_map]
    have hjr : (j : ℕ) < (List.range' (firstCF 1 (foCol (bfsForest [t])) i)
        (foCol (bfsForest [t]) i)).length := by
      simpa [List.length_range'] using hjfo
    simp [List.getElem_range' hjr]
  have hsk : (buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
        (bfsForest [t]).length i).label.skel =
      (bfsForest [t])[i - 1].label.skel := by
    rw [buildTF_label]
    have hr : i - 1 < (bfsRows t).length := by simpa [bfsRows_length] using hk
    rw [bfsLabelAt_skel t i hr]
    simp [bfsRows]
  have hidx' := firstCF_child_lt t hi1 hih hjfo
  have hchSk :
      (buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
          (bfsForest [t]).length i).children[(j : ℕ)].label.skel =
        (bfsForest [t])[i - 1].children[(j : ℕ)].label.skel := by
    rw [hget, buildTF_label]
    have hr : firstCF 1 (foCol (bfsForest [t])) i + (j : ℕ) - 1 <
        (bfsRows t).length := by simpa [bfsRows_length] using hidx'
    rw [bfsLabelAt_skel t (firstCF 1 (foCol (bfsForest [t])) i + j) hr]
    simp [bfsRows]
    have hchild := bfs_child_get t hk hidx' hjorig
    exact (congrArg (fun u => u.label.skel) hchild).symm
  have hjNat :
      (buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
        (bfsForest [t]).length i).children[j] =
      (buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t)
        (bfsForest [t]).length i).children[(j : ℕ)] := rfl
  have hjNatO :
      (bfsForest [t])[i - 1].children[j] =
      (bfsForest [t])[i - 1].children[(j : ℕ)] := rfl
  have hsub := congrArg (fun s : ComputeRowSkeleton => s.subject) hchSk
  have hform := congrArg (fun s : ComputeRowSkeleton => s.formula) hchSk
  have heval := congrArg (fun s : ComputeRowSkeleton => s.evaluation) hchSk
  have hps := congrArg (fun s : ComputeRowSkeleton => s.subject) hsk
  have hpf := congrArg (fun s : ComputeRowSkeleton => s.formula) hsk
  have hpe := congrArg (fun s : ComputeRowSkeleton => s.evaluation) hsk
  refine ⟨?_, ?_, ?_⟩
  · rw [hjNat, hsub, hsk]
    simpa [hjNatO] using hm.1
  · rw [hjNat, hform, hsk]
    simpa [hjNatO] using hm.2.1
  · rw [hjNat, heval, hsk]
    simpa [hjNatO] using hm.2.2

/-! ## `BindComputeRow` on assigned AIR labels -/

theorem bind_bfsLabelAt_airReorder (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p) {i : ℕ}
    (hi : i - 1 < (bfsRows (airReorder p.1)).length) :
    BindComputeRow z (bfsLabelAt (airReorder p.1) i).skel
      (renderNode z α (bfsLabelAt (airReorder p.1) i)).row := by
  have h' : genComputeSkeleton (K := K) fuel subject formula = .ok (p.1, p.2) := by
    simpa [Prod.mk.eta] using h
  have hiW : i - 1 < (bfsForest [airReorder p.1]).length := by
    simpa [bfsRows_length] using hi
  have horig : (bfsForest [airReorder p.1])[i - 1] ∈
      bfsForest [airReorder p.1] := List.getElem_mem hiW
  have hin : InTree (airReorder p.1) (bfsForest [airReorder p.1])[i - 1] :=
    inTree_of_mem_bfsForest_singleton horig
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label p.1 _ hin
  have hstamp : bfsLabelAt (airReorder p.1) i =
      { (bfsForest [airReorder p.1])[i - 1].label with
          stamp := (bfsLabelAt (airReorder p.1) i).stamp } := by
    simp [bfsLabelAt_eq (airReorder p.1) i hi, bfsRows]
  have hb := genComputeSkeleton_inTree_bind z α
    (bfsLabelAt (airReorder p.1) i).stamp h' u0 hu0
  have hskel : (bfsLabelAt (airReorder p.1) i).skel = u0.label.skel := by
    rw [bfsLabelAt_skel (airReorder p.1) i hi]
    simp [bfsRows, hl]
  have hg : bfsLabelAt (airReorder p.1) i =
      { u0.label with stamp := (bfsLabelAt (airReorder p.1) i).stamp } := by
    rw [hstamp, hl]
  rw [hskel, hg]
  exact hb

/-! ## Rendered assigned AIR binding -/

theorem assigned_airReorder_bfs_binding (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p) :
    ∀ t ∈ bfsForest [mapNTree (GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (airReorder p.1))],
      RawComputeTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree_singleton] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have h' : genComputeSkeleton (K := K) fuel subject formula = .ok (p.1, p.2) := by
    simpa [Prod.mk.eta] using h
  have hL : AirLinked (airReorder p.1) := airLinked_airReorder_of_gen h
  have hfanU : u.children.length = fanoutComp u.label.skel.state :=
    bfsAssign_children_len_of_fanout (airReorder p.1)
      (fun n hn => by
        have hin := inTree_of_mem_bfsForest_singleton hn
        exact airReorder_inTree_fanout (fun v hv =>
          genComputeSkeleton_inTree_fanout h' v hv) n hin) hu
  have hmatch : childrenMatchSf u :=
    childrenMatchSf_bfsAssign (fun n hn => childrenMatchSf_bfs_of_AirLinked hL hn) hu
  obtain ⟨i, hi, rfl⟩ := bfsAssign_build hu
  have hr : i - 1 < (bfsRows (airReorder p.1)).length := by
    obtain ⟨_, _, _⟩ := List.mem_range'.mp hi
    simpa [bfsRows_length] using (show i - 1 < (bfsForest [airReorder p.1]).length by omega)
  have hbind : BindComputeRow z
      (buildTF 1 (foCol (bfsForest [airReorder p.1]))
        (bfsLabelAt (airReorder p.1)) (bfsForest [airReorder p.1]).length i).label.skel
      (renderNode z α
        (buildTF 1 (foCol (bfsForest [airReorder p.1]))
          (bfsLabelAt (airReorder p.1)) (bfsForest [airReorder p.1]).length i).label).row := by
    rw [buildTF_label]
    exact bind_bfsLabelAt_airReorder z α h hr
  cases hnode :
      buildTF 1 (foCol (bfsForest [airReorder p.1]))
        (bfsLabelAt (airReorder p.1)) (bfsForest [airReorder p.1]).length i with
  | node g cs =>
    have hfan : cs.length = fanoutComp g.skel.state := by
      have := hfanU
      rw [hnode] at this
      simpa [NTree.children, NTree.label] using this
    have hmatch' : childrenMatchSf (.node g cs) := by
      have := hmatch
      rw [hnode] at this
      exact this
    have hbind' : BindComputeRow z g.skel (renderNode z α g).row := by
      have := hbind
      rw [hnode] at this
      simpa [NTree.label] using this
    refine ⟨?_, childLinkComp_of_match z α g cs hfan hmatch' hbind'⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      exact hfan.symm

/-! ## `setRowCoins` preserves the residual -/

theorem childLinkComp_setRowCoins (a b c : K)
    (t : NTree (State × DTcomp K))
    (h : childLinkComp t.label (fun j => t.childLabel j)) :
    childLinkComp (mapNTree (setRowCoins a b c) t).label
      (fun j => (mapNTree (setRowCoins a b c) t).childLabel j) := by
  intro i hi
  have hi' : (i : ℕ) < fanoutComp t.label.1 := by
    simpa [mapNTree_label, setRowCoins_state] using hi
  have hlink := h i hi'
  change Option.map (fun c => (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e))
      ((mapNTree (setRowCoins a b c) t).childLabel i) =
    some (sfTriple (mapNTree (setRowCoins a b c) t).label.2.2.1 i)
  rw [mapNTree_childLabel, Option.map_map]
  have hsfe :
      (fun c : State × DTcomp K => (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e)) ∘
        setRowCoins a b c =
      fun c => (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e) := by
    funext c
    simp [setRowCoins]
  rw [hsfe]
  simp only [mapNTree_label]
  change Option.map (fun c => (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e))
      (t.childLabel i) =
    some (sfTriple (setRowCoins a b c t.label).2.2.1 i)
  exact hlink

theorem rawComputeBinding_setRowCoins (a b c : K)
    (t : NTree (State × DTcomp K))
    (h : RawComputeTopologyBinding t) :
    RawComputeTopologyBinding (mapNTree (setRowCoins a b c) t) := by
  refine ⟨?_, childLinkComp_setRowCoins a b c t h.2⟩
  · rw [mapNTree_label, mapNTree_children, List.length_map, setRowCoins_state]
    exact h.1

theorem assigned_airReorder_coins_binding (z α a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p) :
    ∀ t ∈ bfsForest [mapNTree
        ((setRowCoins a b c) ∘ GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (airReorder p.1))],
      RawComputeTopologyBinding t := by
  intro t ht
  have hcomp :
      mapNTree ((setRowCoins a b c) ∘ GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (airReorder p.1)) =
      mapNTree (setRowCoins a b c)
        (mapNTree (GenComputeRow.row ∘ renderNode z α)
          (bfsAssign (airReorder p.1))) := by
    simpa [Function.comp] using
      (mapNTree_comp (setRowCoins a b c)
        (GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (airReorder p.1))).symm
  rw [hcomp, bfsForest_mapNTree_singleton] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact rawComputeBinding_setRowCoins a b c u
    (assigned_airReorder_bfs_binding z α h u hu)

/-! ## `ComputeNodesOK` on the assigned AIR tree -/

theorem genComputeSkeleton_airReorder_computeNodes_OK (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p) :
    ComputeNodesOK z α
      (mapNTree GenComputeRow.node
        (renderRows z α (bfsAssign (airReorder p.1)))) := by
  intro u hu
  have h' : genComputeSkeleton (K := K) fuel subject formula = .ok (p.1, p.2) := by
    simpa [Prod.mk.eta] using h
  have hmem :
      u ∈ bfsForest
        [mapNTree GenComputeRow.node
          (renderRows z α (bfsAssign (airReorder p.1)))] :=
    (mem_bfsForest
        [mapNTree GenComputeRow.node
          (renderRows z α (bfsAssign (airReorder p.1)))] u).mpr
      ⟨_, List.mem_singleton.mpr rfl, hu⟩
  rw [renderRows_bfsAssign_bfsForest, bfsForest_bfsAssign, List.mem_map] at hmem
  obtain ⟨n, hn, rfl⟩ := hmem
  rw [List.mem_map] at hn
  obtain ⟨j, hj, rfl⟩ := hn
  have hnmem :
      buildTF 1 (foCol (bfsForest [airReorder p.1]))
          (bfsLabelAt (airReorder p.1))
          (bfsForest [airReorder p.1]).length j ∈
        bfsForest [bfsAssign (airReorder p.1)] := by
    rw [bfsForest_bfsAssign]
    exact List.mem_map.mpr ⟨j, hj, rfl⟩
  have hch := bfsAssign_children_len_of_fanout (airReorder p.1)
    (fun v hv =>
      airReorder_inTree_fanout
        (fun w hw => genComputeSkeleton_inTree_fanout h' w hw) v
        (inTree_of_mem_bfsForest_singleton hv))
    hnmem
  have hnode :
      (mapNTree GenComputeRow.node
          (renderRows z α
            (buildTF 1 (foCol (bfsForest [airReorder p.1]))
              (bfsLabelAt (airReorder p.1))
              (bfsForest [airReorder p.1]).length j))).label =
        (renderNode z α (bfsLabelAt (airReorder p.1) j)).node := by
    simp [renderRows_eq_mapNTree, mapNTree_label, buildTF_label,
      GenComputeRow.node]
  have hj' := lt_bfsRows_of_mem_range' hj
  refine ⟨?flen, ?fstamp, ?fbind, ?ftime⟩
  · rw [mapNTree_children, renderRows_eq_mapNTree, mapNTree_children,
      List.length_map, List.length_map, hch]
    simp [buildTF_label, mapNTree_label, GenComputeRow.node,
      renderNode_op1_skel]
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_skel, renderNode_op1_stamp]
    exact bfsLabelAt_state (airReorder p.1) j hj'
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_skel]
    exact bind_bfsLabelAt_airReorder z α h hj'
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_stamp]
    exact bfsLabelAt_specializes z α (airReorder p.1) hj

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.assigned_airReorder_bfs_binding
#print axioms Nock.NockVMROM.Thm54.TraceGen.assigned_airReorder_coins_binding
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_airReorder_computeNodes_OK
