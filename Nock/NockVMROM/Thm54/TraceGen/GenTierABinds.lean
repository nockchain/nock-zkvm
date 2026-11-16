/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierABinds.lean

  Canonical tree binding of the generated F769 carrier: `ComputeNodesOK`
  and `MemoryNodesOK` lift to `ComputeTreeBinds` / `MemoryTreeBinds`, the
  memory side is transported through LogUp `threadGenForest` (which only
  rewrites `ipre`/`icur`), and `execThreaded` inhabits `BindsAt` against
  `genSemanticSkeleton (bfsAssign dotTree) assignedForest`.

  Compute `childLinkComp` / `ComputeExactTopology` are not claimed here.

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierATopology
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemAccept
import Nock.NockVMROM.Thm54.RawSemanticAssembly
import Nock.NockVMROM.Thm54.NounRealization

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.RawSemanticAssembly

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## List / shape plumbing -/

omit [Field K] in
private theorem wf_tree_list {A : Type*} (lbl : A) (cs : List (NTree A)) :
    2 * totalSize cs + 1 < 2 * totalSize [NTree.node lbl cs] := by
  have h : totalSize [NTree.node lbl cs] = 1 + totalSize cs := by
    rw [totalSize_cons, totalSize_nil]
    simp [NTree.size, totalSize]
  omega

omit [Field K] in
private theorem wf_list_head {A : Type*} (c : NTree A) (rest : List (NTree A)) :
    2 * totalSize [c] < 2 * totalSize (c :: rest) + 1 := by
  rw [totalSize_cons, totalSize_cons, totalSize_nil]
  omega

omit [Field K] in
private theorem wf_list_tail {A : Type*} (c : NTree A) (rest : List (NTree A)) :
    2 * totalSize rest + 1 < 2 * totalSize (c :: rest) + 1 := by
  rw [totalSize_cons]
  have hc : 0 < c.size := by cases c; simp [NTree.size]
  omega

omit [Field K] in
theorem list_unit_eq : ∀ l m : List Unit, l.length = m.length → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | () :: xs, () :: ys, h => by
      simp at h
      exact congrArg (List.cons ()) (list_unit_eq xs ys h)

omit [Field K] in
theorem forall₂_of_map_eq {α β} (f : α → β) :
    ∀ l m, l.map f = m.map f → List.Forall₂ (fun a b => f a = f b) l m
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: m, h => by
      simp [List.map_cons] at h
      exact .cons h.1 (forall₂_of_map_eq f l m h.2)

omit [Field K] in
theorem mapNTree_eq_of {α β} {f g : α → β} (h : ∀ x, f x = g x) :
    ∀ t, mapNTree f t = mapNTree g t
  | .node _ cs => by
      simp only [mapNTree, h]
      refine congrArg _ ?_
      apply List.map_congr_left
      intro c _
      exact mapNTree_eq_of h c

omit [Field K] in
theorem shapeOf_mapNTree {α β} (f : α → β) (t : NTree α) :
    mapNTree (fun _ => ()) (mapNTree f t) = mapNTree (fun _ => ()) t := by
  rw [mapNTree_comp]

/-! ## `ComputeNodesOK` → `ComputeTreeBinds` -/

mutual
theorem computeTreeBinds_of_nodesOK (z α : K) :
    ∀ (T : NTree (ComputeNode K)), ComputeNodesOK z α T →
      ComputeTreeBinds z (mapNTree ComputeNode.skel T)
        (mapNTree ComputeNode.row T)
  | .node lbl cs, h => by
      obtain ⟨hshape, _, hbind, _⟩ := h _ (InTree.here _)
      simp only [NTree.label_node, NTree.children_node] at hshape
      rw [mapNTree, mapNTree]
      refine ComputeTreeBinds.node ?_ hbind
        (computeTreeBindsList_of_nodesOK z α cs
          (fun c hc => h.child (by simpa using hc)))
      simpa using hshape
termination_by T _ => 2 * totalSize [T]
decreasing_by exact wf_tree_list _ _

theorem computeTreeBindsList_of_nodesOK (z α : K) :
    ∀ (cs : List (NTree (ComputeNode K))),
      (∀ c ∈ cs, ComputeNodesOK z α c) →
      List.Forall₂ (ComputeTreeBinds z)
        (cs.map (mapNTree ComputeNode.skel))
        (cs.map (mapNTree ComputeNode.row))
  | [], _ => .nil
  | c :: rest, h =>
      .cons (computeTreeBinds_of_nodesOK z α c (h c (by simp)))
        (computeTreeBindsList_of_nodesOK z α rest
          (fun x hx => h x (by simp [hx])))
termination_by cs _ => 2 * totalSize cs + 1
decreasing_by
  all_goals first
    | exact wf_list_head _ _
    | exact wf_list_tail _ _
end

/-! ## `MemoryNodesOK` → `MemoryTreeBinds` / `MemoryShapeMatch` -/

mutual
theorem memoryTreeBinds_of_nodesOK (z α : K) :
    ∀ (T : NTree (MemoryNode K)), MemoryNodesOK z α T →
      MemoryTreeBinds z (mapNTree MemoryNode.skel T)
        (mapNTree (fun n : MemoryNode K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
            n.row) T)
  | .node lbl cs, h => by
      obtain ⟨hshape, _, hbind, _⟩ := h _ (InTree.here _)
      simp only [NTree.label_node, NTree.children_node] at hshape
      rw [mapNTree, mapNTree]
      refine MemoryTreeBinds.node ?_ (bindMemoryRow_encodeRow hbind)
        (memoryTreeBindsList_of_nodesOK z α cs
          (fun c hc => h.child (by simpa using hc)))
      simpa using hshape
termination_by T _ => 2 * totalSize [T]
decreasing_by exact wf_tree_list _ _

theorem memoryTreeBindsList_of_nodesOK (z α : K) :
    ∀ (cs : List (NTree (MemoryNode K))),
      (∀ c ∈ cs, MemoryNodesOK z α c) →
      List.Forall₂ (MemoryTreeBinds z)
        (cs.map (mapNTree MemoryNode.skel))
        (cs.map (mapNTree (fun n : MemoryNode K =>
            SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb n.row)))
  | [], _ => .nil
  | c :: rest, h =>
      .cons (memoryTreeBinds_of_nodesOK z α c (h c (by simp)))
        (memoryTreeBindsList_of_nodesOK z α rest
          (fun x hx => h x (by simp [hx])))
termination_by cs _ => 2 * totalSize cs + 1
decreasing_by
  all_goals first
    | exact wf_list_head _ _
    | exact wf_list_tail _ _
end

theorem memoryShapeMatch_of_nodesOK (z α : K)
    (T : NTree (MemoryNode K)) (h : MemoryNodesOK z α T) :
    MemoryShapeMatch (mapNTree MemoryNode.skel T)
      (mapNTree (fun n : MemoryNode K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
          n.row) T) :=
  memoryTreeBinds_shapeMatch (memoryTreeBinds_of_nodesOK z α T h)

theorem memoryShapeMatch_congr_exec
    {st : NTree MemoryRowSkeleton}
    {et eu : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryShapeMatch st et)
    (hs : mapNTree (fun _ => ()) et = mapNTree (fun _ => ()) eu) :
    MemoryShapeMatch st eu := by
  refine (MemoryShapeMatch.rec
    (motive_1 := fun (st : NTree MemoryRowSkeleton)
        (et : NTree (MemoryTable.MState × MemoryTable.DTmem K)) _ =>
      ∀ (eu : NTree (MemoryTable.MState × MemoryTable.DTmem K)),
        mapNTree (fun _ => ()) et = mapNTree (fun _ => ()) eu →
          MemoryShapeMatch st eu)
    (motive_2 := fun (sts : List (NTree MemoryRowSkeleton))
        (ets : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) _ =>
      ∀ (eus : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))),
        ets.map (mapNTree (fun _ => ())) =
          eus.map (mapNTree (fun _ => ())) →
            List.Forall₂ MemoryShapeMatch sts eus)
    ?_ ?_ ?_ h) eu hs
  · intro s sc row rc harity _ ih eu heq
    cases eu with
    | node _ rc' =>
      have hcs :
          rc.map (mapNTree (fun _ => ())) =
            rc'.map (mapNTree (fun _ => ())) := by
        simpa [mapNTree] using heq
      exact MemoryShapeMatch.node harity (ih rc' hcs)
  · intro eus heq
    have : eus = [] := by
      simpa using (congrArg List.length heq).symm
    subst this
    exact .nil
  · intro et ets st sts _ _ ihHead ihTail eus heq
    match eus with
    | [] =>
      simp [List.map_cons] at heq
    | eu :: eus' =>
      simp [List.map_cons] at heq
      exact .cons (ihHead eu heq.1) (ihTail eus' heq.2)

/-! ## `renderNode` preserves the pre-seed skeleton -/

theorem renderRows_skel (z α : K) (t : NTree (GenComputeRow K)) :
    mapNTree GenComputeRow.skel (renderRows z α t) =
      mapNTree GenComputeRow.skel t := by
  rw [renderRows_eq_mapNTree, mapNTree_comp]
  exact mapNTree_eq_of (fun g => renderNode_op1_skel z α g) t

theorem mapNTree_node_skel (t : NTree (GenComputeRow K)) :
    mapNTree ComputeNode.skel (mapNTree GenComputeRow.node t) =
      mapNTree GenComputeRow.skel t := by
  rw [mapNTree_comp]
  exact mapNTree_eq_of (fun _ => rfl) t

theorem mapNTree_node_row (t : NTree (GenComputeRow K)) :
    mapNTree ComputeNode.row (mapNTree GenComputeRow.node t) =
      mapNTree GenComputeRow.row t := by
  rw [mapNTree_comp]
  exact mapNTree_eq_of (fun _ => rfl) t

theorem mapNTree_memNode_skel (t : NTree (GenMemoryRow K)) :
    mapNTree MemoryNode.skel (mapNTree GenMemoryRow.node t) =
      mapNTree GenMemoryRow.skel t := by
  rw [mapNTree_comp]
  exact mapNTree_eq_of (fun _ => rfl) t

theorem mapNTree_memNode_row (t : NTree (GenMemoryRow K)) :
    mapNTree MemoryNode.row (mapNTree GenMemoryRow.node t) =
      mapNTree GenMemoryRow.row t := by
  rw [mapNTree_comp]
  exact mapNTree_eq_of (fun _ => rfl) t

theorem mapNTree_memNode_rowE (t : NTree (GenMemoryRow K)) :
    mapNTree (fun n : MemoryNode K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb n.row)
        (mapNTree GenMemoryRow.node t) =
      mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
          g.row) t := by
  rw [mapNTree_comp]
  exact mapNTree_eq_of (fun _ => rfl) t

/-! ## `setGenAcc` preserves `BindMemoryRowA` -/

theorem setGenAcc_skel (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).skel = g.skel :=
  rfl

theorem setGenAcc_memoryChildCell (g : GenMemoryRow K) (a b : K) (i : Fin 2) :
    memoryChildCell (setGenAcc g a b).row.2.2 i =
      memoryChildCell g.row.2.2 i := by
  fin_cases i <;> simp [memoryChildCell, setGenAcc_lc, setGenAcc_rc]

theorem BindMemoryRow_setGenAcc (z : K) (g : GenMemoryRow K) (a b : K)
    (h : BindMemoryRowA z g.skel g.row) :
    BindMemoryRowA z (setGenAcc g a b).skel (setGenAcc g a b).row := by
  rw [setGenAcc_skel]
  obtain ⟨hst, hz, hst', hpt, hch, hmem, hver⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [setGenAcc_row1] using hst
  · simpa [setGenAcc_inputs] using hz
  · simpa [setGenAcc_pub_st] using hst'
  · simpa [setGenAcc_pt] using hpt
  · intro i
    have hcell := setGenAcc_memoryChildCell g a b i
    simpa [hcell] using hch i
  · simpa [setGenAcc_mem] using hmem
  · simpa [setGenAcc, setAcc] using hver

theorem BindMemoryRow_threadGenRow (z : K) (inp : MemoryTable.Inputs K)
    (acc : K) (g : GenMemoryRow K)
    (h : BindMemoryRowA z g.skel g.row) :
    BindMemoryRowA z (threadGenRow inp acc g).2.skel
      (threadGenRow inp acc g).2.row := by
  rw [threadGenRow_snd]
  exact BindMemoryRow_setGenAcc z g _ _ h

theorem threadGenRows_bind (z : K) (inp : MemoryTable.Inputs K) :
    ∀ acc gs,
      (∀ g ∈ gs, BindMemoryRowA z g.skel g.row) →
      List.Forall₂ (BindMemoryRowA z)
        (gs.map GenMemoryRow.skel)
        ((threadGenRows inp acc gs).map GenMemoryRow.row)
  | _, [] => by
      intro
      exact .nil
  | acc, g :: gs => by
      intro h
      refine .cons ?_ ?_
      · exact BindMemoryRow_threadGenRow z inp acc g
          (h g (List.mem_cons.mpr (Or.inl rfl)))
      · exact threadGenRows_bind z inp (threadGenRow inp acc g).1 gs
          (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

/-! ## Threaded forest shape and skeleton -/

theorem threadGenForest_shapeOf (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    (threadGenForest inp acc forest).map (mapNTree (fun _ => ())) =
      forest.map (mapNTree (fun _ => ())) := by
  unfold threadGenForest
  rw [zipBfs_mapNTree]
  have hlabs :
      (threadGenRows inp acc ((bfsForest forest).map NTree.label)).map
          (fun _ => ()) =
        (bfsForest (forest.map (mapNTree (fun _ => ())))).map NTree.label := by
    refine list_unit_eq _ _ ?_
    rw [List.length_map, List.length_map, threadGenRows_length, List.length_map,
      bfsForest_length]
    rw [bfsForest_length, totalSize_map]
  rw [hlabs, zipBfs_self]

theorem threadGenRows_map_skel (inp : MemoryTable.Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).map GenMemoryRow.skel = gs.map GenMemoryRow.skel
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows_cons, threadGenRow_snd, setGenAcc_skel]
      exact threadGenRows_map_skel inp (threadGenRow inp acc g).1 gs

theorem threadGenForest_map_skel (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    (threadGenForest inp acc forest).map (mapNTree GenMemoryRow.skel) =
      forest.map (mapNTree GenMemoryRow.skel) := by
  unfold threadGenForest
  rw [zipBfs_mapNTree, threadGenRows_map_skel]
  have hlabs :
      ((bfsForest forest).map NTree.label).map GenMemoryRow.skel =
        (bfsForest (forest.map (mapNTree GenMemoryRow.skel))).map NTree.label := by
    rw [bfsForest_mapNTree, List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    exact (mapNTree_label GenMemoryRow.skel t).symm
  rw [hlabs, zipBfs_self]

/-! ## Assigned-forest `BindMemoryRow` -/

theorem inTree_bindMemoryRow (z α : K)
    {t u : NTree (GenMemoryRow K)}
    (hOK : MemoryNodesOK z α (mapNTree GenMemoryRow.node t))
    (hu : InTree t u) :
    BindMemoryRowA z u.label.skel u.label.row := by
  have hnode := hOK (mapNTree GenMemoryRow.node u) (mapNTree_inTree _ hu)
  obtain ⟨_, _, hbind, _⟩ := hnode
  simpa [mapNTree_label] using hbind

theorem genMemForest_bfs_bindMemoryRow (z α : K)
    (t : NTree (GenComputeRow K))
    (H : ∀ n, InTree t n →
      ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
        MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    {u : NTree (GenMemoryRow K)}
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb t)
    {v : NTree (GenMemoryRow K)}
    (hv : v ∈ bfsForest [u]) :
    BindMemoryRowA z v.label.skel v.label.row := by
  have hOK := genMemForestFromTree_of_rowOK z α t H u hu
  have hin : InTree u v := by
    have := (mem_bfsForest [u] v).mp hv
    obtain ⟨c, hc, hct⟩ := this
    simp at hc
    subst c
    exact hct
  exact inTree_bindMemoryRow z α hOK hin

theorem assigned_bfs_bindMemoryRow (z α : K) :
    ∀ t ∈ bfsForest
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K)))),
      BindMemoryRowA z t.label.skel t.label.row := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact inTree_bindMemoryRow z α (dotMemForest_OK z α u hu) hin

theorem assigned_memoryShapeMatch (z α : K) :
    ∀ t ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))),
      MemoryShapeMatch (mapNTree GenMemoryRow.skel t)
        (mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
            g.row) t) := by
  intro t ht
  have hOK := dotMemForest_OK z α t ht
  have h := memoryShapeMatch_of_nodesOK (lmb := lmb) z α (mapNTree GenMemoryRow.node t) hOK
  simpa [mapNTree_memNode_skel, mapNTree_memNode_rowE] using h

/-! ## Threaded forest `MemoryShapeMatch` / BFS `BindMemoryRow` -/

omit [Field K] in
theorem forall₂_map {α β γ δ} {S : γ → δ → Prop}
    (f : α → γ) (g : β → δ) {l : List α} {m : List β}
    (h : List.Forall₂ (fun a b => S (f a) (g b)) l m) :
    List.Forall₂ S (l.map f) (m.map g) := by
  induction h with
  | nil => exact .nil
  | cons hR hrest ih => exact .cons hR ih

omit [Field K] in
theorem forall₂_imp_left_mem {α β} {R S : α → β → Prop}
    {l : List α} {m : List β}
    (h : List.Forall₂ R l m)
    (hs : ∀ a b, a ∈ l → R a b → S a b) :
    List.Forall₂ S l m := by
  induction h with
  | nil => exact .nil
  | @cons a b l m hR hrest ih =>
      refine .cons (hs a b (by simp) hR)
        (ih fun x y hx => hs x y (List.mem_cons.mpr (Or.inr hx)))

theorem threadGenForest_memoryShapeMatch (z α : K)
    (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (hOK : ∀ t ∈ forest, MemoryNodesOK z α (mapNTree GenMemoryRow.node t)) :
    List.Forall₂ MemoryShapeMatch
      (forest.map (mapNTree GenMemoryRow.skel))
      ((threadGenForest inp acc forest).map (mapNTree (fun g : GenMemoryRow K
          => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb g.row))) := by
  have hpairs :=
    forall₂_of_map_eq (mapNTree (fun _ => ())) forest
      (threadGenForest inp acc forest) (threadGenForest_shapeOf inp acc forest).symm
  have hlist :
      List.Forall₂
        (fun t u =>
          MemoryShapeMatch (mapNTree GenMemoryRow.skel t)
            (mapNTree (fun g : GenMemoryRow K =>
                SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb g.row) u))
        forest (threadGenForest inp acc forest) := by
    refine forall₂_imp_left_mem hpairs ?_
    intro t u ht hshape
    have hmatch := memoryShapeMatch_of_nodesOK (lmb := lmb) z α
      (mapNTree GenMemoryRow.node t) (hOK t ht)
    have hmatch' :
        MemoryShapeMatch (mapNTree GenMemoryRow.skel t)
          (mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
              g.row) t) := by
      simpa [mapNTree_memNode_skel, mapNTree_memNode_rowE] using hmatch
    refine memoryShapeMatch_congr_exec hmatch' ?_
    rw [shapeOf_mapNTree, shapeOf_mapNTree, hshape]
  exact forall₂_map (mapNTree GenMemoryRow.skel)
    (mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
        g.row)) hlist

theorem threadGenForest_bfs_bindMemoryRow (z : K)
    (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (hbind : ∀ t ∈ bfsForest forest, BindMemoryRowA z t.label.skel t.label.row) :
    List.Forall₂ (BindMemoryRowA z)
      ((bfsForest forest).map (fun t => t.label.skel))
      ((bfsForest (threadGenForest inp acc forest)).map
        (fun t => t.label.row)) := by
  have hlab :
      (bfsForest (threadGenForest inp acc forest)).map NTree.label =
        threadGenRows inp acc ((bfsForest forest).map NTree.label) :=
    threadGenForest_bfs_labels inp acc forest
  have hrow :
      (bfsForest (threadGenForest inp acc forest)).map
          (fun t => t.label.row) =
        (threadGenRows inp acc ((bfsForest forest).map NTree.label)).map
          GenMemoryRow.row := by
    rw [← hlab, List.map_map]
    rfl
  rw [hrow]
  have hbind' := threadGenRows_bind z inp acc
      ((bfsForest forest).map NTree.label)
      (fun g hg => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
        exact hbind t ht)
  simpa [List.map_map] using hbind'

theorem forall₂_bind_encode (z : K) {l : List MemoryRowSkeleton}
    {m : List (NTree (GenMemoryRow K))}
    (h : List.Forall₂ (BindMemoryRowA z) l (m.map (fun t => t.label.row))) :
    List.Forall₂ (BindMemoryRow z) l (m.map (fun t =>
        SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb t.label.row)) := by
  rw [List.forall₂_map_right_iff] at h ⊢
  exact h.imp (fun _ _ hh => bindMemoryRow_encodeRow hh)

theorem assigned_threaded_memoryTreeBinds (z α : K) :
    List.Forall₂ (MemoryTreeBinds z)
      ((genMemForestFromTree (encC z) z α lmb
          (bfsAssign (dotTree (K := K)))).map (mapNTree GenMemoryRow.skel))
      ((threadGenForest (memInputs z) 0
          (genMemForestFromTree (encC z) z α lmb
            (bfsAssign (dotTree (K := K))))).map
        (mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
            g.row))) := by
  refine memoryTreeBinds_forest_of_shapeMatch
    (threadGenForest_memoryShapeMatch z α (memInputs z) 0 _
      (dotMemForest_OK z α)) ?_
  have hskel :
      (bfsForest
          ((genMemForestFromTree (encC z) z α lmb
              (bfsAssign (dotTree (K := K)))).map
            (mapNTree GenMemoryRow.skel))).map NTree.label =
        (bfsForest
            (genMemForestFromTree (encC z) z α lmb
              (bfsAssign (dotTree (K := K))))).map
          (fun t => t.label.skel) := by
    rw [bfsForest_mapNTree, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    exact mapNTree_label _ t
  have hrow :
      (bfsForest
          ((threadGenForest (memInputs z) 0
              (genMemForestFromTree (encC z) z α lmb
                (bfsAssign (dotTree (K := K))))).map
            (mapNTree (fun g : GenMemoryRow K =>
                SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb g.row)))).map NTree.label =
        (bfsForest
            (threadGenForest (memInputs z) 0
              (genMemForestFromTree (encC z) z α lmb
                (bfsAssign (dotTree (K := K)))))).map
          (fun t => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb t.label.row) := by
    rw [bfsForest_mapNTree, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    simp [mapNTree_label]
  rw [hskel, hrow]
  exact forall₂_bind_encode z <| threadGenForest_bfs_bindMemoryRow z (memInputs z) 0 _
    (assigned_bfs_bindMemoryRow z α)

theorem assigned_bfs_bindMemoryRow_air (z α : K) :
    ∀ t ∈ bfsForest
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTreeAir (K := K)))),
      BindMemoryRowA z t.label.skel t.label.row := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact inTree_bindMemoryRow z α (assignedMemForest_OK_air z α u hu) hin

theorem assigned_threaded_memoryTreeBinds_air (z α : K) :
    List.Forall₂ (MemoryTreeBinds z)
      ((genMemForestFromTree (encC z) z α lmb
          (bfsAssign (dotTreeAir (K := K)))).map (mapNTree GenMemoryRow.skel))
      ((threadGenForest (memInputs z) 0
          (genMemForestFromTree (encC z) z α lmb
            (bfsAssign (dotTreeAir (K := K))))).map
        (mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
            g.row))) := by
  refine memoryTreeBinds_forest_of_shapeMatch
    (threadGenForest_memoryShapeMatch z α (memInputs z) 0 _
      (assignedMemForest_OK_air z α)) ?_
  have hskel :
      (bfsForest
          ((genMemForestFromTree (encC z) z α lmb
              (bfsAssign (dotTreeAir (K := K)))).map
            (mapNTree GenMemoryRow.skel))).map NTree.label =
        (bfsForest
            (genMemForestFromTree (encC z) z α lmb
              (bfsAssign (dotTreeAir (K := K))))).map
          (fun t => t.label.skel) := by
    rw [bfsForest_mapNTree, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    exact mapNTree_label _ t
  have hrow :
      (bfsForest
          ((threadGenForest (memInputs z) 0
              (genMemForestFromTree (encC z) z α lmb
                (bfsAssign (dotTreeAir (K := K))))).map
            (mapNTree (fun g : GenMemoryRow K =>
                SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb g.row)))).map NTree.label =
        (bfsForest
            (threadGenForest (memInputs z) 0
              (genMemForestFromTree (encC z) z α lmb
                (bfsAssign (dotTreeAir (K := K)))))).map
          (fun t => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb t.label.row) := by
    rw [bfsForest_mapNTree, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    simp [mapNTree_label]
  rw [hskel, hrow]
  exact forall₂_bind_encode z <| threadGenForest_bfs_bindMemoryRow z (memInputs z) 0 _
    (assigned_bfs_bindMemoryRow_air z α)

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

noncomputable section

def semanticSkeleton (z α : K) : SemanticSkeleton :=
  genSemanticSkeleton (bfsAssign (dotTreeAir (K := K))) (assignedForest z α)

theorem semanticSkeleton_computeTree (z α : K) :
    (semanticSkeleton z α).computeTree =
      mapNTree ComputeNode.skel (dotComputeNodesAir z α) := by
  change mapNTree GenComputeRow.skel (bfsAssign (dotTreeAir (K := K))) =
    mapNTree ComputeNode.skel (dotComputeNodesAir z α)
  rw [dotComputeNodesAir, mapNTree_node_skel, renderRows_skel]

theorem execThreaded_computeTree_nodes (z α : K) :
    (execThreaded z α).computeTree =
      mapNTree ComputeNode.row (dotComputeNodesAir z α) := by
  change computeTree z α = mapNTree ComputeNode.row (dotComputeNodesAir z α)
  rw [computeTree, dotComputeNodesAir, mapNTree_node_row]

theorem computeTreeBinds_threaded (z α : K) :
    ComputeTreeBinds z (semanticSkeleton z α).computeTree
      (execThreaded z α).computeTree := by
  rw [semanticSkeleton_computeTree, execThreaded_computeTree_nodes]
  exact computeTreeBinds_of_nodesOK z α _ (dotComputeNodesAir_OK z α)

theorem memoryForestBinds_threaded (z α : K) :
    List.Forall₂ (MemoryTreeBinds z)
      (semanticSkeleton z α).memoryForest
      (execThreaded z α).memoryForest := by
  change List.Forall₂ (MemoryTreeBinds z)
      ((assignedForest z α).map (mapNTree GenMemoryRow.skel))
      ((memoryForestThreaded z α).map
        (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault)))
  have hf : (memoryForestThreaded z α).map (mapNTree
      (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault)) =
      (threadedForest z α).map
        (mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault
            g.row)) := by
    unfold memoryForestThreaded
    rw [List.map_map]
    refine List.map_congr_left (fun t _ => ?_)
    exact mapNTree_comp _ _ t
  rw [hf]
  unfold threadedForest assignedForest
  exact assigned_threaded_memoryTreeBinds_air z α

theorem bindsAt_threaded (z α : K) :
    BindsAt z (semanticSkeleton z α) (cfg z α) (execThreaded z α) :=
  BindsAt.ofTreeBindings (F := F) (K := K)
    (S := semanticSkeleton z α) (cfg := cfg z α) (exec := execThreaded z α)
    rfl (computeTreeBinds_threaded z α) (memoryForestBinds_threaded z α)

theorem bindsAt_seed :
    BindsAt seedZ (semanticSkeleton seedZ alphaA) (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) :=
  bindsAt_threaded seedZ alphaA

private theorem forall₂_exists_left {α β} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => cases hb
  | cons hab _ ih =>
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- Honest `ver = (st = read_root)` on every executed (encoded) threaded memory row. -/
theorem execThreaded_honestVer (z α : K) :
    ∀ row ∈ (execThreaded z α).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MState.read_root) := by
  intro row hr
  rw [memoryRows_eq_threaded] at hr
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr0
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  have hv := threaded_bfs_ver z α t ht
  simp only [SemanticTimestampStrategy.MemoryRowTemplate.encodeRow_ver,
    SemanticTimestampStrategy.MemoryRowTemplate.encodeRow_st]
  exact hv

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.computeTreeBinds_of_nodesOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.memoryTreeBinds_of_nodesOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.assigned_threaded_memoryTreeBinds
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.bindsAt_seed
