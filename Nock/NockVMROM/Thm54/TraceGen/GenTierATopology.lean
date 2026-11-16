/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierATopology.lean

  Raw `fanout`/`childLink` residual on the generated annotated memory
  forest, transported through the LogUp threader, so `execThreaded`
  inhabits `MemoryExactTopology`.

  Compute `childLinkComp` is not claimed here: the generator's OP6
  NTree children are `[condition, taken]` (DFS order) while `sf1`/`sf2`
  are `[taken, condition]` (evalV order), matching the hand-built
  `Op6ConfigK3` tree rather than `dotTree`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierASemantic
import Nock.NockVMROM.Thm54.RawTopologySoundness

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy

variable {K : Type} [Field K]

variable {lmb : K}

noncomputable section

theorem genAnnotatedNounWalk_root_pt (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).1.label.row.2.2.pt =
      (genAnnotatedNounWalk E z lmb n).2
  | .atom a => by
      simp [genAnnotatedNounWalk, NTree.label, gMemRow9]
  | .cell h t => by
      simp [genAnnotatedNounWalk, NTree.label, gMemRow9, annotatedDecPub]

theorem gMemRow9_state (sk : SemanticStrategy.MemoryRowSkeleton) (e : ℕ)
    (z : K) (pub : MemoryTable.Pub K) :
    (gMemRow9 sk e z pub).row.1 = sk.state :=
  rfl

theorem gMemRow9_pt (sk : SemanticStrategy.MemoryRowSkeleton) (e : ℕ)
    (z : K) (pub : MemoryTable.Pub K) :
    (gMemRow9 sk e z pub).row.2.2.pt = pub.pt :=
  rfl

theorem gMemRow9_lc (sk : SemanticStrategy.MemoryRowSkeleton) (e : ℕ)
    (z : K) (pub : MemoryTable.Pub K) :
    (gMemRow9 sk e z pub).row.2.2.lc = pub.lc :=
  rfl

theorem gMemRow9_rc (sk : SemanticStrategy.MemoryRowSkeleton) (e : ℕ)
    (z : K) (pub : MemoryTable.Pub K) :
    (gMemRow9 sk e z pub).row.2.2.rc = pub.rc :=
  rfl

theorem setGenAcc_pt (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.2.pt = g.row.2.2.pt :=
  rfl

theorem setGenAcc_lc (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.2.lc = g.row.2.2.lc :=
  rfl

theorem setGenAcc_rc (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.2.rc = g.row.2.2.rc :=
  rfl

theorem threadGenRow_pt (inp : MemoryTable.Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.2.2.pt = g.row.2.2.pt := by
  rw [threadGenRow_snd, setGenAcc_pt]

theorem threadGenRow_lc (inp : MemoryTable.Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.2.2.lc = g.row.2.2.lc := by
  rw [threadGenRow_snd, setGenAcc_lc]

theorem threadGenRow_rc (inp : MemoryTable.Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.2.2.rc = g.row.2.2.rc := by
  rw [threadGenRow_snd, setGenAcc_rc]

theorem genAnnotatedNounWalk_root_st (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).1.label.row.1 = nounWalkRootState n
  | .atom a => by
      simp [genAnnotatedNounWalk, NTree.label, gMemRow9, memHaltSkel, nounWalkRootState]
  | .cell h t => by
      simp [genAnnotatedNounWalk, NTree.label, gMemRow9, memDecomposeSkel,
        nounWalkRootState]

theorem genAnnotatedNounWalk_children (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).1.children.length = fanoutMem (nounWalkRootState n)
  | .atom a => by
      simp [genAnnotatedNounWalk, NTree.children, fanoutMem, nounWalkRootState]
  | .cell h t => by
      simp [genAnnotatedNounWalk, NTree.children, fanoutMem, nounWalkRootState]

theorem childLinkMem_walk (E : Noun → ComputeTable.FP K) (z : K) (n : Noun) :
    childLinkMem (mapNTree GenMemoryRow.row (genAnnotatedNounWalk E z lmb n).1).label
      (fun j => (mapNTree GenMemoryRow.row (genAnnotatedNounWalk E z lmb n).1).childLabel j) := by
  intro i hi
  cases n with
  | atom a =>
    have hst : (mapNTree GenMemoryRow.row
        (genAnnotatedNounWalk E z lmb (.atom a)).1).label.1 = .halt := by
      rw [mapNTree_label]
      simp only [genAnnotatedNounWalk_root_st, nounWalkRootState]
    rw [hst] at hi
    simp only [fanoutMem] at hi
    exact absurd hi (Nat.not_lt_zero _)
  | cell hd tl =>
    have hch0 :
        (genAnnotatedNounWalk E z lmb (.cell hd tl)).1.children[0]? =
          some (genAnnotatedNounWalk E z lmb hd).1 := by
      simp [genAnnotatedNounWalk, NTree.children_node]
    have hch1 :
        (genAnnotatedNounWalk E z lmb (.cell hd tl)).1.children[1]? =
          some (genAnnotatedNounWalk E z lmb tl).1 := by
      simp [genAnnotatedNounWalk, NTree.children_node]
    have hlc :
        (mapNTree GenMemoryRow.row (genAnnotatedNounWalk E z lmb (.cell hd tl)).1).label.2.2.lc =
          (genAnnotatedNounWalk E z lmb hd).2 := by
      rw [mapNTree_label]
      simp only [genAnnotatedNounWalk, NTree.label, gMemRow9_lc, annotatedDecPub]
    have hrc :
        (mapNTree GenMemoryRow.row (genAnnotatedNounWalk E z lmb (.cell hd tl)).1).label.2.2.rc =
          (genAnnotatedNounWalk E z lmb tl).2 := by
      rw [mapNTree_label]
      simp only [genAnnotatedNounWalk, NTree.label, gMemRow9_rc, annotatedDecPub]
    fin_cases i
    · dsimp
      rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
      simp only [Option.map_some, memCell, hlc]
      simp [mapNTree_label]
      exact genAnnotatedNounWalk_root_pt E z hd
    · dsimp
      rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch1]
      simp only [Option.map_some, memCell, hrc]
      simp [mapNTree_label]
      exact genAnnotatedNounWalk_root_pt E z tl

theorem rawMemoryBinding_walk (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n t, InTree (genAnnotatedNounWalk E z lmb n).1 t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t)
  | n, t, ht => by
    cases n with
    | atom a =>
      cases ht with
      | here =>
        refine ⟨?_, childLinkMem_walk E z (.atom a)⟩
        · rw [mapNTree_label, mapNTree_children, List.length_map,
            genAnnotatedNounWalk_root_st, genAnnotatedNounWalk_children]
      | sub hs _ =>
        simp [genAnnotatedNounWalk, NTree.children] at hs
    | cell h tl =>
      cases ht with
      | here =>
        refine ⟨?_, childLinkMem_walk E z (.cell h tl)⟩
        · rw [mapNTree_label, mapNTree_children, List.length_map,
            genAnnotatedNounWalk_root_st, genAnnotatedNounWalk_children]
      | sub hs hu =>
        simp [genAnnotatedNounWalk, NTree.children_node, List.mem_cons,
          List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact rawMemoryBinding_walk E z h _ hu
        · exact rawMemoryBinding_walk E z tl _ hu

theorem genAnnotatedVerify_root_pt (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    (genAnnotatedVerify E z lmb root child ax ts recordExp).1.label.row.2.2.pt =
      (genAnnotatedVerify E z lmb root child ax ts recordExp).2 := by
  simp [genAnnotatedVerify, NTree.label, gMemRow9, annotatedVerifyPub]

theorem rawMemoryBinding_verify (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedVerify E z lmb root child ax ts recordExp).1 t) :
    RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      have hs : (genAnnotatedVerify E z lmb root child ax ts recordExp).1.label.row.1 =
          .verify_child := by
        simp only [genAnnotatedVerify, NTree.label, gMemRow9_state, memVerifySkelAx]
      have hl : (genAnnotatedVerify E z lmb root child ax ts recordExp).1.children.length = 1 := by
        simp only [genAnnotatedVerify, NTree.children_node, List.length_cons,
          List.length_nil]
      rw [hs, hl, fanoutMem]
    · intro i hi
      have hfan : fanoutMem
          (mapNTree GenMemoryRow.row
            (genAnnotatedVerify E z lmb root child ax ts recordExp).1).label.1 = 1 := by
        rw [mapNTree_label]
        simp only [genAnnotatedVerify, NTree.label, gMemRow9_state, memVerifySkelAx,
          fanoutMem]
      have hch0 :
          (genAnnotatedVerify E z lmb root child ax ts recordExp).1.children[0]? =
            some (genAnnotatedNounWalk E z lmb child).1 := by
        simp [genAnnotatedVerify, NTree.children_node]
      have hlc :
          (mapNTree GenMemoryRow.row
            (genAnnotatedVerify E z lmb root child ax ts recordExp).1).label.2.2.lc =
            (genAnnotatedNounWalk E z lmb child).2 := by
        rw [mapNTree_label]
        simp only [genAnnotatedVerify, NTree.label, gMemRow9_lc, annotatedVerifyPub]
      fin_cases i
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
        simp only [Option.map_some, memCell, hlc]
        simp [mapNTree_label]
        exact genAnnotatedNounWalk_root_pt E z child
      · apply False.elim
        have hi1 : (1 : ℕ) < 1 := by
          have := hi
          rw [hfan] at this
          exact this
        exact Nat.lt_irrefl 1 hi1
  | sub hs hu =>
    simp [genAnnotatedVerify, NTree.children_node, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    subst hs
    exact rawMemoryBinding_walk E z child _ hu

theorem rawMemoryBinding_walk_bfs (E : Noun → ComputeTable.FP K) (z : K) (n : Noun) :
    ∀ t ∈ bfsForest [mapNTree GenMemoryRow.row (genAnnotatedNounWalk E z lmb n).1],
      RawMemoryTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree_singleton] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ _).mp hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  exact rawMemoryBinding_walk E z n u hin

theorem rawMemoryBinding_verify_bfs (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ t ∈ bfsForest [mapNTree GenMemoryRow.row
        (genAnnotatedVerify E z lmb root child ax ts recordExp).1],
      RawMemoryTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree_singleton] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ _).mp hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  exact rawMemoryBinding_verify E z root child ax ts recordExp u hin

def axis2DecNode (E : Noun → ComputeTable.FP K) (z α : K) (hd tl : Noun) (e : ℕ) :
    NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
      (annotatedDecPub E (.cell hd tl) hd tl
        (genAnnotatedVerify E z lmb (.cell hd tl) hd 2 (α ^ e) e).2
        (genAnnotatedNounWalk E z lmb tl).2
        (descentRootState 1) (nounWalkRootState tl) 0 0 lmb))
    [(genAnnotatedVerify E z lmb (.cell hd tl) hd 2 (α ^ e) e).1,
     (genAnnotatedNounWalk E z lmb tl).1]

theorem genAnnotatedRecordTree_axis2_children (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e).children =
      [axis2DecNode (lmb := lmb) E z α hd tl e] := by
  rw [genAnnotatedRecordTree_eq, genAnnotatedDescent_axis2]
  rfl

def axis3DecNode (E : Noun → ComputeTable.FP K) (z α : K) (hd tl : Noun) (e : ℕ) :
    NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
      (annotatedDecPub E (.cell hd tl) hd tl
        (genAnnotatedNounWalk E z lmb hd).2
        (genAnnotatedVerify E z lmb (.cell hd tl) tl 3 (α ^ e) e).2
        (nounWalkRootState hd) (descentRootState 1) 0 0 lmb))
    [(genAnnotatedNounWalk E z lmb hd).1,
     (genAnnotatedVerify E z lmb (.cell hd tl) tl 3 (α ^ e) e).1]

theorem genAnnotatedRecordTree_axis3_children (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e).children =
      [axis3DecNode (lmb := lmb) E z α hd tl e] := by
  rw [genAnnotatedRecordTree_eq, genAnnotatedDescent_axis3]
  rfl

theorem genAnnotatedRecordTree_axis2_root_state (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e).label.row.1 = .read_root := by
  simp only [genAnnotatedRecordTree_eq, NTree.label, gMemRow9_state, memReadSkelAx]

theorem genAnnotatedRecordTree_axis3_root_state (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e).label.row.1 = .read_root := by
  simp only [genAnnotatedRecordTree_eq, NTree.label, gMemRow9_state, memReadSkelAx]

theorem rawMemoryBinding_record_axis2 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    ∀ t, InTree (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e) t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro t ht
  have hcs := genAnnotatedRecordTree_axis2_children (lmb := lmb) E z α hd tl e
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map,
        genAnnotatedRecordTree_axis2_root_state, hcs]
      simp [fanoutMem]
    · intro i hi
      have hfan : fanoutMem
          (mapNTree GenMemoryRow.row
            (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e)).label.1 = 1 := by
        rw [mapNTree_label, genAnnotatedRecordTree_axis2_root_state, fanoutMem]
      have hch0 :
          (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e).children[0]? =
            some (axis2DecNode (lmb := lmb) E z α hd tl e) := by
        simp [hcs]
      have hlc :
          (mapNTree GenMemoryRow.row
            (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e)).label.2.2.lc =
            (annotatedDecPub E (.cell hd tl) hd tl
              (genAnnotatedVerify E z lmb (.cell hd tl) hd 2 (α ^ e) e).2
              (genAnnotatedNounWalk E z lmb tl).2
              (descentRootState 1) (nounWalkRootState tl) 0 0 lmb).pt := by
        rw [mapNTree_label]
        simp only [genAnnotatedRecordTree_eq, genAnnotatedDescent_axis2, NTree.label,
          gMemRow9_lc, annotatedReadPub]
      fin_cases i
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
        simp only [Option.map_some, memCell, hlc]
        simp [mapNTree_label, NTree.label, gMemRow9_pt, axis2DecNode]
      · apply False.elim
        have hi1 : (1 : ℕ) < 1 := by
          have := hi
          rw [hfan] at this
          exact this
        exact Nat.lt_irrefl 1 hi1
  | sub hs hu =>
    rw [hcs] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    cases hu with
    | here =>
      refine ⟨?_, ?_⟩
      · rw [mapNTree_label, mapNTree_children]
        simp only [axis2DecNode, NTree.label, NTree.children_node, List.length_map,
          List.length_cons, List.length_nil, gMemRow9_state, memDecomposeSkel, fanoutMem]
      · intro i hi
        have hch0 : (axis2DecNode (lmb := lmb) E z α hd tl e).children[0]? =
            some (genAnnotatedVerify E z lmb (.cell hd tl) hd 2 (α ^ e) e).1 := by
          simp [axis2DecNode, NTree.children_node]
        have hch1 : (axis2DecNode (lmb := lmb) E z α hd tl e).children[1]? =
            some (genAnnotatedNounWalk E z lmb tl).1 := by
          simp [axis2DecNode, NTree.children_node]
        have hlc :
            (mapNTree GenMemoryRow.row (axis2DecNode (lmb := lmb) E z α hd tl e)).label.2.2.lc =
              (genAnnotatedVerify E z lmb (.cell hd tl) hd 2 (α ^ e) e).2 := by
          rw [mapNTree_label]
          simp only [axis2DecNode, NTree.label, gMemRow9_lc, annotatedDecPub]
        have hrc :
            (mapNTree GenMemoryRow.row (axis2DecNode (lmb := lmb) E z α hd tl e)).label.2.2.rc =
              (genAnnotatedNounWalk E z lmb tl).2 := by
          rw [mapNTree_label]
          simp only [axis2DecNode, NTree.label, gMemRow9_rc, annotatedDecPub]
        fin_cases i
        · dsimp
          rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
          simp only [Option.map_some, memCell, hlc]
          simp [mapNTree_label, genAnnotatedVerify_root_pt]
        · dsimp
          rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch1]
          simp only [Option.map_some, memCell, hrc]
          simp [mapNTree_label, genAnnotatedNounWalk_root_pt]
    | sub hs2 hu2 =>
      simp only [axis2DecNode, NTree.children_node, List.mem_cons, List.not_mem_nil,
        or_false] at hs2
      rcases hs2 with rfl | rfl
      · exact rawMemoryBinding_verify E z (.cell hd tl) hd 2 (α ^ e) e _ hu2
      · exact rawMemoryBinding_walk E z tl _ hu2

theorem rawMemoryBinding_record_axis3 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    ∀ t, InTree (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e) t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro t ht
  have hcs := genAnnotatedRecordTree_axis3_children (lmb := lmb) E z α hd tl e
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map,
        genAnnotatedRecordTree_axis3_root_state, hcs]
      simp [fanoutMem]
    · intro i hi
      have hfan : fanoutMem
          (mapNTree GenMemoryRow.row
            (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e)).label.1 = 1 := by
        rw [mapNTree_label, genAnnotatedRecordTree_axis3_root_state, fanoutMem]
      have hch0 :
          (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e).children[0]? =
            some (axis3DecNode (lmb := lmb) E z α hd tl e) := by
        simp [hcs]
      have hlc :
          (mapNTree GenMemoryRow.row
            (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e)).label.2.2.lc =
            (annotatedDecPub E (.cell hd tl) hd tl
              (genAnnotatedNounWalk E z lmb hd).2
              (genAnnotatedVerify E z lmb (.cell hd tl) tl 3 (α ^ e) e).2
              (nounWalkRootState hd) (descentRootState 1) 0 0 lmb).pt := by
        rw [mapNTree_label]
        simp only [genAnnotatedRecordTree_eq, genAnnotatedDescent_axis3, NTree.label,
          gMemRow9_lc, annotatedReadPub]
      fin_cases i
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
        simp only [Option.map_some, memCell, hlc]
        simp [mapNTree_label, NTree.label, gMemRow9_pt, axis3DecNode]
      · apply False.elim
        have hi1 : (1 : ℕ) < 1 := by
          have := hi
          rw [hfan] at this
          exact this
        exact Nat.lt_irrefl 1 hi1
  | sub hs hu =>
    rw [hcs] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    cases hu with
    | here =>
      refine ⟨?_, ?_⟩
      · rw [mapNTree_label, mapNTree_children]
        simp only [axis3DecNode, NTree.label, NTree.children_node, List.length_map,
          List.length_cons, List.length_nil, gMemRow9_state, memDecomposeSkel, fanoutMem]
      · intro i hi
        have hch0 : (axis3DecNode (lmb := lmb) E z α hd tl e).children[0]? =
            some (genAnnotatedNounWalk E z lmb hd).1 := by
          simp [axis3DecNode, NTree.children_node]
        have hch1 : (axis3DecNode (lmb := lmb) E z α hd tl e).children[1]? =
            some (genAnnotatedVerify E z lmb (.cell hd tl) tl 3 (α ^ e) e).1 := by
          simp [axis3DecNode, NTree.children_node]
        have hlc :
            (mapNTree GenMemoryRow.row (axis3DecNode (lmb := lmb) E z α hd tl e)).label.2.2.lc =
              (genAnnotatedNounWalk E z lmb hd).2 := by
          rw [mapNTree_label]
          simp only [axis3DecNode, NTree.label, gMemRow9_lc, annotatedDecPub]
        have hrc :
            (mapNTree GenMemoryRow.row (axis3DecNode (lmb := lmb) E z α hd tl e)).label.2.2.rc =
              (genAnnotatedVerify E z lmb (.cell hd tl) tl 3 (α ^ e) e).2 := by
          rw [mapNTree_label]
          simp only [axis3DecNode, NTree.label, gMemRow9_rc, annotatedDecPub]
        fin_cases i
        · dsimp
          rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
          simp only [Option.map_some, memCell, hlc]
          simp [mapNTree_label, genAnnotatedNounWalk_root_pt]
        · dsimp
          rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch1]
          simp only [Option.map_some, memCell, hrc]
          simp [mapNTree_label, genAnnotatedVerify_root_pt]
    | sub hs2 hu2 =>
      simp only [axis3DecNode, NTree.children_node, List.mem_cons, List.not_mem_nil,
        or_false] at hs2
      rcases hs2 with rfl | rfl
      · exact rawMemoryBinding_walk E z hd _ hu2
      · exact rawMemoryBinding_verify E z (.cell hd tl) tl 3 (α ^ e) e _ hu2

theorem rawMemoryBinding_record_axis2_bfs (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ t ∈ bfsForest [mapNTree GenMemoryRow.row
        (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e)],
      RawMemoryTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree_singleton] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ _).mp hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  exact rawMemoryBinding_record_axis2 E z α hd tl e u hin

theorem rawMemoryBinding_record_axis3_bfs (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ t ∈ bfsForest [mapNTree GenMemoryRow.row
        (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e)],
      RawMemoryTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree_singleton] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ _).mp hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  exact rawMemoryBinding_record_axis3 E z α hd tl e u hin

/-! ## Chained axis-3 then axis-2 -/

def chain32InnerDecPub (E : Noun → ComputeTable.FP K) (z α : K)
    (hd2 tl2 : Noun) (e2 : ℕ) : MemoryTable.Pub K :=
  annotatedDecPub E (.cell hd2 tl2) hd2 tl2
    (genAnnotatedVerify E z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
    (genAnnotatedNounWalk E z lmb tl2).2
    (descentContRootState .verify_child 1) (nounWalkRootState tl2) 0 0 lmb

def chain32InnerDec (E : Noun → ComputeTable.FP K) (z α : K)
    (hd2 tl2 : Noun) (e2 : ℕ) : NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memDecomposeSkel (.cell hd2 tl2) hd2 tl2) 0 z
      (chain32InnerDecPub (lmb := lmb) E z α hd2 tl2 e2))
    [(genAnnotatedVerify E z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1,
     (genAnnotatedNounWalk E z lmb tl2).1]

def chain32InnerVerifyPub (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : MemoryTable.Pub K :=
  annotatedVerifyPub E (.cell hd1 (.cell hd2 tl2)) (.cell hd2 tl2) 3 (α ^ e1)
    (chain32InnerDecPub (lmb := lmb) E z α hd2 tl2 e2).pt 0 0 lmb

def chain32InnerVerify (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memVerifySkelAx
        (.cell hd1 (.cell hd2 tl2)) (.cell hd2 tl2) 3) e1 z
      (chain32InnerVerifyPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))
    [chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2]

def chain32InnerReadPub (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : MemoryTable.Pub K :=
  annotatedReadPub E (.cell hd2 tl2) hd2 2 (α ^ e2)
    (chain32InnerVerifyPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).pt 0 0 lmb

def chain32InnerRead (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memReadSkelAx (.cell hd2 tl2) hd2 2) e2 z
      (chain32InnerReadPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))
    [chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2]

def chain32OuterDecPub (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : MemoryTable.Pub K :=
  annotatedDecPub E (.cell hd1 (.cell hd2 tl2)) hd1 (.cell hd2 tl2)
    (genAnnotatedNounWalk E z lmb hd1).2
    (chain32InnerReadPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).pt
    (nounWalkRootState hd1) (descentContRootState .read_root 1) 0 0 lmb

def chain32OuterDec (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memDecomposeSkel
        (.cell hd1 (.cell hd2 tl2)) hd1 (.cell hd2 tl2)) 0 z
      (chain32OuterDecPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))
    [(genAnnotatedNounWalk E z lmb hd1).1,
     chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2]

def chain32RootPub (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : MemoryTable.Pub K :=
  annotatedReadPub E (.cell hd1 (.cell hd2 tl2)) (.cell hd2 tl2) 3 (α ^ e1)
    (chain32OuterDecPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).pt 0 0 lmb

def chain32Root (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memReadSkelAx
        (.cell hd1 (.cell hd2 tl2)) (.cell hd2 tl2) 3) e1 z
      (chain32RootPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))
    [chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2]

theorem genAnnotatedChainedInner_axis3_axis2
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    genAnnotatedChainedInner E z α lmb
      ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
      [⟨.cell hd2 tl2, hd2, 2, e2⟩] =
      ([chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2],
        (chain32InnerReadPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).pt) := by
  unfold genAnnotatedChainedInner
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState]
  rw [genAnnotatedDescentCont_axis2]
  rfl

theorem genAnnotatedChainedTree_axis3_axis2_eq
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] =
      some (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) := by
  rw [genAnnotatedChainedTree_pair]
  simp only [MemRecordReq.root, MemRecordReq.child, MemRecordReq.axis,
    MemRecordReq.recordExp, chainedInnerRootState]
  rw [genAnnotatedChainedInner_axis3_axis2, genAnnotatedDescentCont_axis3]
  rfl

theorem rawMemoryBinding_chain32InnerDec
    (E : Noun → ComputeTable.FP K) (z α : K) (hd2 tl2 : Noun) (e2 : ℕ) :
    ∀ t, InTree (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2) t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro t ht
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children]
      simp only [chain32InnerDec, NTree.label, NTree.children_node, List.length_map,
        List.length_cons, List.length_nil, gMemRow9_state, memDecomposeSkel, fanoutMem]
    · intro i hi
      have hch0 : (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2).children[0]? =
          some (genAnnotatedVerify E z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1 := by
        simp [chain32InnerDec, NTree.children_node]
      have hch1 : (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2).children[1]? =
          some (genAnnotatedNounWalk E z lmb tl2).1 := by
        simp [chain32InnerDec, NTree.children_node]
      have hlc :
          (mapNTree GenMemoryRow.row (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2)).label.2.2.lc =
            (genAnnotatedVerify E z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2 := by
        rw [mapNTree_label]
        simp only [chain32InnerDec, NTree.label, gMemRow9_lc, chain32InnerDecPub,
          annotatedDecPub]
      have hrc :
          (mapNTree GenMemoryRow.row (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2)).label.2.2.rc =
            (genAnnotatedNounWalk E z lmb tl2).2 := by
        rw [mapNTree_label]
        simp only [chain32InnerDec, NTree.label, gMemRow9_rc, chain32InnerDecPub,
          annotatedDecPub]
      fin_cases i
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
        simp only [Option.map_some, memCell, hlc]
        simp [mapNTree_label, genAnnotatedVerify_root_pt]
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch1]
        simp only [Option.map_some, memCell, hrc]
        simp [mapNTree_label, genAnnotatedNounWalk_root_pt]
  | sub hs hu =>
    simp only [chain32InnerDec, NTree.children_node, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with rfl | rfl
    · exact rawMemoryBinding_verify E z (.cell hd2 tl2) hd2 2 (α ^ e2) e2 _ hu
    · exact rawMemoryBinding_walk E z tl2 _ hu

theorem rawMemoryBinding_chain32InnerVerify
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ t, InTree (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro t ht
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children]
      simp only [chain32InnerVerify, NTree.label, NTree.children_node, List.length_map,
        List.length_cons, List.length_nil, gMemRow9_state, memVerifySkelAx, fanoutMem]
    · intro i hi
      have hfan : fanoutMem
          (mapNTree GenMemoryRow.row
            (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)).label.1 = 1 := by
        rw [mapNTree_label]
        simp only [chain32InnerVerify, NTree.label, gMemRow9_state, memVerifySkelAx,
          fanoutMem]
      have hch0 : (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).children[0]? =
          some (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2) := by
        simp [chain32InnerVerify, NTree.children_node]
      have hlc :
          (mapNTree GenMemoryRow.row
            (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)).label.2.2.lc =
            (chain32InnerDecPub (lmb := lmb) E z α hd2 tl2 e2).pt := by
        rw [mapNTree_label]
        simp only [chain32InnerVerify, NTree.label, gMemRow9_lc, chain32InnerVerifyPub,
          annotatedVerifyPub]
      fin_cases i
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
        simp only [Option.map_some, memCell, hlc]
        simp [mapNTree_label, NTree.label, gMemRow9_pt, chain32InnerDec, chain32InnerDecPub]
      · apply False.elim
        have hi1 : (1 : ℕ) < 1 := by
          have := hi
          rw [hfan] at this
          exact this
        exact Nat.lt_irrefl 1 hi1
  | sub hs hu =>
    simp only [chain32InnerVerify, NTree.children_node, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    subst hs
    exact rawMemoryBinding_chain32InnerDec E z α hd2 tl2 e2 _ hu

theorem rawMemoryBinding_chain32InnerRead
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ t, InTree (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro t ht
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children]
      simp only [chain32InnerRead, NTree.label, NTree.children_node, List.length_map,
        List.length_cons, List.length_nil, gMemRow9_state, memReadSkelAx, fanoutMem]
    · intro i hi
      have hfan : fanoutMem
          (mapNTree GenMemoryRow.row
            (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)).label.1 = 1 := by
        rw [mapNTree_label]
        simp only [chain32InnerRead, NTree.label, gMemRow9_state, memReadSkelAx,
          fanoutMem]
      have hch0 : (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).children[0]? =
          some (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) := by
        simp [chain32InnerRead, NTree.children_node]
      have hlc :
          (mapNTree GenMemoryRow.row
            (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)).label.2.2.lc =
            (chain32InnerVerifyPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).pt := by
        rw [mapNTree_label]
        simp only [chain32InnerRead, NTree.label, gMemRow9_lc, chain32InnerReadPub,
          annotatedReadPub]
      fin_cases i
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
        simp only [Option.map_some, memCell, hlc]
        simp [mapNTree_label, NTree.label, gMemRow9_pt, chain32InnerVerify,
          chain32InnerVerifyPub]
      · apply False.elim
        have hi1 : (1 : ℕ) < 1 := by
          have := hi
          rw [hfan] at this
          exact this
        exact Nat.lt_irrefl 1 hi1
  | sub hs hu =>
    simp only [chain32InnerRead, NTree.children_node, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    subst hs
    exact rawMemoryBinding_chain32InnerVerify E z α hd1 hd2 tl2 e1 e2 _ hu

theorem rawMemoryBinding_chain32OuterDec
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ t, InTree (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro t ht
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children]
      simp only [chain32OuterDec, NTree.label, NTree.children_node, List.length_map,
        List.length_cons, List.length_nil, gMemRow9_state, memDecomposeSkel, fanoutMem]
    · intro i hi
      have hch0 : (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).children[0]? =
          some (genAnnotatedNounWalk E z lmb hd1).1 := by
        simp [chain32OuterDec, NTree.children_node]
      have hch1 : (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).children[1]? =
          some (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) := by
        simp [chain32OuterDec, NTree.children_node]
      have hlc :
          (mapNTree GenMemoryRow.row
            (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)).label.2.2.lc =
            (genAnnotatedNounWalk E z lmb hd1).2 := by
        rw [mapNTree_label]
        simp only [chain32OuterDec, NTree.label, gMemRow9_lc, chain32OuterDecPub,
          annotatedDecPub]
      have hrc :
          (mapNTree GenMemoryRow.row
            (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)).label.2.2.rc =
            (chain32InnerReadPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).pt := by
        rw [mapNTree_label]
        simp only [chain32OuterDec, NTree.label, gMemRow9_rc, chain32OuterDecPub,
          annotatedDecPub]
      fin_cases i
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
        simp only [Option.map_some, memCell, hlc]
        simp [mapNTree_label, genAnnotatedNounWalk_root_pt]
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch1]
        simp only [Option.map_some, memCell, hrc]
        simp [mapNTree_label, NTree.label, gMemRow9_pt, chain32InnerRead,
          chain32InnerReadPub]
  | sub hs hu =>
    simp only [chain32OuterDec, NTree.children_node, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with rfl | rfl
    · exact rawMemoryBinding_walk E z hd1 _ hu
    · exact rawMemoryBinding_chain32InnerRead E z α hd1 hd2 tl2 e1 e2 _ hu

theorem rawMemoryBinding_chained_axis3_axis2
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ t, InTree (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro t ht
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children]
      simp only [chain32Root, NTree.label, NTree.children_node, List.length_map,
        List.length_cons, List.length_nil, gMemRow9_state, memReadSkelAx, fanoutMem]
    · intro i hi
      have hfan : fanoutMem
          (mapNTree GenMemoryRow.row
            (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)).label.1 = 1 := by
        rw [mapNTree_label]
        simp only [chain32Root, NTree.label, gMemRow9_state, memReadSkelAx, fanoutMem]
      have hch0 : (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).children[0]? =
          some (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) := by
        simp [chain32Root, NTree.children_node]
      have hlc :
          (mapNTree GenMemoryRow.row
            (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)).label.2.2.lc =
            (chain32OuterDecPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).pt := by
        rw [mapNTree_label]
        simp only [chain32Root, NTree.label, gMemRow9_lc, chain32RootPub,
          annotatedReadPub]
      fin_cases i
      · dsimp
        rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch0]
        simp only [Option.map_some, memCell, hlc]
        simp [mapNTree_label, NTree.label, gMemRow9_pt, chain32OuterDec,
          chain32OuterDecPub]
      · apply False.elim
        have hi1 : (1 : ℕ) < 1 := by
          have := hi
          rw [hfan] at this
          exact this
        exact Nat.lt_irrefl 1 hi1
  | sub hs hu =>
    simp only [chain32Root, NTree.children_node, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    subst hs
    exact rawMemoryBinding_chain32OuterDec E z α hd1 hd2 tl2 e1 e2 _ hu

theorem rawMemoryBinding_chained_axis3_axis2_of_some
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t) :
    ∀ u, InTree t u →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row u) := by
  have heq := genAnnotatedChainedTree_axis3_axis2_eq (lmb := lmb) E z α hd1 hd2 tl2 e1 e2
  rw [heq] at ht
  injection ht with ht
  subst t
  exact rawMemoryBinding_chained_axis3_axis2 E z α hd1 hd2 tl2 e1 e2

theorem rawMemoryBinding_row_singleton_axis2
    (E : Noun → ComputeTable.FP K) (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ u ∈ genRowMemForest E z α lmb [⟨.cell hd tl, hd, 2, e⟩],
      ∀ t, InTree u t →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro u hu t ht
  simp [genRowMemForest_singleton] at hu
  subst u
  exact rawMemoryBinding_record_axis2 E z α hd tl e t ht

theorem rawMemoryBinding_row_singleton_axis3
    (E : Noun → ComputeTable.FP K) (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ u ∈ genRowMemForest E z α lmb [⟨.cell hd tl, tl, 3, e⟩],
      ∀ t, InTree u t →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro u hu t ht
  simp [genRowMemForest_singleton] at hu
  subst u
  exact rawMemoryBinding_record_axis3 E z α hd tl e t ht

theorem rawMemoryBinding_row_chain32
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ u ∈ genRowMemForest E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩],
      ∀ t, InTree u t →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro u hu t ht
  unfold genRowMemForest at hu
  have heq := genAnnotatedChainedTree_axis3_axis2_eq (lmb := lmb) E z α hd1 hd2 tl2 e1 e2
  simp [heq] at hu
  subst u
  exact rawMemoryBinding_chained_axis3_axis2 E z α hd1 hd2 tl2 e1 e2 t ht

theorem rawMemoryBinding_row_three_chain32
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 hd3 tl3 : Noun) (e1 e2 e3 : ℕ) :
    ∀ u ∈ genRowMemForest E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩,
       ⟨.cell hd3 tl3, hd3, 2, e3⟩],
      ∀ t, InTree u t →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro u hu t ht
  unfold genRowMemForest at hu
  have heq := genAnnotatedChainedTree_axis3_axis2_eq (lmb := lmb) E z α hd1 hd2 tl2 e1 e2
  simp [heq, List.mem_append, List.mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact rawMemoryBinding_chained_axis3_axis2 E z α hd1 hd2 tl2 e1 e2 t ht
  · exact rawMemoryBinding_record_axis2 E z α hd3 tl3 e3 t ht

theorem genMemForestFromTree_of_rowBinding (E : Noun → ComputeTable.FP K)
    (z α : K) (t : NTree (GenComputeRow K))
    (H : ∀ n, InTree t n →
      ∀ u ∈ genRowMemForest E z α lmb (extractNodeReqs n.label),
        ∀ v, InTree u v →
          RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v))
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree E z α lmb t)
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) := by
  suffices ∀ N t,
      NTree.size t ≤ N →
      (∀ n, InTree t n →
        ∀ u ∈ genRowMemForest E z α lmb (extractNodeReqs n.label),
          ∀ v, InTree u v →
            RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v)) →
      ∀ u ∈ genMemForestFromTree E z α lmb t,
        ∀ v, InTree u v →
          RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) from
    this (NTree.size t) t le_rfl H u hu v hv
  intro N
  induction N with
  | zero =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [NTree.size] at ht
  | succ N ih =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [genMemForestFromTree] at hu
      rcases hu with hu | hu
      · exact H (.node g cs) (InTree.here _) u hu v hv
      · have recList :
            ∀ cs', (∀ c ∈ cs', c ∈ cs) →
              (∀ t ∈ cs', NTree.size t ≤ N) →
              (∀ t ∈ cs', ∀ n, InTree t n →
                ∀ u ∈ genRowMemForest E z α lmb (extractNodeReqs n.label),
                  ∀ v, InTree u v →
                    RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v)) →
              ∀ u ∈ genMemForestFromList E z α lmb cs',
                ∀ v, InTree u v →
                  RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) := by
          intro cs' hsub hsz H' u' hu' v' hv'
          induction cs' generalizing u' v' with
          | nil => simp [genMemForestFromList] at hu'
          | cons c rest ihcs =>
            simp [genMemForestFromList] at hu'
            rcases hu' with hu' | hu'
            · exact ih c (hsz c (by simp))
                (fun n hn => H' c (by simp) n hn) u' hu' v' hv'
            · refine ihcs ?_ ?_ ?_ u' hu' v' hv'
              · intro c' hc'; exact hsub c' (List.mem_cons_of_mem _ hc')
              · intro t htt; exact hsz t (List.mem_cons_of_mem _ htt)
              · intro t htt; exact H' t (List.mem_cons_of_mem _ htt)
        refine recList cs (fun _ h => h) ?_
          (fun t ht n hn => H n (InTree.sub ht hn)) u hu v hv
        intro c hc
        have hin : NTree.size c ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hsum : NTree.size c ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        simp [NTree.size] at ht
        omega

theorem assigned_rowBinding (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTree (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTree (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTree (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTree (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) i hi']
  rcases dot_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTree (K := K)))[0] = (dotTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTree, skelNode, extractNodeReqsAux_cons3]
    exact rawMemoryBinding_row_three_chain32 (encC z) z α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 2)
  · have hget : (bfsRows (dotTree (K := K)))[1] = (dotCondTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1) (.atom 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[2] = (dotOp2Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact rawMemoryBinding_row_chain32 (encC z) z α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 1)
  · have hget : (bfsRows (dotTree (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1)
      (.cell (.atom 0) (.atom 1))
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1) dotOp9Formula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact rawMemoryBinding_row_three_chain32 (encC z) z α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 2)
  · have hget : (bfsRows (dotTree (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1) dotCore
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1) (.atom 3)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0)

theorem assignedForest_binding (z α : K)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))))
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) :=
  genMemForestFromTree_of_rowBinding (encC z) z α _
    (assigned_rowBinding z α) u hu v hv

theorem assignedForest_bfs_binding (z α : K) :
    ∀ t ∈ bfsForest ((genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTree (K := K)))).map (mapNTree GenMemoryRow.row)),
      RawMemoryTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ _).mp hu
  exact assignedForest_binding z α r hr u hin

/-! ## AIR-ordered memory topology -/

theorem assigned_rowBinding_air (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTreeAir (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTreeAir (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTreeAir (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTreeAir (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) i hi']
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTreeAir (K := K)))[0] = (dotTreeAir (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTreeAir, skelNode, extractNodeReqsAux_cons3]
    exact rawMemoryBinding_row_three_chain32 (encC z) z α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 2)
  · have hget : (bfsRows (dotTreeAir (K := K)))[1] = (dotOp2Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact rawMemoryBinding_row_chain32 (encC z) z α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 1)
  · have hget : (bfsRows (dotTreeAir (K := K)))[2] = (dotCondTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1) (.atom 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1)
      (.cell (.atom 0) (.atom 1))
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1) dotOp9Formula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact rawMemoryBinding_row_three_chain32 (encC z) z α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 2)
  · have hget : (bfsRows (dotTreeAir (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1) dotCore
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact rawMemoryBinding_row_singleton_axis3 (encC z) z α (.atom 1) (.atom 3)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0)

theorem assignedForest_binding_air (z α : K)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTreeAir (K := K))))
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) :=
  genMemForestFromTree_of_rowBinding (encC z) z α _
    (assigned_rowBinding_air z α) u hu v hv

theorem assignedForest_bfs_binding_air (z α : K) :
    ∀ t ∈ bfsForest ((genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTreeAir (K := K)))).map (mapNTree GenMemoryRow.row)),
      RawMemoryTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ _).mp hu
  exact assignedForest_binding_air z α r hr u hin

/-! ## LogUp threader preserves topology -/

def memTopo (g : GenMemoryRow K) :
    MemoryTable.MState × MemoryTable.Cell K × MemoryTable.Cell K ×
      MemoryTable.Cell K :=
  (g.row.1, g.row.2.2.pt, g.row.2.2.lc, g.row.2.2.rc)

theorem memTopo_setGenAcc (g : GenMemoryRow K) (a b : K) :
    memTopo (setGenAcc g a b) = memTopo g := by
  simp only [memTopo, setGenAcc_row1, setGenAcc_pt, setGenAcc_lc, setGenAcc_rc]

theorem threadGenRow_memTopo (inp : MemoryTable.Inputs K) (acc : K)
    (g : GenMemoryRow K) :
    memTopo (threadGenRow inp acc g).2 = memTopo g := by
  rw [threadGenRow_snd, memTopo_setGenAcc]

theorem threadGenRows_map_memTopo (inp : MemoryTable.Inputs K) :
    ∀ acc gs, (threadGenRows inp acc gs).map memTopo = gs.map memTopo
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows_cons, threadGenRow_memTopo]
      exact threadGenRows_map_memTopo inp (threadGenRow inp acc g).1 gs

omit [Field K] in
theorem flatMap_children_mapNTree' {α β} (f : α → β) :
    ∀ ts : List (NTree α),
      (ts.map (mapNTree f)).flatMap NTree.children =
        (ts.flatMap NTree.children).map (mapNTree f)
  | [] => rfl
  | t :: rest => by
      simp [List.flatMap_cons, mapNTree_children,
        flatMap_children_mapNTree' f rest]

omit [Field K] in
theorem zipLevel_mapNTree {α β} (f : α → β) :
    ∀ ts : List (NTree α), ∀ labs,
      (zipLevel ts labs).map (mapNTree f) =
        zipLevel (ts.map (mapNTree f)) (labs.map f)
  | [], _ => by simp [zipLevel]
  | ts, [] => by simp [zipLevel, zipLevel_nil_labs]
  | .node _ cs :: rest, _ :: labs => by
      simp [zipLevel_cons, mapNTree, zipLevel_mapNTree f rest labs]

omit [Field K] in
theorem graft_mapNTree {α β} (f : α → β) :
    ∀ ts kids : List (NTree α),
      (graft ts kids).map (mapNTree f) =
        graft (ts.map (mapNTree f)) (kids.map (mapNTree f))
  | [], _ => by simp [graft]
  | .node lbl cs :: rest, kids => by
      simp [graft, mapNTree, List.map_take]
      rw [← List.map_drop]
      exact graft_mapNTree f rest (kids.drop cs.length)

omit [Field K] in
theorem zipBfs_mapNTree {α β} (f : α → β) :
    ∀ ts : List (NTree α), ∀ labs,
      (zipBfs ts labs).map (mapNTree f) =
        zipBfs (ts.map (mapNTree f)) (labs.map f) := by
  intro ts labs
  suffices ∀ N ts, totalSize ts ≤ N → ∀ labs,
      (zipBfs ts labs).map (mapNTree f) =
        zipBfs (ts.map (mapNTree f)) (labs.map f) from
    this (totalSize ts) ts le_rfl labs
  intro N
  induction N with
  | zero =>
    intro ts ht labs
    have : ts = [] := by
      cases ts with
      | nil => rfl
      | cons t rest =>
        have : 1 ≤ t.size := by
          cases t with
          | node _ _ => simp [NTree.size]
        rw [totalSize_cons] at ht
        omega
    subst this
    simp [zipBfs_nil]
  | succ N ih =>
    intro ts ht labs
    match ts with
    | [] => simp [zipBfs_nil]
    | t :: rest =>
      rw [zipBfs_cons, graft_mapNTree, zipLevel_mapNTree]
      simp only [List.map_cons]
      rw [zipBfs_cons]
      have hsz : totalSize ((t :: rest).flatMap NTree.children) ≤ N := by
        have h := totalSize_flatMap_children (t :: rest)
        simp only [List.length_cons] at h
        omega
      congr 1
      rw [ih _ hsz]
      congr 1
      · exact (flatMap_children_mapNTree' f (t :: rest)).symm
      · simp [List.map_drop]

theorem threadGenForest_map_memTopo (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    (threadGenForest inp acc forest).map (mapNTree memTopo) =
      forest.map (mapNTree memTopo) := by
  unfold threadGenForest
  rw [zipBfs_mapNTree, threadGenRows_map_memTopo]
  have hlabs :
      ((bfsForest forest).map NTree.label).map memTopo =
        (bfsForest (forest.map (mapNTree memTopo))).map NTree.label := by
    rw [bfsForest_mapNTree, List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    exact (mapNTree_label memTopo t).symm
  rw [hlabs, zipBfs_self]

theorem threadGenForest_bfs_memTopo (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    (bfsForest (threadGenForest inp acc forest)).map (mapNTree memTopo) =
      (bfsForest forest).map (mapNTree memTopo) := by
  rw [← bfsForest_mapNTree, threadGenForest_map_memTopo, bfsForest_mapNTree]

theorem binding_of_memTopo (t u : NTree (GenMemoryRow K))
    (heq : mapNTree memTopo t = mapNTree memTopo u)
    (hb : RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t)) :
    RawMemoryTopologyBinding (mapNTree GenMemoryRow.row u) := by
  cases t with
  | node gt cs =>
    cases u with
    | node gu ds =>
      have hlab : memTopo gt = memTopo gu := by
        simpa [mapNTree] using congrArg NTree.label heq
      have hcs : cs.map (mapNTree memTopo) = ds.map (mapNTree memTopo) := by
        simpa [mapNTree] using congrArg NTree.children heq
      have hlen : cs.length = ds.length := by
        simpa using congrArg List.length hcs
      have hst : gt.row.1 = gu.row.1 := by
        simpa [memTopo] using congrArg (fun p : MemoryTable.MState × _ × _ × _ => p.1) hlab
      have hlc : gt.row.2.2.lc = gu.row.2.2.lc := by
        simpa [memTopo] using
          congrArg (fun p : MemoryTable.MState × _ × _ × _ => p.2.2.1) hlab
      have hrc : gt.row.2.2.rc = gu.row.2.2.rc := by
        simpa [memTopo] using
          congrArg (fun p : MemoryTable.MState × _ × _ × _ => p.2.2.2) hlab
      have hfan : fanoutMem gt.row.1 = cs.length := by
        have := hb.1
        simp [mapNTree] at this
        exact this
      refine ⟨?_, ?_⟩
      · simp [mapNTree]
        rw [← hst, ← hlen]
        exact hfan
      · intro i hi
        have hilt : (i : ℕ) < ds.length := by
          have hfanU : fanoutMem
              (mapNTree GenMemoryRow.row (.node gu ds)).label.1 = ds.length := by
            simp [mapNTree]
            rw [← hst, ← hlen]
            exact hfan
          have := hi
          rw [hfanU] at this
          exact this
        have hch :
            ((mapNTree GenMemoryRow.row (.node gu ds)).childLabel i).map
              (fun c => c.2.2.pt) =
            ((mapNTree GenMemoryRow.row (.node gt cs)).childLabel i).map
              (fun c => c.2.2.pt) := by
          rw [mapNTree_childLabel, mapNTree_childLabel]
          simp only [NTree.childLabel, NTree.childOpt, Option.map_map]
          have hget :
              (cs[(i : ℕ)]?).map (mapNTree memTopo) =
                (ds[(i : ℕ)]?).map (mapNTree memTopo) := by
            simpa [List.getElem?_map] using congrArg (fun l => l[(i : ℕ)]?) hcs
          cases hcs_i : cs[(i : ℕ)]? with
          | none =>
            have hds_i : ds[(i : ℕ)]? = none := by
              simpa [hcs_i] using hget.symm
            simp [hcs_i, hds_i]
          | some c =>
            cases hds_i : ds[(i : ℕ)]? with
            | none =>
              simp [hcs_i, hds_i] at hget
            | some d =>
              have hcd : mapNTree memTopo c = mapNTree memTopo d := by
                simpa [hcs_i, hds_i] using hget
              have hpt : c.label.row.2.2.pt = d.label.row.2.2.pt := by
                have := congrArg NTree.label hcd
                simp [mapNTree_label, memTopo] at this
                exact this.2.1
              simp [hcs_i, hds_i, Function.comp, mapNTree_label, hpt]
        have hcell :
            memCell (mapNTree GenMemoryRow.row (.node gu ds)).label i =
              memCell (mapNTree GenMemoryRow.row (.node gt cs)).label i := by
          fin_cases i
          · simp [memCell, mapNTree_label, hlc]
          · simp [memCell, mapNTree_label, hrc]
        have hlink := hb.2 i (by
          simpa [mapNTree_label, hst] using hi)
        rw [hch, hcell]
        exact hlink

theorem threadGenForest_bfs_binding (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest (forest.map (mapNTree GenMemoryRow.row)),
      RawMemoryTopologyBinding t) :
    ∀ t ∈ bfsForest ((threadGenForest inp acc forest).map
        (mapNTree GenMemoryRow.row)),
      RawMemoryTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree] at ht
  obtain ⟨tth, hth, rfl⟩ := List.mem_map.mp ht
  have hmem :
      mapNTree memTopo tth ∈
        (bfsForest (threadGenForest inp acc forest)).map (mapNTree memTopo) :=
    List.mem_map.mpr ⟨tth, hth, rfl⟩
  rw [threadGenForest_bfs_memTopo] at hmem
  obtain ⟨u, hu, heq⟩ := List.mem_map.mp hmem
  have hbu : RawMemoryTopologyBinding (mapNTree GenMemoryRow.row u) := by
    apply H
    rw [bfsForest_mapNTree]
    exact List.mem_map.mpr ⟨u, hu, rfl⟩
  exact binding_of_memTopo u tth heq hbu

/-- The Form R row encode preserves the local memory topology binding (it only rewrites
    `mem`/`cprime?`/`lambda?`; state, `pt`, `lc`, `rc` and the child count are untouched). -/
theorem rawMemoryBinding_encodeRow
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (h : RawMemoryTopologyBinding t) :
    RawMemoryTopologyBinding
      (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb) t) := by
  obtain ⟨hf, hl⟩ := h
  refine ⟨?_, ?_⟩
  · simpa [mapNTree_label, mapNTree_children] using hf
  · intro i hi
    have hi' : (i : ℕ) < fanoutMem t.label.1 := by simpa [mapNTree_label] using hi
    have hl' := hl i hi'
    have hcomp : ((fun c : MemoryTable.MState × MemoryTable.DTmem K => c.2.2.pt) ∘
        (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb)) =
        (fun c : MemoryTable.MState × MemoryTable.DTmem K => c.2.2.pt) :=
      funext fun c => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow_pt lmb c
    have hc : memCell (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb t.label) i =
        memCell t.label i := by
      fin_cases i <;> simp [memCell, SemanticTimestampStrategy.MemoryRowTemplate.encodeRow_lc,
        SemanticTimestampStrategy.MemoryRowTemplate.encodeRow_rc]
    show ((mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb) t).childLabel i).map
        (fun c => c.2.2.pt) =
      some (memCell (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb) t).label i)
    rw [mapNTree_childLabel, Option.map_map, hcomp, mapNTree_label, hc]
    exact hl'

end

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

theorem computeTree_eq_map (z α : K) :
    computeTree z α =
      mapNTree GenComputeRow.row (renderRows z α (bfsAssign (dotTreeAir (K := K)))) :=
  rfl

theorem computeTree_eq_composed (z α : K) :
    computeTree z α =
      mapNTree (GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (dotTreeAir (K := K))) := by
  rw [computeTree_eq_map, renderRows_eq_mapNTree z α]
  exact mapNTree_comp _ _ _

theorem computeTree_fanout (z α : K)
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K))
    (ht : t ∈ bfsForest [computeTree z α]) :
    ComputeTable.fanoutComp t.label.1 = t.children.length := by
  rw [computeTree_eq_composed] at ht
  have hmap :
      bfsForest [mapNTree (GenComputeRow.row ∘ renderNode z α)
          (bfsAssign (dotTreeAir (K := K)))] =
        (bfsForest [bfsAssign (dotTreeAir (K := K))]).map
          (mapNTree (GenComputeRow.row ∘ renderNode z α)) :=
    bfsForest_mapNTree_singleton _ _
  rw [hmap] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hlen : (mapNTree (GenComputeRow.row ∘ renderNode z α) u).children.length =
      u.children.length := by
    simp [mapNTree_children]
  rw [hlen]
  have hstate :
      (mapNTree (GenComputeRow.row ∘ renderNode z α) u).label.1 =
        (renderNode z α u.label).row.1 := by
    simp [mapNTree_label]
  rw [hstate, renderNode_state_agree, renderNode_state_eq]
  exact (bfsAssign_air_children_len hu).symm

theorem memoryForestThreaded_binding (z α : K) :
    ∀ t ∈ bfsForest (memoryForestThreaded z α),
      RawMemoryTopologyBinding t := by
  unfold memoryForestThreaded threadedForest assignedForest
  exact threadGenForest_bfs_binding (memInputs z) 0 _
    (assignedForest_bfs_binding_air z α)

theorem memoryExactTopology_seed :
    MemoryExactTopology (execThreaded seedZ alphaA) :=
  memoryExactTopology_of_rowsAccepted_and_binding memoryRowsAccepted_seed <| by
    intro t ht
    change t ∈ bfsForest ((execThreadedA seedZ alphaA).memoryForest.map
      (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault))) at ht
    rw [bfsForest_mapNTree] at ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact rawMemoryBinding_encodeRow u (memoryForestThreaded_binding seedZ alphaA u hu)

theorem computeExactTopology_seed :
    ComputeExactTopology (execThreaded seedZ alphaA) :=
  computeExactTopology_of_rowsAccepted_and_binding
    (computeRowsAccepted_threaded seedZ alphaA seedZ_ne_zero) <| by
    intro t ht
    change t ∈ bfsForest [computeTree seedZ alphaA] at ht
    rw [computeTree_eq_composed] at ht
    exact assigned_air_bfs_binding seedZ alphaA t ht

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.rawMemoryBinding_walk
#print axioms Nock.NockVMROM.Thm54.TraceGen.rawMemoryBinding_verify
#print axioms Nock.NockVMROM.Thm54.TraceGen.rawMemoryBinding_record_axis2
#print axioms Nock.NockVMROM.Thm54.TraceGen.rawMemoryBinding_record_axis3
#print axioms Nock.NockVMROM.Thm54.TraceGen.rawMemoryBinding_chained_axis3_axis2
#print axioms Nock.NockVMROM.Thm54.TraceGen.rawMemoryBinding_row_chain32
#print axioms Nock.NockVMROM.Thm54.TraceGen.rawMemoryBinding_row_three_chain32
#print axioms Nock.NockVMROM.Thm54.TraceGen.assignedForest_bfs_binding
#print axioms Nock.NockVMROM.Thm54.TraceGen.assignedForest_bfs_binding_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.threadGenForest_bfs_binding
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.computeTree_fanout
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memoryExactTopology_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.computeExactTopology_seed
