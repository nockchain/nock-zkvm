/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulTopology.lean

  Raw memory `fanout`/`childLink` on the generated annotated record
  trees, lifted through the assigned matmul forest and LogUp threader
  so `execThreaded` inhabits `MemoryExactTopology`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSemantic
import Nock.NockVMROM.Thm54.TraceGen.GenTierATopology
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderBinding
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

/-! ## Generic descent / record-tree binding -/

theorem genAnnotatedDescent_singleton (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    ∃ t, (genAnnotatedDescent E z lmb root child recAxis ts recordExp
            currentNoun remainingAxis).1 = [t] := by
  set cs := (genAnnotatedDescent E z lmb root child recAxis ts recordExp
      currentNoun remainingAxis).1 with hcs
  have hlen : cs.length = 1 := by
    rw [hcs]
    exact genAnnotatedDescent_length E z root child recAxis ts recordExp
      currentNoun remainingAxis
  match cs with
  | [] => simp at hlen
  | [t] => exact ⟨t, rfl⟩
  | _ :: _ :: _ => simp at hlen

theorem genAnnotatedDescent_root_pt (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : (genAnnotatedDescent E z lmb root child recAxis ts recordExp
            currentNoun remainingAxis).1 = [t]) :
    t.label.row.2.2.pt =
      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
        currentNoun remainingAxis).2 := by
  unfold genAnnotatedDescent at ht
  split at ht
  · rename_i hlt
    simp at ht
    subst t
    unfold genAnnotatedDescent
    simp only [hlt]
    exact genAnnotatedVerify_root_pt E z root child recAxis ts recordExp
  · rename_i hge
    split at ht
    · rename_i hbit
      simp at ht
      subst t
      simp [NTree.label, gMemRow9_pt]
      conv_rhs =>
        unfold genAnnotatedDescent
        simp [hge, hbit]
    · rename_i hbit
      simp at ht
      subst t
      simp [NTree.label, gMemRow9_pt]
      conv_rhs =>
        unfold genAnnotatedDescent
        simp [hge, hbit]

theorem childLinkMem_of_getElem (parent : NTree (GenMemoryRow K))
    (i : Fin 2) (c : NTree (GenMemoryRow K))
    (hch : parent.children[(i : ℕ)]? = some c)
    (hcell : memCell parent.label.row i = c.label.row.2.2.pt) :
    ((mapNTree GenMemoryRow.row parent).childLabel i).map (fun x => x.2.2.pt) =
      some (memCell (mapNTree GenMemoryRow.row parent).label i) := by
  rw [mapNTree_childLabel, NTree.childLabel, NTree.childOpt, hch]
  simp only [Option.map_some]
  simp [hcell]

theorem childLinkMem_two (parent left right : NTree (GenMemoryRow K))
    (hch : parent.children = [left, right])
    (hlc : parent.label.row.2.2.lc = left.label.row.2.2.pt)
    (hrc : parent.label.row.2.2.rc = right.label.row.2.2.pt) :
    childLinkMem (mapNTree GenMemoryRow.row parent).label
      (fun j => (mapNTree GenMemoryRow.row parent).childLabel j) := by
  intro i hi
  have h0 : parent.children[0]? = some left := by simp [hch]
  have h1 : parent.children[1]? = some right := by simp [hch]
  fin_cases i
  · exact childLinkMem_of_getElem parent 0 left h0 (by simp [memCell, hlc])
  · exact childLinkMem_of_getElem parent 1 right h1 (by simp [memCell, hrc])

theorem childLinkMem_one (parent child : NTree (GenMemoryRow K))
    (hch : parent.children = [child])
    (hlc : parent.label.row.2.2.lc = child.label.row.2.2.pt)
    (hfan : fanoutMem parent.label.row.1 = 1) :
    childLinkMem (mapNTree GenMemoryRow.row parent).label
      (fun j => (mapNTree GenMemoryRow.row parent).childLabel j) := by
  intro i hi
  have hi' : (i : ℕ) < 1 := by
    simpa [mapNTree_label, hfan] using hi
  have h0 : parent.children[0]? = some child := by simp [hch]
  fin_cases i
  · exact childLinkMem_of_getElem parent 0 child h0 (by simp [memCell, hlc])
  · exact (Nat.lt_irrefl 1 hi').elim

theorem rawMemoryBinding_descent (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ remainingAxis currentNoun u,
      u ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
            currentNoun remainingAxis).1 →
      ∀ t, InTree u t →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro remainingAxis
  induction remainingAxis using Nat.strongRecOn with
  | ind n ih =>
    intro currentNoun u hu t ht
    unfold genAnnotatedDescent at hu
    split at hu
    · simp at hu
      subst u
      exact rawMemoryBinding_verify E z root child recAxis ts recordExp t ht
    · rename_i hge
      split at hu
      · simp at hu
        subst u
        obtain ⟨d, hd⟩ := genAnnotatedDescent_singleton (lmb := lmb) E z root child recAxis
          ts recordExp (formulaTail currentNoun) (axisRest n)
        cases ht with
        | here =>
          refine ⟨?_, ?_⟩
          · rw [mapNTree_label, mapNTree_children, List.length_map]
            simp [gMemRow9_state, memDecomposeSkel, fanoutMem, hd]
          · have hch :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).2
                      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                        (formulaTail currentNoun) (axisRest n)).2
                      (nounWalkRootState (formulaHead currentNoun))
                      (descentRootState (axisRest n)) 0 0 lmb))
                  ([ (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).1 ] ++
                    (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                      (formulaTail currentNoun) (axisRest n)).1)).children =
                  [(genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).1, d] := by
              simp [NTree.children_node, hd]
            have hlc :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).2
                      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                        (formulaTail currentNoun) (axisRest n)).2
                      (nounWalkRootState (formulaHead currentNoun))
                      (descentRootState (axisRest n)) 0 0 lmb))
                  ([ (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).1 ] ++
                    (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                      (formulaTail currentNoun) (axisRest n)).1)).label.row.2.2.lc =
                  (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).2 := by
              simp [NTree.label, gMemRow9_lc, annotatedDecPub]
            have hrc :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).2
                      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                        (formulaTail currentNoun) (axisRest n)).2
                      (nounWalkRootState (formulaHead currentNoun))
                      (descentRootState (axisRest n)) 0 0 lmb))
                  ([ (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).1 ] ++
                    (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                      (formulaTail currentNoun) (axisRest n)).1)).label.row.2.2.rc =
                  (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                    (formulaTail currentNoun) (axisRest n)).2 := by
              simp [NTree.label, gMemRow9_rc, annotatedDecPub]
            have hpt := genAnnotatedDescent_root_pt E z root child recAxis ts
              recordExp (formulaTail currentNoun) (axisRest n) d hd
            have hwalk := genAnnotatedNounWalk_root_pt (lmb := lmb) E z (formulaHead currentNoun)
            exact childLinkMem_two _ _ _ hch (hlc.trans hwalk.symm) (hrc.trans hpt.symm)
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append] at hs
          rcases hs with rfl | hs
          · exact rawMemoryBinding_walk E z (formulaHead currentNoun) _ hu'
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaTail currentNoun) _ hs t hu'
      · simp at hu
        subst u
        obtain ⟨d, hd⟩ := genAnnotatedDescent_singleton (lmb := lmb) E z root child recAxis
          ts recordExp (formulaHead currentNoun) (axisRest n)
        cases ht with
        | here =>
          refine ⟨?_, ?_⟩
          · rw [mapNTree_label, mapNTree_children, List.length_map]
            simp [gMemRow9_state, memDecomposeSkel, fanoutMem, hd]
          · have hch :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                        (formulaHead currentNoun) (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).2
                      (descentRootState (axisRest n))
                      (nounWalkRootState (formulaTail currentNoun)) 0 0 lmb))
                  ((genAnnotatedDescent E z lmb root child recAxis ts recordExp
                      (formulaHead currentNoun) (axisRest n)).1 ++
                    [(genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).1])).children =
                  [d, (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).1] := by
              simp [NTree.children_node, hd]
            have hlc :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                        (formulaHead currentNoun) (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).2
                      (descentRootState (axisRest n))
                      (nounWalkRootState (formulaTail currentNoun)) 0 0 lmb))
                  ((genAnnotatedDescent E z lmb root child recAxis ts recordExp
                      (formulaHead currentNoun) (axisRest n)).1 ++
                    [(genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).1])).label.row.2.2.lc =
                  (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                    (formulaHead currentNoun) (axisRest n)).2 := by
              simp [NTree.label, gMemRow9_lc, annotatedDecPub]
            have hrc :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
                        (formulaHead currentNoun) (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).2
                      (descentRootState (axisRest n))
                      (nounWalkRootState (formulaTail currentNoun)) 0 0 lmb))
                  ((genAnnotatedDescent E z lmb root child recAxis ts recordExp
                      (formulaHead currentNoun) (axisRest n)).1 ++
                    [(genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).1])).label.row.2.2.rc =
                  (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).2 := by
              simp [NTree.label, gMemRow9_rc, annotatedDecPub]
            have hpt := genAnnotatedDescent_root_pt E z root child recAxis ts
              recordExp (formulaHead currentNoun) (axisRest n) d hd
            have hwalk := genAnnotatedNounWalk_root_pt (lmb := lmb) E z (formulaTail currentNoun)
            exact childLinkMem_two _ _ _ hch (hlc.trans hpt.symm) (hrc.trans hwalk.symm)
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hs
          rcases hs with hs | rfl
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaHead currentNoun) _ hs t hu'
          · exact rawMemoryBinding_walk E z (formulaTail currentNoun) _ hu'

theorem rawMemoryBinding_record (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ) :
    ∀ t, InTree (genAnnotatedRecordTree E z α lmb root child axis recordExp) t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro t ht
  rw [genAnnotatedRecordTree_eq] at ht
  obtain ⟨d, hd⟩ := genAnnotatedDescent_singleton (lmb := lmb) E z root child axis
    (α ^ recordExp) recordExp root axis
  cases ht with
  | here =>
    refine ⟨?_, ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [gMemRow9_state, memReadSkelAx, fanoutMem, hd]
    · have hch :
          (NTree.node
            (gMemRow9 (memReadSkelAx root child axis) recordExp z
              (annotatedReadPub E root child axis (α ^ recordExp)
                (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
                  recordExp root axis).2 0 0 lmb))
            (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
              recordExp root axis).1).children = [d] := by
        simp [NTree.children_node, hd]
      have hlc :
          (NTree.node
            (gMemRow9 (memReadSkelAx root child axis) recordExp z
              (annotatedReadPub E root child axis (α ^ recordExp)
                (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
                  recordExp root axis).2 0 0 lmb))
            (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
              recordExp root axis).1).label.row.2.2.lc =
            (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
              recordExp root axis).2 := by
        simp [NTree.label, gMemRow9_lc, annotatedReadPub]
      have hpt := genAnnotatedDescent_root_pt E z root child axis
        (α ^ recordExp) recordExp root axis d hd
      have hfan :
          fanoutMem
            (NTree.node
              (gMemRow9 (memReadSkelAx root child axis) recordExp z
                (annotatedReadPub E root child axis (α ^ recordExp)
                  (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
                    recordExp root axis).2 0 0 lmb))
              (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
                recordExp root axis).1).label.row.1 = 1 := by
        simp [NTree.label, gMemRow9_state, memReadSkelAx, fanoutMem]
      exact childLinkMem_one _ _ hch (hlc.trans hpt.symm) hfan
  | sub hs hu =>
    exact rawMemoryBinding_descent E z root child axis (α ^ recordExp)
      recordExp axis root _ hs t hu

/-! ## Continuation / chained-record binding -/

theorem genAnnotatedDescentCont_singleton (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (h1 : cont.length = 1) (currentNoun : Noun) (remainingAxis : ℕ) :
    ∃ t, (genAnnotatedDescentCont E z lmb cont contCell contState
            currentNoun remainingAxis).1 = [t] := by
  set cs := (genAnnotatedDescentCont E z lmb cont contCell contState
      currentNoun remainingAxis).1 with hcs
  have hlen : cs.length = 1 := by
    rw [hcs]
    exact genAnnotatedDescentCont_length_one E z cont contCell contState h1
      currentNoun remainingAxis
  match cs with
  | [] => simp at hlen
  | [t] => exact ⟨t, rfl⟩
  | _ :: _ :: _ => simp at hlen

theorem genAnnotatedDescentCont_root_pt (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (hpt0 : ∀ u ∈ cont, u.label.row.2.2.pt = contCell)
    (currentNoun : Noun) (remainingAxis : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : (genAnnotatedDescentCont E z lmb cont contCell contState
            currentNoun remainingAxis).1 = [t]) :
    t.label.row.2.2.pt =
      (genAnnotatedDescentCont E z lmb cont contCell contState
        currentNoun remainingAxis).2 := by
  unfold genAnnotatedDescentCont at ht
  split at ht
  · rename_i hlt
    simp [hlt] at ht
    have hu : t ∈ cont := by simp [ht]
    have hpt := hpt0 t hu
    unfold genAnnotatedDescentCont
    simp [hlt, hpt]
  · rename_i hge
    split at ht
    · rename_i hbit
      simp at ht
      subst t
      simp [NTree.label, gMemRow9_pt]
      conv_rhs =>
        unfold genAnnotatedDescentCont
        simp [hge, hbit]
    · rename_i hbit
      simp at ht
      subst t
      simp [NTree.label, gMemRow9_pt]
      conv_rhs =>
        unfold genAnnotatedDescentCont
        simp [hge, hbit]

theorem rawMemoryBinding_descentCont (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (h1 : cont.length = 1)
    (hpt0 : ∀ u ∈ cont, u.label.row.2.2.pt = contCell)
    (Hcont : ∀ u ∈ cont, ∀ t, InTree u t →
      RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t)) :
    ∀ remainingAxis currentNoun u,
      u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
            currentNoun remainingAxis).1 →
      ∀ t, InTree u t →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t) := by
  intro remainingAxis
  induction remainingAxis using Nat.strongRecOn with
  | ind n ih =>
    intro currentNoun u hu t ht
    unfold genAnnotatedDescentCont at hu
    split at hu
    · exact Hcont u hu t ht
    · rename_i hge
      split at hu
      · simp at hu
        subst u
        obtain ⟨d, hd⟩ := genAnnotatedDescentCont_singleton (lmb := lmb) E z cont contCell
          contState h1 (formulaTail currentNoun) (axisRest n)
        cases ht with
        | here =>
          refine ⟨?_, ?_⟩
          · rw [mapNTree_label, mapNTree_children, List.length_map]
            simp [gMemRow9_state, memDecomposeSkel, fanoutMem, hd]
          · have hch :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).2
                      (genAnnotatedDescentCont E z lmb cont contCell contState
                        (formulaTail currentNoun) (axisRest n)).2
                      (nounWalkRootState (formulaHead currentNoun))
                      (descentContRootState contState (axisRest n)) 0 0 lmb))
                  ([(genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).1] ++
                    (genAnnotatedDescentCont E z lmb cont contCell contState
                      (formulaTail currentNoun) (axisRest n)).1)).children =
                  [(genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).1, d] := by
              simp [NTree.children_node, hd]
            have hlc :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).2
                      (genAnnotatedDescentCont E z lmb cont contCell contState
                        (formulaTail currentNoun) (axisRest n)).2
                      (nounWalkRootState (formulaHead currentNoun))
                      (descentContRootState contState (axisRest n)) 0 0 lmb))
                  ([(genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).1] ++
                    (genAnnotatedDescentCont E z lmb cont contCell contState
                      (formulaTail currentNoun) (axisRest n)).1)).label.row.2.2.lc =
                  (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).2 := by
              simp [NTree.label, gMemRow9_lc, annotatedDecPub]
            have hrc :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).2
                      (genAnnotatedDescentCont E z lmb cont contCell contState
                        (formulaTail currentNoun) (axisRest n)).2
                      (nounWalkRootState (formulaHead currentNoun))
                      (descentContRootState contState (axisRest n)) 0 0 lmb))
                  ([(genAnnotatedNounWalk E z lmb (formulaHead currentNoun)).1] ++
                    (genAnnotatedDescentCont E z lmb cont contCell contState
                      (formulaTail currentNoun) (axisRest n)).1)).label.row.2.2.rc =
                  (genAnnotatedDescentCont E z lmb cont contCell contState
                    (formulaTail currentNoun) (axisRest n)).2 := by
              simp [NTree.label, gMemRow9_rc, annotatedDecPub]
            have hpt := genAnnotatedDescentCont_root_pt E z cont contCell
              contState hpt0 (formulaTail currentNoun) (axisRest n) d hd
            have hwalk := genAnnotatedNounWalk_root_pt (lmb := lmb) E z
              (formulaHead currentNoun)
            exact childLinkMem_two _ _ _ hch (hlc.trans hwalk.symm)
              (hrc.trans hpt.symm)
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append] at hs
          rcases hs with rfl | hs
          · exact rawMemoryBinding_walk E z (formulaHead currentNoun) _ hu'
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaTail currentNoun) _ hs t hu'
      · simp at hu
        subst u
        obtain ⟨d, hd⟩ := genAnnotatedDescentCont_singleton (lmb := lmb) E z cont contCell
          contState h1 (formulaHead currentNoun) (axisRest n)
        cases ht with
        | here =>
          refine ⟨?_, ?_⟩
          · rw [mapNTree_label, mapNTree_children, List.length_map]
            simp [gMemRow9_state, memDecomposeSkel, fanoutMem, hd]
          · have hch :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedDescentCont E z lmb cont contCell contState
                        (formulaHead currentNoun) (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).2
                      (descentContRootState contState (axisRest n))
                      (nounWalkRootState (formulaTail currentNoun)) 0 0 lmb))
                  ((genAnnotatedDescentCont E z lmb cont contCell contState
                      (formulaHead currentNoun) (axisRest n)).1 ++
                    [(genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).1])).children =
                  [d, (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).1] := by
              simp [NTree.children_node, hd]
            have hlc :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedDescentCont E z lmb cont contCell contState
                        (formulaHead currentNoun) (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).2
                      (descentContRootState contState (axisRest n))
                      (nounWalkRootState (formulaTail currentNoun)) 0 0 lmb))
                  ((genAnnotatedDescentCont E z lmb cont contCell contState
                      (formulaHead currentNoun) (axisRest n)).1 ++
                    [(genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).1])).label.row.2.2.lc =
                  (genAnnotatedDescentCont E z lmb cont contCell contState
                    (formulaHead currentNoun) (axisRest n)).2 := by
              simp [NTree.label, gMemRow9_lc, annotatedDecPub]
            have hrc :
                (NTree.node
                  (gMemRow9 (memDecomposeSkel currentNoun
                      (formulaHead currentNoun) (formulaTail currentNoun)) 0 z
                    (annotatedDecPub E currentNoun (formulaHead currentNoun)
                      (formulaTail currentNoun)
                      (genAnnotatedDescentCont E z lmb cont contCell contState
                        (formulaHead currentNoun) (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).2
                      (descentContRootState contState (axisRest n))
                      (nounWalkRootState (formulaTail currentNoun)) 0 0 lmb))
                  ((genAnnotatedDescentCont E z lmb cont contCell contState
                      (formulaHead currentNoun) (axisRest n)).1 ++
                    [(genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).1])).label.row.2.2.rc =
                  (genAnnotatedNounWalk E z lmb (formulaTail currentNoun)).2 := by
              simp [NTree.label, gMemRow9_rc, annotatedDecPub]
            have hpt := genAnnotatedDescentCont_root_pt E z cont contCell
              contState hpt0 (formulaHead currentNoun) (axisRest n) d hd
            have hwalk := genAnnotatedNounWalk_root_pt (lmb := lmb) E z
              (formulaTail currentNoun)
            exact childLinkMem_two _ _ _ hch (hlc.trans hpt.symm)
              (hrc.trans hwalk.symm)
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hs
          rcases hs with hs | rfl
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaHead currentNoun) _ hs t hu'
          · exact rawMemoryBinding_walk E z (formulaTail currentNoun) _ hu'

theorem genAnnotatedChainedInner_length (E : Noun → ComputeTable.FP K)
    (z α : K) (prev : MemRecordReq) :
    ∀ rest, (genAnnotatedChainedInner E z α lmb prev rest).1.length = 1
  | [] => by simp [genAnnotatedChainedInner]
  | _ :: _ => by simp [genAnnotatedChainedInner]

theorem genAnnotatedChainedInner_root_pt (E : Noun → ComputeTable.FP K)
    (z α : K) (prev : MemRecordReq) :
    ∀ rest u, u ∈ (genAnnotatedChainedInner E z α lmb prev rest).1 →
      u.label.row.2.2.pt = (genAnnotatedChainedInner E z α lmb prev rest).2
  | [], u, hu => by
      simp [genAnnotatedChainedInner] at hu
      subst u
      exact genAnnotatedVerify_root_pt E z prev.root prev.child prev.axis
        (α ^ prev.recordExp) prev.recordExp
  | r :: more, u, hu => by
      simp [genAnnotatedChainedInner] at hu
      subst u
      simp [NTree.label, gMemRow9_pt]
      conv_rhs => unfold genAnnotatedChainedInner

theorem rawMemoryBinding_chainedInner (E : Noun → ComputeTable.FP K)
    (z α : K) (prev : MemRecordReq) :
    ∀ rest u, u ∈ (genAnnotatedChainedInner E z α lmb prev rest).1 →
      ∀ t, InTree u t →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t)
  | [], u, hu, t, ht => by
      simp [genAnnotatedChainedInner] at hu
      subst u
      exact rawMemoryBinding_verify E z prev.root prev.child prev.axis
        (α ^ prev.recordExp) prev.recordExp t ht
  | r :: more, u, hu, t, ht => by
      simp [genAnnotatedChainedInner] at hu
      subst u
      set inner := genAnnotatedChainedInner E z α lmb r more
      set dcont := genAnnotatedDescentCont E z lmb inner.1 inner.2
        (chainedInnerRootState more) r.root r.axis
      have h1 : inner.1.length = 1 := genAnnotatedChainedInner_length E z α r more
      have hpt0 : ∀ v ∈ inner.1, v.label.row.2.2.pt = inner.2 :=
        genAnnotatedChainedInner_root_pt E z α r more
      have Hinner : ∀ v ∈ inner.1, ∀ w, InTree v w →
          RawMemoryTopologyBinding (mapNTree GenMemoryRow.row w) :=
        rawMemoryBinding_chainedInner E z α r more
      obtain ⟨d, hd⟩ := genAnnotatedDescentCont_singleton (lmb := lmb) E z inner.1 inner.2
        (chainedInnerRootState more) h1 r.root r.axis
      have hd' : dcont.1 = [d] := by simpa [dcont] using hd
      cases ht with
      | here =>
        refine ⟨?_, ?_⟩
        · rw [mapNTree_label, mapNTree_children, List.length_map]
          simp [gMemRow9_state, memReadSkelAx, fanoutMem]
        · have hch :
              (NTree.node
                (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z
                  (annotatedReadPub E r.root r.child r.axis (α ^ r.recordExp)
                    (annotatedVerifyPub E prev.root prev.child prev.axis
                      (α ^ prev.recordExp) dcont.2 0 0 lmb).pt 0 0 lmb))
                [NTree.node
                  (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                    prev.recordExp z
                    (annotatedVerifyPub E prev.root prev.child prev.axis
                      (α ^ prev.recordExp) dcont.2 0 0 lmb))
                  dcont.1]).children =
                [NTree.node
                  (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                    prev.recordExp z
                    (annotatedVerifyPub E prev.root prev.child prev.axis
                      (α ^ prev.recordExp) dcont.2 0 0 lmb))
                  dcont.1] := by
            simp [NTree.children_node]
          have hlc :
              (NTree.node
                (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z
                  (annotatedReadPub E r.root r.child r.axis (α ^ r.recordExp)
                    (annotatedVerifyPub E prev.root prev.child prev.axis
                      (α ^ prev.recordExp) dcont.2 0 0 lmb).pt 0 0 lmb))
                [NTree.node
                  (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                    prev.recordExp z
                    (annotatedVerifyPub E prev.root prev.child prev.axis
                      (α ^ prev.recordExp) dcont.2 0 0 lmb))
                  dcont.1]).label.row.2.2.lc =
                (annotatedVerifyPub E prev.root prev.child prev.axis
                  (α ^ prev.recordExp) dcont.2 0 0 lmb).pt := by
            simp [NTree.label, gMemRow9_lc, annotatedReadPub]
          have hfan :
              fanoutMem
                (NTree.node
                  (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z
                    (annotatedReadPub E r.root r.child r.axis (α ^ r.recordExp)
                      (annotatedVerifyPub E prev.root prev.child prev.axis
                        (α ^ prev.recordExp) dcont.2 0 0 lmb).pt 0 0 lmb))
                  [NTree.node
                    (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                      prev.recordExp z
                      (annotatedVerifyPub E prev.root prev.child prev.axis
                        (α ^ prev.recordExp) dcont.2 0 0 lmb))
                    dcont.1]).label.row.1 = 1 := by
            simp [NTree.label, gMemRow9_state, memReadSkelAx, fanoutMem]
          have hchild_pt :
              (NTree.node
                (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                  prev.recordExp z
                  (annotatedVerifyPub E prev.root prev.child prev.axis
                    (α ^ prev.recordExp) dcont.2 0 0 lmb))
                dcont.1).label.row.2.2.pt =
                (annotatedVerifyPub E prev.root prev.child prev.axis
                  (α ^ prev.recordExp) dcont.2 0 0 lmb).pt := by
            simp [NTree.label, gMemRow9_pt]
          exact childLinkMem_one _ _ hch (hlc.trans hchild_pt.symm) hfan
      | sub hs hu' =>
        simp [NTree.children_node, List.mem_cons, List.not_mem_nil,
          or_false] at hs
        subst hs
        cases hu' with
        | here =>
          refine ⟨?_, ?_⟩
          · rw [mapNTree_label, mapNTree_children, List.length_map]
            simp [gMemRow9_state, memVerifySkelAx, fanoutMem, hd']
          · have hch :
                (NTree.node
                  (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                    prev.recordExp z
                    (annotatedVerifyPub E prev.root prev.child prev.axis
                      (α ^ prev.recordExp) dcont.2 0 0 lmb))
                  dcont.1).children = [d] := by
              simp [NTree.children_node, hd']
            have hlc :
                (NTree.node
                  (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                    prev.recordExp z
                    (annotatedVerifyPub E prev.root prev.child prev.axis
                      (α ^ prev.recordExp) dcont.2 0 0 lmb))
                  dcont.1).label.row.2.2.lc = dcont.2 := by
              simp [NTree.label, gMemRow9_lc, annotatedVerifyPub]
            have hpt := genAnnotatedDescentCont_root_pt E z inner.1 inner.2
              (chainedInnerRootState more) hpt0 r.root r.axis d hd
            have hfan :
                fanoutMem
                  (NTree.node
                    (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                      prev.recordExp z
                      (annotatedVerifyPub E prev.root prev.child prev.axis
                        (α ^ prev.recordExp) dcont.2 0 0 lmb))
                    dcont.1).label.row.1 = 1 := by
              simp [NTree.label, gMemRow9_state, memVerifySkelAx, fanoutMem]
            exact childLinkMem_one _ _ hch (hlc.trans hpt.symm) hfan
        | sub hs' hu'' =>
          exact rawMemoryBinding_descentCont E z inner.1 inner.2
            (chainedInnerRootState more) h1 hpt0 Hinner r.axis r.root
            _ hs' t hu''

theorem rawMemoryBinding_chainedTree (E : Noun → ComputeTable.FP K)
    (z α : K) :
    ∀ reqs t, genAnnotatedChainedTree E z α lmb reqs = some t →
      ∀ u, InTree t u →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row u)
  | [], t, ht, _, _ => by simp [genAnnotatedChainedTree] at ht
  | [r], t, ht, u, hu => by
      simp [genAnnotatedChainedTree] at ht
      subst t
      exact rawMemoryBinding_record E z α r.root r.child r.axis r.recordExp u hu
  | r :: r2 :: rest, t, ht, u, hu => by
      simp [genAnnotatedChainedTree] at ht
      subst t
      set inner := genAnnotatedChainedInner E z α lmb r (r2 :: rest)
      set dcont := genAnnotatedDescentCont E z lmb inner.1 inner.2
        (chainedInnerRootState (r2 :: rest)) r.root r.axis
      have h1 : inner.1.length = 1 :=
        genAnnotatedChainedInner_length E z α r (r2 :: rest)
      have hpt0 : ∀ v ∈ inner.1, v.label.row.2.2.pt = inner.2 :=
        genAnnotatedChainedInner_root_pt E z α r (r2 :: rest)
      have Hinner : ∀ v ∈ inner.1, ∀ w, InTree v w →
          RawMemoryTopologyBinding (mapNTree GenMemoryRow.row w) :=
        rawMemoryBinding_chainedInner E z α r (r2 :: rest)
      obtain ⟨d, hd⟩ := genAnnotatedDescentCont_singleton (lmb := lmb) E z inner.1 inner.2
        (chainedInnerRootState (r2 :: rest)) h1 r.root r.axis
      have hd' : dcont.1 = [d] := by simpa [dcont] using hd
      cases hu with
      | here =>
        refine ⟨?_, ?_⟩
        · rw [mapNTree_label, mapNTree_children, List.length_map]
          simp [gMemRow9_state, memReadSkelAx, fanoutMem, hd']
        · have hch :
              (NTree.node
                (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z
                  (annotatedReadPub E r.root r.child r.axis (α ^ r.recordExp)
                    dcont.2 0 0 lmb))
                dcont.1).children = [d] := by
            simp [NTree.children_node, hd']
          have hlc :
              (NTree.node
                (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z
                  (annotatedReadPub E r.root r.child r.axis (α ^ r.recordExp)
                    dcont.2 0 0 lmb))
                dcont.1).label.row.2.2.lc = dcont.2 := by
            simp [NTree.label, gMemRow9_lc, annotatedReadPub]
          have hpt := genAnnotatedDescentCont_root_pt E z inner.1 inner.2
            (chainedInnerRootState (r2 :: rest)) hpt0 r.root r.axis d hd
          have hfan :
              fanoutMem
                (NTree.node
                  (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z
                    (annotatedReadPub E r.root r.child r.axis (α ^ r.recordExp)
                      dcont.2 0 0 lmb))
                  dcont.1).label.row.1 = 1 := by
            simp [NTree.label, gMemRow9_state, memReadSkelAx, fanoutMem]
          exact childLinkMem_one _ _ hch (hlc.trans hpt.symm) hfan
      | sub hs hu' =>
        exact rawMemoryBinding_descentCont E z inner.1 inner.2
          (chainedInnerRootState (r2 :: rest)) h1 hpt0 Hinner r.axis r.root
          _ hs u hu'

theorem genRowMemForest_binding (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ reqs u, u ∈ genRowMemForest E z α lmb reqs →
      ∀ t, InTree u t →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row t)
  | [], u, hu, t, _ => by simp [genRowMemForest] at hu
  | [r], u, hu, t, ht => by
      simp [genRowMemForest] at hu
      subst u
      exact rawMemoryBinding_record E z α r.root r.child r.axis r.recordExp t ht
  | [r1, r2], u, hu, t, ht => by
      simp only [genRowMemForest] at hu
      by_cases hc : r1.child = r2.root
      · rw [if_pos hc] at hu
        cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
        | none =>
          rw [hch] at hu
          simp at hu
          rcases hu with rfl | rfl
          · exact rawMemoryBinding_record E z α r1.root r1.child r1.axis
              r1.recordExp t ht
          · exact rawMemoryBinding_record E z α r2.root r2.child r2.axis
              r2.recordExp t ht
        | some tree =>
          rw [hch] at hu
          simp at hu
          subst u
          exact rawMemoryBinding_chainedTree E z α [r1, r2] tree hch t ht
      · rw [if_neg hc] at hu
        simp at hu
        rcases hu with rfl | rfl
        · exact rawMemoryBinding_record E z α r1.root r1.child r1.axis
            r1.recordExp t ht
        · exact rawMemoryBinding_record E z α r2.root r2.child r2.axis
            r2.recordExp t ht
  | [r1, r2, r3], u, hu, t, ht => by
      simp only [genRowMemForest, List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact genRowMemForest_binding E z α [r1, r2] u hu t ht
      · exact rawMemoryBinding_record E z α r3.root r3.child r3.axis
          r3.recordExp t ht
  | r1 :: r2 :: r3 :: r4 :: rest, u, hu, t, ht => by
      unfold genRowMemForest at hu
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hu
      exact rawMemoryBinding_record E z α r.root r.child r.axis r.recordExp t ht

#print axioms rawMemoryBinding_descent
#print axioms rawMemoryBinding_record
#print axioms genRowMemForest_binding

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

theorem mm_assigned_rowBinding (z α : K)
    (n : NTree (GenComputeRow K))
    (_hn : InTree (bfsAssign (mmTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v →
        RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) :=
  fun u hu v hv => genRowMemForest_binding (encC z) z α _ u hu v hv

theorem assignedForest_binding (z α : K)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (mmTreeAir (K := K))))
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    RawMemoryTopologyBinding (mapNTree GenMemoryRow.row v) :=
  genMemForestFromTree_of_rowBinding (encC z) z α _
    (fun n hn => mm_assigned_rowBinding z α n hn) u hu v hv

theorem assignedForest_bfs_binding (z α : K) :
    ∀ t ∈ bfsForest ((assignedForest z α).map (mapNTree GenMemoryRow.row)),
      RawMemoryTopologyBinding t := by
  intro t ht
  unfold assignedForest at ht
  rw [bfsForest_mapNTree] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ _).mp hu
  exact assignedForest_binding z α r hr u hin

theorem memoryForestThreaded_binding (z α : K) :
    ∀ t ∈ bfsForest (memoryForestThreaded z α),
      RawMemoryTopologyBinding t := by
  unfold memoryForestThreaded threadedForest
  exact threadGenForest_bfs_binding (memInputs z) 0 _
    (assignedForest_bfs_binding z α)

theorem memoryForest_binding_enc (z α : K) :
    ∀ t ∈ bfsForest ((execThreadedA z α).memoryForest.map
        (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault))),
      RawMemoryTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hF : (execThreadedA z α).memoryForest = memoryForestThreaded z α := rfl
  rw [hF] at hu
  have hall := memoryForestThreaded_binding z α
  have hb : RawMemoryTopologyBinding u := hall u hu
  exact rawMemoryBinding_encodeRow u hb

theorem memoryExactTopology_seed :
    MemoryExactTopology (execThreaded seedZ alphaA) :=
  memoryExactTopology_of_rowsAccepted_and_binding memoryRowsAccepted_seed
    (memoryForest_binding_enc seedZ alphaA)

theorem computeTree_eq_composed (z α : K) :
    computeTree z α =
      mapNTree ((setRowCoins (0 : K) 0 1) ∘ GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (mmTreeAir (K := K))) := by
  unfold computeTree mmTreeAir
  rw [renderRows_eq_mapNTree]
  exact mapNTree_comp _ _ _

theorem computeExactTopology_seed :
    ComputeExactTopology (execThreaded seedZ alphaA) :=
  computeExactTopology_of_rowsAccepted_and_binding
    computeRowsAccepted_threaded <| by
    intro t ht
    change t ∈ bfsForest [computeTree seedZ alphaA] at ht
    rw [computeTree_eq_composed] at ht
    unfold mmTreeAir at ht
    exact assigned_airReorder_coins_binding seedZ alphaA 0 0 1
      (mmTree_gen (K := K)) t ht

theorem traversable_seed
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    TraversableChainedSemanticExactLanguage (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) where
  chained := chained hfirst
  compute_topology := computeExactTopology_seed
  memory_topology := memoryExactTopology_seed

end

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memoryExactTopology_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.computeExactTopology_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.traversable_seed
