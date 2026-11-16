/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAComputeLink.lean

  Compute `childLinkComp` on the AIR-ordered Tier A tree `dotTreeAir`
  (children `[taken, condition]` matching `sf1`/`sf2`).  Transported
  through `bfsAssign`/`renderNode`, so the assigned rendered forest
  inhabits `RawComputeTopologyBinding`.

  `dotTree` and `Gen.lean` are not edited: the generator still emits
  DFS `[condition, taken]`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAData
import Nock.NockVMROM.Thm54.RawTopologySoundness
import Mathlib.Tactic.IntervalCases
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTierAComputeLink

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy

variable {K : Type} [Field K]

omit [Field K] in
theorem mapNTree_childLabel {α β : Type*} (f : α → β) (t : NTree α) (i : ℕ) :
    (mapNTree f t).childLabel i = (t.childLabel i).map f := by
  cases t with
  | node _ cs =>
    simp [NTree.childLabel, NTree.childOpt, mapNTree_children, List.getElem?_map]
    congr 1
    ext u
    exact mapNTree_label f u

/-! ## Rendered `(s,f,e)` / `sfTriple` follow the skeleton -/

theorem renderNode_sfe (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.2.2.1.s = encC z g.skel.subject ∧
      (renderNode z α g).row.2.2.1.f = encC z g.skel.formula ∧
      (renderNode z α g).row.2.2.1.e = encC z g.skel.evaluation := by
  unfold renderNode
  cases g.skel.state <;>
    simp [renderOp0Row, renderOp1Row, renderOp2Row, renderOp3Row, renderOp4Row,
      renderOp5Row, renderOp6Row, renderOp7Row, renderOp8Row, renderOp9Row,
      renderConsRow]

theorem renderNode_sfTriple_s2 (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s2) (i : Fin 3) :
    sfTriple (renderNode z α g).row.2.2.1 i =
      (encC z (P8Census.skeletonSubformula g.skel i TripleSlot.subject),
        encC z (P8Census.skeletonSubformula g.skel i TripleSlot.formula),
        encC z (P8Census.skeletonSubformula g.skel i TripleSlot.result)) := by
  rw [renderNode_op2_row z α g h]
  fin_cases i <;> simp [sfTriple, renderOp2Row]

theorem renderNode_sfTriple_s6 (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s6) (i : Fin 3)
    (hi : (i : ℕ) < fanoutComp g.skel.state) :
    sfTriple (renderNode z α g).row.2.2.1 i =
      (encC z (P8Census.skeletonSubformula g.skel i TripleSlot.subject),
        encC z (P8Census.skeletonSubformula g.skel i TripleSlot.formula),
        encC z (P8Census.skeletonSubformula g.skel i TripleSlot.result)) := by
  rw [renderNode_op6_row z α g h]
  rw [h] at hi
  fin_cases i
  · simp [sfTriple, renderOp6Row]
  · simp [sfTriple, renderOp6Row]
  · simp [fanoutComp] at hi

theorem renderNode_sfTriple_s9 (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s9) (i : Fin 3)
    (hi : (i : ℕ) < fanoutComp g.skel.state) :
    sfTriple (renderNode z α g).row.2.2.1 i =
      (encC z (P8Census.skeletonSubformula g.skel i TripleSlot.subject),
        encC z (P8Census.skeletonSubformula g.skel i TripleSlot.formula),
        encC z (P8Census.skeletonSubformula g.skel i TripleSlot.result)) := by
  rw [renderNode_op9_row z α g h]
  rw [h] at hi
  fin_cases i
  · simp [sfTriple, renderOp9Row]
  · simp [sfTriple, renderOp9Row]
  · simp [fanoutComp] at hi

theorem renderNode_state (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.1 = g.skel.state := by
  unfold renderNode
  cases g.skel.state <;> rfl

/-! ## Named child skeletons match parent `sf` slots -/

theorem dotOp2_matches_op6_sf0 :
    (dotOp2Tree (K := K)).label.skel.subject =
      P8Census.skeletonSubformula dotOp6Skel 0 TripleSlot.subject ∧
    (dotOp2Tree (K := K)).label.skel.formula =
      P8Census.skeletonSubformula dotOp6Skel 0 TripleSlot.formula ∧
    (dotOp2Tree (K := K)).label.skel.evaluation =
      P8Census.skeletonSubformula dotOp6Skel 0 TripleSlot.result := by
  simp [dotOp2Tree, skelNode, dotOp2Skel, genSkelOp2, dotOp6Skel, genSkelOp6,
    P8Census.skeletonSubformula, fanoutComp]

theorem dotCond_matches_op6_sf1 :
    (dotCondTree (K := K)).label.skel.subject =
      P8Census.skeletonSubformula dotOp6Skel 1 TripleSlot.subject ∧
    (dotCondTree (K := K)).label.skel.formula =
      P8Census.skeletonSubformula dotOp6Skel 1 TripleSlot.formula ∧
    (dotCondTree (K := K)).label.skel.evaluation =
      P8Census.skeletonSubformula dotOp6Skel 1 TripleSlot.result := by
  simp [dotCondTree, skelNode, genSkelOp1, dotOp6Skel, genSkelOp6,
    P8Census.skeletonSubformula, fanoutComp]

theorem dotOp1B_matches_op2_sf0 :
    (dotOp1BTree (K := K)).label.skel.subject =
      P8Census.skeletonSubformula dotOp2Skel 0 TripleSlot.subject ∧
    (dotOp1BTree (K := K)).label.skel.formula =
      P8Census.skeletonSubformula dotOp2Skel 0 TripleSlot.formula ∧
    (dotOp1BTree (K := K)).label.skel.evaluation =
      P8Census.skeletonSubformula dotOp2Skel 0 TripleSlot.result := by
  simp [dotOp1BTree, skelNode, genSkelOp1, dotOp2Skel, genSkelOp2,
    P8Census.skeletonSubformula, fanoutComp]

theorem dotOp1C_matches_op2_sf1 :
    (dotOp1CTree (K := K)).label.skel.subject =
      P8Census.skeletonSubformula dotOp2Skel 1 TripleSlot.subject ∧
    (dotOp1CTree (K := K)).label.skel.formula =
      P8Census.skeletonSubformula dotOp2Skel 1 TripleSlot.formula ∧
    (dotOp1CTree (K := K)).label.skel.evaluation =
      P8Census.skeletonSubformula dotOp2Skel 1 TripleSlot.result := by
  simp [dotOp1CTree, skelNode, genSkelOp1, dotOp2Skel, genSkelOp2,
    P8Census.skeletonSubformula, fanoutComp]

theorem dotOp9_matches_op2_sf2 :
    (dotOp9Tree (K := K)).label.skel.subject =
      P8Census.skeletonSubformula dotOp2Skel 2 TripleSlot.subject ∧
    (dotOp9Tree (K := K)).label.skel.formula =
      P8Census.skeletonSubformula dotOp2Skel 2 TripleSlot.formula ∧
    (dotOp9Tree (K := K)).label.skel.evaluation =
      P8Census.skeletonSubformula dotOp2Skel 2 TripleSlot.result := by
  simp [dotOp9Tree, skelNode, dotOp9Skel, genSkelOp9, dotOp2Skel, genSkelOp2,
    P8Census.skeletonSubformula, fanoutComp, dotOp2Sf2, dotOp2Sf1]

theorem dotOp9Core_matches_op9_sf0 :
    (dotOp9CoreTree (K := K)).label.skel.subject =
      P8Census.skeletonSubformula dotOp9Skel 0 TripleSlot.subject ∧
    (dotOp9CoreTree (K := K)).label.skel.formula =
      P8Census.skeletonSubformula dotOp9Skel 0 TripleSlot.formula ∧
    (dotOp9CoreTree (K := K)).label.skel.evaluation =
      P8Census.skeletonSubformula dotOp9Skel 0 TripleSlot.result := by
  simp [dotOp9CoreTree, skelNode, genSkelOp1, dotOp9Skel, genSkelOp9,
    P8Census.skeletonSubformula, fanoutComp]

theorem dotOp9Invoke_matches_op9_sf1 :
    (dotOp9InvokeTree (K := K)).label.skel.subject =
      P8Census.skeletonSubformula dotOp9Skel 1 TripleSlot.subject ∧
    (dotOp9InvokeTree (K := K)).label.skel.formula =
      P8Census.skeletonSubformula dotOp9Skel 1 TripleSlot.formula ∧
    (dotOp9InvokeTree (K := K)).label.skel.evaluation =
      P8Census.skeletonSubformula dotOp9Skel 1 TripleSlot.result := by
  simp [dotOp9InvokeTree, skelNode, genSkelOp1, dotOp9Skel, genSkelOp9,
    P8Census.skeletonSubformula, fanoutComp]

/-! ## `childLinkComp` on named AIR nodes -/

theorem childLinkComp_of_sfe (z α : K) (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K)))
    (_hfan : cs.length = fanoutComp g.skel.state)
    (hmatch : ∀ i : Fin 3, (hi : (i : ℕ) < cs.length) →
      (cs[(i : ℕ)]'hi).label.skel.subject =
        P8Census.skeletonSubformula g.skel i TripleSlot.subject ∧
      (cs[(i : ℕ)]'hi).label.skel.formula =
        P8Census.skeletonSubformula g.skel i TripleSlot.formula ∧
      (cs[(i : ℕ)]'hi).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel i TripleSlot.result)
    (hsf : g.skel.state = State.s2 ∨ g.skel.state = State.s6 ∨
      g.skel.state = State.s9) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α) (.node g cs)).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α) (.node g cs)).childLabel j) := by
  intro i hi
  have hi' : (i : ℕ) < cs.length := by
    have := hi
    simp [mapNTree_label, Function.comp, renderNode_state] at this
    omega
  have hget : cs[(i : ℕ)]? = some (cs[(i : ℕ)]'hi') :=
    List.getElem?_eq_getElem hi'
  have hsfe := renderNode_sfe z α (cs[(i : ℕ)]'hi').label
  have hsfP := hmatch i hi'
  have hfanI : (i : ℕ) < fanoutComp g.skel.state := by
    simpa [mapNTree_label, Function.comp, renderNode_state] using hi
  have htrip : sfTriple (renderNode z α g).row.2.2.1 i =
      (encC z (P8Census.skeletonSubformula g.skel i TripleSlot.subject),
        encC z (P8Census.skeletonSubformula g.skel i TripleSlot.formula),
        encC z (P8Census.skeletonSubformula g.skel i TripleSlot.result)) := by
    rcases hsf with h | h | h
    · exact renderNode_sfTriple_s2 z α g h i
    · exact renderNode_sfTriple_s6 z α g h i hfanI
    · exact renderNode_sfTriple_s9 z α g h i hfanI
  dsimp
  rw [mapNTree_childLabel]
  simp [NTree.childLabel, NTree.childOpt, NTree.children_node, hget, mapNTree_label,
    Function.comp]
  rw [htrip]
  apply Prod.ext
  · exact hsfe.1.trans (congrArg (encC z) hsfP.1)
  · apply Prod.ext
    · exact hsfe.2.1.trans (congrArg (encC z) hsfP.2.1)
    · exact hsfe.2.2.trans (congrArg (encC z) hsfP.2.2)

theorem childLinkComp_leaf (lbl : State × DTcomp K)
    (hfan : fanoutComp lbl.1 = 0) :
    childLinkComp lbl (fun _ => none) := by
  intro i hi
  rw [hfan] at hi
  exact absurd hi (Nat.not_lt_zero _)

theorem childLink_op1 (z α : K) (t : NTree (GenComputeRow K))
    (hstate : t.label.skel.state = State.s1)
    (hch : t.children = []) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α) t).label
      (fun j => (mapNTree (GenComputeRow.row ∘ renderNode z α) t).childLabel j) := by
  intro i hi
  have hst :
      (mapNTree (GenComputeRow.row ∘ renderNode z α) t).label.1 = State.s1 := by
    cases t with
    | node g cs =>
      simp [mapNTree_label, Function.comp, renderNode_state]
      simpa [NTree.label] using hstate
  rw [hst] at hi
  simp [fanoutComp] at hi

theorem childLink_dotTreeAir_root (z α : K) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α)
        (dotTreeAir (K := K))).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α)
          (dotTreeAir (K := K))).childLabel j) := by
  dsimp only [dotTreeAir]
  refine childLinkComp_of_sfe z α _ [dotOp2Tree, dotCondTree] ?_ ?_ ?_
  · rfl
  · intro i hi
    fin_cases i
    · simpa [skelNode] using dotOp2_matches_op6_sf0
    · simpa [skelNode] using dotCond_matches_op6_sf1
    · simp at hi
  · exact Or.inr (Or.inl rfl)

theorem childLink_dotOp2Tree (z α : K) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α)
        (dotOp2Tree (K := K))).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α)
          (dotOp2Tree (K := K))).childLabel j) := by
  dsimp only [dotOp2Tree]
  refine childLinkComp_of_sfe z α _ [dotOp1BTree, dotOp1CTree, dotOp9Tree] ?_ ?_ ?_
  · rfl
  · intro i hi
    fin_cases i
    · simpa [skelNode] using dotOp1B_matches_op2_sf0
    · simpa [skelNode] using dotOp1C_matches_op2_sf1
    · simpa [skelNode] using dotOp9_matches_op2_sf2
  · exact Or.inl rfl

theorem childLink_dotOp9Tree (z α : K) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α)
        (dotOp9Tree (K := K))).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α)
          (dotOp9Tree (K := K))).childLabel j) := by
  dsimp only [dotOp9Tree]
  refine childLinkComp_of_sfe z α _ [dotOp9CoreTree, dotOp9InvokeTree] ?_ ?_ ?_
  · rfl
  · intro i hi
    fin_cases i
    · simpa [skelNode] using dotOp9Core_matches_op9_sf0
    · simpa [skelNode] using dotOp9Invoke_matches_op9_sf1
    · simp at hi
  · exact Or.inr (Or.inr rfl)

theorem rawComputeBinding_air (z α : K) :
    ∀ t, InTree (dotTreeAir (K := K)) t →
      RawComputeTopologyBinding
        (mapNTree (GenComputeRow.row ∘ renderNode z α) t) := by
  intro t ht
  have hcs : (dotTreeAir (K := K)).children = [dotOp2Tree, dotCondTree] := rfl
  cases ht with
  | here =>
    refine ⟨?_, childLink_dotTreeAir_root z α⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state, dotTreeAir, skelNode, genSkelOp6,
        fanoutComp]
      rfl
  | sub hs hu =>
    rw [hcs] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have h2 : (dotOp2Tree (K := K)).children =
          [dotOp1BTree, dotOp1CTree, dotOp9Tree] := rfl
      cases hu with
      | here =>
        refine ⟨?_, childLink_dotOp2Tree z α⟩
        · rw [mapNTree_label, mapNTree_children, List.length_map]
          simp [Function.comp, renderNode_state, dotOp2Tree, skelNode, genSkelOp2,
            fanoutComp]
          rfl
      | sub hs2 hu2 =>
        rw [h2] at hs2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs2
        rcases hs2 with rfl | rfl | rfl
        · cases hu2 with
          | here =>
            refine ⟨?_, childLink_op1 z α _ rfl rfl⟩
            · rw [mapNTree_label, mapNTree_children, List.length_map]
              simp [Function.comp, renderNode_state, dotOp1BTree, skelNode,
                genSkelOp1, fanoutComp]
          | sub hs3 _ =>
            simp [dotOp1BTree, NTree.children] at hs3
        · cases hu2 with
          | here =>
            refine ⟨?_, childLink_op1 z α _ rfl rfl⟩
            · rw [mapNTree_label, mapNTree_children, List.length_map]
              simp [Function.comp, renderNode_state, dotOp1CTree, skelNode,
                genSkelOp1, fanoutComp]
          | sub hs3 _ =>
            simp [dotOp1CTree, NTree.children] at hs3
        · have h9 : (dotOp9Tree (K := K)).children =
              [dotOp9CoreTree, dotOp9InvokeTree] := rfl
          cases hu2 with
          | here =>
            refine ⟨?_, childLink_dotOp9Tree z α⟩
            · rw [mapNTree_label, mapNTree_children, List.length_map]
              simp [Function.comp, renderNode_state, dotOp9Tree, skelNode,
                genSkelOp9, fanoutComp]
              rfl
          | sub hs9 hu9 =>
            rw [h9] at hs9
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hs9
            rcases hs9 with rfl | rfl
            · cases hu9 with
              | here =>
                refine ⟨?_, childLink_op1 z α _ rfl rfl⟩
                · rw [mapNTree_label, mapNTree_children, List.length_map]
                  simp [Function.comp, renderNode_state, dotOp9CoreTree, skelNode,
                    genSkelOp1, fanoutComp]
              | sub hsL _ =>
                simp [dotOp9CoreTree, NTree.children] at hsL
            · cases hu9 with
              | here =>
                refine ⟨?_, childLink_op1 z α _ rfl rfl⟩
                · rw [mapNTree_label, mapNTree_children, List.length_map]
                  simp [Function.comp, renderNode_state, dotOp9InvokeTree, skelNode,
                    genSkelOp1, fanoutComp]
              | sub hsL _ =>
                simp [dotOp9InvokeTree, NTree.children] at hsL
    · cases hu with
      | here =>
        refine ⟨?_, childLink_op1 z α _ rfl rfl⟩
        · rw [mapNTree_label, mapNTree_children, List.length_map]
          simp [Function.comp, renderNode_state, dotCondTree, skelNode,
            genSkelOp1, fanoutComp]
      | sub hsC _ =>
        simp [dotCondTree, NTree.children] at hsC

/-! ## Assigned AIR forest: same skels, same `childLinkComp` -/

theorem dot_air_bfs_index (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length) :
    i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
  simp [dot_air_bfsForest, List.mem_range'] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  interval_cases k <;> simp

theorem bfsLabelAt_air_skel1 :
    (bfsLabelAt (dotTreeAir (K := K)) 1).skel = dotOp6Skel := by
  have hi : 1 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_skel (dotTreeAir (K := K)) 1 hi]
  simp [dot_air_bfsRows]
  rfl

theorem bfsLabelAt_air_skel2 :
    (bfsLabelAt (dotTreeAir (K := K)) 2).skel = (dotOp2Tree (K := K)).label.skel := by
  have hi : 2 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_skel (dotTreeAir (K := K)) 2 hi]
  simp [dot_air_bfsRows]

theorem bfsLabelAt_air_skel3 :
    (bfsLabelAt (dotTreeAir (K := K)) 3).skel = (dotCondTree (K := K)).label.skel := by
  have hi : 3 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_skel (dotTreeAir (K := K)) 3 hi]
  simp [dot_air_bfsRows]

theorem bfsLabelAt_air_skel4 :
    (bfsLabelAt (dotTreeAir (K := K)) 4).skel = (dotOp1BTree (K := K)).label.skel := by
  have hi : 4 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_skel (dotTreeAir (K := K)) 4 hi]
  simp [dot_air_bfsRows]

theorem bfsLabelAt_air_skel5 :
    (bfsLabelAt (dotTreeAir (K := K)) 5).skel = (dotOp1CTree (K := K)).label.skel := by
  have hi : 5 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_skel (dotTreeAir (K := K)) 5 hi]
  simp [dot_air_bfsRows]

theorem bfsLabelAt_air_skel6 :
    (bfsLabelAt (dotTreeAir (K := K)) 6).skel = dotOp9Skel := by
  have hi : 6 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_skel (dotTreeAir (K := K)) 6 hi]
  simp [dot_air_bfsRows]
  rfl

theorem bfsLabelAt_air_skel7 :
    (bfsLabelAt (dotTreeAir (K := K)) 7).skel =
      (dotOp9CoreTree (K := K)).label.skel := by
  have hi : 7 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_skel (dotTreeAir (K := K)) 7 hi]
  simp [dot_air_bfsRows]

theorem bfsLabelAt_air_skel8 :
    (bfsLabelAt (dotTreeAir (K := K)) 8).skel =
      (dotOp9InvokeTree (K := K)).label.skel := by
  have hi : 8 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_skel (dotTreeAir (K := K)) 8 hi]
  simp [dot_air_bfsRows]

theorem foCol_air_1 : foCol (bfsForest [dotTreeAir (K := K)]) 1 = 2 := by
  unfold foCol
  simp [dot_air_bfsForest]
  rfl

theorem foCol_air_2 : foCol (bfsForest [dotTreeAir (K := K)]) 2 = 3 := by
  unfold foCol
  simp [dot_air_bfsForest]
  rfl

theorem foCol_air_3 : foCol (bfsForest [dotTreeAir (K := K)]) 3 = 0 := by
  unfold foCol
  simp [dot_air_bfsForest]
  rfl

theorem foCol_air_4 : foCol (bfsForest [dotTreeAir (K := K)]) 4 = 0 := by
  unfold foCol
  simp [dot_air_bfsForest]
  rfl

theorem foCol_air_5 : foCol (bfsForest [dotTreeAir (K := K)]) 5 = 0 := by
  unfold foCol
  simp [dot_air_bfsForest]
  rfl

theorem foCol_air_6 : foCol (bfsForest [dotTreeAir (K := K)]) 6 = 2 := by
  unfold foCol
  simp [dot_air_bfsForest]
  rfl

theorem foCol_air_7 : foCol (bfsForest [dotTreeAir (K := K)]) 7 = 0 := by
  unfold foCol
  simp [dot_air_bfsForest]
  rfl

theorem foCol_air_8 : foCol (bfsForest [dotTreeAir (K := K)]) 8 = 0 := by
  unfold foCol
  simp [dot_air_bfsForest]
  rfl

def airBuild (i : ℕ) : NTree (GenComputeRow K) :=
  buildTF 1 (foCol (bfsForest [dotTreeAir (K := K)]))
    (bfsLabelAt (dotTreeAir (K := K)))
    (bfsForest [dotTreeAir (K := K)]).length i

theorem airBuild_label (i : ℕ) :
    (airBuild (K := K) i).label = bfsLabelAt (dotTreeAir (K := K)) i :=
  buildTF_label _ _ _ _ _

theorem air_hne : [dotTreeAir (K := K)] ≠ [] := List.cons_ne_nil _ _

theorem airBuild_children (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ (bfsForest [dotTreeAir (K := K)]).length) :
    (airBuild (K := K) i).children =
      (List.range' (firstCF 1 (foCol (bfsForest [dotTreeAir (K := K)])) i)
        (foCol (bfsForest [dotTreeAir (K := K)]) i)).map airBuild := by
  unfold airBuild
  rw [buildTF_children,
    childIdxsF_eq (kroots := 1) (fo := foCol (bfsForest [dotTreeAir (K := K)]))
      (h := (bfsForest [dotTreeAir (K := K)]).length)
      (foCol_Sf_tilingF _ air_hne) (foCol_BFSValidF _ air_hne) hi1 hih]

theorem firstCF_air_1 :
    firstCF 1 (foCol (bfsForest [dotTreeAir (K := K)])) 1 = 2 := by
  dsimp only [firstCF]
  rw [Sf_zero]

theorem firstCF_air_2 :
    firstCF 1 (foCol (bfsForest [dotTreeAir (K := K)])) 2 = 4 := by
  dsimp only [firstCF]
  rw [Sf_succ, Sf_zero, foCol_air_1]

theorem firstCF_air_6 :
    firstCF 1 (foCol (bfsForest [dotTreeAir (K := K)])) 6 = 7 := by
  dsimp only [firstCF]
  have h1 : Sf (foCol (bfsForest [dotTreeAir (K := K)])) 1 = 2 := by
    rw [Sf_succ, Sf_zero, foCol_air_1]
  have h2 : Sf (foCol (bfsForest [dotTreeAir (K := K)])) 2 = 5 := by
    rw [Sf_succ, h1, foCol_air_2]
  have h3 : Sf (foCol (bfsForest [dotTreeAir (K := K)])) 3 = 5 := by
    rw [Sf_succ, h2, foCol_air_3]
  have h4 : Sf (foCol (bfsForest [dotTreeAir (K := K)])) 4 = 5 := by
    rw [Sf_succ, h3, foCol_air_4]
  have h5 : Sf (foCol (bfsForest [dotTreeAir (K := K)])) 5 = 5 := by
    rw [Sf_succ, h4, foCol_air_5]
  rw [h5]

theorem bfsAssign_air_eq_node :
    bfsAssign (dotTreeAir (K := K)) =
      .node (bfsAssign (dotTreeAir (K := K))).label
        (bfsAssign (dotTreeAir (K := K))).children := by
  cases bfsAssign (dotTreeAir (K := K)); rfl

theorem bfsAssign_air_children :
    (bfsAssign (dotTreeAir (K := K))).children =
      [airBuild (K := K) 2, airBuild (K := K) 3] := by
  rw [bfsAssign]
  change (airBuild (K := K) 1).children = _
  rw [airBuild_children 1 (by omega) (by simp [dot_air_bfsForest]),
    firstCF_air_1, foCol_air_1]
  rfl

theorem airBuild_2_children :
    (airBuild (K := K) 2).children =
      [airBuild (K := K) 4, airBuild (K := K) 5, airBuild (K := K) 6] := by
  rw [airBuild_children 2 (by omega) (by simp [dot_air_bfsForest]),
    firstCF_air_2, foCol_air_2]
  rfl

theorem airBuild_3_children : (airBuild (K := K) 3).children = [] := by
  rw [airBuild_children 3 (by omega) (by simp [dot_air_bfsForest]), foCol_air_3]
  rfl

theorem airBuild_4_children : (airBuild (K := K) 4).children = [] := by
  rw [airBuild_children 4 (by omega) (by simp [dot_air_bfsForest]), foCol_air_4]
  rfl

theorem airBuild_5_children : (airBuild (K := K) 5).children = [] := by
  rw [airBuild_children 5 (by omega) (by simp [dot_air_bfsForest]), foCol_air_5]
  rfl

theorem airBuild_6_children :
    (airBuild (K := K) 6).children =
      [airBuild (K := K) 7, airBuild (K := K) 8] := by
  rw [airBuild_children 6 (by omega) (by simp [dot_air_bfsForest]),
    firstCF_air_6, foCol_air_6]
  rfl

theorem airBuild_7_children : (airBuild (K := K) 7).children = [] := by
  rw [airBuild_children 7 (by omega) (by simp [dot_air_bfsForest]), foCol_air_7]
  rfl

theorem airBuild_8_children : (airBuild (K := K) 8).children = [] := by
  rw [airBuild_children 8 (by omega) (by simp [dot_air_bfsForest]), foCol_air_8]
  rfl

theorem childLink_airBuild_op6 (z α : K) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α)
        (airBuild (K := K) 1)).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α)
          (airBuild (K := K) 1)).childLabel j) := by
  have hcs := airBuild_children (K := K) 1 (by omega)
    (by simp [dot_air_bfsForest])
  rw [firstCF_air_1, foCol_air_1] at hcs
  have hg : (airBuild (K := K) 1).label.skel = dotOp6Skel := by
    rw [airBuild_label, bfsLabelAt_air_skel1]
  cases hnode : airBuild (K := K) 1 with
  | node g cs =>
    have hg' : g.skel = dotOp6Skel := by
      simpa [hnode, NTree.label] using hg
    have hcs' : cs = [airBuild (K := K) 2, airBuild (K := K) 3] := by
      have h := hcs
      rw [hnode] at h
      simpa [NTree.children, List.range'] using h
    subst hcs'
    refine childLinkComp_of_sfe z α g _ ?_ ?_ ?_
    · rw [hg']; rfl
    · intro i hi
      have h2 : (airBuild (K := K) 2).label.skel =
          (dotOp2Tree (K := K)).label.skel := by
        rw [airBuild_label, bfsLabelAt_air_skel2]
      have h3 : (airBuild (K := K) 3).label.skel =
          (dotCondTree (K := K)).label.skel := by
        rw [airBuild_label, bfsLabelAt_air_skel3]
      simp at hi
      interval_cases hval : (i : ℕ)
      · have hi0 : i = 0 := Fin.ext hval
        subst hi0
        simp only [List.getElem_cons_zero]
        rw [h2, hg']
        simpa [dotOp2Tree, skelNode] using (dotOp2_matches_op6_sf0 (K := K))
      · have hi1 : i = 1 := Fin.ext hval
        subst hi1
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        rw [h3, hg']
        simpa [dotCondTree, skelNode] using (dotCond_matches_op6_sf1 (K := K))
    · exact Or.inr (Or.inl (by rw [hg']; rfl))

theorem childLink_airBuild_op2 (z α : K) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α)
        (airBuild (K := K) 2)).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α)
          (airBuild (K := K) 2)).childLabel j) := by
  have hcs := airBuild_2_children (K := K)
  have hg : (airBuild (K := K) 2).label.skel = dotOp2Skel := by
    rw [airBuild_label, bfsLabelAt_air_skel2]
    rfl
  cases hnode : airBuild (K := K) 2 with
  | node g cs =>
    have hg' : g.skel = dotOp2Skel := by
      simpa [hnode, NTree.label] using hg
    have hcs' : cs = [airBuild (K := K) 4, airBuild (K := K) 5, airBuild (K := K) 6] := by
      have h := hcs
      rw [hnode] at h
      simpa [NTree.children] using h
    subst hcs'
    refine childLinkComp_of_sfe z α g _ ?_ ?_ ?_
    · rw [hg']; rfl
    · intro i hi
      have h4 : (airBuild (K := K) 4).label.skel =
          (dotOp1BTree (K := K)).label.skel := by
        rw [airBuild_label, bfsLabelAt_air_skel4]
      have h5 : (airBuild (K := K) 5).label.skel =
          (dotOp1CTree (K := K)).label.skel := by
        rw [airBuild_label, bfsLabelAt_air_skel5]
      have h6 : (airBuild (K := K) 6).label.skel = dotOp9Skel := by
        rw [airBuild_label, bfsLabelAt_air_skel6]
      have hbound : (i : ℕ) < 3 := by simpa using hi
      interval_cases hval : (i : ℕ)
      · have hi0 : i = 0 := Fin.ext hval
        subst hi0
        simp only [List.getElem_cons_zero]
        rw [h4, hg']
        simpa [dotOp1BTree, skelNode] using (dotOp1B_matches_op2_sf0 (K := K))
      · have hi1 : i = 1 := Fin.ext hval
        subst hi1
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        rw [h5, hg']
        simpa [dotOp1CTree, skelNode] using (dotOp1C_matches_op2_sf1 (K := K))
      · have hi2 : i = 2 := Fin.ext hval
        subst hi2
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        rw [h6, hg']
        simpa [dotOp9Tree, skelNode] using (dotOp9_matches_op2_sf2 (K := K))
    · exact Or.inl (by rw [hg']; rfl)

theorem childLink_airBuild_op9 (z α : K) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α)
        (airBuild (K := K) 6)).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α)
          (airBuild (K := K) 6)).childLabel j) := by
  have hcs := airBuild_6_children (K := K)
  have hg : (airBuild (K := K) 6).label.skel = dotOp9Skel := by
    rw [airBuild_label, bfsLabelAt_air_skel6]
  cases hnode : airBuild (K := K) 6 with
  | node g cs =>
    have hg' : g.skel = dotOp9Skel := by
      simpa [hnode, NTree.label] using hg
    have hcs' : cs = [airBuild (K := K) 7, airBuild (K := K) 8] := by
      have h := hcs
      rw [hnode] at h
      simpa [NTree.children] using h
    subst hcs'
    refine childLinkComp_of_sfe z α g _ ?_ ?_ ?_
    · rw [hg']; rfl
    · intro i hi
      have h7 : (airBuild (K := K) 7).label.skel =
          (dotOp9CoreTree (K := K)).label.skel := by
        rw [airBuild_label, bfsLabelAt_air_skel7]
      have h8 : (airBuild (K := K) 8).label.skel =
          (dotOp9InvokeTree (K := K)).label.skel := by
        rw [airBuild_label, bfsLabelAt_air_skel8]
      simp at hi
      interval_cases hval : (i : ℕ)
      · have hi0 : i = 0 := Fin.ext hval
        subst hi0
        simp only [List.getElem_cons_zero]
        rw [h7, hg']
        simpa [dotOp9CoreTree, skelNode] using (dotOp9Core_matches_op9_sf0 (K := K))
      · have hi1 : i = 1 := Fin.ext hval
        subst hi1
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        rw [h8, hg']
        simpa [dotOp9InvokeTree, skelNode] using (dotOp9Invoke_matches_op9_sf1 (K := K))
    · exact Or.inr (Or.inr (by rw [hg']; rfl))

theorem childLink_airBuild_op1 (z α : K) (i : ℕ)
    (hch : (airBuild (K := K) i).children = [])
    (hstate : (airBuild (K := K) i).label.skel.state = State.s1) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α)
        (airBuild (K := K) i)).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α)
          (airBuild (K := K) i)).childLabel j) :=
  childLink_op1 z α _ hstate hch

theorem bfsAssign_air_recon :
    reconForest 1 (foCol (bfsForest [dotTreeAir (K := K)]))
        (bfsLabelAt (dotTreeAir (K := K)))
        (bfsForest [dotTreeAir (K := K)]).length =
      [bfsAssign (dotTreeAir (K := K))] := by
  rw [reconForest_one, bfsAssign]

theorem bfsForest_bfsAssign_air :
    bfsForest [bfsAssign (dotTreeAir (K := K))] =
      (List.range' 1 (bfsForest [dotTreeAir (K := K)]).length).map
        (buildTF 1 (foCol (bfsForest [dotTreeAir (K := K)]))
          (bfsLabelAt (dotTreeAir (K := K)))
          (bfsForest [dotTreeAir (K := K)]).length) := by
  rw [← bfsAssign_air_recon, bfsForest_reconForest]
  · exact Nat.le_refl 1
  · exact foCol_Sf_tilingF [dotTreeAir (K := K)] air_hne
  · exact foCol_BFSValidF [dotTreeAir (K := K)] air_hne

theorem dotTreeAir_bfs_fanout {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [dotTreeAir (K := K)]) :
    n.children.length = fanoutComp n.label.skel.state := by
  simp [dot_air_bfsForest] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem bfsAssign_air_children_len {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [bfsAssign (dotTreeAir (K := K))]) :
    n.children.length = fanoutComp n.label.skel.state := by
  have hne : [dotTreeAir (K := K)] ≠ [] := List.cons_ne_nil _ _
  have hSf := foCol_Sf_tilingF [dotTreeAir (K := K)] hne
  have hvalid := foCol_BFSValidF [dotTreeAir (K := K)] hne
  rw [bfsForest_bfsAssign_air, List.mem_map] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  obtain ⟨k, hk, hik⟩ := List.mem_range'.mp hi
  have hi1 : 1 ≤ i := by omega
  have hih : i ≤ (bfsForest [dotTreeAir (K := K)]).length := by omega
  have hch :
      (buildTF 1 (foCol (bfsForest [dotTreeAir (K := K)]))
          (bfsLabelAt (dotTreeAir (K := K)))
          (bfsForest [dotTreeAir (K := K)]).length i).children.length =
        foCol (bfsForest [dotTreeAir (K := K)]) i := by
    rw [buildTF_children, childIdxsF_eq (kroots := 1) _ _ hSf hvalid hi1 hih,
      List.length_map, List.length_range']
  rw [hch, buildTF_label]
  have hi' : i - 1 < (bfsForest [dotTreeAir (K := K)]).length := by omega
  have hfo :
      foCol (bfsForest [dotTreeAir (K := K)]) i =
        (bfsForest [dotTreeAir (K := K)])[i - 1].children.length := by
    simp [foCol, List.getElem?_eq_getElem hi']
  rw [hfo]
  have horig : (bfsForest [dotTreeAir (K := K)])[i - 1] ∈
      bfsForest [dotTreeAir (K := K)] := List.getElem_mem hi'
  have hfan := dotTreeAir_bfs_fanout horig
  have hskel :
      (bfsLabelAt (dotTreeAir (K := K)) i).skel =
        (bfsForest [dotTreeAir (K := K)])[i - 1].label.skel := by
    have hr : i - 1 < (bfsRows (dotTreeAir (K := K))).length := by
      simpa [bfsRows_length] using hi'
    rw [bfsLabelAt_skel _ i hr]
    simp [bfsRows]
  rw [hskel]
  exact hfan

theorem assigned_air_bfs_binding (z α : K) :
    ∀ t ∈ bfsForest [mapNTree (GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (dotTreeAir (K := K)))],
      RawComputeTopologyBinding t := by
  intro t ht
  rw [bfsForest_mapNTree_singleton] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  rw [bfsForest_bfsAssign_air, List.mem_map] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  change RawComputeTopologyBinding
    (mapNTree (GenComputeRow.row ∘ renderNode z α) (airBuild i))
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨?_, childLink_airBuild_op6 z α⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      rw [airBuild_label, bfsLabelAt_air_skel1]
      have hlen : (airBuild (K := K) 1).children.length = 2 := by
        rw [airBuild_children 1 (by omega) (by simp [dot_air_bfsForest]),
          List.length_map, List.length_range', foCol_air_1]
      rw [hlen]
      simp [genSkelOp6, fanoutComp]
      rfl
  · refine ⟨?_, childLink_airBuild_op2 z α⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      rw [airBuild_label]
      have hskel : (bfsLabelAt (dotTreeAir (K := K)) 2).skel = dotOp2Skel := by
        rw [bfsLabelAt_air_skel2]; rfl
      rw [hskel]
      have hlen : (airBuild (K := K) 2).children.length = 3 := by
        rw [airBuild_2_children]; rfl
      rw [hlen]
      simp [genSkelOp2, fanoutComp]
      rfl
  · refine ⟨?_, childLink_airBuild_op1 z α 3 airBuild_3_children ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      rw [airBuild_label, bfsLabelAt_air_skel3]
      have hlen : (airBuild (K := K) 3).children.length = 0 := by
        rw [airBuild_3_children]; rfl
      rw [hlen]
      simp [dotCondTree, skelNode, genSkelOp1, fanoutComp]
    · rw [airBuild_label, bfsLabelAt_air_skel3]
      rfl
  · refine ⟨?_, childLink_airBuild_op1 z α 4 airBuild_4_children ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      rw [airBuild_label, bfsLabelAt_air_skel4]
      have hlen : (airBuild (K := K) 4).children.length = 0 := by
        rw [airBuild_4_children]; rfl
      rw [hlen]
      simp [dotOp1BTree, skelNode, genSkelOp1, fanoutComp]
    · rw [airBuild_label, bfsLabelAt_air_skel4]
      rfl
  · refine ⟨?_, childLink_airBuild_op1 z α 5 airBuild_5_children ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      rw [airBuild_label, bfsLabelAt_air_skel5]
      have hlen : (airBuild (K := K) 5).children.length = 0 := by
        rw [airBuild_5_children]; rfl
      rw [hlen]
      simp [dotOp1CTree, skelNode, genSkelOp1, fanoutComp]
    · rw [airBuild_label, bfsLabelAt_air_skel5]
      rfl
  · refine ⟨?_, childLink_airBuild_op9 z α⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      rw [airBuild_label, bfsLabelAt_air_skel6]
      have hlen : (airBuild (K := K) 6).children.length = 2 := by
        rw [airBuild_6_children]; rfl
      rw [hlen]
      simp [genSkelOp9, fanoutComp]
      rfl
  · refine ⟨?_, childLink_airBuild_op1 z α 7 airBuild_7_children ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      rw [airBuild_label, bfsLabelAt_air_skel7]
      have hlen : (airBuild (K := K) 7).children.length = 0 := by
        rw [airBuild_7_children]; rfl
      rw [hlen]
      simp [dotOp9CoreTree, skelNode, genSkelOp1, fanoutComp]
    · rw [airBuild_label, bfsLabelAt_air_skel7]
      rfl
  · refine ⟨?_, childLink_airBuild_op1 z α 8 airBuild_8_children ?_⟩
    · rw [mapNTree_label, mapNTree_children, List.length_map]
      simp [Function.comp, renderNode_state]
      rw [airBuild_label, bfsLabelAt_air_skel8]
      have hlen : (airBuild (K := K) 8).children.length = 0 := by
        rw [airBuild_8_children]; rfl
      rw [hlen]
      simp [dotOp9InvokeTree, skelNode, genSkelOp1, fanoutComp]
    · rw [airBuild_label, bfsLabelAt_air_skel8]
      rfl

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.childLink_dotTreeAir_root
#print axioms Nock.NockVMROM.Thm54.TraceGen.rawComputeBinding_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.assigned_air_bfs_binding
