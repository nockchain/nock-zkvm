/-
  Nock/NockVMROM/Thm54/TraceGen/GenSkeletonFanout.lean

  Every node of a `genComputeSkeleton` tree has paper compute fan-out
  (`fanoutComp` of its skeleton state).  Used to lift `ComputeNodesOK`
  off named BFS forests (Tier A) onto opaque generated trees (matmul).

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open ComputeTable

variable {K : Type} [Field K]

/-- Opcode heads that `genComputeSkeleton` classifies. -/
theorem nat_lt_twelve_or_ge (op : ℕ) :
    op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨
      op = 6 ∨ op = 7 ∨ op = 8 ∨ op = 9 ∨ op = 10 ∨ op = 11 ∨ 12 ≤ op := by
  omega

/-- Every node of a successfully generated compute tree has paper fan-out. -/
theorem genComputeSkeleton_inTree_fanout
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    u.children.length = fanoutComp u.label.skel.state := by
  induction fuel generalizing subject formula t result u with
  | zero =>
    simp [genComputeSkeleton] at h
  | succ n ih =>
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ =>
          simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              simp [skelNode, genSkelCons, fanoutComp]
            | sub hs hu' =>
              simp [NTree.children] at hs
              rcases hs with rfl | rfl
              · exact ih hL _ hu'
              · exact ih hR _ hu'
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · -- OP_0
          cases tl with
          | cell _ _ =>
            simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none =>
              simp [genComputeSkeleton, hslot] at h
            | some _ =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                simp [skelNode, genSkelOp0, fanoutComp]
              | sub hs _ =>
                simp [NTree.children] at hs
        · -- OP_1
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            simp [skelNode, genSkelOp1, fanoutComp]
          | sub hs _ =>
            simp [NTree.children] at hs
        · -- OP_2
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  cases hu with
                  | here =>
                    simp [skelNode, genSkelOp2, fanoutComp]
                  | sub hs hu' =>
                    simp [NTree.children] at hs
                    rcases hs with rfl | rfl | rfl
                    · exact ih hB _ hu'
                    · exact ih hC _ hu'
                    · exact ih hM _ hu'
        · -- OP_3
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              simp [skelNode, genSkelOp3, fanoutComp]
            | sub hs hu' =>
              simp [NTree.children] at hs
              cases hs
              exact ih hcall _ hu'
        · -- OP_4
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none =>
              simp [genComputeSkeleton, hcall, hlus] at h
            | some _ =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                simp [skelNode, genSkelOp4, fanoutComp]
              | sub hs hu' =>
                simp [NTree.children] at hs
                cases hs
                exact ih hcall _ hu'
        · -- OP_5
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  simp [skelNode, genSkelOp5, fanoutComp]
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        · -- OP_6
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ =>
              simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ =>
                simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ =>
                  simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      cases hu with
                      | here =>
                        simp [skelNode, genSkelOp6, fanoutComp]
                      | sub hs hu' =>
                        simp [NTree.children] at hs
                        rcases hs with rfl | rfl
                        · exact ih hcond _ hu'
                        · exact ih htaken _ hu'
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        cases hu with
                        | here =>
                          simp [skelNode, genSkelOp6, fanoutComp]
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · exact ih hcond _ hu'
                          · exact ih htaken _ hu'
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · -- OP_7
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  simp [skelNode, genSkelOp7, fanoutComp]
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        · -- OP_8
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  simp [skelNode, genSkelOp8, fanoutComp]
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        · -- OP_9
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ =>
              simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none =>
                  simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    cases hu with
                    | here =>
                      simp [skelNode, genSkelOp9, fanoutComp]
                    | sub hs hu' =>
                      simp [NTree.children] at hs
                      rcases hs with rfl | rfl
                      · exact ih hcore _ hu'
                      · exact ih hinv _ hu'
        · -- OP_10 notROM
          simp [genComputeSkeleton] at h
        · -- OP_11 notROM
          simp [genComputeSkeleton] at h
        · -- ≥ 12 malformed
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

/-- BFS rows of a generated tree inherit paper fan-out -/
theorem genComputeSkeleton_bfs_fanout
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [t]) :
    n.children.length = fanoutComp n.label.skel.state := by
  have hin : InTree t n := by
    have := (mem_bfsForest [t] n).mp hn
    obtain ⟨c, hc, hct⟩ := this
    simp at hc
    subst c
    exact hct
  exact genComputeSkeleton_inTree_fanout h n hin

/-! ## `bfsAssign` preserves paper fan-out -/

theorem bfsAssign_recon (t : NTree (GenComputeRow K)) :
    reconForest 1 (foCol (bfsForest [t])) (bfsLabelAt t) (bfsForest [t]).length =
      [bfsAssign t] := by
  rw [reconForest_one, bfsAssign]

theorem bfsForest_bfsAssign (t : NTree (GenComputeRow K)) :
    bfsForest [bfsAssign t] =
      (List.range' 1 (bfsForest [t]).length).map
        (buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t) (bfsForest [t]).length) := by
  have hne : [t] ≠ [] := List.cons_ne_nil _ _
  rw [← bfsAssign_recon, bfsForest_reconForest]
  · exact Nat.le_refl 1
  · exact foCol_Sf_tilingF [t] hne
  · exact foCol_BFSValidF [t] hne

/-- Assigned-tree BFS nodes have paper fan-out whenever the original forest does. -/
theorem bfsAssign_children_len_of_fanout (t : NTree (GenComputeRow K))
    (hfan : ∀ n ∈ bfsForest [t],
      n.children.length = fanoutComp n.label.skel.state)
    {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [bfsAssign t]) :
    n.children.length = fanoutComp n.label.skel.state := by
  have hne : [t] ≠ [] := List.cons_ne_nil _ _
  have hSf := foCol_Sf_tilingF [t] hne
  have hvalid := foCol_BFSValidF [t] hne
  rw [bfsForest_bfsAssign, List.mem_map] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  obtain ⟨k, hk, hik⟩ := List.mem_range'.mp hi
  have hi1 : 1 ≤ i := by omega
  have hih : i ≤ (bfsForest [t]).length := by omega
  have hch :
      (buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t) (bfsForest [t]).length i).children.length =
        foCol (bfsForest [t]) i := by
    rw [buildTF_children, childIdxsF_eq (kroots := 1) _ _ hSf hvalid hi1 hih,
      List.length_map, List.length_range']
  rw [hch, buildTF_label]
  have hi' : i - 1 < (bfsForest [t]).length := by omega
  have hfo :
      foCol (bfsForest [t]) i = (bfsForest [t])[i - 1].children.length := by
    simp [foCol, List.getElem?_eq_getElem hi']
  rw [hfo]
  have horig : (bfsForest [t])[i - 1] ∈ bfsForest [t] := List.getElem_mem hi'
  have hskel : (bfsLabelAt t i).skel = (bfsForest [t])[i - 1].label.skel := by
    have hr : i - 1 < (bfsRows t).length := by
      simpa [bfsRows_length] using hi'
    rw [bfsLabelAt_skel t i hr]
    simp [bfsRows]
  rw [hskel]
  exact hfan _ horig

theorem genComputeSkeleton_bfsAssign_fanout
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [bfsAssign t]) :
    n.children.length = fanoutComp n.label.skel.state :=
  bfsAssign_children_len_of_fanout t
    (fun _ hn => genComputeSkeleton_bfs_fanout h hn) hn

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_inTree_fanout
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfs_fanout
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfsAssign_fanout
