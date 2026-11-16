/-
  Nock/NockVMROM/Thm54/VclL/Handle/ChildLinkH.lean

  Additive.

  `childNouns r` is the noun form of `ChipH.children` (the `(subject, formula, evaluation)` the parent's own
  columns designate for each child, per state).  `inTree_childCols` / `airReorder_childCols`: the skeleton
  of every node of a generated (and AIR-reordered) tree has child triples equal to `childNouns` of its
  hosted honest row (the generator induction of `inTree_rowShape`, with the new conclusion);
  `child_link_nouns`: in the committed BFS tree, every child's `(s, f, e)` nouns are `childNouns` of its
  parent's row (with `childrenMatchSf` from the AIR link).  So `childLinkComp` at handle labels is the
  image of this under `hdl`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestMh

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.VclL

/-- The `(subject, formula, evaluation)` nouns of the children of a row, per state, read off the row's own
columns (the noun form of `ChipH.children`). -/
def childNouns (r : RowN) : List (Noun × Noun × Noun) :=
  match r.op with
  | 2 => [(r.s, r.fth, r.sf1), (r.s, r.ftt, r.sf2), (r.sf1, r.sf2, r.e)]
  | 3 => [(r.s, r.ft, r.sf1)]
  | 4 => [(r.s, r.ft, r.sf1)]
  | 5 => [(r.s, r.fth, r.sf1), (r.s, r.ftt, r.sf2)]
  | 6 => [(r.s, r.m, r.sf1), (r.s, r.fth, r.sf2)]
  | 7 => [(r.sf2, r.ftt, r.sf1), (r.s, r.fth, r.sf2)]
  | 8 => [(r.m, r.ftt, r.sf1), (r.s, r.fth, r.sf2)]
  | 9 => [(r.s, r.ftt, r.sf1), (r.sf1, r.m, r.sf2)]
  | 10 => [(r.s, r.fh, r.sf1), (r.s, r.ft, r.sf2)]
  | _ => []

/-- The skeleton's child triples are the nouns the parent's columns designate. -/
def ChildCols (sk : ComputeRowSkeleton) : Prop :=
  ∀ i : Fin 3, ∀ hi : (i : ℕ) < fanoutComp sk.state,
    (sk.subformula i hi .subject, sk.subformula i hi .formula, sk.subformula i hi .result) =
      (childNouns (rowOfSkelH sk)).getD i (.atom 0, .atom 0, .atom 0)

section Shape
variable {K : Type} [Field K]

/-- **Every node of a generated tree has a semantic noun row matching its skeleton.** -/
theorem inTree_childCols
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    ChildCols u.label.skel := by
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
              simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelCons, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
            | some slotR =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp0, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
              | sub hs _ =>
                simp [NTree.children] at hs
        · -- OP_1
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp1, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
                    simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp2, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
              simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp3, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
            | some rr =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨k, hk, hrr⟩ := lus_eq_some hlus
              cases hu with
              | here =>
                simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp4, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
                  simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp5, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
                        simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp6, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
                          simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp6, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
                  simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp7, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
                  simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp8, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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
                      simp [ChildCols, childNouns, rowOfSkelH, rowOfSkel, childT, skelNode, genSkelOp9, fanoutComp, VclL.hdN, VclL.tlN, Fin.forall_fin_succ, P8Census.skeletonSubformula]
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

/-- **Transport to the AIR-reordered tree.** -/
theorem airReorder_childCols
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree (airReorder t) u) :
    ChildCols u.label.skel := by
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hu
  rw [hl]; exact inTree_childCols h u0 hu0

/-- **The child link at nouns** (`childLinkComp` over handle labels, noun form): in the committed
(AIR-reordered, BFS) tree, the `(s, f, e)` nouns of the `i`-th child of every node are the nouns the
parent's own handle columns designate for it (`childNouns` of the hosted honest row, the noun form of
`ChipH.children`).  From `childrenMatchSf` (the existing AIR link) and `ChildCols`. -/
theorem child_link_nouns
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    {n : NTree (GenComputeRow K)} (hn : n ∈ bfsForest [airReorder t])
    (i : Fin 3) (hi : (i : ℕ) < n.children.length) :
    ((n.children[i]'hi).label.skel.subject, (n.children[i]'hi).label.skel.formula,
      (n.children[i]'hi).label.skel.evaluation) =
      (childNouns (rowOfSkelH n.label.skel)).getD i (.atom 0, .atom 0, .atom 0) := by
  have hL : AirLinked (airReorder t) := airLinked_airReorder_of_gen h
  have hm := childrenMatchSf_bfs_of_AirLinked hL hn i hi
  have hfan : n.children.length = fanoutComp n.label.skel.state :=
    airReorder_inTree_fanout (fun v hv => genComputeSkeleton_inTree_fanout h v hv) n
      (inTree_of_mem_bfsForest_singleton hn)
  have hi' : (i : ℕ) < fanoutComp n.label.skel.state := hfan ▸ hi
  have hc := airReorder_childCols h n (inTree_of_mem_bfsForest_singleton hn) i hi'
  rw [← hc]
  simp only [P8Census.skeletonSubformula, dif_pos hi'] at hm
  rw [hm.1, hm.2.1, hm.2.2]

end Shape

end Nock.NockVMROM.Thm54.VclL.Handle
