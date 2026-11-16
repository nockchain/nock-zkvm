/-
  Nock/NockVMROM/Thm54/VclL/Handle/PathKeyShape.lean

  **The path keys of the generated rows**.  Additive.

  `pkOf r` is the OP0 / OP9 path read of the noun row `r` (`(s, ft)` on OP0, `(sf1, fth)` on OP9).
  `inTree_pathKeys`: every node of a generated tree has `rowPathKeys g = pkOf (rowOfSkel g.skel)`;
  the induction mirrors `inTree_rowShape`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestShape
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRows
import Nock.NockVMROM.Thm54.TraceGen.GenSlotKeys
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowTerms

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticStrategy

/-- The OP0 / OP9 path read of a noun row. -/
def pkOf (r : RowN) : List (Noun × ℕ) :=
  (if r.op = 0 then [(r.s, atomVal r.ft)] else []) ++
  (if r.op = 9 then [(r.sf1, atomVal r.fth)] else [])

section Shape
variable {K : Type} [Field K]

/-- The path-key shape of a node. -/
def PKS (g : GenComputeRow K) : Prop := VclL.rowPathKeys g = pkOf (rowOfSkel g.skel)
open Nock.NockVMROM.Thm54.VclL.Compute in
theorem rpk_eq (g : GenComputeRow K) :
    VclL.rowPathKeys g = match g.skel.state with
      | .s0 => (VclL.rowSlotKeys g)[1]?.toList
      | .s9 => (VclL.rowSlotKeys g)[2]?.toList
      | _ => [] := by
  unfold VclL.rowPathKeys VclL.rowKeysAt
  rw [Compute.TowerD.path_slots]
  cases g.skel.state <;> simp
  · cases h : (rowSlotKeys g)[1]? <;> simp [List.filterMap, h]
  · cases h : (rowSlotKeys g)[2]? <;> simp [List.filterMap, h]

theorem inTree_pathKeys
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    PKS u.label := by
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
              simp [rowOfSkel, childT, skelNode, genSkelCons, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                simp [rowOfSkel, childT, skelNode, genSkelOp0, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
              | sub hs _ =>
                simp [NTree.children] at hs
        · -- OP_1
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            simp [rowOfSkel, childT, skelNode, genSkelOp1, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                    simp [rowOfSkel, childT, skelNode, genSkelOp2, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
              simp [rowOfSkel, childT, skelNode, genSkelOp3, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                simp [rowOfSkel, childT, skelNode, genSkelOp4, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                  simp [rowOfSkel, childT, skelNode, genSkelOp5, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                        simp [rowOfSkel, childT, skelNode, genSkelOp6, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                          simp [rowOfSkel, childT, skelNode, genSkelOp6, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                  simp [rowOfSkel, childT, skelNode, genSkelOp7, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                  simp [rowOfSkel, childT, skelNode, genSkelOp8, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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
                      simp [rowOfSkel, childT, skelNode, genSkelOp9, fanoutComp, VclL.hdN, VclL.tlN, PKS, pkOf, rpk_eq, VclL.rowSlotKeys, atomVal]
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


end Shape

end Nock.NockVMROM.Thm54.VclL.Handle
