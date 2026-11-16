/-
  Nock/NockVMROM/Thm54/TraceGen/GenConsHead.lean

  **At a `cons` row the formula head is a cell.**

  This is the one shape fact `rowBad_card_le_of_shape` takes as a hypothesis, and the
  last structural step before `V_comp` is generic.  It is not cosmetic: at a `cons` row `hdyck` asks
  `(encC z (formulaHead s.formula)).dyck ≠ 0`, and an **atom**'s dyck fingerprint is `0`, so if a `cons` row could carry an atom head the condition would be false at
  *every* seed and no bad-seed bound could exist.

  `RowCellIdentities.formula_cons` (`CensusExtraClosure.lean:1326`) gives
  `s.formula =.cell (skeletonDec s.f_h) (skeletonDec s.f_t)` at every row — the formula is always
  a cell — but `f_h` is the **opcode atom** at an opcode row, so that says nothing about the head
  being a cell.

  The generator settles it by construction: `genComputeSkeleton` (`Gen.lean:546`) emits a `cons` row
  in exactly one branch, `|.cell (.cell lh lt) rtail =>`, and `genSkelCons` (`Gen.lean:115`) sets
  `formula :=.cell leftF rightF` with `leftF =.cell lh lt`.  Every other branch matches
  `.cell (.atom op) tail` and sets a non-`cons` state.  So the induction is: at the `cons` node the
  head is `.cell lh lt`; at every opcode node the `state =.cons` hypothesis is contradictory; and
  children follow by the inductive hypothesis.

  Proof shape mirrors `genComputeSkeleton_inTree_fanout` (`GenSkeletonFanout.lean:31`) case for case
  — same twelve-way `nat_lt_twelve_or_ge` split, same recursive-call destructuring — with each
  `here` case discharging the state hypothesis instead of computing a fan-out.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

/-- **At a `cons` row of any accepted program, the formula head is a cell.**

The hypothesis `rowBad_card_le_of_shape` needs, discharged. -/
theorem genComputeSkeleton_inTree_consHead
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    u.label.skel.state = State.cons →
      ∃ a b, formulaHead u.label.skel.formula = Noun.cell a b := by
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
              intro _
              refine ⟨lh, lt, ?_⟩
              simp [skelNode, genSkelCons, formulaHead]
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
                intro hst
                simp [skelNode, genSkelOp0] at hst
              | sub hs _ =>
                simp [NTree.children] at hs
        · -- OP_1
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            intro hst
            simp [skelNode, genSkelOp1] at hst
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
                    intro hst
                    simp [skelNode, genSkelOp2] at hst
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
              intro hst
              simp [skelNode, genSkelOp3] at hst
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
                intro hst
                simp [skelNode, genSkelOp4] at hst
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
                  intro hst
                  simp [skelNode, genSkelOp5] at hst
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
                        intro hst
                        simp [skelNode, genSkelOp6] at hst
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
                          intro hst
                          simp [skelNode, genSkelOp6] at hst
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
                  intro hst
                  simp [skelNode, genSkelOp7] at hst
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
                  intro hst
                  simp [skelNode, genSkelOp8] at hst
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
                      intro hst
                      simp [skelNode, genSkelOp9] at hst
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

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_inTree_consHead
