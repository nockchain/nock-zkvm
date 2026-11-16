/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestShape.lean

  Additive; `Gen.lean` is read, never edited.

  `RowN` is the noun data one honest compute row of `computeChipVCLH` is built from (formula
  decomposition, the two sub-evaluations `sf1 / sf2`, the hosted multipurpose noun `m`), in the chip's
  conventions (`ChipH.children`): OP5 `sf1 sf2` = operands; OP6 `sf1` = taken result, `sf2` = condition,
  `m` = taken formula; OP7 `sf2` = helper `sb`, `sf1` = result; OP8 `m = [sb s]`, `sf2 = sb`;
  OP9 `sf1` = core, `m` = arm, `sf2` = result.

  `RowN.Sem` is the per-opcode semantic content the chip's gates need, and
  `inTree_rowShape` / `genRowsT_rowShape`-style transport show EVERY node of a generated tree
  (and of the AIR-reordered tree) has a `RowN` with `Sem` matching its skeleton.  The induction
  mirrors `genComputeSkeleton_inTree_fanout`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenMemTable
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

namespace Nock.NockVMROM.Thm54.VclL.Handle


open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticStrategy

/-- The chip's op index of a compute state (`OP_j` at `j`, `cons` at `10`). -/
def opOfState : State → ℕ
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4 | .s5 => 5 | .s6 => 6 | .s7 => 7
  | .s8 => 8 | .s9 => 9 | .cons => 10

/-- **The noun data of one honest handle row.** -/
structure RowN where
  op : ℕ
  s : Noun
  f : Noun
  e : Noun
  fh : Noun := .atom 0
  ft : Noun := .atom 0
  fth : Noun := .atom 0
  ftt : Noun := .atom 0
  ftth : Noun := .atom 0
  fttt : Noun := .atom 0
  sf1 : Noun := .atom 0
  sf2 : Noun := .atom 0
  m : Noun := .atom 0

/-- **The per-opcode semantic content of a row** (what the chip's gates need, at noun level). -/
def RowN.Sem (r : RowN) : Prop :=
  match r.op with
  | 0 => r.fh = .atom 0 ∧ r.f = .cell r.fh r.ft ∧ ∃ ax, r.ft = .atom ax ∧ Noun.slot ax r.s = some r.e
  | 1 => r.fh = .atom 1 ∧ r.f = .cell r.fh r.ft ∧ r.e = r.ft
  | 2 => r.fh = .atom 2 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt
  | 3 => r.fh = .atom 3 ∧ r.f = .cell r.fh r.ft ∧ r.e = Noun.wut r.sf1
  | 4 => r.fh = .atom 4 ∧ r.f = .cell r.fh r.ft ∧ ∃ n, r.sf1 = .atom n ∧ r.e = .atom (n + 1)
  | 5 => r.fh = .atom 5 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.e = Noun.tis r.sf1 r.sf2
  | 6 => r.fh = .atom 6 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧
      r.ftt = .cell r.ftth r.fttt ∧ r.e = r.sf1 ∧
      ((r.sf2 = .atom 0 ∧ r.m = r.ftth) ∨ (r.sf2 = .atom 1 ∧ r.m = r.fttt))
  | 7 => r.fh = .atom 7 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf1
  | 8 => r.fh = .atom 8 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf1 ∧
      r.m = .cell r.sf2 r.s
  | 9 => r.fh = .atom 9 ∧ r.f = .cell r.fh r.ft ∧ r.ft = .cell r.fth r.ftt ∧ r.e = r.sf2 ∧
      ∃ ax, r.fth = .atom ax ∧ Noun.slot ax r.sf1 = some r.m
  | 10 => (∃ a b, r.fh = .cell a b) ∧ r.f = .cell r.fh r.ft ∧ r.e = .cell r.sf1 r.sf2
  | _ => False

/-- The result / formula / subject noun of the `i`-th child of a skeleton row (`atom 0` when absent). -/
def childT (sk : ComputeRowSkeleton) (i : Fin 3) (slot : TripleSlot) : Noun :=
  if h : (i : ℕ) < fanoutComp sk.state then sk.subformula i h slot else .atom 0

/-- **The honest noun row of a skeleton row** (chip conventions, see the header). -/
def rowOfSkel (sk : ComputeRowSkeleton) : RowN :=
  let f := sk.formula
  let ft := VclL.tlN f
  let ftt := VclL.tlN ft
  let c0 := childT sk 0 .result
  let c1 := childT sk 1 .result
  match sk.state with
  | .s0 => { op := 0, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft }
  | .s1 => { op := 1, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft }
  | .s2 => { op := 2, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft,
             fth := VclL.hdN ft, ftt := ftt, sf1 := c0, sf2 := c1 }
  | .s3 => { op := 3, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft,
             sf1 := c0 }
  | .s4 => { op := 4, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft,
             sf1 := c0 }
  | .s5 => { op := 5, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft,
             fth := VclL.hdN ft, ftt := ftt, sf1 := c0, sf2 := c1 }
  | .s6 => { op := 6, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft,
             fth := VclL.hdN ft, ftt := ftt, ftth := VclL.hdN ftt,
             fttt := VclL.tlN ftt, sf1 := c0, sf2 := c1,
             m := if c1 = .atom 0 then VclL.hdN ftt else VclL.tlN ftt }
  | .s7 => { op := 7, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft,
             fth := VclL.hdN ft, ftt := ftt, sf1 := c0, sf2 := c1 }
  | .s8 => { op := 8, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft,
             fth := VclL.hdN ft, ftt := ftt, sf1 := c0, sf2 := c1,
             m := .cell c1 sk.subject }
  | .s9 => { op := 9, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f, ft := ft,
             fth := VclL.hdN ft, ftt := ftt, sf1 := c0, sf2 := c1,
             m := childT sk 1 .formula }
  | .cons => { op := 10, s := sk.subject, f := f, e := sk.evaluation, fh := VclL.hdN f,
               ft := ft, sf1 := c0, sf2 := c1 }

section Shape
variable {K : Type} [Field K]

/-- **Every node of a generated tree has a semantic noun row matching its skeleton.** -/
theorem inTree_rowShape
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    (rowOfSkel u.label.skel).Sem := by
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
              simp [rowOfSkel, childT, skelNode, genSkelCons, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
                simp [rowOfSkel, childT, skelNode, genSkelOp0, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
                exact hslot
              | sub hs _ =>
                simp [NTree.children] at hs
        · -- OP_1
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            simp [rowOfSkel, childT, skelNode, genSkelOp1, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
                    simp [rowOfSkel, childT, skelNode, genSkelOp2, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
              simp [rowOfSkel, childT, skelNode, genSkelOp3, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
                simp [rowOfSkel, childT, skelNode, genSkelOp4, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
                exact ⟨k, hk, hrr⟩
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
                  simp [rowOfSkel, childT, skelNode, genSkelOp5, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
                        simp [rowOfSkel, childT, skelNode, genSkelOp6, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
                          simp [rowOfSkel, childT, skelNode, genSkelOp6, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
                  simp [rowOfSkel, childT, skelNode, genSkelOp7, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
                  simp [rowOfSkel, childT, skelNode, genSkelOp8, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
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
                      simp [rowOfSkel, childT, skelNode, genSkelOp9, fanoutComp, VclL.hdN, VclL.tlN, RowN.Sem]
                      exact hslot
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

/-- **Transport to the AIR-reordered tree** (the committed tree whose BFS rows are the trace). -/
theorem airReorder_rowShape
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree (airReorder t) u) :
    (rowOfSkel u.label.skel).Sem := by
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hu
  rw [hl]; exact inTree_rowShape h u0 hu0

end Shape

end Nock.NockVMROM.Thm54.VclL.Handle
