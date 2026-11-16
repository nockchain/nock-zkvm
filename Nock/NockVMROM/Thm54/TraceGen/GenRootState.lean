/-
  Nock/NockVMROM/Thm54/TraceGen/GenRootState.lean

  Generator-side root state.

  `genComputeSkeleton` classifies the formula the same way `rootStateOfFormula` does:
  a cell head is `cons`; an atom head `op` is `stateOfOpcode op`; unsupported opcodes
  (`10`, `11`, `≥ 12`) and atom formulas are `.error`.  No case is vacuous.

  `Gen.lean` is not edited.

  Paper: the paper.  Lean: `ComputeWalkSeed.rootStateOfFormula`,
  `TraceGen/Gen.lean::genComputeSkeleton`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout
import Nock.NockVMROM.Thm54.ComputeWalkSeed
import Nock.NockVMROM.Thm54.SemanticStrategy

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000


theorem rootStateOfFormula_cell_atom (op : ℕ) (tl : Noun) :
    rootStateOfFormula (.cell (.atom op) tl) = stateOfOpcode op :=
  rfl

theorem rootStateOfFormula_cell_cell (lh lt r : Noun) :
    rootStateOfFormula (.cell (.cell lh lt) r) = .cons :=
  rfl

theorem rootStateOfFormula_atom (k : ℕ) :
    rootStateOfFormula (.atom k) = .cons :=
  rfl

theorem stateOfOpcode_toNat {st : State} (hne : st ≠ .cons) :
    stateOfOpcode st.toNat = st := by
  cases st <;> first | contradiction | rfl

/-- **The generated root state's opcode is the public formula's head**.
    The root projection is `NTree.label` of the emitted tree; `skelNode` copies
    `genSkel*`'s `state`.  Unsupported opcodes are `.error`. -/
theorem genComputeSkeleton_root_state
    (fuel : ℕ) (subject formula : Noun)
    (t : NTree (GenComputeRow K)) (result : Noun)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    t.label.skel.state = rootStateOfFormula formula := by
  induction fuel generalizing subject formula t result with
  | zero =>
    simp [genComputeSkeleton] at h
  | succ n _ih =>
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ => simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [skelNode, genSkelCons, rootStateOfFormula_cell_cell]
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · cases tl with
          | cell _ _ => simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hslot] at h
            | some _ =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [skelNode, genSkelOp0, rootStateOfFormula_cell_atom, stateOfOpcode]
        · simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [skelNode, genSkelOp1, rootStateOfFormula_cell_atom, stateOfOpcode]
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  simp [skelNode, genSkelOp2, rootStateOfFormula_cell_atom, stateOfOpcode]
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [skelNode, genSkelOp3, rootStateOfFormula_cell_atom, stateOfOpcode]
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none => simp [genComputeSkeleton, hcall, hlus] at h
            | some _ =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [skelNode, genSkelOp4, rootStateOfFormula_cell_atom, stateOfOpcode]
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [skelNode, genSkelOp5, rootStateOfFormula_cell_atom, stateOfOpcode]
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ => simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ => simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp [skelNode, genSkelOp6, rootStateOfFormula_cell_atom, stateOfOpcode]
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        simp [skelNode, genSkelOp6, rootStateOfFormula_cell_atom, stateOfOpcode]
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [skelNode, genSkelOp7, rootStateOfFormula_cell_atom, stateOfOpcode]
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [skelNode, genSkelOp8, rootStateOfFormula_cell_atom, stateOfOpcode]
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none => simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ => simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    simp [skelNode, genSkelOp9, rootStateOfFormula_cell_atom, stateOfOpcode]
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

/-- `BindComputeRow` copies the skeleton state onto the committed row (`row.state = skeleton.state`).
    Combined with `genComputeSkeleton_root_state` this is the row-level root-state fact. -/
theorem BindComputeRow_root_state
    {z : K} {s : ComputeRowSkeleton}
    {row : State × ComputeTable.DTcomp K}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (hgen : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hskel : s = t.label.skel)
    (hbind : BindComputeRow z s row) :
    row.2.2.1.state = rootStateOfFormula formula := by
  have hst : row.2.2.1.state = s.state := hbind.2.2.1
  rw [hst, hskel, genComputeSkeleton_root_state fuel subject formula t result hgen]

/-- F73 unfolding: formula `[1 2]` has head atom `1`, so the root state is `OP_1`.  Not bare `rfl` on a generated skeleton. -/
theorem f73_formula_root_state :
    rootStateOfFormula (.cell (.atom 1) (.atom 2)) = .s1 := by
  rw [rootStateOfFormula_cell_atom]
  rfl

/-- F97 unfolding: formula `[5 …]` has head atom `5`, so the root state is `OP_5`.  Not bare `rfl` on a generated skeleton. -/
theorem f97_formula_root_state (tl : Noun) :
    rootStateOfFormula (.cell (.atom 5) tl) = .s5 := by
  rw [rootStateOfFormula_cell_atom]
  rfl

theorem genComputeSkeleton_root_state_K_is_parameter
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    t.label.skel.state = rootStateOfFormula formula :=
  genComputeSkeleton_root_state (K := K) fuel subject formula t result h

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_root_state
#print axioms Nock.NockVMROM.Thm54.TraceGen.BindComputeRow_root_state
#print axioms Nock.NockVMROM.Thm54.TraceGen.f73_formula_root_state
#print axioms Nock.NockVMROM.Thm54.TraceGen.f97_formula_root_state
