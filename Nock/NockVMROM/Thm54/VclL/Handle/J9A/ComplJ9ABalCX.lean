/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalCX.lean

  Case split on `l.chip`: `old` is J-8's `ComplJ8OfBalG.xEnt_par` (`colX9_old`); `s0B` / `s10B` are the new
  `.x` entries of `ents0New` / `ents2New` / `ents1New` from `SemN9`; `s10S` has no active `.x` entry. -/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABase
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.TeleX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalCX

open Nock Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc selS)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
  (slotsX9 slot0X9 slot1X9 slot2X9 slot3X9 statesX9 extSlot ents0New ents1New ents2New ents3New sS0B sS10B sS10S)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 ChipSt9 SemN9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castEntX castSlotX)

noncomputable section

section Aux
variable {F : Type} [Field F]

/-- The selector sum of an entry evaluates to the sum of its state columns. -/
theorem selS_eval9 (col : ℕ → F) (st : List ℕ) :
    (selS st : CoeffExpr F).eval (⟨col, col, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env F) =
      (st.map col).sum := by
  unfold ChipH.selS
  rw [CoeffExpr.eval_sumList]
  simp [ChipH.cc, CoeffExpr.eval]

/-- Every state of a twin entry is one of the twenty states. -/
theorem states_ok9 : ∀ S ∈ (slotsX9 : List (SlotX F)), ∀ x ∈ S.ents, ∀ i ∈ x.states, i ∈ statesX9 := by
  intro S hS x hx i hi
  rw [← Nock.NockVMROM.Thm54.VclL.Handle.TeleX9.slotsX9_cast (F := F)] at hS
  obtain ⟨S', hS', rfl⟩ := List.mem_map.mp hS
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
  exact (Nock.NockVMROM.Thm54.VclL.Handle.TeleX9.slotsX9_states_ok S' hS' x' hx').1 i hi

/-- Every state of a J-8 entry is below `17`. -/
theorem states_okX : ∀ S ∈ (ChipHX.slotsX : List (SlotX F)), ∀ x ∈ S.ents, ∀ i ∈ x.states, i < 17 := by
  intro S hS x hx i hi
  rw [← Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.slotsX_cast (F := F)] at hS
  obtain ⟨S', hS', rfl⟩ := List.mem_map.mp hS
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
  exact (Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX.slotsX_states_ok S' hS' x' hx').1 i hi

/-- Classification of the entries of the twin's slots. -/
theorem ent_cases9 (S : SlotX F) (hS : S ∈ (slotsX9 : List (SlotX F))) (x : EntX F) (hx : x ∈ S.ents) :
    (∃ S0 ∈ (ChipHX.slotsX : List (SlotX F)), x ∈ S0.ents) ∨ x ∈ (ents0New : List (EntX F)) ∨
      x ∈ (ents1New : List (EntX F)) ∨ x ∈ (ents2New : List (EntX F)) ∨ x ∈ (ents3New : List (EntX F)) := by
  simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · change x ∈ slot0X.ents ++ ents0New at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl ⟨slot0X, by simp [ChipHX.slotsX], h⟩
    · exact Or.inr (Or.inl h)
  · change x ∈ slot1X.ents ++ ents1New at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl ⟨slot1X, by simp [ChipHX.slotsX], h⟩
    · exact Or.inr (Or.inr (Or.inl h))
  · change x ∈ slot2X.ents ++ ents2New at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl ⟨slot2X, by simp [ChipHX.slotsX], h⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · change x ∈ slot3X.ents ++ ents3New at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl ⟨slot3X, by simp [ChipHX.slotsX], h⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end Aux

/-- **An active `.x` entry of the twin's slots at the honest columns of a J-9 A row `l` is a parent-cell
record `(parent, left, right)` with `hN l.rn parent = cell (hN l.rn left) (hN l.rn right)`.** `old` rows use
`RowOKX` and the `s3` decode (as J-8's `xEnt_par`); `s0B` / `s10B` rows use `SemN9`; `s10S` has no active `.x`
entry. -/
theorem xEnt_par9 {p : ℕ} [Fact p.Prime] {R : Nock.Jet.Registry} (H : Noun → ℕ × ℕ)
    (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (l : LX9) (fst lst : ZMod p)
    (hsem : SemN9 R l) (hok : l.chip = .old → HonestCompX.RowOKX p l.rn) (hH : HonestCompX.HdlOK p H)
    (hs3 : l.chip = .old → l.rn.st = .s3 → l.rn.sf1.isCell = true → l.rn.sf1 = .cell l.rn.ftth l.rn.fttt)
    (S : SlotX (ZMod p)) (hS : S ∈ (slotsX9 : List (SlotX (ZMod p)))) (x : EntX (ZMod p)) (hx : x ∈ S.ents)
    (hb : x.bal = .x)
    (hact : x.act.eval (⟨colX9 H pd idOf l fst lst, colX9 H pd idOf l fst lst, fun _ => 0, fun _ => 0⟩ :
      Nock.Reified.Env (ZMod p)) ≠ 0) :
    ∃ kP kL kR, x.rcd = cellRecX (hdX kP) (hdX kL) (hdX kR) ∧
      HonestCompX.hN l.rn kP = .cell (HonestCompX.hN l.rn kL) (HonestCompX.hN l.rn kR) ∧
      kP < 12 ∧ kL < 12 ∧ kR < 12 := by
  have hsel : (selS x.states : CoeffExpr (ZMod p)).eval
      (⟨colX9 H pd idOf l fst lst, colX9 H pd idOf l fst lst, fun _ => 0, fun _ => 0⟩ :
        Nock.Reified.Env (ZMod p)) ≠ 0 := fun h => hact (by simp [EntX.act, CoeffExpr.eval, h])
  rw [selS_eval9] at hsel
  rcases ent_cases9 S hS x hx with ⟨S0, hS0, hx0⟩ | h0 | h1 | h2 | h3
  · -- an entry of J-8's slots
    have hlt := states_okX S0 hS0 x hx0
    cases hc : l.chip
    · rw [colX9_old H pd idOf l fst lst hc] at hact
      have hact' : x.act.eval (⟨Nock.V1J8.FillX.colXE H pd l.rn fst lst, Nock.V1J8.FillX.colXE H pd l.rn fst lst,
          fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p)) ≠ 0 := by
        rw [Nock.V1J8.FillX.colXE_eq]; exact hact
      exact ComplJ8OfBalG.xEnt_par H pd l.rn fst lst (hok hc) hH (hs3 hc) S0 hS0 x hx0 hb hact'
    all_goals
      exfalso; apply hsel
      refine List.sum_eq_zero fun v hv => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
      have := hlt i hi
      simp [colX9, hc, colS0B, colS10B, colS10S, this]
  · -- `ents0New`: `(f; fh; ft)` on `s0B` / `s10B`
    simp only [ents0New, List.mem_singleton] at h0
    subst h0
    refine ⟨1, 5, 6, rfl, ?_, by decide, by decide, by decide⟩
    cases hc : l.chip
    · exfalso; apply hsel
      simp [colX9, hc, colX_ge69, sS0B, sS10B]
    · simp only [SemN9, hc] at hsem
      have h := hsem.1
      simp only [RowNX.SemN, hsem.2.1] at h
      exact h.2.1
    · simp only [SemN9, hc] at hsem
      have h := hsem.1
      simp only [RowNX.SemN, hsem.2.1] at h
      exact h.2.1
    · exfalso; apply hsel
      simp [colX9, hc, colS10S, sS0B, sS10B]
  · -- `ents1New`: `(ft; fth; ftt)` on `s10B` (the other entry is `.s`)
    simp only [ents1New, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl
    · refine ⟨6, 7, 8, rfl, ?_, by decide, by decide, by decide⟩
      cases hc : l.chip
      · exfalso; apply hsel
        simp [colX9, hc, colX_ge69, sS10B]
      · exfalso; apply hsel
        simp [colX9, hc, colS0B, sS10B]
      · simp only [SemN9, hc] at hsem
        have h := hsem.1
        simp only [RowNX.SemN, hsem.2.1] at h
        exact h.2.2.1
      · exfalso; apply hsel
        simp [colX9, hc, colS10S, sS10B]
    · simp at hb
  · -- `ents2New`: `(fth; ftth; fttt)` on `s10B`
    simp only [ents2New, List.mem_singleton] at h2
    subst h2
    refine ⟨7, 9, 10, rfl, ?_, by decide, by decide, by decide⟩
    cases hc : l.chip
    · exfalso; apply hsel
      simp [colX9, hc, colX_ge69, sS10B]
    · exfalso; apply hsel
      simp [colX9, hc, colS0B, sS10B]
    · simp only [SemN9, hc] at hsem
      have h := hsem.1
      simp only [RowNX.SemN, hsem.2.1] at h
      exact h.2.2.2.1
    · exfalso; apply hsel
      simp [colX9, hc, colS10S, sS10B]
  · -- `ents3New`: both entries are `.s`
    simp only [ents3New, List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with rfl | rfl <;> simp at hb

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalCX

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalCX
#print axioms xEnt_par9
end Axioms
