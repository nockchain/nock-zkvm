/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalPC.lean

* `pSum9`: twin of `ComplJ8OfBalG.pSum` over `slotsX9` / `HonestTraceX9.env0`.
  * `pSum9_expand`: `pSum9 = pRow` (J-8's `pRow` VERBATIM: the new J-9 A slot entries are `.x` / `.s`, never `.p`).
  * `pRow_row9`: per row kind (`old`, `s0B`, `s10B`, `s10S`), `pRow` at the honest columns `colX9` is the `Tc` total
    over the row's walk entries `consEntriesX9`, with the `2 ≤ axis` filter.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ACompRow
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AReads
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestTraceX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfComp
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.TeleX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABase
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalPW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPC

noncomputable section

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (pRow Tc DX_walk)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (slotsX9 slot0X9 slot1X9 slot2X9 slot3X9 extSlot
  ents0New ents1New ents2New ents3New)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 ChipSt9 SemN9 segRow)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 colS0B colS10B colS10S)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (consEntriesX9)
open Nock.J9A.NounAx (top segRd)

section P9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
  (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The `.p` reciprocal sum of a J-9 A compute row: twin of `ComplJ8OfBalG.pSum` over `slotsX9`. -/
def pSum9 (j : ℕ) : 𝕂′ :=
  ((slotsX9 (F := ℚ)).map fun S => ((S.ents.filter fun x => decide (x.bal = Bal.p)).map fun x =>
    algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act (HonestTraceX9.env0 H pd idOf W chalV pubVal j)) *
      (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
        (HonestTraceX9.env0 H pd idOf W chalV pubVal j) x.rcd)⁻¹).sum +
    (match S.pair with
     | some (fl, a, c, bb) => if bb = Bal.p then
         algebraMap (ZMod p) 𝕂′ ((HonestTraceX9.env0 H pd idOf W chalV pubVal j).trace fl) *
          ((DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
              (HonestTraceX9.env0 H pd idOf W chalV pubVal j) a)⁻¹ +
           (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
              (HonestTraceX9.env0 H pd idOf W chalV pubVal j) c)⁻¹)
         else 0
     | none => 0)).sum

/-- **`pSum9_expand`**: the `.p` sum of a J-9 A compute row is J-8's `pRow` at the row's columns (the new
entries of `slotsX9` are `.x` / `.s`, so the `.p` part is J-8's formula unchanged). -/
theorem pSum9_expand (χ : Coins frameJ8 K) (j : ℕ) :
    pSum9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j =
      pRow δ (HonestTraceX9.env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace χ := by
  unfold pSum9 pRow
  set e := HonestTraceX9.env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j with he
  have hch : e.chal = VerJ8.chalVJ8 b χ := rfl
  simp only [slotsX9, slot0X9, slot1X9, slot2X9, slot3X9, extSlot, ents0New, ents1New, ents2New, ents3New,
    ChipHX.slotsX, ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.filter_cons, List.filter_nil, List.cons_append, List.nil_append,
    List.append_nil]
  simp [DX_walk δ b e χ hch, EntX.act, ChipHX.evalQX, ChipH.selS, ChipH.notC, ChipH.cc, CoeffExpr.sumList,
    ChipHX.xS, ChipHX.xE, ChipHX.xSf1, ChipHX.xSf2, ChipHX.xFt, ChipHX.xFth, ChipHX.xFtth, ChipHX.xFttt,
    ChipHX.xM, ChipHX.hdX, ChipHX.vX, ChipHX.z1X, ChipHX.prX, ChipHX.sS10, ChipHX.pr2X]
  ring

end P9

section Row9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`pRow_row9`**: the `.p` sum of a J-9 A row's honest columns is the `Tc` total over the row's walk entries
`consEntriesX9`, dropping axis-`1` entries (`2 ≤ axis`).  Row facts: `old` rows are J-8's `RowOKX` (and their
entries sit at axes `≥ 2`, J-8's `consEntriesX_sound`); `s0B` / `s10B` rows are op-0 / op-10 rows; `s10S` rows are
`segRow`s whose segment read is a field element. -/
theorem pRow_row9 (χ : Coins frameJ8 K) (l : LX9) (fl ll : ZMod p) (hH : HonestCompX.HdlOK p H)
    (hold : l.chip = .old → HonestCompX.RowOKX p l.rn)
    (hax : l.chip = .old → ∀ x ∈ consEntriesX l.rn, 2 ≤ x.2.1)
    (h0 : l.chip = .s0B → l.rn.st = .s0) (h10 : l.chip = .s10B → l.rn.st = .s10)
    (hshape : l.chip = .s10S → l.rn = segRow l.n l.m l.rn.s l.rn.e)
    (hseg : l.chip = .s10S → segRd l.n l.m < p)
    (hseg0 : l.chip = .s10S → l.n ≠ 0 ∧ l.m ≤ top l.n) :
    pRow δ (colX9 H pd idOf l fl ll) χ =
      (((consEntriesX9 l).filter fun x => decide (2 ≤ x.2.1)).map (Tc δ H χ)).sum := by
  cases hc : l.chip with
  | old =>
    rw [ComplJ9ACompRow.colX9_old H pd idOf l fl ll hc]
    have h := ComplJ8OfBalG.pRow_row δ H pd χ l.rn fl ll (hold hc) hH
    rw [h, show consEntriesX9 l = consEntriesX l.rn by simp [consEntriesX9, hc]]
    rw [List.filter_eq_self.mpr fun x hx => by simpa using hax hc x hx]
  | s0B =>
    have e0 : colX9 H pd idOf l fl ll 0 = 0 := by simp [colX9, hc, colS0B]
    have e9 : colX9 H pd idOf l fl ll 9 = 0 := by simp [colX9, hc, colS0B]
    have e11 : colX9 H pd idOf l fl ll 11 = 0 := by simp [colX9, hc, colS0B]
    have e24 : colX9 H pd idOf l fl ll 24 = 0 := by
      simp [colX9, hc, colS0B, HonestCompX.colX, HonestCompX.cPr, h0 hc]
    unfold pRow
    rw [e0, e9, e11, e24]
    simp [consEntriesX9, hc]
  | s10B =>
    have e0 : colX9 H pd idOf l fl ll 0 = 0 := by simp [colX9, hc, colS10B]
    have e9 : colX9 H pd idOf l fl ll 9 = 0 := by simp [colX9, hc, colS10B]
    have e11 : colX9 H pd idOf l fl ll 11 = 0 := by simp [colX9, hc, colS10B]
    have e24 : colX9 H pd idOf l fl ll 24 = 0 := by
      simp [colX9, hc, colS10B, HonestCompX.colX, HonestCompX.cPr, h10 hc]
    unfold pRow
    rw [e0, e9, e11, e24]
    simp [consEntriesX9, hc]
  | s10S =>
    have hs := hshape hc
    have hsg := hseg hc
    have hsf1 : l.rn.sf1 = l.rn.s := by rw [hs]; rfl
    have hsf2 : l.rn.sf2 = l.rn.e := by rw [hs]; rfl
    have hm : l.rn.m = .atom (segRd l.n l.m) := by rw [hs]; rfl
    have hva : HonestCompX.hv (F := ZMod p) H (.atom (segRd l.n l.m)) = ((segRd l.n l.m : ℕ) : ZMod p) := by
      show (((H (.atom _)).2 : ℕ) : ZMod p) = _
      rw [hH.small _ hsg]
    have e0 : colX9 H pd idOf l fl ll 0 = 0 := by simp [colX9, hc, colS10S]
    have e9 : colX9 H pd idOf l fl ll 9 = 0 := by simp [colX9, hc, colS10S]
    have e11 : colX9 H pd idOf l fl ll 11 = 0 := by simp [colX9, hc, colS10S]
    have e24 : colX9 H pd idOf l fl ll 24 = 1 - (if segRd l.n l.m = 1 then 1 else 0) := by
      simp [colX9, hc, colS10S]
    have e32 : colX9 H pd idOf l fl ll 32 = (((H l.rn.s).2 : ℕ) : ZMod p) := by
      simp [colX9, hc, colS10S, HonestCompX.hv, hsf1]
    have e34 : colX9 H pd idOf l fl ll 34 = (((H l.rn.e).2 : ℕ) : ZMod p) := by
      simp [colX9, hc, colS10S, HonestCompX.hv, hsf2]
    have e48 : colX9 H pd idOf l fl ll 48 = ((segRd l.n l.m : ℕ) : ZMod p) := by
      simp [colX9, hc, colS10S, hm, hva]
    have e43 : colX9 H pd idOf l fl ll 43 = (((H l.rn.ftth).1 : ℕ) : ZMod p) := by
      simp [colX9, hc, colS10S, HonestCompX.hk]
    have e44 : colX9 H pd idOf l fl ll 44 = (((H l.rn.ftth).2 : ℕ) : ZMod p) := by
      simp [colX9, hc, colS10S, HonestCompX.hv]
    have e45 : colX9 H pd idOf l fl ll 45 = (((H l.rn.fttt).1 : ℕ) : ZMod p) := by
      simp [colX9, hc, colS10S, HonestCompX.hk]
    have e46 : colX9 H pd idOf l fl ll 46 = (((H l.rn.fttt).2 : ℕ) : ZMod p) := by
      simp [colX9, hc, colS10S, HonestCompX.hv]
    unfold pRow
    rw [e0, e9, e11, e24, e32, e34, e48, e43, e44, e45, e46]
    by_cases h1 : segRd l.n l.m = 1
    · simp [consEntriesX9, hc, h1]
    · have h2 : 2 ≤ segRd l.n l.m := by
        have := Nock.J9A.NounAx.segRd_pos (hseg0 hc).1 l.m (hseg0 hc).2
        omega
      simp [consEntriesX9, hc, h1, h2, Tc]

end Row9

/-! ## 2 (part 1): the row's `.p` balance term at the stage-2 environment is `pSum9` -/

section OneHot9
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- The index of the row's one-hot state. -/
def stX9 (l : LX9) : ℕ :=
  match l.chip with
  | .old => Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx l.rn.st
  | .s0B => 123
  | .s10B => 124
  | .s10S => 125

/-- **The honest columns are one-hot over the twin's 20 states.** -/
theorem onehot9 (l : LX9) (fst lst : F) (e : Nock.Reified.Env F) (he : e.trace = colX9 H pd idOf l fst lst) :
    ChipHX9.OneHotAt9 e (stX9 l) := by
  intro i hi
  rw [he]
  have hi' : i < 17 ∨ i = 123 ∨ i = 124 ∨ i = 125 := by
    simp only [ChipHX9.statesX9, ChipHX9.newStates, ChipHX.nStates, ChipHX9.sS0B, ChipHX9.sS10B,
      ChipHX9.sS10S, List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  cases hc : l.chip with
  | old =>
    rw [ComplJ9ACompRow.colX9_old H pd idOf l fst lst hc]
    have hlt : Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx l.rn.st < 17 :=
      Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx_lt _
    simp only [stX9, hc]
    rcases hi' with h | rfl | rfl | rfl
    · simp [HonestCompX.colX, h, eq_comm]
    · rw [if_neg (by omega)]; simp [HonestCompX.colX]
    · rw [if_neg (by omega)]; simp [HonestCompX.colX]
    · rw [if_neg (by omega)]; simp [HonestCompX.colX]
  | s0B =>
    simp only [stX9, hc]
    rcases hi' with h | rfl | rfl | rfl
    · simp [colX9, hc, colS0B, h, show i ≠ 123 by omega]
    · simp [colX9, hc, colS0B]
    · simp [colX9, hc, colS0B]
    · simp [colX9, hc, colS0B]
  | s10B =>
    simp only [stX9, hc]
    rcases hi' with h | rfl | rfl | rfl
    · simp [colX9, hc, colS10B, h, show i ≠ 124 by omega]
    · simp [colX9, hc, colS10B]
    · simp [colX9, hc, colS10B]
    · simp [colX9, hc, colS10B]
  | s10S =>
    simp only [stX9, hc]
    rcases hi' with h | rfl | rfl | rfl
    · simp [colX9, hc, colS10S, h, show i ≠ 125 by omega]
    · simp [colX9, hc, colS10S]
    · simp [colX9, hc, colS10S]
    · simp [colX9, hc, colS10S]

/-- **The pair flag column `24` (`pr`) is boolean on every honest row.** -/
theorem col24_bool (l : LX9) (fst lst : F) :
    colX9 H pd idOf l fst lst 24 = 0 ∨ colX9 H pd idOf l fst lst 24 = 1 := by
  have hcPr : ∀ r : RowNX, HonestCompX.cPr (F := F) r = 0 ∨ HonestCompX.cPr (F := F) r = 1 := by
    intro r
    unfold HonestCompX.cPr
    split
    · split_ifs
      · right; rfl
      · left; rfl
    · right; rfl
    · left; rfl
  cases hc : l.chip with
  | old => rw [ComplJ9ACompRow.colX9_old H pd idOf l fst lst hc, HonestCompX.cx24]; exact hcPr _
  | s0B =>
    have : colX9 H pd idOf l fst lst 24 = HonestCompX.cPr (F := F) l.rn := by
      simp [colX9, hc, colS0B, HonestCompX.colX]
    rw [this]; exact hcPr _
  | s10B =>
    have : colX9 H pd idOf l fst lst 24 = HonestCompX.cPr (F := F) l.rn := by
      simp [colX9, hc, colS10B, HonestCompX.colX]
    rw [this]; exact hcPr _
  | s10S =>
    have : colX9 H pd idOf l fst lst 24 = 1 - (if segRd l.n l.m = 1 then 1 else 0) := by
      simp [colX9, hc, colS10S]
    rw [this]
    by_cases h : segRd l.n l.m = 1 <;> simp [h]

end OneHot9

section TermP9
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (env0 env1 preT9 invV9 baseT9 r0 r0_iff okFs9 trX9_pre limb_inv9
  limb_invIm9 slot_index9)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleX9 (termQX9)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
  (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

set_option maxHeartbeats 2000000 in
/-- **The compute row's `.p` balance term (twin)**: at the stage-2 environment it is `pSum9` (the `.p` pair needs
its two denominators nonzero when its flag is `1`; `s10B` rows are op-10 rows). -/
theorem termQX9_p (j : ℕ)
    (hl10 : (rowAt9 W (j + 1)).chip = .s10B → (rowAt9 W (j + 1)).rn.st = .s10)
    (hpair : ∀ S ∈ (slotsX9 : List (SlotX ℚ)), ∀ fl a c bb, S.pair = some (fl, a, c, bb) →
      (env0 H pd idOf W chalV pubVal j).trace fl = 1 →
      TeleCQX.DX δ (Compute.TowerD.gatherEnv b (env0 H pd idOf W chalV pubVal j))
          (env0 H pd idOf W chalV pubVal j) a ≠ 0 ∧
        TeleCQX.DX δ (Compute.TowerD.gatherEnv b (env0 H pd idOf W chalV pubVal j))
          (env0 H pd idOf W chalV pubVal j) c ≠ 0) :
    termQX9 δ b (env1 b δ H pd idOf W chalV pubVal j) .p = pSum9 δ b H pd idOf W chalV pubVal j := by
  set e0 := env0 H pd idOf W chalV pubVal j with he0
  set e1 := env1 b δ H pd idOf W chalV pubVal j with he1
  have hT : e0.trace = colX9 H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) := rfl
  have hOH := onehot9 H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) e0 hT
  unfold termQX9 pSum9
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have hS' : castSlotX (F := ZMod p) S ∈ slotsX9 (F := ZMod p) := by
    rw [← TeleX9.slotsX9_cast]; exact List.mem_map_of_mem hS
  have htr : ∀ c, r0 c = true → e1.trace c = e0.trace c := fun c hc => by
    rw [r0_iff] at hc
    show preT9 b δ H pd idOf W chalV pubVal j c = HonestTraceX9.baseT9 H pd idOf W j c
    unfold preT9
    split_ifs <;> first | rfl | omega
  have hcong : ∀ g : CoeffExpr ℚ, HonestTraceX.okC okFs9 g = true →
      ChipHX.evalQX g e1 = ChipHX.evalQX g e0 := by
    intro g hg
    rw [← HonestTraceX.eval_mapC_castX, ← HonestTraceX.eval_mapC_castX]
    refine HonestTraceX.eval_okC okFs9 _ (by rw [HonestTraceX.okC_mapC]; exact hg) e1 e0 fun k i hk => ?_
    cases k <;> simp only [okFs9, Bool.false_eq_true] at hk
    exact htr i hk
  have hokS := List.all_eq_true.mp HonestTraceX9.slotsAct_ok9 S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokS
  rw [hcong _ hokS.1.1.1.2]
  obtain ⟨s, hs4, hSs, hinv, hinvIm⟩ := slot_index9 hS'
  have hl1 : Compute.LogUp.limbVal b e1.trace (69 + 6 * s) =
      Quad.re _ (invV9 b δ H pd idOf W chalV pubVal j (HonestTraceX9.slotAt9 s)) := by
    rw [← limb_inv9 b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX9.trX9_pre b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (Or.inl (by have := k.isLt; omega))]
    rfl
  have hl2 : Compute.LogUp.limbVal b e1.trace (72 + 6 * s) =
      Quad.im _ (invV9 b δ H pd idOf W chalV pubVal j (HonestTraceX9.slotAt9 s)) := by
    rw [← limb_invIm9 b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX9.trX9_pre b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (Or.inl (by have := k.isLt; omega))]
    rfl
  have hinvQ : TeleCQX.invQX δ (Compute.TowerD.gatherEnv b e1) S =
      HonestSlotX.aVal b δ (castSlotX S) e0 * (HonestSlotX.dVal b δ (castSlotX S) e0)⁻¹ := by
    have h1 : S.inv = 69 + 6 * s := hinv
    have h2 : S.invIm = 72 + 6 * s := hinvIm
    show Quad.mk _ (Compute.LogUp.limbVal b e1.trace S.inv) (Compute.LogUp.limbVal b e1.trace S.invIm) = _
    rw [h1, h2, hl1, hl2, Quad.mk_re_im, invV9, ← hSs]
  rw [hinvQ, TeleCQX.evalQX_actB, ComplJ8CompPole.aVal_expand, ComplJ8CompPole.dVal_expand]
  have hpw0 := TeleX9.act_pairwise9 hOH hS
  have hpw : S.ents.Pairwise fun x y =>
      algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0) * algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX y.act e0) = 0 :=
    hpw0.imp fun h => by rw [← map_mul, h, map_zero]
  have hrcd : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).rcd = x.rcd := fun _ => rfl
  have hact : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).act.eval e0 = ChipHX.evalQX x.act e0 :=
    fun x => TeleCQX.castEntX_act x e0
  simp only [castSlotX, List.map_map, Function.comp_def, hrcd, hact]
  have hsum : ∀ l : List (EntX ℚ), algebraMap (ZMod p) 𝕂′ (l.map fun x => ChipHX.evalQX x.act e0).sum =
      (l.map fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0)).sum := fun l => by
    rw [map_list_sum, List.map_map]; rfl
  rw [map_add, hsum, hsum]
  cases hp : S.pair with
  | none =>
    simp only [map_zero, add_zero]
    have := ComplJ8OfBalG.onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
      (fun x => TeleCQX.DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.p)) 0 0 0 hpw
      (fun h => absurd rfl h)
    simpa using this
  | some q =>
    obtain ⟨fl, a, c, bb⟩ := q
    have hf : algebraMap (ZMod p) 𝕂′ (e0.trace fl) ≠ 0 → ∀ x ∈ S.ents,
        algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0) = 0 := by
      intro hne x hx
      have hfl : e0.trace fl ≠ 0 := fun h => hne (by rw [h, map_zero])
      have h0 := ComplJ9AOfComp.hex9 H pd idOf (castSlotX S) hS' e0 (rowAt9 W (j + 1)) (fl1 (j + 1))
        (llW W (j + 1)) hT hl10 fl a c bb hp hfl (castEntX x) (List.mem_map_of_mem hx)
      rw [← hact, h0, map_zero]
    by_cases hb : bb = Bal.p
    · simp only [hb, if_true]
      have hfb : e0.trace fl = 0 ∨ e0.trace fl = 1 := by
        simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
        rcases hS with rfl | rfl | rfl | rfl
        · simp [slot0X9, extSlot, ChipHX.slot0X] at hp
        · simp [slot1X9, extSlot, ChipHX.slot1X] at hp
        · simp only [slot2X9, extSlot, ChipHX.slot2X, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, -⟩ := hp
          rw [hT, show ChipHX.prX = 24 from rfl]
          exact col24_bool H pd idOf _ _ _
        · simp only [slot3X9, extSlot, ChipHX.slot3X, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨-, -, -, rfl⟩ := hp
          simp at hb
      have hfb' : algebraMap (ZMod p) 𝕂′ (e0.trace fl) = 0 ∨ algebraMap (ZMod p) 𝕂′ (e0.trace fl) = 1 := by
        rcases hfb with h | h <;> simp [h]
      have hpf : TeleCQX.pairFX e0 S = e0.trace fl := by simp [TeleCQX.pairFX, hp]
      rw [hpf]
      refine ComplJ8OfBalG.onehot_slot_pair S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
        (fun x => TeleCQX.DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.p))
        (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw hf hfb' fun h1 => ?_
      have h1' : e0.trace fl = 1 := by
        rcases hfb with h | h
        · rw [h, map_zero] at h1; exact absurd h1 zero_ne_one
        · exact h
      exact hpair S hS fl a c bb hp h1'
    · simp only [hb, if_false, map_zero, add_zero]
      exact ComplJ8OfBalG.onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
        (fun x => TeleCQX.DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.p))
        (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw hf

/-- **The pair denominators are nonzero outside the twin slot poles** (twin of `ComplJ8OfBalG.hpair_good`). -/
theorem hpair9_good (n : ℕ) (pub : ℕ → ZMod p) (χ : Coins frameJ8 K)
    (hg : ∀ s ∈ ComplJ9ARun.compPoles9 (K := K) δ H pd idOf W n, χ ∉ s.ev) (j : ℕ) (hj : j < n) :
    ∀ S ∈ (slotsX9 : List (SlotX ℚ)), ∀ fl a c bb, S.pair = some (fl, a, c, bb) →
      (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pub j).trace fl = 1 →
      TeleCQX.DX δ (Compute.TowerD.gatherEnv b (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pub j))
          (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pub j) a ≠ 0 ∧
        TeleCQX.DX δ (Compute.TowerD.gatherEnv b (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pub j))
          (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pub j) c ≠ 0 := by
  intro S hS fl a c bb hp _
  have hS' : castSlotX (F := ZMod p) S ∈ slotsX9 (F := ZMod p) := by
    rw [← TeleX9.slotsX9_cast]; exact List.mem_map_of_mem hS
  have hpS : (castSlotX (F := ZMod p) S).pair = some (fl, a, c, bb) := hp
  obtain ⟨la, lc⟩ := (ComplJ9AOfComp.hlen9 _ hS').2 fl a c bb hpS
  have hmem : ∀ s ∈ ComplJ8CompPole.slotPoles δ (castSlotX (F := ZMod p) S)
      (env0 H pd idOf W (fun _ => (0 : ZMod p)) (fun _ => 0) j), χ ∉ s.ev := fun s hs => hg s (by
        simp only [ComplJ9ARun.compPoles9, List.mem_flatMap]
        exact ⟨j, List.mem_range.mpr hj, _, hS', hs⟩)
  have hρ := ComplJ8Bad.ρH_re δ χ
  rw [ComplJ8CompPole.den_split δ b _ χ rfl a la, ComplJ8CompPole.den_split δ b _ χ rfl c lc]
  refine ⟨?_, ?_⟩
  · exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12
      (ComplJ8CompPole.pf δ (env0 H pd idOf W (fun _ => (0 : ZMod p)) (fun _ => 0) j) a) χ _ hρ
      (hmem _ (by simp [ComplJ8CompPole.slotPoles, hpS]))
  · exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12
      (ComplJ8CompPole.pf δ (env0 H pd idOf W (fun _ => (0 : ZMod p)) (fun _ => 0) j) c) χ _ hρ
      (hmem _ (by simp [ComplJ8CompPole.slotPoles, hpS]))

/-- The honest accumulator term over the cast slots is the `ℚ`-template term. -/
theorem termVal_slotsF9 (bl : Bal) (im : Bool) (eF : Nock.Reified.Env (ZMod p)) :
    Compute.LogUp.termVal b (HonestTraceX9.slotsF9 bl im) eF =
      TeleCQX.termValX b (TeleX9.slotsB9 bl im) eF := by
  simp only [Compute.LogUp.termVal, TeleCQX.termValX, HonestTraceX9.slotsF9, HonestTraceX9.slotsQ9,
    TeleX9.slotsB9, List.map_map, Function.comp_def, castSlot, HonestTraceX.eval_mapC_castX]

/-- **A twin accumulator pair is the sum of the rows' `𝕂′` balance terms.** -/
theorem acc_rows9 (N a : ℕ) (bl : Bal)
    (hre : HonestTraceX.accSpec a = (bl, false)) (him : HonestTraceX.accSpec (a + 1) = (bl, true)) :
    Quad.mk (algebraMap (ZMod p) K δ) (HonestTraceX9.accV9 b δ H pd idOf W chalV pubVal a N)
        (HonestTraceX9.accV9 b δ H pd idOf W chalV pubVal (a + 1) N) =
      ∑ j ∈ Finset.range N, termQX9 δ b (env1 b δ H pd idOf W chalV pubVal j) bl := by
  simp only [HonestTraceX9.accV9, hre, him]
  rw [← TeleCQX.mk_fsumX]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TeleX9.termQX9_eq, termVal_slotsF9, termVal_slotsF9]

/-- **The compute path public is the sum of the rows' `.p` balance terms** (twin of `rhoC4_rows`; `accTA 2/3`). -/
theorem rho4_rows9 (N : ℕ) :
    Quad.mk (algebraMap (ZMod p) K δ) (HonestTraceX9.accV9 b δ H pd idOf W chalV pubVal 2 N)
        (HonestTraceX9.accV9 b δ H pd idOf W chalV pubVal 3 N) =
      ∑ j ∈ Finset.range N, termQX9 δ b (env1 b δ H pd idOf W chalV pubVal j) .p :=
  acc_rows9 δ b H pd idOf W chalV pubVal N 2 .p rfl rfl

end TermP9

/-! ## 2 (part 3): the compute total -/

section Total9
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (env0 env1)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (Node9 genX9T genX9T_inTree semN9_of_node9 rowsOfT9 SemN9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A W9 N9 N9_def idOfA accTA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (Wp)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPAx (Tw)
open Nock.Jet.Autogen (Tpl)

/-- **The reads of an old row of the J-9 A tree are defined slots at axes `≥ 2`.** -/
theorem old_entries {R : Nock.Jet.Registry} {t : NTree SkelX} {u : NTree LX9} (hu : Node9 R t u)
    (hchip : u.label.chip = .old) :
    ∀ x ∈ consEntriesX u.label.rn, 2 ≤ x.2.1 ∧ Noun.slot x.2.1 x.1 = some x.2.2 := by
  have hsem := semN9_of_node9 hu
  rcases hu with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ | hseg
  · simp only [ComplJ9AGen.genX9T_label] at hchip hsem ⊢
    simp only [SemN9, hchip] at hsem
    exact consEntriesX_sound v.label hsem.1
  · rw [ComplJ9AGen.liftT_label] at hchip hsem ⊢
    have hs : (rowOfSkelX v.label).SemN R := hsem.1
    exact consEntriesX_sound v.label hs
  · rcases hseg with ⟨n, m, s', e, new, -, -, -, rfl⟩ | ⟨X, Y, rfl⟩
    · rw [ComplJ9AGen.segT_label] at hchip; simp at hchip
    · intro x hx
      simp [ComplJ9AGen.tNode, ComplJ9AGen.tRow, consEntriesX] at hx

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

local notation "𝕂″" => Quad (algebraMap (ZMod p) K δ)

set_option maxHeartbeats 4000000 in
/-- **The compute path public `ρ 4` of the J-9 A run is the sum of `Wp` over the J-9 A walk reads.** -/
theorem rho4_total (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
    (h31A : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
    (hax9 : ProgAxOK9A p t) (hop5 : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8.ProgOp5OK p t)
    (hlen : (j9aDataOf p Rg Rt hgen).cells.length < p)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) (χ : Coins frameJ8 K)
    (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    ((BRun9A δ b Rt hgen hpG h31A).M χ).ρ 4 =
      ((ComplJ9AReads.walkReadsX9 (rowsOfT9 t)).map fun x =>
        Wp δ (j9aDataOf p Rg Rt hgen) χ (readRecH (j9aDataOf p Rg Rt hgen).cells x)).sum := by
  have hp62 : 2 ^ 62 < p := lt_trans (by norm_num) (ComplJ9AChains.hp63_of_G hpG)
  have hH : HonestCompX.HdlOK p (j9aDataOf p Rg Rt hgen).H := ComplJ9AOfComp.hHA' (p := p) Rt hgen
  have hg : ∀ e ∈ Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.compPoles9 (K := K) δ (j9aDataOf p Rg Rt hgen).H
      (j9aDataOf p Rg Rt hgen).pd (idOfA (p := p) Rt hgen) (W9 t) (N9 t), χ ∉ e.ev := fun e he =>
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.good_fam δ b Rt hgen hpG h31A hχ _
      (List.mem_append_right _ (by unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.famsNew; simp)) e he
  have hρ : ((BRun9A δ b Rt hgen hpG h31A).M χ).ρ 4 =
      Quad.mk _ (accTA δ b Rt hgen χ 2) (accTA δ b Rt hgen χ 3) := by
    show Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.ρA δ b Rt hgen χ 4 = _
    simp [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.ρA]
  rw [hρ]
  show Quad.mk _ (HonestTraceX9.accV9 b δ (j9aDataOf p Rg Rt hgen).H (j9aDataOf p Rg Rt hgen).pd
      (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 2 (N9 t))
    (HonestTraceX9.accV9 b δ (j9aDataOf p Rg Rt hgen).H (j9aDataOf p Rg Rt hgen).pd
      (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 3 (N9 t)) = _
  rw [rho4_rows9 δ b (j9aDataOf p Rg Rt hgen).H (j9aDataOf p Rg Rt hgen).pd (idOfA (p := p) Rt hgen) (W9 t)
    (VerJ8.chalVJ8 b χ) (fun _ => 0) (N9 t)]
  set g : NTree LX9 → 𝕂″ := fun u => (((consEntriesX9 u.label).filter fun x => decide (2 ≤ x.2.1)).map
    fun x => Wp δ (j9aDataOf p Rg Rt hgen) χ (readRecH (j9aDataOf p Rg Rt hgen).cells (x.1, x.2.1))).sum with hgdef
  have hrow : ∀ j ∈ Finset.range (N9 t),
      Nock.NockVMROM.Thm54.VclL.Handle.TeleX9.termQX9 δ b (env1 b δ (j9aDataOf p Rg Rt hgen).H
        (j9aDataOf p Rg Rt hgen).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j) .p =
        g ((W9 t).getD j (genX9T t)) := by
    intro j hj
    have hj' : j < N9 t := Finset.mem_range.mp hj
    have hjW : j < (W9 t).length := by have := N9_def t; omega
    rw [termQX9_p δ b _ _ _ (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j (ComplJ9AOfComp.s10B_rows hgen j hj')
      (hpair9_good δ b _ _ _ (W9 t) (N9 t) (fun _ => 0) χ hg j hj'),
      pSum9_expand δ b _ _ _ (W9 t) (fun _ => 0) χ j, List.getD_eq_getElem _ _ hjW]
    have hmemW : (W9 t)[j]'hjW ∈ bfsForest [genX9T t] := List.getElem_mem hjW
    obtain ⟨c, hc', hcu⟩ := (mem_bfsForest _ _).1 hmemW
    simp only [List.mem_singleton] at hc'
    subst hc'
    have hnode := genX9T_inTree hgen hcu
    have hsem := semN9_of_node9 hnode
    have hrw : rowAt9 (W9 t) (j + 1) = ((W9 t)[j]'hjW).label := by
      simp [rowAt9, List.getElem?_eq_getElem hjW]
    have hT : (env0 (j9aDataOf p Rg Rt hgen).H (j9aDataOf p Rg Rt hgen).pd (idOfA (p := p) Rt hgen) (W9 t)
        (VerJ8.chalVJ8 b χ) (fun _ => 0) j).trace =
        colX9 (j9aDataOf p Rg Rt hgen).H (j9aDataOf p Rg Rt hgen).pd (idOfA (p := p) Rt hgen)
          ((W9 t)[j]'hjW).label (fl1 (j + 1)) (llW (W9 t) (j + 1)) := by
      rw [← hrw]; rfl
    have hent : ∀ x ∈ consEntriesX9 ((W9 t)[j]'hjW).label, Noun.slot x.2.1 x.1 = some x.2.2 := by
      intro x hx
      cases hc : ((W9 t)[j]'hjW).label.chip with
      | old => exact (old_entries hnode hc x (by simpa [consEntriesX9, hc] using hx)).2
      | s0B => simp [consEntriesX9, hc] at hx
      | s10B => simp [consEntriesX9, hc] at hx
      | s10S =>
        have hs := hsem
        simp only [SemN9, hc] at hs
        obtain ⟨-, -, -, -, -, h1, h2⟩ := hs
        simp only [consEntriesX9, hc, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact h1
        · exact h2
    rw [hT, pRow_row9 δ _ _ _ χ ((W9 t)[j]'hjW).label (fl1 (j + 1)) (llW (W9 t) (j + 1)) hH
      (fun hc => (ComplJ9ABase.old_facts hpG hgen hax9 hop5 _ _ (ComplJ9AOfComp.hpairA Rt hgen hpG hop5) hnode hc).1)
      (fun hc x hx => (old_entries hnode hc x hx).1)
      (fun hc => by have hs := hsem; simp only [SemN9, hc] at hs; exact hs.2.1)
      (fun hc => by have hs := hsem; simp only [SemN9, hc] at hs; exact hs.2.1)
      (fun hc => by have hs := hsem; simp only [SemN9, hc] at hs; exact hs.2.2.1)
      (fun hc => by
        have hs := hsem; simp only [SemN9, hc] at hs
        exact lt_of_lt_of_le (Nock.J9A.NounAx.segRd_lt _ _) (by
          have := ComplJ9AChains.hp63_of_G hpG
          have h33 : (2 : ℕ) ^ 33 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
          omega))
      (fun hc => by have hs := hsem; simp only [SemN9, hc] at hs; exact ⟨hs.1, hs.2.1⟩)]
    refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
    obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
    have h2 : 2 ≤ x.2.1 := by simpa using hx2
    have hsl := hent x hx1
    have hrd : (x.1, x.2.1) ∈ (j9aDataOf p Rg Rt hgen).reads := by
      rw [ComplJ9ADataRec.j9aDataOf_reads]
      refine List.mem_append_left _ ?_
      unfold ComplJ9AReads.walkReadsX9
      refine List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨((W9 t)[j]'hjW).label, ?_, List.mem_map_of_mem hx1⟩, by simpa using h2⟩
      simp only [rowsOfT9, List.toList_toArray, List.mem_map]
      exact ⟨_, List.getElem_mem hjW, rfl⟩
    have hTc : Tc δ (j9aDataOf p Rg Rt hgen).H χ x = Tw δ (j9aDataOf p Rg Rt hgen).H χ (x.1, x.2.1) := by
      simp only [Tc, Tw, hsl, Option.getD_some]
    rw [hTc]
    exact ComplJ9ABalPW.Tw_eq_Wp δ Rt hgen hlen hp62 hwalk9 χ _ hrd
  rw [Finset.sum_congr rfl hrow, N9_def t, ComplJ8OfBal.sum_range_getD' (genX9T t) g (W9 t)]
  have hper : ∀ u : NTree LX9,
      ((((consEntriesX9 u.label).map fun x => (x.1, x.2.1)).filter fun q => decide (2 ≤ q.2)).map fun x =>
        Wp δ (j9aDataOf p Rg Rt hgen) χ (readRecH (j9aDataOf p Rg Rt hgen).cells x)).sum = g u := by
    intro u
    simp only [hgdef, List.filter_map, List.map_map, Function.comp_def]
  unfold ComplJ9AReads.walkReadsX9
  simp only [rowsOfT9, List.toList_toArray, List.filter_flatMap, List.flatMap_map, Function.comp_def]
  rw [ComplJ8OfBalG.sum_flatMap_map]
  simp only [hper]

end Total9

end

#print axioms pSum9_expand
#print axioms pRow_row9
#print axioms onehot9
#print axioms termQX9_p
#print axioms rho4_total

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPC
