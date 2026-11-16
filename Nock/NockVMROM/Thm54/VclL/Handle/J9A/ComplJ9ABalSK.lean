/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalSK.lean

  **J-9 A L7 C3 S8: the TAG key bridge.**  The S2 tag weight of an `s0B` / `s10B` consumer row `l` equals
  `ComplJ9ABalSAx.tagKW` of its key `axKey9 l = some k` (the weight of the key's chain-last tag provide).

  * `segN_top`: `segN n X (top n) = Y` when `n ≥ 2^32` and `/n X = Y` (`chain_inv` at `k = top n`).
  * `tagKW_eq`: `tagKW (X, n)` is `tagW` of the 8-entry record `(H X).2, H(atom n), H Y, id`.
  * `tagW_s0B`, `tagW_s10B`: the two row forms (`gT9_s0B` / `gT9_s10B`'s right-hand sides) equal `tagKW k`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSRow
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChainsRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSK

noncomputable section

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
open Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx
open Nock.J9A.NounAx (top segAx segRd)

theorem top_pos {n : ℕ} (h : 2 ^ 32 ≤ n) : 1 ≤ top n := by
  unfold top
  exact Nat.le_log_of_pow_le (by norm_num) (by simpa using h)

/-- The chain's last noun is the read result. -/
theorem segN_top {n : ℕ} (X Y : Noun) (h32 : 2 ^ 32 ≤ n) (hX : Noun.slot n X = some Y) :
    segN n X (top n) = Y := by
  have hn : n ≠ 0 := by
    have : (0 : ℕ) < 2 ^ 32 := by norm_num
    omega
  have hinv := chain_inv n X Y hn hX (top n) le_rfl
  have h0 : top n - top n = 0 := Nat.sub_self _
  rw [h0] at hinv
  have hne : (0 : ℕ) ≠ top n := by have := top_pos h32; omega
  have hax : segAx n 0 = segRd n 0 := by
    simp [segAx, segRd, hne]
    omega
  rw [segN_eq, h0, segX, ← hax, hinv]
  rfl

section Tag
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`tagKW` of a key `(X, n)` with `/n X = Y`**: the weight of the record
`((H X).2, H(atom n), H Y, id n)`. -/
theorem tagKW_eq (nA : ℕ) (H : Noun → ℕ × ℕ) (rows : Array LX9) (χ : Coins frameJ8 K) (X Y : Noun) (n : ℕ)
    (hH : HonestCompX.HdlOK p H) (h32 : 2 ^ 32 ≤ n) (hX : Noun.slot n X = some Y) :
    tagKW δ nA H rows χ (X, n) =
      tagW δ χ (tagRec (K := K) (((H X).2 : ℕ) : ZMod p) (((H (.atom n)).1 : ℕ) : ZMod p)
        (((H (.atom n)).2 : ℕ) : ZMod p) (((H Y).1 : ℕ) : ZMod p) (((H Y).2 : ℕ) : ZMod p)
        ((idOf9 p nA H (fieldAx9 p rows) n : ℕ) : ZMod p)) := by
  unfold tagKW
  rw [tagVec_last, segN_top X Y h32 hX]
  by_cases hp : n < p
  · have h1 := hH.small n hp
    have h2 : decide (n < p) = true := decide_eq_true hp
    simp only [h2, if_true, h1]
    simp
  · have hp' : p ≤ n := Nat.le_of_not_lt hp
    have h1 := hH.big n hp'
    have h2 : decide (n < p) = false := decide_eq_false hp
    have h3 := idOf9_big (p := p) (nA := nA) (H := H) (fx := fieldAx9 p rows) hp'
    simp only [h2, h3, if_false, Bool.false_eq_true]
    rw [h1]
    simp

/-- **`s0B` row**: the S2 tag weight (`gT9_s0B`) equals `tagKW` of the key `(rn.s, n)`. -/
theorem tagW_s0B {R : Nock.Jet.Registry} (nA : ℕ) (H : Noun → ℕ × ℕ) (rows : Array LX9)
    (χ : Coins frameJ8 K) (hH : HonestCompX.HdlOK p H) (l : LX9) (hsem : SemN9 R l) (hc : l.chip = .s0B)
    (k : Noun × ℕ) (hk : axKey9 l = some k) :
    tagW δ χ (tagRec (K := K) ((H l.rn.s).2 : ℕ) ((H l.rn.ft).1 : ℕ) ((H l.rn.ft).2 : ℕ)
        ((H l.rn.e).1 : ℕ) ((H l.rn.e).2 : ℕ) ((idOf9 p nA H (fieldAx9 p rows) l.n : ℕ) : ZMod p)) =
      tagKW δ nA H rows χ k := by
  simp only [axKey9, hc, Option.some.injEq] at hk
  subst hk
  simp only [SemN9, hc] at hsem
  obtain ⟨hs, hst, hft, hbig⟩ := hsem
  unfold RowNX.SemN at hs
  rw [hst] at hs
  obtain ⟨-, -, ax, hax, hsl⟩ := hs
  rw [hft] at hax
  have hn : l.n = ax := by injection hax
  have hsl' : Noun.slot l.n l.rn.s = some l.rn.e := by rw [hn]; exact hsl
  have h32 : 2 ^ 32 ≤ l.n := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hbig
  rw [tagKW_eq δ nA H rows χ _ _ _ hH h32 hsl', hft]

/-- **`s10B` row**: the S2 tag weight (`gT9_s10B`) equals `tagKW` of the key `(rn.e, n)`. -/
theorem tagW_s10B {R : Nock.Jet.Registry} (nA : ℕ) (H : Noun → ℕ × ℕ) (rows : Array LX9)
    (χ : Coins frameJ8 K) (hH : HonestCompX.HdlOK p H) (l : LX9) (hsem : SemN9 R l) (hc : l.chip = .s10B)
    (k : Noun × ℕ) (hk : axKey9 l = some k) :
    tagW δ χ (tagRec (K := K) ((H l.rn.e).2 : ℕ) ((H l.rn.ftth).1 : ℕ) ((H l.rn.ftth).2 : ℕ)
        ((H l.rn.sf1).1 : ℕ) ((H l.rn.sf1).2 : ℕ) ((idOf9 p nA H (fieldAx9 p rows) l.n : ℕ) : ZMod p)) =
      tagKW δ nA H rows χ k := by
  simp only [axKey9, hc, Option.some.injEq] at hk
  subst hk
  simp only [SemN9, hc] at hsem
  obtain ⟨hs, hst, hft, hbig⟩ := hsem
  unfold RowNX.SemN at hs
  rw [hst] at hs
  obtain ⟨-, -, -, -, a, ha, hed⟩ := hs
  rw [hft] at ha
  have hn : l.n = a := by injection ha
  have h32 : 2 ^ 32 ≤ l.n := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hbig
  have hsl : Noun.slot l.n l.rn.e = some l.rn.sf1 := by
    rw [hn]; exact slot_edit a (by omega) _ _ _ hed
  rw [tagKW_eq δ nA H rows χ _ _ _ hH h32 hsl, hft]

end Tag

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSK

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSK.segN_top
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSK.tagKW_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSK.tagW_s0B
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSK.tagW_s10B
