/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/R0MSplitP1.lean

 **Trace uniqueness on the P1 fragment: the cell table's round 0 split into the noun columns and the four
 multiplicity columns.**

 `OpenR0MP1.cols_eq_of_set` takes the multiplicity columns `mv mx mx1 mh` (cell columns `16, 17, 128, 129`,
 `MulCol`) as a hypothesis `hmul`; they are the consumer counts, which are only known equal after the keys and the
 consumer lists, which in turn read the cell table. This module removes that circularity:
 * §1 **`cols_eq_of_set_nm`**: every column `< 334` that is NOT a multiplicity column is determined by the noun set
 alone (the multiplicities enter `rowA_eq` only as pass-through columns; the sort keys `kF` read none of them,
 `kF_congr_nm`).
 * §2 the fingerprints without the multiplicities: `clr` (zero `mv`, `mx` of a B0 row); the B0 decoder reads no
 multiplicity (`decodeB0_clr`, `decodeTree_clr`); **`cell_fps_eq_nm`**, **`cell_round1_eq_nm`**: the round-1 roles
 `p l r` from the non-multiplicity round-0 columns.
 * §3 the keys: `keys_cong_nm` (the validity and export keys read the roles `0 .. 17` and `idx lo hi`),
 `keyVec5_keyHK_congr_nm` (the handle-export key reads no multiplicity).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1

noncomputable section

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)

/-- **The four multiplicity columns** of the cell side row: `mv = 16`, `mx = 17`, `mx1 = 128`, `mh = 129`. -/
abbrev MulCol (j : ℕ) : Prop := j = 16 ∨ j = 17 ∨ j = 128 ∨ j = 129

theorem mulCol_names : Cell.mv = 16 ∧ Cell.mx = 17 ∧ Cell.mx1 = 128 ∧ CellH.mh = 129 := ⟨rfl, rfl, rfl, rfl⟩

/-! ## 1. The noun columns from the noun set -/

section Gen
variable {p : ℕ} [Fact p.Prime]

/-- A key component reads no multiplicity column. -/
theorem kF_congr_nm {t t' : ℕ → ZMod p} (h : ∀ j < 262, ¬ MulCol j → t j = t' j) (k : ℕ) : kF t k = kF t' k := by
  have hb : ∀ base, 130 ≤ base ∧ base + 32 ≤ 262 →
      (bitSum base 32 : CoeffExpr (ZMod p)).eval ⟨t, fun _ => 0, fun _ => 0, fun _ => 0⟩ =
        (bitSum base 32 : CoeffExpr (ZMod p)).eval ⟨t', fun _ => 0, fun _ => 0, fun _ => 0⟩ := by
    intro base hbase
    rw [bitSum_eval, bitSum_eval]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    show (2 : ZMod p) ^ i * t (base + i) = (2 : ZMod p) ^ i * t' (base + i)
    rw [h _ (by omega) (by unfold MulCol; omega)]
  unfold kF
  match k with
  | 0 => exact h Cell.hi (by decide) (by decide)
  | 1 => exact h Cell.lo (by decide) (by decide)
  | 2 => exact h Cell.wL (by decide) (by decide)
  | 3 => exact hb _ (by decide)
  | 4 => exact hb _ (by decide)
  | 5 => exact h Cell.wR (by decide) (by decide)
  | 6 => exact hb _ (by decide)
  | k + 7 => exact hb _ (by decide)

end Gen

section Main
variable {p : ℕ} [Fact p.Prime] {v v' : ℕ → ℕ → ZMod p} {n n' : ℕ} {N N' : ℕ → Noun}

/-- **`rowA_eq` without the multiplicities**: every non-multiplicity column below `264`. -/
theorem rowA_eq_nm (T : TableM v n) (L : NounLink v n N) (K : KindRows v n)
    (T' : TableM v' n) (L' : NounLink v' n N') (K' : KindRows v' n) (hpG : p = Nock.Atoms.p)
    {i : ℕ} (hi : i < n) (hrow : RowsEq v v' N N' i) :
    ∀ j < 264, ¬ MulCol j → v i j = v' i j := by
  have hp := hp63_of hpG
  have hpv : p = 18446744069414584321 := hpG.trans pG
  obtain ⟨hNi, e_idx, e_wL, e_idL, e_aL, e_wR, e_idR, e_aR, e_lo, e_hi⟩ := hrow
  obtain ⟨A, B, hNA, hl, hr⟩ := L.link i hi
  obtain ⟨A', B', hNA', hl', hr'⟩ := L'.link i hi
  rw [← hNi, hNA] at hNA'
  injection hNA' with hA hB
  subst hA; subst hB
  obtain ⟨e_loL, e_hiL, rkL, loLlt, hiLlt⟩ := side_lohi T L T' L' hp (atomL T hi) (atomL T' hi) hl hl'
  obtain ⟨e_loR, e_hiR, rkR, loRlt, hiRlt⟩ := side_lohi T L T' L' hp (atomR T hi) (atomR T' hi) hr hr'
  -- masks
  have e_isF : v i Cell.isF = v' i Cell.isF := by rw [T.isF i hi, T'.isF i hi]
  have e_isL : v i Cell.isL = v' i Cell.isL := by rw [T.isL i hi, T'.isL i hi]
  -- carry
  have h62 : (2 : ZMod p) ^ 62 ≠ 0 := by
    intro h
    have hc : ((2 ^ 62 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by exact_mod_cast h
    have := natCast_inj_lt hc (by rw [hpv]; norm_num) (by rw [hpv]; norm_num)
    norm_num at this
  have c1 : v i Cell.lo + 2 ^ 62 * v i Cell.carry - (v i Cell.loL + v i Cell.loR + 1) = 0 := (T.cell hi).rkLo
  have c2 : v' i Cell.lo + 2 ^ 62 * v' i Cell.carry - (v' i Cell.loL + v' i Cell.loR + 1) = 0 :=
    (T'.cell hi).rkLo
  have e_carry : v i Cell.carry = v' i Cell.carry :=
    mul_left_cancel₀ h62 (by linear_combination c1 - c2 - e_lo + e_loL + e_loR)
  -- the rank bits
  have p62 : 2 ^ 62 ≤ p := by rw [hpv]; norm_num
  have p48 : 2 ^ 48 ≤ p := by rw [hpv]; norm_num
  have p32 : 2 ^ 32 ≤ p := by rw [hpv]; norm_num
  have a1 : v i Cell.lo = ∑ m ∈ Finset.range 62, (2 : ZMod p) ^ m * v i (Cell.bit0 + m) :=
    sub_eq_zero.mp (T.cell hi).loBits
  have a2 : v' i Cell.lo = ∑ m ∈ Finset.range 62, (2 : ZMod p) ^ m * v' i (Cell.bit0 + m) :=
    sub_eq_zero.mp (T'.cell hi).loBits
  have b1 : v i Cell.hi = ∑ m ∈ Finset.range 48, (2 : ZMod p) ^ m * v i (Cell.bit0 + 62 + m) :=
    sub_eq_zero.mp (T.cell hi).hiBits
  have b2 : v' i Cell.hi = ∑ m ∈ Finset.range 48, (2 : ZMod p) ^ m * v' i (Cell.bit0 + 62 + m) :=
    sub_eq_zero.mp (T'.cell hi).hiBits
  have bl := bits_unique (x := fun m => v i (Cell.bit0 + m)) (y := fun m => v' i (Cell.bit0 + m)) 62 p62
    (fun m hm => (T.cell hi).bits m (by omega)) (fun m hm => (T'.cell hi).bits m (by omega))
    (by
      show ∑ m ∈ Finset.range 62, (2 : ZMod p) ^ m * v i (Cell.bit0 + m) =
        ∑ m ∈ Finset.range 62, (2 : ZMod p) ^ m * v' i (Cell.bit0 + m)
      rw [← a1, ← a2, e_lo])
  have bh := bits_unique (x := fun m => v i (Cell.bit0 + 62 + m)) (y := fun m => v' i (Cell.bit0 + 62 + m)) 48 p48
    (fun m hm => by
      show v i (Cell.bit0 + 62 + m) = 0 ∨ v i (Cell.bit0 + 62 + m) = 1
      rw [Nat.add_assoc]; exact (T.cell hi).bits (62 + m) (by omega))
    (fun m hm => by
      show v' i (Cell.bit0 + 62 + m) = 0 ∨ v' i (Cell.bit0 + 62 + m) = 1
      rw [Nat.add_assoc]; exact (T'.cell hi).bits (62 + m) (by omega))
    (by
      show ∑ m ∈ Finset.range 48, (2 : ZMod p) ^ m * v i (Cell.bit0 + 62 + m) =
        ∑ m ∈ Finset.range 48, (2 : ZMod p) ^ m * v' i (Cell.bit0 + 62 + m)
      rw [← b1, ← b2, e_hi])
  -- kind bits and rank inverses
  have kL := kind_eval (K.left hi)
  have kL' := kind_eval (K'.left hi)
  have kR := kind_eval (K.right hi)
  have kR' := kind_eval (K'.right hi)
  have pL := PinsP1.canonM_left (envAt v i) (T.hM i hi)
  have pL' := PinsP1.canonM_left (envAt v' i) (T'.hM i hi)
  have pR := PinsP1.canonM_right (envAt v i) (T.hM i hi)
  have pR' := PinsP1.canonM_right (envAt v' i) (T'.hM i hi)
  simp only [envAt] at kL kL' kR kR' pL pL' pR pR'
  obtain ⟨e_kbL, e_invL⟩ := side_kind e_wL e_loL e_hiL (T.cell hi).wL (T'.cell hi).wL kL kL' pL.2.2 pL'.2.2
    (fun hw => limbsum_ne_zero hp loLlt hiLlt (by rw [rkL]; exact side_pos L hl hw))
  obtain ⟨e_kbR, e_invR⟩ := side_kind e_wR e_loR e_hiR (T.cell hi).wR (T'.cell hi).wR kR kR' pR.2.2 pR'.2.2
    (fun hw => limbsum_ne_zero hp loRlt hiRlt (by rw [rkR]; exact side_pos L hr hw))
  -- the limb bits
  obtain ⟨c3, c4, c6, c7, -⟩ := T.limbs hpG hi
  obtain ⟨c3', c4', c6', c7', -⟩ := T'.limbs hpG hi
  have xL : xF (v i) Cell.wL Cell.idL Cell.aL = xF (v' i) Cell.wL Cell.idL Cell.aL := by
    unfold xF; rw [e_wL, e_idL, e_aL]
  have xR : xF (v i) Cell.wR Cell.idR Cell.aR = xF (v' i) Cell.wR Cell.idR Cell.aR := by
    unfold xF; rw [e_wR, e_idR, e_aR]
  have k3 : kF (v i) 3 = kF (v' i) 3 := ZMod.val_injective p (by rw [c3, c3', xL])
  have k4 : kF (v i) 4 = kF (v' i) 4 := ZMod.val_injective p (by rw [c4, c4', xL])
  have k6 : kF (v i) 6 = kF (v' i) 6 := ZMod.val_injective p (by rw [c6, c6', xR])
  have k7 : kF (v i) 7 = kF (v' i) 7 := ZMod.val_injective p (by rw [c7, c7', xR])
  have hlimb : ∀ (c : ℕ), c < 4 → ∀ m < 32,
      v i (SideM.A + 32 * c + m) = 0 ∨ v i (SideM.A + 32 * c + m) = 1 :=
    fun c hc => limbL_bits (T.mrow hi).limb c hc
  have hlimb' : ∀ (c : ℕ), c < 4 → ∀ m < 32,
      v' i (SideM.A + 32 * c + m) = 0 ∨ v' i (SideM.A + 32 * c + m) = 1 :=
    fun c hc => limbL_bits (T'.mrow hi).limb c hc
  have grp : ∀ (c k : ℕ), c < 4 → kF (v i) k = kF (v' i) k →
      (∀ t : ℕ → ZMod p, kF t k = ∑ m ∈ Finset.range 32, (2 : ZMod p) ^ m * t (SideM.A + 32 * c + m)) →
      ∀ m < 32, v i (SideM.A + 32 * c + m) = v' i (SideM.A + 32 * c + m) := by
    intro c k hc hk hsum
    refine bits_unique (x := fun m => v i (SideM.A + 32 * c + m)) (y := fun m => v' i (SideM.A + 32 * c + m)) 32
      p32 (hlimb c hc) (hlimb' c hc) ?_
    show ∑ m ∈ Finset.range 32, (2 : ZMod p) ^ m * v i (SideM.A + 32 * c + m) =
      ∑ m ∈ Finset.range 32, (2 : ZMod p) ^ m * v' i (SideM.A + 32 * c + m)
    rw [← hsum, ← hsum]; exact hk
  have g0 := grp 0 3 (by norm_num) k3 fun t => kF_eq_sum t _ (Or.inl ⟨rfl, rfl⟩)
  have g1 := grp 1 4 (by norm_num) k4 fun t => kF_eq_sum t _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have g2 := grp 2 6 (by norm_num) k6 fun t => kF_eq_sum t _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have g3 := grp 3 7 (by norm_num) k7 fun t => kF_eq_sum t _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  -- the inverse-or-zero columns
  obtain ⟨t1, t2⟩ := tgates_eval (T.mrow hi).sideL
  obtain ⟨t1', t2'⟩ := tgates_eval (T'.mrow hi).sideL
  obtain ⟨u1, u2⟩ := tgates_eval (T.mrow hi).sideR
  obtain ⟨u1', u2'⟩ := tgates_eval (T'.mrow hi).sideR
  simp only [envAt] at t1 t2 t1' t2' u1 u2 u1' u2'
  have sL : ∑ m ∈ Finset.range 32, (2 : ZMod p) ^ m * v i (SideM.bLh 0 + m) =
      ∑ m ∈ Finset.range 32, (2 : ZMod p) ^ m * v' i (SideM.bLh 0 + m) :=
    Finset.sum_congr rfl fun m hm => by
      have := g0 m (Finset.mem_range.mp hm)
      simp only [SideM.bLh, SideM.A] at this ⊢
      rw [show 134 + 0 + m = 134 + 32 * 0 + m by ring, this]
  have sR : ∑ m ∈ Finset.range 32, (2 : ZMod p) ^ m * v i (SideM.bRh 0 + m) =
      ∑ m ∈ Finset.range 32, (2 : ZMod p) ^ m * v' i (SideM.bRh 0 + m) :=
    Finset.sum_congr rfl fun m hm => by
      have := g2 m (Finset.mem_range.mp hm)
      simp only [SideM.bRh, SideM.A] at this ⊢
      rw [show 134 + 64 + m = 134 + 32 * 2 + m by ring, this]
  have e_tL : v i SideM.tL = v' i SideM.tL := by rw [inv_det t1 t2, inv_det t1' t2', sL]
  have e_tR : v i SideM.tR = v' i SideM.tR := by rw [inv_det u1 u2, inv_det u1' u2', sR]
  -- assembly
  intro j hj hnm
  rcases (by omega : j < 18 ∨ (18 ≤ j ∧ j < 80) ∨ (80 ≤ j ∧ j < 128) ∨ (128 ≤ j ∧ j < 134) ∨
      (134 ≤ j ∧ j < 166) ∨ (166 ≤ j ∧ j < 198) ∨ (198 ≤ j ∧ j < 230) ∨ (230 ≤ j ∧ j < 262) ∨
      j = 262 ∨ j = 263) with h | h | h | h | h | h | h | h | h | h
  · interval_cases j
    exacts [e_isF, e_isL, e_idx, e_idL, e_idR, e_wL, e_wR, e_aL, e_aR, e_lo, e_hi, e_loL, e_hiL, e_loR, e_hiR,
      e_carry, (hnm (Or.inl rfl)).elim, (hnm (Or.inr (Or.inl rfl))).elim]
  · have := bl (j - 18) (by omega)
    simp only [Cell.bit0] at this
    rwa [show 18 + (j - 18) = j by omega] at this
  · have := bh (j - 80) (by omega)
    simp only [Cell.bit0] at this
    rwa [show 18 + 62 + (j - 80) = j by omega] at this
  · obtain ⟨h1, h2⟩ := h
    interval_cases j
    exacts [(hnm (Or.inr (Or.inr (Or.inl rfl)))).elim, (hnm (Or.inr (Or.inr (Or.inr rfl)))).elim, e_kbL, e_kbR, e_invL, e_invR]
  · have := g0 (j - 134) (by omega); simp only [SideM.A] at this
    rwa [show 134 + 32 * 0 + (j - 134) = j by omega] at this
  · have := g1 (j - 166) (by omega); simp only [SideM.A] at this
    rwa [show 134 + 32 * 1 + (j - 166) = j by omega] at this
  · have := g2 (j - 198) (by omega); simp only [SideM.A] at this
    rwa [show 134 + 32 * 2 + (j - 198) = j by omega] at this
  · have := g3 (j - 230) (by omega); simp only [SideM.A] at this
    rwa [show 134 + 32 * 3 + (j - 230) = j by omega] at this
  · subst h; exact e_tL
  · subst h; exact e_tR

/-- **`cols_eq_of_set_nm`**: `cols_eq_of_set` without `hmul`, on the non-multiplicity columns. -/
theorem cols_eq_of_set_nm (T : TableM v n) (L : NounLink v n N) (K : KindRows v n)
    (T' : TableM v' n') (L' : NounLink v' n' N') (K' : KindRows v' n')
    (hpG : p = Nock.Atoms.p) (hnp : n ≤ p) (hnp' : n' ≤ p)
    (hset : ∀ m, (∃ i < n, N i = m) ↔ (∃ j < n', N' j = m)) :
    n = n' ∧ ∀ i < n, ∀ j < 334, ¬ MulCol j → v i j = v' i j := by
  obtain ⟨hn, hrows⟩ := rows_eq_of_set T L T' L' hpG hnp hnp' hset
  subst hn
  have hp := hp63_of hpG
  have hA : ∀ i < n, ∀ j < 264, ¬ MulCol j → v i j = v' i j := fun i hi => rowA_eq_nm T L K T' L' K' hpG hi (hrows i hi)
  refine ⟨rfl, fun i hi j hj hnm => ?_⟩
  by_cases hj264 : j < 264
  · exact hA i hi j hj264 hnm
  have hm := T.mrow hi
  have hm' := T'.mrow hi
  by_cases hlast : i + 1 = n
  · have hL : (envAt v i).trace Cell.isL = 1 := by
      show v i Cell.isL = 1; rw [T.isL i hi]; simp [hlast]
    have hL' : (envAt v' i).trace Cell.isL = 1 := by
      show v' i Cell.isL = 1; rw [T'.isL i hi]; simp [hlast]
    obtain ⟨s1, d1⟩ := gadget_last hm hL
    obtain ⟨s2, d2⟩ := gadget_last hm' hL'
    rcases (by omega : j < 272 ∨ (272 ≤ j ∧ j < 334)) with h | h
    · have a := s1 (j - 264) (by omega); have b := s2 (j - 264) (by omega)
      simp only [envAt, SideM.s, SideM.A] at a b
      rw [show 134 + 130 + (j - 264) = j by omega] at a b
      rw [a, b]
    · have a := d1 (j - 272) (by omega); have b := d2 (j - 272) (by omega)
      simp only [envAt, SideM.d, SideM.A] at a b
      rw [show 134 + 138 + (j - 272) = j by omega] at a b
      rw [a, b]
  · have hi1 : i + 1 < n := by omega
    have hL : (envAt v i).trace Cell.isL = 0 := by
      show v i Cell.isL = 0; rw [T.isL i hi]; simp [hlast]
    have hL' : (envAt v' i).trace Cell.isL = 0 := by
      show v' i Cell.isL = 0; rw [T'.isL i hi]; simp [hlast]
    obtain ⟨s, d⟩ := gadget_eq hp hm hm' hL hL'
      (fun k => kF_congr_nm (fun j hj hm => hA i hi j (by omega) hm) k)
      (fun k => kF_congr_nm (fun j hj hm => hA (i + 1) hi1 j (by omega) hm) k)
    rcases (by omega : j < 272 ∨ (272 ≤ j ∧ j < 334)) with h | h
    · have a := s (j - 264) (by omega)
      simp only [envAt, SideM.s, SideM.A] at a
      rwa [show 134 + 130 + (j - 264) = j by omega] at a
    · have a := d (j - 272) (by omega)
      simp only [envAt, SideM.d, SideM.A] at a
      rwa [show 134 + 138 + 0 + (j - 272) = j by omega] at a

end Main

/-! ## 2. The fingerprints without the multiplicities -/

section Clr
variable {q : ℕ}

/-- A B0 row with its two multiplicities zeroed. -/
def clr (c : VclL.CellRowB0 q) : VclL.CellRowB0 q := { c with mv := 0, mx := 0 }

/-- **The B0 decoder reads no multiplicity.** -/
theorem decodeB0_clr (t : List (VclL.CellRowB0 q)) : ∀ f i, VclL.decodeB0 (t.map clr) f i = VclL.decodeB0 t f i
  | 0, i => rfl
  | f + 1, i => by
    simp only [VclL.decodeB0, List.getElem?_map, Option.bind_map, Function.comp_def, decodeB0_clr t f]
    rfl

theorem preZ_clr (t : List (VclL.CellRowB0 q)) (i : ℕ) :
    VclL.preZNounOfTable (t.map clr) i = VclL.preZNounOfTable t i :=
  decodeB0_clr t _ i

/-- **The two-provider decoder reads no multiplicity.** -/
theorem decodeTree_clr (t : List (VclL.CellRowB0 q)) (ext : ℕ → Option Noun) :
    ∀ f i, VclL.decodeTree (t.map clr) (VclL.leaf2 q ext) f i = VclL.decodeTree t (VclL.leaf2 q ext) f i
  | 0, i => rfl
  | f + 1, i => by
    simp only [VclL.decodeTree, List.getElem?_map, Option.bind_map, Function.comp_def, decodeTree_clr t ext f]
    rfl

theorem preZ2_clr (t : List (VclL.CellRowB0 q)) (ext : ℕ → Option Noun) (i : ℕ) :
    VclL.preZNounOfTable2 (t.map clr) ext i = VclL.preZNounOfTable2 t ext i :=
  decodeTree_clr t ext _ i

end Clr

section CellFpsNm
variable {q : ℕ} [Fact q.Prime] {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **`cell_fps_eq` without the multiplicities**: the round-0 tables need only agree after `clr`. -/
theorem cell_fps_eq_nm (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t t' : List (VclL.CellRow q Kfp)}
    {vl vl' : List (VclL.VKey Kfp)} (h : VclL.TableAccepts z t vl) (h' : VclL.TableAccepts z t' vl')
    (hb0 : (t.map (·.b0)).map clr = (t'.map (·.b0)).map clr) {c c' : VclL.CellRow q Kfp} (hc : c ∈ t)
    (hc' : c' ∈ t') (hbb : clr c.b0 = clr c'.b0) : c.p = c'.p ∧ c.l = c'.l ∧ c.r = c'.r := by
  obtain ⟨L, R, hd, hp, hl, hr, -⟩ := VclL.row_genuine hq hz h hc
  obtain ⟨L', R', hd', hp', hl', hr', -⟩ := VclL.row_genuine hq hz h' hc'
  have hidx : c.b0.idx = c'.b0.idx := by simpa [clr] using congrArg VclL.CellRowB0.idx hbb
  rw [← preZ_clr, hb0, hidx, preZ_clr, hd'] at hd
  have e := Option.some.inj hd
  injection e with e1 e2
  subst e1 e2
  exact ⟨hp.trans hp'.symm, hl.trans hl'.symm, hr.trans hr'.symm⟩

end CellFpsNm

section B0Nm
variable {F : Type} [Field F] [DecidableEq F]

/-- **`cellB0Of` after `clr` reads no multiplicity column.** -/
theorem cellB0Of_clr_congr {e e' : Env F} (h : ∀ j < 129, ¬ MulCol j → e.trace j = e'.trace j) :
    clr (cellB0Of e) = clr (cellB0Of e') := by
  simp only [clr, cellB0Of, h Cell.idx (by decide) (by decide), h Cell.idL (by decide) (by decide),
    h Cell.idR (by decide) (by decide), h Cell.wL (by decide) (by decide), h Cell.wR (by decide) (by decide),
    h Cell.aL (by decide) (by decide), h Cell.aR (by decide) (by decide), h Cell.lo (by decide) (by decide),
    h Cell.hi (by decide) (by decide), h Cell.loL (by decide) (by decide), h Cell.hiL (by decide) (by decide),
    h Cell.loR (by decide) (by decide), h Cell.hiR (by decide) (by decide),
    h Cell.carry (by decide) (by decide)]

end B0Nm

section RoundNm
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1 Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs pubs' : ℕ → K)

/-- **`cell_round1_eq` without the multiplicities**: equal NON-multiplicity round-0 columns give equal
fingerprint roles `p l r` (`𝕂`-roles `0 .. 17`). -/
theorem cell_round1_eq_nm (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    {Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}
    {Q' : Fin (cellChipHQKW δF b hn nodes orbit chals pubs').rap.w → F[X]}
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hsat' : (cellChipHQKW δF b hn nodes orbit chals pubs').rap.Satisfies Q')
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hbind' : (cellChipHQKW δF b hn nodes orbit chals pubs').BindsPreprocessing Q')
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (hserved : ValidityServed (cellTableOf δF b nodes orbit chals pubs
      (restrictHQKWCell δF b hn nodes orbit chals pubs Q)))
    (hserved' : ValidityServed (cellTableOf δF b nodes orbit chals pubs'
      (restrictHQKWCell δF b hn nodes orbit chals pubs' Q')))
    (h0 : ∀ (i : Fin n) (j : ℕ), j < 134 → ¬ MulCol j →
      (hqkEF b nodes orbit chals pubs Q i).trace j = (hqkEF b nodes orbit chals pubs' Q' i).trace j) :
    ∀ (i : Fin n), ∀ r < 18,
      (wEK δF b nodes orbit chals pubs Q i).trace r = (wEK δF b nodes orbit chals pubs' Q' i).trace r := by
  have hsat0 := cellChipHQKW_restrict_cell_sat δF b hn nodes orbit chals pubs Q hsat
  have hbind0 := cellChipHQKW_restrict_bind δF b hn nodes orbit chals pubs Q hbind
  have hsat0' := cellChipHQKW_restrict_cell_sat δF b hn nodes orbit chals pubs' Q' hsat'
  have hbind0' := cellChipHQKW_restrict_bind δF b hn nodes orbit chals pubs' Q' hbind'
  have hA := cellTable_accepts δF b hn nodes orbit chals pubs _ hsat0 hF hq hz hbind0 hinj hadj hnp hserved []
  have hA' := cellTable_accepts δF b hn nodes orbit chals pubs' _ hsat0' hF hq hz hbind0' hinj hadj hnp
    hserved' []
  have hbi : ∀ i : Fin n,
      clr (cellB0Of (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)) =
        clr (cellB0Of (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)) := by
    intro i
    rw [← cellB0Of_hqkw δF b hn nodes orbit chals pubs Q i, ← cellB0Of_hqkw δF b hn nodes orbit chals pubs' Q' i]
    exact cellB0Of_clr_congr (fun j hj hm => h0 i j (by omega) hm)
  have hb0 : ((cellTableOf δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q)).map
      (·.b0)).map clr = ((cellTableOf δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q')).map
      (·.b0)).map clr := by
    unfold cellTableOf
    rw [List.map_ofFn, List.map_ofFn, List.map_ofFn, List.map_ofFn]
    congr 1
    funext i
    exact hbi i
  intro i r hr
  have hc : cellRowOf δF (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) ∈
      cellTableOf δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hc' : cellRowOf δF (cellEnvK δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)
      (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) ∈
      cellTableOf δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  obtain ⟨hp, hl, hrr⟩ := cell_fps_eq_nm hq hz hA hA' hb0 hc hc' (hbi i)
  have hpp : (QFP.var Cell.pR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) =
      (QFP.var Cell.pR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)
      (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) := hp
  have hll : (QFP.var Cell.lR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) =
      (QFP.var Cell.lR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)
      (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) := hl
  have hrr' : (QFP.var Cell.rR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) =
      (QFP.var Cell.rR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)
      (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) := hrr
  rw [← cellEnvK_trace_eq δF b hn nodes orbit chals pubs Q i (by omega),
    ← cellEnvK_trace_eq δF b hn nodes orbit chals pubs' Q' i (by omega)]
  rcases (by omega : r < 6 ∨ (6 ≤ r ∧ r < 12) ∨ 12 ≤ r) with h | h | h
  · have := qfp_roles δF hpp r (by show r < 6; omega)
    simpa [Cell.pR] using this
  · have := qfp_roles δF hll (r - 6) (by omega)
    simpa [Cell.lR, show 6 + (r - 6) = r by omega] using this
  · have := qfp_roles δF hrr' (r - 12) (by omega)
    simpa [Cell.rR, show 12 + (r - 12) = r by omega] using this

end RoundNm

/-! ## 3. The keys without the multiplicities -/

section KeysNm
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  {eK eK' : Env K} {eF eF' : Env F}

/-- **The validity key and the two export keys read the roles `0 .. 17` and `idx lo hi` only.** -/
theorem keys_cong_nm (hK : ∀ r < 18, eK.trace r = eK'.trace r) (hidx : eF.trace Cell.idx = eF'.trace Cell.idx)
    (hlo : eF.trace Cell.lo = eF'.trace Cell.lo) (hhi : eF.trace Cell.hi = eF'.trace Cell.hi) :
    (∀ e ∈ (Cell.vKeyP : List (QE F)), e.ev δF eK eF = e.ev δF eK' eF') ∧
    (∀ e ∈ (Cell.xKeyS (0 : F)), e.ev δF eK eF = e.ev δF eK' eF') ∧
    (∀ e ∈ (Cell.xKeyS (1 : F)), e.ev δF eK eF = e.ev δF eK' eF') := by
  have V : ∀ r, r + 1 < 18 → (QE.var r : QE F).ev δF eK eF = (QE.var r : QE F).ev δF eK' eF' :=
    fun r hr => var_cong δF hK r hr
  have B : (QE.base (cv Cell.idx) : QE F).ev δF eK eF = (QE.base (cv Cell.idx) : QE F).ev δF eK' eF' := by
    rw [ev_base, ev_base]; simp only [CoeffExpr.eval, cv]; rw [hidx]
  have Mk : (QE.mk2 (cv Cell.lo) (cv Cell.hi) : QE F).ev δF eK eF =
      (QE.mk2 (cv Cell.lo) (cv Cell.hi) : QE F).ev δF eK' eF' := by
    rw [ev_mk2, ev_mk2]; simp only [CoeffExpr.eval, cv]; rw [hlo, hhi]
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [Cell.vKeyP, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact Mk
    · exact B
  · intro e he
    simp only [Cell.xKeyS, Cell.xKey, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.append_assoc,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact B
    · exact base_cst_cong δF _
  · intro e he
    simp only [Cell.xKeyS, Cell.xKey, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.append_assoc,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact B
    · exact base_cst_cong δF _

/-- Equal entries give equal key vectors. -/
theorem keyVec_congr {m : ℕ} {es : List (QE F)} (h : ∀ e ∈ es, e.ev δF eK eF = e.ev δF eK' eF') :
    keyVec δF m es eK eF = keyVec δF m es eK' eF' := by
  funext c
  simp only [keyVec]
  by_cases hc : (c : ℕ) < es.length
  · rw [List.getD_eq_getElem _ _ hc]; exact h _ (List.getElem_mem hc)
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

end KeysNm

section KeyHNm
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The handle-export key reads no multiplicity column.** -/
theorem keyVec5_keyHK_congr_nm {e e' : Env F} (h : ∀ j < 134, ¬ MulCol j → e.trace j = e'.trace j) :
    (ServeH.keyVec5 (K := K) (keyHK (F := F)) e) = ServeH.keyVec5 (keyHK (F := F)) e' := by
  have h1 := h Cell.idx (by decide) (by decide)
  have h2 := h Cell.wL (by decide) (by decide)
  have h3 := h CellTwinK.kbL (by decide) (by decide)
  have h4 := h Cell.idL (by decide) (by decide)
  have h5 := h Cell.aL (by decide) (by decide)
  have h6 := h Cell.wR (by decide) (by decide)
  have h7 := h CellTwinK.kbR (by decide) (by decide)
  have h8 := h Cell.idR (by decide) (by decide)
  have h9 := h Cell.aR (by decide) (by decide)
  funext c
  simp only [ServeH.keyVec5]
  congr 1
  fin_cases c <;>
    simp [keyHK, CellH.valE, CoeffExpr.eval, cv, notE, h1, h2, h3, h4, h5, h6, h7, h8, h9]

end KeyHNm

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.mulCol_names
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.kF_congr_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.rowA_eq_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.cols_eq_of_set_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.decodeB0_clr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.decodeTree_clr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.cell_fps_eq_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.cellB0Of_clr_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.cell_round1_eq_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.keys_cong_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.keyVec_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1.keyVec5_keyHK_congr_nm
