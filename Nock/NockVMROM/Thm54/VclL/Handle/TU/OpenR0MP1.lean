/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/OpenR0MP1.lean

 **The cell table's round-0 and aux columns are determined by its noun set (trace uniqueness, P1 fragment).**

 Setting (as `CellOrderP1`): two tables of row values `v, v' : ℕ → ℕ → ZMod p` with `n` rows, each satisfying the
 side gates and the cell base gates (`TableM`), the kind gates (`KindRows`), and linked to row nouns `N, N'`
 (`NounLink`), with the same noun SET.

 * §1 `bits_unique` (binary representations below `p` are unique), `inv_det` (a canonical inverse-or-zero column is
 `z⁻¹`), `kind_det` (a side's kind bit is `0` and its rank inverse is `0` or `(lo + hi)⁻¹`).
 * §2 per-row facts: the child rank limbs `loL hiL loR hiR`, the carry, the rank bits, the kind bits and rank inverses,
 the `128` limb bits and the two inverse-or-zero columns.
 * §3 the sort gadget's one-hot `s` and difference bits `d`: the one-hot index is the first differing key component.
 * §4 **`cols_eq_of_set`**: the two tables have the same row count and agree on every column `< 334` (the `134`
 round-0 cell columns and the `200` aux columns) at every row, given the four multiplicity columns
 `mv mx mx1 mh` agree (hypothesis `hmul`).
 * §5 the bridge to `OpenP1.r0M` / `OpenP1.auxM`: `TableM` and `KindRows` of the side row values `vM` from
 `AcceptsCanon` (`tableM_of_accepts`, `kindRows_of_accepts`), and **`r0M_auxM_of_set`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1

noncomputable section

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)

/-! ## 1. Generic lemmas -/

section Gen
variable {p : ℕ} [Fact p.Prime]

/-- **Binary representations are unique below `p`.** -/
theorem bits_unique {x y : ℕ → ZMod p} : ∀ n, 2 ^ n ≤ p → (∀ i < n, x i = 0 ∨ x i = 1) →
    (∀ i < n, y i = 0 ∨ y i = 1) →
    ∑ i ∈ Finset.range n, (2 : ZMod p) ^ i * x i = ∑ i ∈ Finset.range n, (2 : ZMod p) ^ i * y i →
    ∀ i < n, x i = y i
  | 0, _, _, _, _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, hp, hx, hy, hs => by
    obtain ⟨m, hm, hme⟩ := bits_cast x n (fun i hi => hx i (by omega))
    obtain ⟨m', hm', hme'⟩ := bits_cast y n (fun i hi => hy i (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hme, hme'] at hs
    have h2 : 2 ^ n ≤ p := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hp
    have hpow : (2 : ZMod p) ^ n = ((2 ^ n : ℕ) : ZMod p) := by push_cast; rfl
    have hps : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    have htop : x n = y n := by
      rcases hx n (by omega) with h1 | h1 <;> rcases hy n (by omega) with h1' | h1'
      · rw [h1, h1']
      · exfalso
        rw [h1, h1', mul_zero, add_zero, mul_one] at hs
        have hc : ((m : ℕ) : ZMod p) = ((m' + 2 ^ n : ℕ) : ZMod p) := by push_cast; exact hs
        have := natCast_inj_lt hc (by omega) (by omega)
        omega
      · exfalso
        rw [h1, h1', mul_zero, add_zero, mul_one] at hs
        have hc : ((m + 2 ^ n : ℕ) : ZMod p) = ((m' : ℕ) : ZMod p) := by push_cast; exact hs
        have := natCast_inj_lt hc (by omega) (by omega)
        omega
      · rw [h1, h1']
    have hrest : (m : ZMod p) = m' := by rw [htop] at hs; exact add_right_cancel hs
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact bits_unique n h2 (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
        (by rw [hme, hme', hrest]) i hi
    · exact htop

/-- **A canonical inverse-or-zero column is `z⁻¹`** (`z·(z·t − 1) = 0`, `t·(z·t − 1) = 0`). -/
theorem inv_det {F : Type} [Field F] {z t : F} (h1 : z * (z * t - 1) = 0) (h2 : t * (z * t - 1) = 0) :
    t = z⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp only [zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero] at h2
    rw [h2, inv_zero]
  · have : z * t - 1 = 0 := (mul_eq_zero.mp h1).resolve_left hz
    exact eq_inv_of_mul_eq_one_right (by linear_combination this)

/-- **A side's kind bit and rank inverse**: with the five kind gates, the E2 pin, a boolean weight, and a
nonzero child rank when weighted, `kb = 0` and `inv = 0` (atom child) or `(lo + hi)⁻¹` (cell child). -/
theorem kind_det {F : Type} [Field F] {w kb inv lo hi : F} (hw : w = 0 ∨ w = 1) (g2 : kb * lo = 0)
    (g3 : kb * hi = 0) (g4 : w * (1 - kb) * ((lo + hi) * inv - 1) = 0) (g5 : kb * (1 - w) = 0)
    (e2 : (1 - w + w * kb) * inv = 0) (hne : w = 1 → lo + hi ≠ 0) :
    kb = 0 ∧ (w = 0 → inv = 0) ∧ (w = 1 → inv = (lo + hi)⁻¹) := by
  rcases hw with rfl | rfl
  · simp only [sub_zero, mul_one] at g5
    subst g5
    simp only [sub_zero, zero_mul, add_zero, one_mul] at e2
    exact ⟨rfl, fun _ => e2, fun h => absurd h zero_ne_one⟩
  · have hs := hne rfl
    have hkb : kb = 0 := by
      have : kb * (lo + hi) = 0 := by linear_combination g2 + g3
      exact (mul_eq_zero.mp this).resolve_right hs
    subst hkb
    simp only [one_mul, sub_zero, mul_one] at g4
    exact ⟨rfl, fun h => absurd h one_ne_zero, fun _ => eq_inv_of_mul_eq_one_right (by linear_combination g4)⟩

/-- The five kind gates of one side, evaluated. -/
theorem kind_eval {F : Type} [Field F] {e : Env F} {kb inv w lo hi : ℕ}
    (h : ∀ g ∈ CellTwinK.sideGates (F := F) kb inv w lo hi, g.eval e = 0) :
    e.trace kb * e.trace lo = 0 ∧ e.trace kb * e.trace hi = 0 ∧
      e.trace w * (1 - e.trace kb) * ((e.trace lo + e.trace hi) * e.trace inv - 1) = 0 ∧
      e.trace kb * (1 - e.trace w) = 0 := by
  simp only [CellTwinK.sideGates, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨-, g2, g3, g4, g5⟩ := h
  simp only [CoeffExpr.eval, cv, notE] at g2 g3 g4 g5
  exact ⟨g2, g3, g4, g5⟩

/-- The canonical inverse-or-zero gates of one side, evaluated (`z = bitSum h 32 − (2^32 − 1)`). -/
theorem tgates_eval {F : Type} [Field F] {e : Env F} {w id a kb inv h l t : ℕ}
    (hS : ∀ g ∈ sideM (F := F) w id a kb inv h l t, g.eval e = 0) :
    (∑ i ∈ Finset.range 32, (2 : F) ^ i * e.trace (h + i) - (2 ^ 32 - 1)) *
        ((∑ i ∈ Finset.range 32, (2 : F) ^ i * e.trace (h + i) - (2 ^ 32 - 1)) * e.trace t - 1) = 0 ∧
      e.trace t * ((∑ i ∈ Finset.range 32, (2 : F) ^ i * e.trace (h + i) - (2 ^ 32 - 1)) * e.trace t - 1) = 0 := by
  simp only [sideM, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hS
  obtain ⟨-, g2, g3, -⟩ := hS
  simp only [CoeffExpr.eval, cv, bitSum_eval] at g2 g3
  exact ⟨g2, g3⟩

/-- A key component reads the columns below `262` only. -/
theorem kF_congr {t t' : ℕ → ZMod p} (h : ∀ j < 262, t j = t' j) (k : ℕ) : kF t k = kF t' k := by
  have hb : ∀ base, base + 32 ≤ 262 →
      (bitSum base 32 : CoeffExpr (ZMod p)).eval ⟨t, fun _ => 0, fun _ => 0, fun _ => 0⟩ =
        (bitSum base 32 : CoeffExpr (ZMod p)).eval ⟨t', fun _ => 0, fun _ => 0, fun _ => 0⟩ := by
    intro base hbase
    rw [bitSum_eval, bitSum_eval]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    show (2 : ZMod p) ^ i * t (base + i) = (2 : ZMod p) ^ i * t' (base + i)
    rw [h _ (by omega)]
  unfold kF
  match k with
  | 0 => exact h Cell.hi (by decide)
  | 1 => exact h Cell.lo (by decide)
  | 2 => exact h Cell.wL (by decide)
  | 3 => exact hb _ (by decide)
  | 4 => exact hb _ (by decide)
  | 5 => exact h Cell.wR (by decide)
  | 6 => exact hb _ (by decide)
  | k + 7 => exact hb _ (by decide)

theorem kF_eq_sum (t : ℕ → ZMod p) {k : ℕ} (base : ℕ)
    (hk : (k = 3 ∧ base = SideM.bLh 0) ∨ (k = 4 ∧ base = SideM.bLl 0) ∨ (k = 6 ∧ base = SideM.bRh 0) ∨
      (k = 7 ∧ base = SideM.bRl 0)) :
    kF t k = ∑ i ∈ Finset.range 32, (2 : ZMod p) ^ i * t (base + i) := by
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (unfold kF; exact bitSum_eval _ _ _)

end Gen

/-! ## 2. Per-row facts of two tables with the same nouns -/

section Rows
variable {p : ℕ} [Fact p.Prime]

/-- **The kind gates hold at every row.** -/
def KindRows (v : ℕ → ℕ → ZMod p) (n : ℕ) : Prop :=
  ∀ i < n, ∀ g ∈ CellTwinK.kindGates (F := ZMod p), g.eval (envAt v i) = 0

variable {v v' : ℕ → ℕ → ZMod p} {n : ℕ} {N N' : ℕ → Noun}

theorem KindRows.left (K : KindRows v n) {i : ℕ} (hi : i < n) :
    ∀ g ∈ CellTwinK.sideGates (F := ZMod p) CellTwinK.kbL CellTwinK.invL Cell.wL Cell.loL Cell.hiL,
      g.eval (envAt v i) = 0 :=
  fun g hg => K i hi g (by unfold CellTwinK.kindGates; exact List.mem_append_left _ hg)

theorem KindRows.right (K : KindRows v n) {i : ℕ} (hi : i < n) :
    ∀ g ∈ CellTwinK.sideGates (F := ZMod p) CellTwinK.kbR CellTwinK.invR Cell.wR Cell.loR Cell.hiR,
      g.eval (envAt v i) = 0 :=
  fun g hg => K i hi g (by unfold CellTwinK.kindGates; exact List.mem_append_right _ hg)

theorem atomL (T : TableM v n) {i : ℕ} (hi : i < n) :
    v i Cell.wL = 0 → v i Cell.loL = 0 ∧ v i Cell.hiL = 0 := fun hw => by
  have h1 := (T.cell hi).aLlo; have h2 := (T.cell hi).aLhi
  change (1 - v i Cell.wL) * v i Cell.loL = 0 at h1
  change (1 - v i Cell.wL) * v i Cell.hiL = 0 at h2
  rw [hw, sub_zero, one_mul] at h1 h2; exact ⟨h1, h2⟩

theorem atomR (T : TableM v n) {i : ℕ} (hi : i < n) :
    v i Cell.wR = 0 → v i Cell.loR = 0 ∧ v i Cell.hiR = 0 := fun hw => by
  have h1 := (T.cell hi).aRlo; have h2 := (T.cell hi).aRhi
  change (1 - v i Cell.wR) * v i Cell.loR = 0 at h1
  change (1 - v i Cell.wR) * v i Cell.hiR = 0 at h2
  rw [hw, sub_zero, one_mul] at h1 h2; exact ⟨h1, h2⟩

/-- **A linked side's rank limbs** agree between two tables whose side links name the same child noun. -/
theorem side_lohi (T : TableM v n) (L : NounLink v n N) (T' : TableM v' n) (L' : NounLink v' n N')
    (hp : 2 ^ 63 < p) {i w id a lo hi : ℕ} {X : Noun}
    (hatom : v i w = 0 → v i lo = 0 ∧ v i hi = 0) (hatom' : v' i w = 0 → v' i lo = 0 ∧ v' i hi = 0)
    (hs : SideLink v n N i w id a lo hi X) (hs' : SideLink v' n N' i w id a lo hi X) :
    v i lo = v' i lo ∧ v i hi = v' i hi ∧ (v i hi).val * 2 ^ 62 + (v i lo).val = nCells X ∧
      (v i lo).val < 2 ^ 62 ∧ (v i hi).val < 2 ^ 62 := by
  obtain ⟨a1, a2, a3⟩ := T.side_rank hp hatom hs fun c hc hN => T.rank_eq_cells L hp X c hc hN
  obtain ⟨b1, b2, b3⟩ := T'.side_rank hp hatom' hs' fun c hc hN => T'.rank_eq_cells L' hp X c hc hN
  refine ⟨ZMod.val_injective p ?_, ZMod.val_injective p ?_, a3, a1, a2⟩ <;> rw [two62] at a1 a2 a3 b1 b2 b3 <;> omega

/-- A weighted side's child is a cell (rank `≥ 1`). -/
theorem side_pos (L : NounLink v n N) {i w id a lo hi : ℕ} {X : Noun} (hs : SideLink v n N i w id a lo hi X)
    (hw : v i w = 1) : 1 ≤ nCells X := by
  rcases hs with ⟨h0, -⟩ | ⟨-, c, hc, -, hN, -⟩
  · rw [hw] at h0; exact absurd h0 one_ne_zero
  · obtain ⟨A, B, hNc, -, -⟩ := L.link c hc
    rw [← hN, hNc]; simp [nCells]

/-- A positive rank has a nonzero limb sum. -/
theorem limbsum_ne_zero (hp : 2 ^ 63 < p) {lo hi : ZMod p} (hlo : lo.val < 2 ^ 62) (hhi : hi.val < 2 ^ 62)
    (hpos : 1 ≤ hi.val * 2 ^ 62 + lo.val) : lo + hi ≠ 0 := by
  intro h
  have hc : ((lo.val + hi.val : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
    push_cast; simp only [ZMod.natCast_zmod_val]; exact h
  rw [two62] at hlo hhi hpos; rw [two63] at hp
  have := natCast_inj_lt hc (by omega) (by omega)
  omega

/-- **The kind bit and rank inverse of one side** agree. -/
theorem side_kind {i w lo hi kb inv : ℕ}
    (hw : v i w = v' i w) (hlo : v i lo = v' i lo) (hhi : v i hi = v' i hi)
    (hwb : v i w = 0 ∨ v i w = 1) (hwb' : v' i w = 0 ∨ v' i w = 1)
    (k1 : v i kb * v i lo = 0 ∧ v i kb * v i hi = 0 ∧
      v i w * (1 - v i kb) * ((v i lo + v i hi) * v i inv - 1) = 0 ∧ v i kb * (1 - v i w) = 0)
    (k1' : v' i kb * v' i lo = 0 ∧ v' i kb * v' i hi = 0 ∧
      v' i w * (1 - v' i kb) * ((v' i lo + v' i hi) * v' i inv - 1) = 0 ∧ v' i kb * (1 - v' i w) = 0)
    (e2 : (1 - v i w + v i w * v i kb) * v i inv = 0) (e2' : (1 - v' i w + v' i w * v' i kb) * v' i inv = 0)
    (hne : v i w = 1 → v i lo + v i hi ≠ 0) :
    v i kb = v' i kb ∧ v i inv = v' i inv := by
  have hne' : v' i w = 1 → v' i lo + v' i hi ≠ 0 := by rw [← hw, ← hlo, ← hhi]; exact hne
  obtain ⟨a1, a2, a3⟩ := kind_det hwb k1.1 k1.2.1 k1.2.2.1 k1.2.2.2 e2 hne
  obtain ⟨b1, b2, b3⟩ := kind_det hwb' k1'.1 k1'.2.1 k1'.2.2.1 k1'.2.2.2 e2' hne'
  refine ⟨a1.trans b1.symm, ?_⟩
  rcases hwb with h | h
  · rw [a2 h, b2 (hw ▸ h)]
  · rw [a3 h, b3 (hw ▸ h), hlo, hhi]

end Rows

/-! ## 3. The one-hot index and the difference bits -/

section Gadget
variable {p : ℕ} [Fact p.Prime]

/-- **The gadget at a non-last row, explicitly**: `s` is the indicator of `k0`, the keys agree below `k0`, differ at
`k0`, and the difference bits encode `key_next(k0) − key(k0) − 1`. -/
theorem gadget_row {e : Env (ZMod p)} (hp : 2 ^ 63 < p) (hm : MRow e) (hL : e.trace Cell.isL = 0) :
    ∃ k0 < 8, (∀ k < 8, e.trace (SideM.s k) = if k = k0 then 1 else 0) ∧
      (∀ j < k0, kF e.traceNext j = kF e.trace j) ∧ kF e.traceNext k0 ≠ kF e.trace k0 ∧
      ∑ i ∈ Finset.range 62, (2 : ZMod p) ^ i * e.trace (SideM.d 0 + i) =
        kF e.traceNext k0 - kF e.trace k0 - 1 := by
  have hot := hm.hot
  rw [hL, sub_zero, one_mul, sub_eq_zero] at hot
  obtain ⟨k0, hk0, hs⟩ := onehot (fun k => e.trace (SideM.s k)) (fun k hk => hm.sd k (by omega)) hot (by omega)
  have hdbool : ∀ i < 62, e.trace (SideM.d 0 + i) = 0 ∨ e.trace (SideM.d 0 + i) = 1 := fun i hi => by
    have e1 : SideM.d 0 + i = SideM.A + 130 + (8 + i) := by simp only [SideM.d]; omega
    rw [e1]; exact hm.sd (8 + i) (by omega)
  obtain ⟨m, hm62, hD⟩ := bits_cast (fun i => e.trace (SideM.d 0 + i)) 62 hdbool
  have hdif := hm.dif
  rw [hL, sub_zero, one_mul] at hdif
  have hterm : ∀ k ∈ Finset.range 8, e.trace (SideM.s k) * (kF e.traceNext k - kF e.trace k) =
      if k0 = k then kF e.traceNext k - kF e.trace k else 0 := fun k hk => by
    rw [hs k (Finset.mem_range.mp hk)]
    by_cases h : k = k0
    · subst h; simp
    · simp [h, Ne.symm h]
  have hk0' : k0 ∈ Finset.range 8 := Finset.mem_range.mpr hk0
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq] at hdif
  simp only [hk0', ite_true] at hdif
  have hsum : ∑ i ∈ Finset.range 62, (2 : ZMod p) ^ i * e.trace (SideM.d 0 + i) =
      kF e.traceNext k0 - kF e.trace k0 - 1 := by linear_combination -hdif
  refine ⟨k0, hk0, hs, fun j hj => ?_, ?_, hsum⟩
  · have hf := hm.first j (by omega)
    rw [hL, sub_zero, one_mul] at hf
    have hmap : (((List.range 8).filter fun k => decide (j < k)).map fun k => e.trace (SideM.s k)) =
        (((List.range 8).filter fun k => decide (j < k)).map fun k => if k = k0 then (1 : ZMod p) else 0) := by
      refine List.map_congr_left fun k hk => ?_
      exact hs k (List.mem_range.mp (List.mem_filter.mp hk).1)
    have hmem : k0 ∈ (List.range 8).filter fun k => decide (j < k) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hk0, by simp [hj]⟩
    rw [hmap, sum_indicator k0 _ (List.nodup_range.filter _)] at hf
    simp only [hmem, ite_true, one_mul, sub_eq_zero] at hf
    exact hf
  · intro hEq
    have h0 : ((1 + m : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
      push_cast
      have : (m : ZMod p) = kF e.traceNext k0 - kF e.trace k0 - 1 := by
        rw [← hD]; exact hsum
      rw [this, hEq]; ring
    rw [two63] at hp
    have := natCast_inj_lt h0 (by rw [two62] at hm62; omega) (by omega)
    omega

/-- **The gadget columns of one non-last row agree** between two tables whose keys agree at the row and the next. -/
theorem gadget_eq {e e' : Env (ZMod p)} (hp : 2 ^ 63 < p) (hm : MRow e) (hm' : MRow e')
    (hL : e.trace Cell.isL = 0) (hL' : e'.trace Cell.isL = 0)
    (hkC : ∀ k, kF e.trace k = kF e'.trace k) (hkN : ∀ k, kF e.traceNext k = kF e'.traceNext k) :
    (∀ k < 8, e.trace (SideM.s k) = e'.trace (SideM.s k)) ∧
      ∀ i < 62, e.trace (SideM.d 0 + i) = e'.trace (SideM.d 0 + i) := by
  obtain ⟨k0, hk0, hs, hlt, hne, hsum⟩ := gadget_row hp hm hL
  obtain ⟨k1, hk1, hs', hlt', hne', hsum'⟩ := gadget_row hp hm' hL'
  have hk : k0 = k1 := by
    rcases lt_trichotomy k0 k1 with h | h | h
    · exact absurd (by rw [hkC, hkN]; exact hlt' k0 h) hne
    · exact h
    · exact absurd (by rw [← hkC, ← hkN]; exact hlt k1 h) hne'
  subst hk
  refine ⟨fun k hk => by rw [hs k hk, hs' k hk], ?_⟩
  have hdbool : ∀ (E : Env (ZMod p)), MRow E → ∀ i < 62, E.trace (SideM.d 0 + i) = 0 ∨ E.trace (SideM.d 0 + i) = 1 :=
    fun E hE i hi => by
      have e1 : SideM.d 0 + i = SideM.A + 130 + (8 + i) := by simp only [SideM.d]; omega
      rw [e1]; exact hE.sd (8 + i) (by omega)
  refine bits_unique (x := fun i => e.trace (SideM.d 0 + i)) (y := fun i => e'.trace (SideM.d 0 + i)) 62
    (by rw [two63] at hp; norm_num; omega) (hdbool e hm) (hdbool e' hm') ?_
  show ∑ i ∈ Finset.range 62, (2 : ZMod p) ^ i * e.trace (SideM.d 0 + i) =
    ∑ i ∈ Finset.range 62, (2 : ZMod p) ^ i * e'.trace (SideM.d 0 + i)
  rw [hsum, hsum', hkC, hkN]

/-- At the last row the gadget columns are `0`. -/
theorem gadget_last {e : Env (ZMod p)} (hm : MRow e) (hL : e.trace Cell.isL = 1) :
    (∀ k < 8, e.trace (SideM.s k) = 0) ∧ ∀ i < 62, e.trace (SideM.d i) = 0 := by
  refine ⟨fun k hk => ?_, fun i hi => ?_⟩
  · have := hm.lastS k hk; rwa [hL, one_mul] at this
  · have := hm.lastD i hi; rwa [hL, one_mul] at this

end Gadget

/-! ## 4. Every column of two tables with the same noun set -/

section Main
variable {p : ℕ} [Fact p.Prime] {v v' : ℕ → ℕ → ZMod p} {n n' : ℕ} {N N' : ℕ → Noun}

/-- The row equalities `rows_eq_of_set` concludes. -/
def RowsEq (v v' : ℕ → ℕ → ZMod p) (N N' : ℕ → Noun) (i : ℕ) : Prop :=
  N i = N' i ∧ v i Cell.idx = v' i Cell.idx ∧
    v i Cell.wL = v' i Cell.wL ∧ v i Cell.idL = v' i Cell.idL ∧ v i Cell.aL = v' i Cell.aL ∧
    v i Cell.wR = v' i Cell.wR ∧ v i Cell.idR = v' i Cell.idR ∧ v i Cell.aR = v' i Cell.aR ∧
    v i Cell.lo = v' i Cell.lo ∧ v i Cell.hi = v' i Cell.hi

/-- The four multiplicity columns agree at a row. -/
def MulEq (v v' : ℕ → ℕ → ZMod p) (i : ℕ) : Prop :=
  v i Cell.mv = v' i Cell.mv ∧ v i Cell.mx = v' i Cell.mx ∧ v i Cell.mx1 = v' i Cell.mx1 ∧
    v i CellH.mh = v' i CellH.mh

/-- **Stage A at one row**: every column below `264` (the `134` round-0 cell columns, the `128` limb bits and the two
inverse-or-zero columns). -/
theorem rowA_eq (T : TableM v n) (L : NounLink v n N) (K : KindRows v n)
    (T' : TableM v' n) (L' : NounLink v' n N') (K' : KindRows v' n) (hpG : p = Nock.Atoms.p)
    {i : ℕ} (hi : i < n) (hrow : RowsEq v v' N N' i) (hmul : MulEq v v' i) :
    ∀ j < 264, v i j = v' i j := by
  have hp := hp63_of hpG
  have hpv : p = 18446744069414584321 := hpG.trans pG
  obtain ⟨hNi, e_idx, e_wL, e_idL, e_aL, e_wR, e_idR, e_aR, e_lo, e_hi⟩ := hrow
  obtain ⟨m_v, m_x, m_x1, m_h⟩ := hmul
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
  intro j hj
  rcases (by omega : j < 18 ∨ (18 ≤ j ∧ j < 80) ∨ (80 ≤ j ∧ j < 128) ∨ (128 ≤ j ∧ j < 134) ∨
      (134 ≤ j ∧ j < 166) ∨ (166 ≤ j ∧ j < 198) ∨ (198 ≤ j ∧ j < 230) ∨ (230 ≤ j ∧ j < 262) ∨
      j = 262 ∨ j = 263) with h | h | h | h | h | h | h | h | h | h
  · interval_cases j
    exacts [e_isF, e_isL, e_idx, e_idL, e_idR, e_wL, e_wR, e_aL, e_aR, e_lo, e_hi, e_loL, e_hiL, e_loR, e_hiR,
      e_carry, m_v, m_x]
  · have := bl (j - 18) (by omega)
    simp only [Cell.bit0] at this
    rwa [show 18 + (j - 18) = j by omega] at this
  · have := bh (j - 80) (by omega)
    simp only [Cell.bit0] at this
    rwa [show 18 + 62 + (j - 80) = j by omega] at this
  · obtain ⟨h1, h2⟩ := h
    interval_cases j
    exacts [m_x1, m_h, e_kbL, e_kbR, e_invL, e_invR]
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

/-- **`cols_eq_of_set`: the cell table's round-0 and aux columns are determined by its noun set.** Two tables with
the side gates, the cell base gates, the masks, the kind gates and a noun link, with the same noun SET and agreeing
multiplicity columns `mv mx mx1 mh`, have the same row count and agree on every column `< 334` at every row. -/
theorem cols_eq_of_set (T : TableM v n) (L : NounLink v n N) (K : KindRows v n)
    (T' : TableM v' n') (L' : NounLink v' n' N') (K' : KindRows v' n')
    (hpG : p = Nock.Atoms.p) (hnp : n ≤ p) (hnp' : n' ≤ p)
    (hset : ∀ m, (∃ i < n, N i = m) ↔ (∃ j < n', N' j = m))
    (hmul : ∀ i < n, MulEq v v' i) :
    n = n' ∧ ∀ i < n, ∀ j < 334, v i j = v' i j := by
  obtain ⟨hn, hrows⟩ := rows_eq_of_set T L T' L' hpG hnp hnp' hset
  subst hn
  have hp := hp63_of hpG
  have hA : ∀ i < n, ∀ j < 264, v i j = v' i j := fun i hi => rowA_eq T L K T' L' K' hpG hi (hrows i hi) (hmul i hi)
  refine ⟨rfl, fun i hi j hj => ?_⟩
  by_cases hj264 : j < 264
  · exact hA i hi j hj264
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
      (fun k => kF_congr (fun j hj => hA i hi j (by omega)) k)
      (fun k => kF_congr (fun j hj => hA (i + 1) hi1 j (by omega)) k)
    rcases (by omega : j < 272 ∨ (272 ≤ j ∧ j < 334)) with h | h
    · have a := s (j - 264) (by omega)
      simp only [envAt, SideM.s, SideM.A] at a
      rwa [show 134 + 130 + (j - 264) = j by omega] at a
    · have a := d (j - 272) (by omega)
      simp only [envAt, SideM.d, SideM.A] at a
      rwa [show 134 + 138 + 0 + (j - 272) = j by omega] at a

end Main

/-! ## 5. The bridge from `AcceptsCanon` -/

section Bridge
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

/-- A trace view agreeing with `tr.M` on the first `134` columns reads, at the node `ω^i`, the side row values
`vM` of rows `i` and `i + 1`. -/
theorem envOfTrace_vM_agree (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i : ℕ) (cv pv : ℕ → ZMod p)
    {w : ℕ} (Q : Fin w → (ZMod p)[X]) (hw : 134 ≤ w)
    (hQ : ∀ (j : ℕ) (hj : j < 134), Q ⟨j, by omega⟩ = tr.M ⟨j, by omega⟩) :
    (∀ j < 134, (envAt (vM tr ax ω) i).trace j = (Reify.envOfTrace Q ω (ω ^ i) cv pv).trace j) ∧
      ∀ j < 134, (envAt (vM tr ax ω) i).traceNext j = (Reify.envOfTrace Q ω (ω ^ i) cv pv).traceNext j := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · show vM tr ax ω i j = _
    simp only [Reify.envOfTrace]
    rw [dif_pos (by omega), vM_base tr ax ω i hj, hQ j hj]
  · show vM tr ax ω (i + 1) j = _
    simp only [Reify.envOfTrace]
    rw [dif_pos (by omega), vM_base tr ax ω (i + 1) hj, hQ j hj, pow_succ']

/-- **The side row values of an accepted trace form a cell table** (`TableM`) **with the kind gates**
(`KindRows`): the side gates from `canonM` (`rows_of_canonM`), the cell base gates and the kind gates from the
cell chip's satisfaction (transferred through the first `134` columns), the masks from `BindsPreprocessing`. -/
theorem tableM_of_accepts {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) :
    TableM (vM tr ax Pb.orbitC.ω) Pb.nC ∧ KindRows (vM tr ax Pb.orbitC.ω) Pb.nC := by
  obtain ⟨hA, hC⟩ := h
  have hPb := hC.hPb
  subst hPb
  have hside := rows_of_canonM b hC.hM
  have hrow : ∀ i (hi : i < (canonPb hpG sz c).nC),
      (∀ g ∈ Cell.baseGates (F := ZMod p), g.eval (envAt (vM tr ax (canonPb hpG sz c).orbitC.ω) i) = 0) ∧
      (∀ g ∈ CellTwinK.kindGates (F := ZMod p), g.eval (envAt (vM tr ax (canonPb hpG sz c).orbitC.ω) i) = 0) := by
    intro i hi
    have hl := (expandChip_satisfies_iff_language (CellTwinKW.cellTemplateHQKW δ) b _ _ (canonPb hpG sz c).orbitC _
      (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC)).mp hA.hsatC ((canonPb hpG sz c).nodesC ⟨i, hi⟩)
      (mem_rowNodeSet _ _)
    have hx : (canonPb hpG sz c).nodesC ⟨i, hi⟩ = (canonPb hpG sz c).orbitC.ω ^ i := rfl
    rw [hx] at hl
    obtain ⟨ht, hn⟩ := envOfTrace_vM_agree tr ax (canonPb hpG sz c).orbitC.ω i _ _
      (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC) (by rw [CellTwinKW.cellChipHQKW_width]; norm_num)
      (fun j hj => rfl)
    refine ⟨cellBase_transfer (fun j hj => ht j (by omega)) (fun j hj => hn j (by omega))
      fun g hg => hl.1 g (List.mem_append_left _ hg), fun g hg => ?_⟩
    exact (colsBelow_eval (CellTwinK.kindGates_below g hg) ht hn).trans (hl.1 g (List.mem_append_right _ hg))
  have hmask : ∀ i (hi : i < (canonPb hpG sz c).nC),
      vM tr ax (canonPb hpG sz c).orbitC.ω i Cell.isF = (if i = 0 then 1 else 0) ∧
        vM tr ax (canonPb hpG sz c).orbitC.ω i Cell.isL = (if i + 1 = (canonPb hpG sz c).nC then 1 else 0) := by
    intro i hi
    obtain ⟨m1, m2⟩ := CellTwinKW.cellHQKW_masks δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC
      (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC _ hA.hbindC hA.hinjC ⟨i, hi⟩
    have e1 := (envOfTrace_vM_agree tr ax (canonPb hpG sz c).orbitC.ω i
      (slotVal b 134 (chalsMJ8 δ χ)) (slotVal b 134 M.pubsC)
      (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC) (by rw [CellTwinKW.cellChipHQKW_width]; norm_num)
      (fun j hj => rfl)).1
    have f1 := e1 Cell.isF (by decide)
    have f2 := e1 Cell.isL (by decide)
    change vM tr ax _ i Cell.isF = _ at f1
    change vM tr ax _ i Cell.isL = _ at f2
    refine ⟨f1.trans m1, f2.trans (m2.trans ?_)⟩
    simp only
    split_ifs <;> first | rfl | omega
  exact ⟨⟨fun i hi => hside i hi, fun i hi => (hrow i hi).1, fun i hi => (hmask i hi).1,
    fun i hi => (hmask i hi).2⟩, fun i hi => (hrow i hi).2⟩

/-- **`r0M_auxM_of_set`: the open facts `OpenP1.r0M` and `OpenP1.auxM`**, from two `AcceptsCanon` tuples at one
layout and coin, noun links `N`, `N'` of their side row values with the same noun SET, and agreeing multiplicity
columns `mv mx mx1 mh`. -/
theorem r0M_auxM_of_set {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    {N N' : ℕ → Noun} (L : NounLink (vM tr ax Pb.orbitC.ω) Pb.nC N)
    (L' : NounLink (vM tr' ax' Pb.orbitC.ω) Pb.nC N')
    (hset : ∀ m, (∃ i < Pb.nC, N i = m) ↔ (∃ j < Pb.nC, N' j = m))
    (hmul : ∀ i < Pb.nC, MulEq (vM tr ax Pb.orbitC.ω) (vM tr' ax' Pb.orbitC.ω) i) :
    (∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) ∧
      (∀ j i, (ax.M j).eval (Pb.nodesC i) = (ax'.M j).eval (Pb.nodesC i)) := by
  obtain ⟨T, K⟩ := tableM_of_accepts δ b h
  obtain ⟨T', K'⟩ := tableM_of_accepts δ b h'
  have hnp : Pb.nC ≤ p := by
    have := h.1.hnpC; rw [ZMod.ringChar_zmod_n] at this; omega
  obtain ⟨-, hcol⟩ := cols_eq_of_set T L K T' L' K' hpG hnp hnp hset hmul
  have hPb := h.2.hPb
  subst hPb
  refine ⟨fun j hj i => ?_, fun j i => ?_⟩
  · have := hcol i i.isLt j (by omega)
    rw [vM_base tr ax _ i hj, vM_base tr' ax' _ i hj] at this
    exact this
  · have := hcol i i.isLt (SideM.A + j) (by simp only [SideM.A]; omega)
    rw [vM_aux tr ax _ i j.isLt, vM_aux tr' ax' _ i j.isLt] at this
    exact this

end Bridge

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1.bits_unique
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1.kind_det
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1.gadget_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1.rowA_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1.cols_eq_of_set
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1.tableM_of_accepts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1.r0M_auxM_of_set
