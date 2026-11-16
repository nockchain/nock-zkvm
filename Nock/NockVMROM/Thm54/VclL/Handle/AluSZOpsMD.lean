/-
  * §1 row facts: `f1` / `f2` flags, slot heads and tags, **the 6-bit length counter** (`cn_small`, `len_le`:
    every `mS mV mW` slot has `≤ 62` rows), **the `mQM` bound** (`qm_lt`: a 25-bit `Q` lane is `< 2^25`).
  * §2 **the latches** `RL`, `RO` carried from the `f1` row to the `f2` row, on the mirror (`latch_poly`) and on the
    chip (`RL_carry`), together `latch`; the `f2` row's `D1` (`D1_f2`); `D2` at any first row (`D2_head`).
  * §3 **the view link** (`factor_link`: `L = H` on a factor slot, by the link polynomial on `mV`) and the halves
    `E + 2^16·O = A` (`halves`), which feed `Nock.Atoms.ArithSZ`'s `mul_lift_gate` / `div_lift_gate` (their `link_lift`).
  * §4 block shapes: `shape_mul` (`ra rb rc mQM`) and **the 7-slot div/mod shape** `shape7`
    (`ra rx rb ry rs mQM mQ1`), and the 7-slot block sum `D_seven`.
  * §5 **`mul_sound`**, `divmod_core`, **`div_sound`**, **`mod_sound`**; §6 **`op_sound6`** (all six ops).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent (cl onb rowAt laneL laneO laneBits limbPolyQ atomPoly BX hornerP
  packP hpackP Hp HOp Lp Lf RLp ROp D1p D2p blockSum blockRows linkP callPolys hdrs)
open Nock.Atoms (val B Canonical limbPoly natPoly Fp)

noncomputable section

variable {K : Type} [Field K] [Algebra Fp K] {δ : Fp} [Fact (¬ IsSquare (algebraMap Fp K δ))]

local notation "𝕂′" => Quad (algebraMap Fp K δ)

namespace Ctx
variable [Algebra Fp (Quad (algebraMap Fp K δ))] {R : Rows δ K} (X : Ctx R)

/-! ## 1. Row facts -/

omit X in
theorem f1_val {i : ℕ} (hi : i < R.n) : (R.eF i).trace f1 = (R.eF i).trace fst *
    ((R.eF i).trace oMul * (R.eF i).trace ra + ((R.eF i).trace oDiv + (R.eF i).trace oMod) * (R.eF i).trace rx) := by
  have g := R.G hi (mem_flag (a := ar (.sub (cv f1) (.mul (cv fst) (.add (.mul (cv oMul) (cv ra))
    (.mul (sumC [oDiv, oMod]) (cv rx)))))) (by simp [gFlag]))
  simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at g
  linear_combination g

omit X in
theorem f2_val {i : ℕ} (hi : i < R.n) : (R.eF i).trace f2 = (R.eF i).trace fst * (R.eF i).trace rb *
    ((R.eF i).trace oMul + ((R.eF i).trace oDiv + (R.eF i).trace oMod)) := by
  have g := R.G hi (mem_flag (a := ar (.sub (cv f2) (prod3 (cv fst) (cv rb) (sumC [oMul, oDiv, oMod]))))
    (by simp [gFlag]))
  simp only [AG.gate, ar, prod3, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at g
  linear_combination g

omit X in
/-- An `f2` row carries the role `rb`. -/
theorem rb_of_f2 {i : ℕ} (hi : i < R.n) (h : R.v i f2 = 1) : R.v i rb = 1 := by
  rcases R.b_role hi (j := rb) (by simp [roleCols]) with h0 | h1
  · have e := f2_val (R := R) hi
    rw [show (R.eF i).trace f2 = 1 from h, show (R.eF i).trace rb = 0 from h0] at e
    simp at e
  · exact h1

omit X in
theorem f2_ne {i : ℕ} (hi : i < R.n) (h0 : R.v i rb = 0) : R.v i f2 ≠ 1 := fun h => by
  have := rb_of_f2 hi h; rw [h0] at this; exact zero_ne_one this

omit X in
theorem f1_of_fst0 {i : ℕ} (hi : i < R.n) (hf : R.v i fst = 0) : R.v i f1 = 0 := by
  show (R.eF i).trace f1 = 0
  rw [f1_val hi, show (R.eF i).trace fst = 0 from hf, zero_mul]

omit X in
theorem f1_of_tags {i : ℕ} (hi : i < R.n) (h1 : R.v i ra = 0) (h2 : R.v i rx = 0) : R.v i f1 = 0 := by
  show (R.eF i).trace f1 = 0
  rw [f1_val hi, show (R.eF i).trace ra = 0 from h1, show (R.eF i).trace rx = 0 from h2]; ring

omit X in
/-- A row of a slot carrying `fst` is the slot's first row. -/
theorem in_head {i m : ℕ} (s : R.Slot i m) {x : ℕ} (h1 : i ≤ x) (h2 : x < i + m) (hf : R.v x fst = 1) : x = i := by
  by_contra hc
  have := s.fst1 (x - i) (by omega) (by omega)
  rw [show i + (x - i) = x by omega, hf] at this
  exact one_ne_zero this

omit X in
/-- A row of a slot of tag `c` has every other tag `0`. -/
theorem in_tag {i m : ℕ} (s : R.Slot i m) {c : ℕ} (hc : c ∈ roleCols ++ [mQ1, mQM]) (h1 : R.v i c = 1)
    {d : ℕ} (hd : d ∈ roleCols ++ [mQ1, mQM]) (hdc : d ≠ c) {x : ℕ} (hx1 : i ≤ x) (hx2 : x < i + m) :
    R.v x d = 0 := by
  have hcm : c ∈ roleCols ++ modeCols := by
    rcases List.mem_append.mp hc with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (by simp [modeCols] at h ⊢; tauto)
  have hs := s.same (x - i) (by omega) c hcm
  rw [show i + (x - i) = x by omega, h1] at hs
  exact (R.tag_onehot (by have := s.lt; omega) hc hs).2 d hd hdc

omit X in
/-- A role slot reads a handle or a witness (`mR mS mV mW`), not a `Q` mode. -/
theorem role_mode {i m : ℕ} (s : R.Slot i m) {r : ℕ} (hr : r ∈ roleCols) (h1 : R.v i r = 1) :
    R.v i mR = 1 ∨ R.v i mS = 1 ∨ R.v i mV = 1 ∨ R.v i mW = 1 := by
  have hi : i < R.n := by have := s.lt; omega
  obtain ⟨hL, h0⟩ := R.tag_onehot hi (c := r) (List.mem_append_left _ hr) h1
  have hq1 := h0 mQ1 (by simp) (by rintro rfl; revert hr; decide)
  have hqm := h0 mQM (by simp) (by rintro rfl; revert hr; decide)
  obtain ⟨c, hc, hc1⟩ := mode_some hi hL
  simp only [modeCols, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hc1
  · exact Or.inr (Or.inl hc1)
  · exact Or.inr (Or.inr (Or.inl hc1))
  · exact Or.inr (Or.inr (Or.inr hc1))
  · exfalso; rw [hc1] at hq1; exact one_ne_zero hq1
  · exfalso; rw [hc1] at hqm; exact one_ne_zero hqm

omit X in
/-- A factor slot is not read-only (`gCompat`). -/
theorem not_mR {i : ℕ} (hi : i < R.n)
    (hσ : (R.eF i).trace oMul * ((R.eF i).trace ra + (R.eF i).trace rb) +
      ((R.eF i).trace oDiv + (R.eF i).trace oMod) * ((R.eF i).trace rx + (R.eF i).trace rb) = 1) :
    R.v i mR ≠ 1 := by
  intro h1
  have g := R.G hi (mem_compat (a := ar (.mul (cv mR) (.add (.mul (cv oMul) (sumC [ra, rb]))
    (.mul (sumC [oDiv, oMod]) (sumC [rx, rb]))))) (by simp [gCompat]))
  simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at g
  rw [hσ, show (R.eF i).trace mR = 1 from h1, one_mul] at g
  exact one_ne_zero g

omit X in
theorem compat_mW0 {i : ℕ} (hi : i < R.n) {x o : ℕ} (hx : R.v i x = 1) (ho : R.v i o = 1)
    (hg : (ar (prod3 (cv x) (cv o) (cv mW)) : AG Fp) ∈ gCompat) : R.v i mW = 0 := by
  have g := R.G hi (mem_compat hg)
  simp only [AG.gate, ar, prod3, cv, CoeffExpr.eval] at g
  rw [show (R.eF i).trace x = 1 from hx, show (R.eF i).trace o = 1 from ho, one_mul, one_mul] at g
  exact g

omit X in
theorem compat_mW1 {i : ℕ} (hi : i < R.n) {x o : ℕ} (hx : R.v i x = 1) (ho : R.v i o = 1)
    (hg : (ar (prod3 (cv x) (cv o) (notE (cv mW))) : AG Fp) ∈ gCompat) : R.v i mW = 1 := by
  have g := R.G hi (mem_compat hg)
  simp only [AG.gate, ar, prod3, notE, cv, CoeffExpr.eval] at g
  rw [show (R.eF i).trace x = 1 from hx, show (R.eF i).trace o = 1 from ho, one_mul, one_mul] at g
  show (R.eF i).trace mW = 1
  linear_combination -g

/-! ### The 6-bit length counter -/

omit X in
/-- **The counter reads `≤ 62`** (`cn = Σ 2^k c_k`, booleans, `cA·cB = 0`). -/
theorem cn_small {i : ℕ} (hi : i < R.n) : ∃ n : ℕ, n ≤ 62 ∧ R.v i cn = (n : Fp) := by
  have hb : ∀ k < 6, (R.eF i).trace (cb0 + k) = 0 ∨ (R.eF i).trace (cb0 + k) = 1 := fun k hk =>
    R.boolc hi (Rows.mem_cap (by
      unfold gCap
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))
  have g := R.G hi (Rows.mem_cap (a := ar (.sub (cv cn) cnE)) (by simp [gCap]))
  simp only [AG.gate, ar, cnE, eval_bitSum, CoeffExpr.eval, cv] at g
  have hv : R.v i cn = ((∑ k ∈ Finset.range 6, 2 ^ k * b01 (R.eF i) (cb0 + k) : ℕ) : Fp) := by
    push_cast
    have e : ∑ k ∈ Finset.range 6, (2 : Fp) ^ k * ((b01 (R.eF i) (cb0 + k) : ℕ) : Fp) =
        ∑ k ∈ Finset.range 6, (2 : Fp) ^ k * (R.eF i).trace (cb0 + k) :=
      Finset.sum_congr rfl fun k hk => by rw [b01_cast (hb k (Finset.mem_range.mp hk))]
    rw [e]; exact sub_eq_zero.mp g
  refine ⟨_, ?_, hv⟩
  by_contra hcon
  have hl : ∀ k, b01 (R.eF i) (cb0 + k) ≤ 1 := fun k => b01_le _ _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reducePow] at hcon
  have l0 := hl 0; have l1 := hl 1; have l2 := hl 2; have l3 := hl 3; have l4 := hl 4; have l5 := hl 5
  have one : ∀ k < 6, (R.eF i).trace (cb0 + k) = 1 := by
    intro k hk
    have : b01 (R.eF i) (cb0 + k) = 1 := by interval_cases k <;> omega
    rw [← b01_cast (hb k hk), this]; simp
  have gA := R.G hi (Rows.mem_cap (a := ar (.sub (cv cA) (prod3 (cv cb0) (cv (cb0 + 1)) (cv (cb0 + 2)))))
    (by simp [gCap]))
  have gB := R.G hi (Rows.mem_cap (a := ar (.sub (cv cB) (prod3 (cv (cb0 + 3)) (cv (cb0 + 4)) (cv (cb0 + 5)))))
    (by simp [gCap]))
  have gAB := R.G hi (Rows.mem_cap (a := ar (.mul (cv cA) (cv cB))) (by simp [gCap]))
  simp only [AG.gate, ar, prod3, CoeffExpr.eval, cv] at gA gB gAB
  have t0 := one 0 (by norm_num)
  rw [Nat.add_zero] at t0
  rw [t0, one 1 (by norm_num), one 2 (by norm_num)] at gA
  rw [one 3 (by norm_num), one 4 (by norm_num), one 5 (by norm_num)] at gB
  have eA : (R.eF i).trace cA = 1 := by linear_combination gA
  have eB : (R.eF i).trace cB = 1 := by linear_combination gB
  rw [eA, eB, one_mul] at gAB
  exact one_ne_zero gAB

omit X in
/-- **A Horner value slot (`mS mV mW`) has at most 62 rows** (the counter starts at `1` and steps by `1`). -/
theorem len_le {i m : ℕ} (s : R.Slot i m) {md : ℕ} (hmd : md ∈ [mS, mV, mW]) (h1 : R.v i md = 1) : m ≤ 62 := by
  have hmc : md ∈ modeCols := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmd
    rcases hmd with rfl | rfl | rfl <;> simp [modeCols]
  have hz : ∀ j < m, (hzV : CoeffExpr Fp).eval (R.eF (i + j)) = 1 := by
    intro j hj
    have hij : i + j < R.n := by have := s.lt; omega
    have hs : R.v (i + j) md = 1 := (s.same j hj md (List.mem_append_right _ hmc)).trans h1
    have h0 := R.mode_onehot hij (s.lane j hj) hmc hs
    simp only [hzV, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    simp only [Rows.v] at hs h0
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmd
    rcases hmd with rfl | rfl | rfl
    · rw [hs, h0 mV (by simp [modeCols]) (by decide), h0 mW (by simp [modeCols]) (by decide)]; ring
    · rw [hs, h0 mS (by simp [modeCols]) (by decide), h0 mW (by simp [modeCols]) (by decide)]; ring
    · rw [hs, h0 mS (by simp [modeCols]) (by decide), h0 mV (by simp [modeCols]) (by decide)]; ring
  have hc : ∀ j < m, R.v (i + j) cn = ((j + 1 : ℕ) : Fp) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hi : i < R.n := by have := s.lt; omega
      have g := R.G hi (Rows.mem_cap (a := ar (prod3 (cv fst) hzV (.sub (cv cn) (.const 1)))) (by simp [gCap]))
      have hz0 := hz 0 hj
      simp only [Nat.add_zero] at hz0 ⊢
      simp only [AG.gate, ar, prod3, CoeffExpr.eval, cv, hz0] at g
      rw [show (R.eF i).trace fst = 1 from s.fst0] at g
      show (R.eF i).trace cn = _
      push_cast; linear_combination g
    | succ j ih =>
      intro hj
      have hr : i + j < R.n := by have := s.lt; omega
      have hn : i + j + 1 < R.n := by have := s.lt; omega
      have g := R.G hr (Rows.mem_cap (a := ar (prod3 hzV (notE (cv eos)) (.sub (.sub (nv cn) (cv cn)) (.const 1))))
        (by simp [gCap]))
      simp only [AG.gate, ar, prod3, notE, CoeffExpr.eval, cv, nv, hz j (by omega), R.nextF _ hn] at g
      rw [show (R.eF (i + j)).trace eos = 0 from s.eos0 j hj, show (R.eF (i + j)).trace cn = _ from ih (by omega),
        show i + j + 1 = i + (j + 1) by omega] at g
      show (R.eF (i + (j + 1))).trace cn = _
      push_cast at g ⊢; linear_combination g
  by_contra hcon
  have hr : i + 62 < R.n := by have := s.lt; omega
  obtain ⟨n, hn, hv⟩ := cn_small (R := R) hr
  have e := (hc 62 (by omega)).symm.trans hv
  have := castFp_inj (x := 62 + 1) (y := n) (by norm_num) (by omega) e
  omega

/-- **The `mQM` bound**: a 25-bit `Q` lane is `< 2^25` (`mQM·b_t = 0`, `t ≥ 25`). -/
theorem qm_lt {i m : ℕ} (s : R.Slot i m) (h1 : R.v i mQM = 1) : ∀ x ∈ lanes (laneL X.al) i m, x < 2 ^ 25 := by
  refine lanes_bound _ fun j hj => ?_
  have hr : i + j < R.n := by have := s.lt; omega
  have hq : R.v (i + j) mQM = 1 := (s.same j hj mQM (by simp [modeCols])).trans h1
  have hz : ∀ t < 7, (cl X.al (i + j) (bt0 + (25 + t))).val = 0 := by
    intro t ht
    have g := R.G hr (mem_bits (a := ar (.mul (cv mQM) (cv (bt0 + 25 + t))))
      (List.mem_append_right _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)))
    simp only [AG.gate, ar, cv, CoeffExpr.eval] at g
    rw [show (R.eF (i + j)).trace mQM = 1 from hq, one_mul] at g
    rw [X.hal.val _ hr, ← Nat.add_assoc]
    show ((R.eF (i + j)).trace (bt0 + 25 + t)).val = 0
    rw [g]; simp
  have e : laneL X.al (i + j) = ∑ t ∈ Finset.range 25, 2 ^ t * (cl X.al (i + j) (bt0 + t)).val := by
    unfold laneL
    rw [show (32 : ℕ) = 25 + 7 from rfl, Finset.sum_range_add,
      Finset.sum_eq_zero (s := Finset.range 7) (fun t ht => by rw [hz t (Finset.mem_range.mp ht), mul_zero]),
      add_zero]
  rw [e]
  have := sum_bits_lt (fun t => if t < 25 then (cl X.al (i + j) (bt0 + t)).val else 0)
    (fun t => by split_ifs with h; exact bitv_le X.hal hr (by omega); omega) 25
  rwa [show (∑ t ∈ Finset.range 25, 2 ^ t * (if t < 25 then (cl X.al (i + j) (bt0 + t)).val else 0)) =
    ∑ t ∈ Finset.range 25, 2 ^ t * (cl X.al (i + j) (bt0 + t)).val from
    Finset.sum_congr rfl fun t ht => by rw [if_pos (Finset.mem_range.mp ht)]] at this

/-! ## 2. The latches `RL`, `RO` (carried from the `f1` row to the `f2` row) -/

omit X in
/-- **The mirror latch**: from an `f1` row along lane rows without `f1`, `RL = Lf`, `RO = HO` of the `f1` row. -/
theorem latch_poly (al : List ALRow) (t : List (CellRowB0 Nock.Atoms.p)) {i0 : ℕ} (h0 : onb al i0 f1 = true) :
    ∀ d, (∀ s, 1 ≤ s → s ≤ d → onb al (i0 + s) f1 = false ∧ onb al (i0 + s) sL = true) →
      RLp al t (i0 + d) = Lf al t i0 ∧ ROp al (i0 + d) = HOp al i0
  | 0, _ => by
    cases i0 with
    | zero => simp [RLp, ROp, h0]
    | succ i0 => simp [RLp, ROp, h0]
  | d + 1, hs => by
    obtain ⟨e1, e2⟩ := latch_poly al t h0 d (fun s h1 h2 => hs s h1 (by omega))
    obtain ⟨a1, a2⟩ := hs (d + 1) (by omega) le_rfl
    rw [show i0 + (d + 1) = (i0 + d) + 1 by omega] at a1 a2 ⊢
    simp [RLp, ROp, a1, a2, e1, e2]

omit X in
/-- **The chip latch**: `RL`, `RO` are constant along lane rows (`qz ((1 − isLT)·sL′) (RL′) RL`). -/
theorem RL_carry {i0 : ℕ} : ∀ d, i0 + d < R.n → (∀ t, 1 ≤ t → t ≤ d → R.v (i0 + t) sL = 1) →
    (QE.var RL).ev δ (R.eK (i0 + d)) (R.eF (i0 + d)) = (QE.var RL).ev δ (R.eK i0) (R.eF i0) ∧
    (QE.var RO).ev δ (R.eK (i0 + d)) (R.eF (i0 + d)) = (QE.var RO).ev δ (R.eK i0) (R.eF i0)
  | 0, _, _ => ⟨rfl, rfl⟩
  | d + 1, hn, hl => by
    obtain ⟨ih1, ih2⟩ := RL_carry d (by omega) (fun t h1 h2 => hl t h1 (by omega))
    have hr : i0 + d < R.n := by omega
    have hn' : i0 + d + 1 < R.n := by omega
    have hL := hl (d + 1) (by omega) le_rfl
    have hσ : ((.mul (notE (cv isLT)) (nv sL)) : CoeffExpr Fp).eval (R.eF (i0 + d)) = 1 := by
      simp only [CoeffExpr.eval, nv, notE, cv, R.nextF _ hn', R.notLast _ hn']
      rw [show i0 + d + 1 = i0 + (d + 1) by omega]; simp only [Rows.v] at hL; rw [hL]; ring
    have g1 := R.QZ hr (mem_identQ (e := qz (.mul (notE (cv isLT)) (nv sL)) (QE.next RL) (QE.var RL)) (by simp [identQ])) hσ
    have g2 := R.QZ hr (mem_identQ (e := qz (.mul (notE (cv isLT)) (nv sL)) (QE.next RO) (QE.var RO)) (by simp [identQ])) hσ
    rw [ev_next, R.nextK _ hn' RL, R.nextK _ hn' (RL + 1)] at g1
    rw [ev_next, R.nextK _ hn' RO, R.nextK _ hn' (RO + 1)] at g2
    simp only [ev_var] at ih1 ih2 g1 g2 ⊢
    rw [show i0 + (d + 1) = i0 + d + 1 by omega]
    exact ⟨g1.trans ih1, g2.trans ih2⟩

/-- **The latch** from an `f1` slot `s0` (mode `mS mV mW`) to the next slot's first row (no `f1` there):
the mirror's `RL`/`RO` there are `Lf`/`HO` of the `f1` row, and they evaluate to the chip's `RL`/`RO`. -/
theorem latch {i0 m0 m1 : ℕ} (s0 : R.Slot i0 m0) (s1 : R.Slot (i0 + m0) m1)
    (hf1 : R.v i0 f1 = 1) (hmd : R.v i0 mS = 1 ∨ R.v i0 mV = 1 ∨ R.v i0 mW = 1)
    (hf1' : R.v (i0 + m0) f1 = 0) :
    RLp X.al X.t (i0 + m0) = Lf X.al X.t i0 ∧ ROp X.al (i0 + m0) = HOp X.al i0 ∧
    aeval R.y (RLp X.al X.t (i0 + m0)) = (QE.var RL).ev δ (R.eK (i0 + m0)) (R.eF (i0 + m0)) ∧
    aeval R.y (ROp X.al (i0 + m0)) = (QE.var RO).ev δ (R.eK (i0 + m0)) (R.eF (i0 + m0)) := by
  have hi0 : i0 < R.n := by have := s0.lt; omega
  have hn1 : i0 + m0 < R.n := by have := s1.lt; have := s1.pos; omega
  have hlane : ∀ t, 1 ≤ t → t ≤ m0 → R.v (i0 + t) sL = 1 := fun t h1 h2 => by
    rcases Nat.lt_or_ge t m0 with h | h
    · exact s0.lane t h
    · have := s1.lane 0 (by have := s1.pos; omega)
      rw [Nat.add_zero] at this; rw [show t = m0 by omega]; exact this
  have hf0 : ∀ t, 1 ≤ t → t ≤ m0 → R.v (i0 + t) f1 = 0 := fun t h1 h2 => by
    rcases Nat.lt_or_ge t m0 with h | h
    · exact f1_of_fst0 (by omega) (s0.fst1 t h1 h)
    · rw [show t = m0 by omega]; exact hf1'
  have hp := latch_poly X.al X.t (onb_true X.hal hi0 hf1) m0 (fun t h1 h2 =>
    ⟨onb_zero X.hal (by omega) (hf0 t h1 h2), onb_true X.hal (by omega) (hlane t h1 h2)⟩)
  obtain ⟨c1, c2⟩ := RL_carry (R := R) m0 hn1 hlane
  have g1 := R.QZ hi0 (mem_identQ (e := qz (cv f1) (QE.var RL) (QE.var L)) (by simp [identQ]))
    (by simp only [CoeffExpr.eval, cv]; exact hf1)
  have g2 := R.QZ hi0 (mem_identQ (e := qz (cv f1) (QE.var RO) (QE.var HO)) (by simp [identQ]))
    (by simp only [CoeffExpr.eval, cv]; exact hf1)
  have hLf := (X.Lp_ev s0).2 (Or.inr hmd)
  have hHO : aeval R.y (HOp X.al i0) = (QE.var HO).ev δ (R.eK i0) (R.eF i0) := by
    rcases hmd with h | h | h
    · exact X.HOp_ev s0 (md := mS) (by simp) h
    · exact X.HOp_ev s0 (md := mV) (by simp) h
    · exact X.HOp_ev s0 (md := mW) (by simp) h
  refine ⟨hp.1, hp.2, ?_, ?_⟩
  · rw [hp.1, hLf, c1, g1]
  · rw [hp.2, hHO, c2, g2]

/-- **The `f2` row's `D1`** (`qContr`: `D1 = RL·L + (y − B)·RO·HO`), mirror and chip. -/
theorem D1_f2 {i m : ℕ} (s : R.Slot i m) (hf2 : R.v i f2 = 1)
    (hmd : R.v i mS = 1 ∨ R.v i mV = 1 ∨ R.v i mW = 1)
    (hRL : aeval R.y (RLp X.al X.t i) = (QE.var RL).ev δ (R.eK i) (R.eF i))
    (hRO : aeval R.y (ROp X.al i) = (QE.var RO).ev δ (R.eK i) (R.eF i)) :
    D1p X.al X.t i = RLp X.al X.t i * Lf X.al X.t i + BX * (ROp X.al i * HOp X.al i) ∧
      aeval R.y (D1p X.al X.t i) = (QE.var D1).ev δ (R.eK i) (R.eF i) := by
  have hi : i < R.n := by have := s.lt; omega
  have hL := s.lane 0 (by have := s.pos; omega)
  rw [Nat.add_zero] at hL
  have e : D1p X.al X.t i = RLp X.al X.t i * Lf X.al X.t i + BX * (ROp X.al i * HOp X.al i) := by
    simp [D1p, onb_zero X.hal hi (R.lane_sH hi hL), onb_true X.hal hi s.fst0, onb_true X.hal hi hf2]
  refine ⟨e, ?_⟩
  have g := R.QZ hi (mem_identQ (e := qz (cv f2) (QE.var D1)
    (QE.add (QE.mul δ (QE.var RL) (QE.var L)) (QE.mul δ yMB (QE.mul δ (QE.var RO) (QE.var HO)))))
    (by simp [identQ])) (by simp only [CoeffExpr.eval, cv]; exact hf2)
  rw [ev_add, ev_mul, ev_mul, ev_mul, yMB_ev hi] at g
  have hLf := (X.Lp_ev s).2 (Or.inr hmd)
  have hHO : aeval R.y (HOp X.al i) = (QE.var HO).ev δ (R.eK i) (R.eF i) := by
    rcases hmd with h | h | h
    · exact X.HOp_ev s (md := mS) (by simp) h
    · exact X.HOp_ev s (md := mV) (by simp) h
    · exact X.HOp_ev s (md := mW) (by simp) h
  rw [e, g, map_add, map_mul, map_mul, map_mul, aeval_BX, hRL, hLf, hRO, hHO]

/-- `D2` at a slot's first row is `cf2·L` (every first row, `f2` or not). -/
theorem D2_head {i m : ℕ} (s : R.Slot i m) : D2p X.al X.t i = Polynomial.C (R.v i cf2) * Lp X.al X.t i := by
  have hi : i < R.n := by have := s.lt; omega
  have hL := s.lane 0 (by have := s.pos; omega)
  rw [Nat.add_zero] at hL
  simp [D2p, onb_zero X.hal hi (R.lane_sH hi hL), onb_true X.hal hi s.fst0, X.hal.val i hi]

/-! ## 3. The view link and the halves -/

/-- **The view link** (`L = H` on a factor slot: by `qVal` on `mS mW`, by the link polynomial on `mV`). -/
theorem factor_link {h k : ℕ} (bk : R.Block h k) (hz : ∀ P ∈ callPolys X.al X.t h, P = 0) {i m : ℕ}
    (s : R.Slot i m) (h1 : h + 1 ≤ i) (h2 : i ≤ h + k) (hmd : R.v i mS = 1 ∨ R.v i mV = 1 ∨ R.v i mW = 1) :
    Lp X.al X.t i = Hp X.al i ∧ Lf X.al X.t i = Hp X.al i := by
  have hi : i < R.n := by have := s.lt; omega
  have hL := s.lane 0 (by have := s.pos; omega)
  rw [Nat.add_zero] at hL
  have md := X.Lp_mode hi hL
  rcases hmd with h1' | h1' | h1'
  · exact md.2.1 (Or.inl h1')
  · obtain ⟨e, e'⟩ := md.1 (Or.inr h1')
    obtain ⟨o1, o2, o3⟩ := X.onbs bk
    have hmem : linkP X.al X.t i ∈ callPolys X.al X.t h := by
      unfold callPolys
      refine List.mem_append_right _ (List.mem_map.mpr ⟨i, ?_, rfl⟩)
      rw [blockRows_eq X.al k _ h o1 o2 o3]
      exact List.mem_map.mpr ⟨i - h - 1, List.mem_range.mpr (by omega), by omega⟩
    have h0 := hz _ hmem
    have el : linkP X.al X.t i = Hp X.al i - atomPoly X.t (cl X.al i sv).val := by
      simp [linkP, onb_true X.hal hi s.fst0, onb_true X.hal hi h1']
    rw [el, X.hal.val i hi sv, sub_eq_zero] at h0
    exact ⟨e.trans h0.symm, e'.trans h0.symm⟩
  · exact md.2.1 (Or.inr h1')

omit X in
/-- **The halves**: `E + 2^16·O = A` on the lanes of a slot (`ℓ = e + 2^16·o` per row). -/
theorem halves (al : List ALRow) (i m : ℕ) :
    limbPolyQ (q := Nock.Atoms.p) (lanes (laneE al) i m) +
      Polynomial.C (2 ^ 16 : Fp) * limbPolyQ (q := Nock.Atoms.p) (lanes (laneO al) i m) =
      limbPolyQ (q := Nock.Atoms.p) (lanes (laneL al) i m) := by
  have e : laneL al = fun j => laneE al j + 2 ^ 16 * laneO al j := by
    funext j; exact laneL_split al j
  rw [e, limbPolyQ_lanes_add]
  norm_num

/-- **A factor's link**, `Nock.Atoms.ArithSZ`'s form: `limbPoly E + 2^16·limbPoly O = limbPoly l` for the factor's limb list `l`. -/
theorem factor_halves {h k : ℕ} (bk : R.Block h k) (hz : ∀ P ∈ callPolys X.al X.t h, P = 0) {i m : ℕ}
    (s : R.Slot i m) (h1 : h + 1 ≤ i) (h2 : i ≤ h + k) (hmd : R.v i mS = 1 ∨ R.v i mV = 1 ∨ R.v i mW = 1)
    {l : List ℕ} (hl : Lp X.al X.t i = limbPolyQ l) :
    limbPoly (lanes (laneE X.al) i m) + Polynomial.C (2 ^ 16 : Fp) * limbPoly (lanes (laneO X.al) i m) =
      limbPoly l := by
  have := halves X.al i m
  rw [← X.Hp_poly s, ← (X.factor_link bk hz s h1 h2 hmd).1, hl] at this
  exact this

/-! ## 4. Block shapes and the 7-slot block sum -/

omit X in
/-- **The `mul` shape** `ra rb rc mQM` (the terminal `mQM` is followed by a non-lane row on `mul`). -/
theorem shape_mul {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hop : R.v h oMul = 1)
    (hσ : ∀ e : Env Fp, (∀ c ∈ Rows.constCols, e.trace c = R.v h c) →
      (sumC [oAdd, oSub, oLt, oMul] : CoeffExpr Fp).eval e = 1 ∧ (sumC [oAdd, oSub, oMul] : CoeffExpr Fp).eval e = 1 ∧
      (cv oMul : CoeffExpr Fp).eval e = 1) :
    ∃ ma mb mc mq, R.Slot (h + 1) ma ∧ R.Slot (h + 1 + ma) mb ∧ R.Slot (h + 1 + ma + mb) mc ∧
      R.Slot (h + 1 + ma + mb + mc) mq ∧ R.v (h + 1) ra = 1 ∧ R.v (h + 1 + ma) rb = 1 ∧
      R.v (h + 1 + ma + mb) rc = 1 ∧ R.v (h + 1 + ma + mb + mc) mQM = 1 ∧
      R.Block h (ma + mb + mc + mq) ∧ ∀ j ≤ ma + mb + mc + mq, ∀ c ∈ Rows.constCols, R.v (h + j) c = R.v h c := by
  obtain ⟨hn1, hra, hL1, hf1⟩ := R.after_hdr hh hH
  obtain ⟨ma, sa⟩ := R.slot_of hn1 hL1 hf1
  obtain ⟨l1, hrb, mb, sb⟩ := step (a := 0) hh rfl (fun j h1 h2 => by omega) sa (r := ra) (by simp [roleCols]) hra
    (σ := sumC [oAdd, oSub, oLt, oMul]) (t := rb) (by simp [gSeq]) (fun e he => (hσ e he).1) (by simp [roleCols])
  obtain ⟨l2, hrc, mc, sc⟩ := step (a := ma) hh rfl (fun j h1 h2 => l1 j h1 (by omega)) sb (r := rb)
    (by simp [roleCols]) hrb (σ := sumC [oAdd, oSub, oMul]) (t := rc) (by simp [gSeq]) (fun e he => (hσ e he).2.1)
    (by simp [roleCols])
  obtain ⟨l3, hq, mq, sq⟩ := step (a := ma + mb) hh (by omega) (fun j h1 h2 => l2 j h1 h2) sc (r := rc)
    (by simp [roleCols]) hrc (σ := cv oMul) (t := mQM) (by simp [gSeq]) (fun e he => (hσ e he).2.2) (by simp)
  have hl : ∀ j, 1 ≤ j → j ≤ ma + mb + mc + mq → R.v (h + j) sL = 1 := by
    intro j h1 h2
    by_cases hj : j ≤ ma + mb + mc
    · exact l3 j h1 hj
    · have := sq.lane (j - 1 - (ma + mb + mc)) (by omega)
      rwa [show h + 1 + ma + mb + mc + (j - 1 - (ma + mb + mc)) = h + j by omega] at this
  have hcst := R.const_run (h := h) (k := ma + mb + mc + mq) (by have := sq.lt; omega) hl
  obtain ⟨hk, he, hL, hcq⟩ := Rows.Slot.lastRow R sq
  have hn := R.not_last hk (Or.inr hL)
  have g := R.G hk (Rows.mem_seq (a := ar (.mul (prod3 (cv eos) (cv mQM) (cv oMul)) (nv sL))) (by simp [gSeq]))
  have hq' := hcq mQM (by simp [modeCols])
  have hmul : R.v (h + 1 + ma + mb + mc + mq - 1) oMul = 1 := by
    rw [show h + 1 + ma + mb + mc + mq - 1 = h + (ma + mb + mc + mq) by have := sq.pos; omega,
      hcst _ le_rfl oMul (by simp [Rows.constCols, opCols])]
    exact hop
  simp only [AG.gate, ar, prod3, cv, nv, CoeffExpr.eval, R.nextF _ hn] at g
  rw [show (R.eF (h + 1 + ma + mb + mc + mq - 1)).trace eos = 1 from he,
    show (R.eF (h + 1 + ma + mb + mc + mq - 1)).trace mQM = 1 from hq'.trans hq,
    show (R.eF (h + 1 + ma + mb + mc + mq - 1)).trace oMul = 1 from hmul, one_mul, one_mul, one_mul] at g
  have e1 : h + 1 + ma + mb + mc + mq - 1 + 1 = h + (ma + mb + mc + mq) + 1 := by have := sq.pos; omega
  rw [e1] at g hn
  exact ⟨ma, mb, mc, mq, sa, sb, sc, sq, hra, hrb, hrc, hq, ⟨hn, hH, hl, g⟩, hcst⟩

omit X in
/-- **The 7-slot div/mod shape** `ra rx rb ry rs mQM mQ1` (for div/mod). -/
theorem shape7 {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1)
    (hσ : ∀ e : Env Fp, (∀ c ∈ Rows.constCols, e.trace c = R.v h c) →
      (sumC [oDiv, oMod] : CoeffExpr Fp).eval e = 1) :
    ∃ m1 m2 m3 m4 m5 m6 m7, R.Slot (h + 1) m1 ∧ R.Slot (h + 1 + m1) m2 ∧ R.Slot (h + 1 + m1 + m2) m3 ∧
      R.Slot (h + 1 + m1 + m2 + m3) m4 ∧ R.Slot (h + 1 + m1 + m2 + m3 + m4) m5 ∧
      R.Slot (h + 1 + m1 + m2 + m3 + m4 + m5) m6 ∧ R.Slot (h + 1 + m1 + m2 + m3 + m4 + m5 + m6) m7 ∧
      R.v (h + 1) ra = 1 ∧ R.v (h + 1 + m1) rx = 1 ∧ R.v (h + 1 + m1 + m2) rb = 1 ∧
      R.v (h + 1 + m1 + m2 + m3) ry = 1 ∧ R.v (h + 1 + m1 + m2 + m3 + m4) rs = 1 ∧
      R.v (h + 1 + m1 + m2 + m3 + m4 + m5) mQM = 1 ∧ R.v (h + 1 + m1 + m2 + m3 + m4 + m5 + m6) mQ1 = 1 ∧
      R.Block h (m1 + m2 + m3 + m4 + m5 + m6 + m7) ∧
      ∀ j ≤ m1 + m2 + m3 + m4 + m5 + m6 + m7, ∀ c ∈ Rows.constCols, R.v (h + j) c = R.v h c := by
  have one : ∀ e : Env Fp, (∀ c ∈ Rows.constCols, e.trace c = R.v h c) →
      (CoeffExpr.const 1 : CoeffExpr Fp).eval e = 1 := fun e _ => rfl
  obtain ⟨hn1, hra, hL1, hf1⟩ := R.after_hdr hh hH
  obtain ⟨m1, s1⟩ := R.slot_of hn1 hL1 hf1
  obtain ⟨l1, t2, m2, s2⟩ := step (a := 0) hh rfl (fun j h1 h2 => by omega) s1 (r := ra) (by simp [roleCols]) hra
    (σ := sumC [oDiv, oMod]) (t := rx) (by simp [gSeq]) hσ (by simp [roleCols])
  obtain ⟨l2, t3, m3, s3⟩ := step (a := m1) hh rfl (fun j h1 h2 => l1 j h1 (by omega)) s2 (r := rx)
    (by simp [roleCols]) t2 (σ := .const 1) (t := rb) (by simp [gSeq]) one (by simp [roleCols])
  obtain ⟨l3, t4, m4, s4⟩ := step (a := m1 + m2) hh (by omega) (fun j h1 h2 => l2 j h1 h2) s3 (r := rb)
    (by simp [roleCols]) t3 (σ := sumC [oDiv, oMod]) (t := ry) (by simp [gSeq]) hσ (by simp [roleCols])
  obtain ⟨l4, t5, m5, s5⟩ := step (a := m1 + m2 + m3) hh (by omega) (fun j h1 h2 => l3 j h1 h2) s4 (r := ry)
    (by simp [roleCols]) t4 (σ := .const 1) (t := rs) (by simp [gSeq]) one (by simp [roleCols])
  obtain ⟨l5, t6, m6, s6⟩ := step (a := m1 + m2 + m3 + m4) hh (by omega) (fun j h1 h2 => l4 j h1 h2) s5 (r := rs)
    (by simp [roleCols]) t5 (σ := .const 1) (t := mQM) (by simp [gSeq]) one (by simp)
  obtain ⟨l6, t7, m7, s7⟩ := step (a := m1 + m2 + m3 + m4 + m5) hh (by omega) (fun j h1 h2 => l5 j h1 h2) s6
    (r := mQM) (by simp [modeCols]) t6 (σ := sumC [oDiv, oMod]) (t := mQ1) (by simp [gSeq]) hσ (by simp)
  have hl : ∀ j, 1 ≤ j → j ≤ m1 + m2 + m3 + m4 + m5 + m6 + m7 → R.v (h + j) sL = 1 := by
    intro j h1 h2
    by_cases hj : j ≤ m1 + m2 + m3 + m4 + m5 + m6
    · exact l6 j h1 hj
    · have := s7.lane (j - 1 - (m1 + m2 + m3 + m4 + m5 + m6)) (by omega)
      rwa [show h + 1 + m1 + m2 + m3 + m4 + m5 + m6 + (j - 1 - (m1 + m2 + m3 + m4 + m5 + m6)) = h + j by omega]
        at this
  have hcst := R.const_run (h := h) (k := m1 + m2 + m3 + m4 + m5 + m6 + m7) (by have := s7.lt; omega) hl
  obtain ⟨hk, he, hL, hcq⟩ := Rows.Slot.lastRow R s7
  have hn := R.not_last hk (Or.inr hL)
  have g := R.G hk (Rows.mem_seq (a := ar (prod3 (cv eos) (cv mQ1) (nv sL))) (by simp [gSeq]))
  have hq' := hcq mQ1 (by simp [modeCols])
  simp only [AG.gate, ar, prod3, cv, nv, CoeffExpr.eval, R.nextF _ hn] at g
  rw [show (R.eF (h + 1 + m1 + m2 + m3 + m4 + m5 + m6 + m7 - 1)).trace eos = 1 from he,
    show (R.eF (h + 1 + m1 + m2 + m3 + m4 + m5 + m6 + m7 - 1)).trace mQ1 = 1 from hq'.trans t7,
    one_mul, one_mul] at g
  have e1 : h + 1 + m1 + m2 + m3 + m4 + m5 + m6 + m7 - 1 + 1 = h + (m1 + m2 + m3 + m4 + m5 + m6 + m7) + 1 := by
    have := s7.pos; omega
  rw [e1] at g hn
  exact ⟨m1, m2, m3, m4, m5, m6, m7, s1, s2, s3, s4, s5, s6, s7, hra, t2, t3, t4, t5, t6, t7, ⟨hn, hH, hl, g⟩, hcst⟩

/-- **The block sum of a 7-slot block**: `D(hdr) + Σ D(slot heads) = 0` from the block polynomial. -/
theorem D_seven (D : ℕ → (ZMod Nock.Atoms.p)[X]) {h m1 m2 m3 m4 m5 m6 m7 : ℕ}
    (s1 : R.Slot (h + 1) m1) (s2 : R.Slot (h + 1 + m1) m2) (s3 : R.Slot (h + 1 + m1 + m2) m3)
    (s4 : R.Slot (h + 1 + m1 + m2 + m3) m4) (s5 : R.Slot (h + 1 + m1 + m2 + m3 + m4) m5)
    (s6 : R.Slot (h + 1 + m1 + m2 + m3 + m4 + m5) m6) (s7 : R.Slot (h + 1 + m1 + m2 + m3 + m4 + m5 + m6) m7)
    (bk : R.Block h (m1 + m2 + m3 + m4 + m5 + m6 + m7)) (h0 : blockSum X.al D X.al.length h = 0)
    (hss : ∀ {i m : ℕ}, R.Slot i m → ∀ i' : ℕ, i' = i → ∑ j ∈ Finset.range m, D (i' + j) = D i) :
    D h + (D (h + 1) + D (h + 1 + m1) + D (h + 1 + m1 + m2) + D (h + 1 + m1 + m2 + m3) +
      D (h + 1 + m1 + m2 + m3 + m4) + D (h + 1 + m1 + m2 + m3 + m4 + m5) +
      D (h + 1 + m1 + m2 + m3 + m4 + m5 + m6)) = 0 := by
  obtain ⟨o1, o2, o3⟩ := X.onbs bk
  rw [blockSum_eq X.al _ _ _ h o1 o2 o3, sum_head, sum_shift _ _ (m1 + m2 + m3 + m4 + m5 + m6) m7,
    sum_shift _ _ (m1 + m2 + m3 + m4 + m5) m6, sum_shift _ _ (m1 + m2 + m3 + m4) m5,
    sum_shift _ _ (m1 + m2 + m3) m4, sum_shift _ _ (m1 + m2) m3, sum_shift _ _ m1 m2,
    hss s1 (h + 1) rfl, hss s2 (h + 1 + m1) rfl, hss s3 (h + 1 + (m1 + m2)) (by omega),
    hss s4 (h + 1 + (m1 + m2 + m3)) (by omega), hss s5 (h + 1 + (m1 + m2 + m3 + m4)) (by omega),
    hss s6 (h + 1 + (m1 + m2 + m3 + m4 + m5)) (by omega),
    hss s7 (h + 1 + (m1 + m2 + m3 + m4 + m5 + m6)) (by omega)] at h0
  exact h0

/-! ## 5. `mul`, `div`, `mod` -/

/-- **`mul_sound`**: an accepted `mul` call block (hdr row `h`, the gates of every row, the served reads, and the
conclusion of `outside_arithSZ` for this call) computes `primSem mul` on the decoded handles. -/
theorem mul_sound {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hop : R.v h oMul = 1)
    (hout : (∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0) → ∀ P ∈ callPolys X.al X.t h, P = 0) :
    ∃ na nb nc, HDen X.r (R.v h kA) (R.v h vA) na ∧ HDen X.r (R.v h kB) (R.v h vB) nb ∧
      HDen X.r (R.v h kE) (R.v h vE) nc ∧ Nock.Jet.Prim.primSem .mul na nb = some nc := by
  have ho : oMul ∈ opCols := by simp [opCols]
  have V := fun e he => op_vals hh hH ho hop e he
  obtain ⟨ma, mb, mc, mq, sa, sb, sc, sq, ha1, hb1, hc1, hq1, bk, hcst⟩ :=
    shape_mul (R := R) hh hH hop (fun e he => by
      have v := V e he
      simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, v oAdd (by simp [opCols]), v oSub (by simp [opCols]), v oLt (by simp [opCols]),
        v oMul (by simp [opCols])]
      simp [oAdd, oSub, oLt, oMul])
  have bl := bk.lt
  have := sa.pos; have := sb.pos; have := sc.pos; have := sq.pos
  have Cs := fun i (h1 : h ≤ i) (h2 : i ≤ h + (ma + mb + mc + mq)) => cst_at hcst h1 h2
  have ia : h + 1 < R.n := by omega
  have ib : h + 1 + ma < R.n := by omega
  have ic : h + 1 + ma + mb < R.n := by omega
  have iq : h + 1 + ma + mb + mc < R.n := by omega
  have Va := V _ (Cs (h + 1) (by omega) (by omega))
  have Vb := V _ (Cs (h + 1 + ma) (by omega) (by omega))
  have Vc := V _ (Cs (h + 1 + ma + mb) (by omega) (by omega))
  have Ta := (R.tag_onehot ia (c := ra) (by simp [roleCols]) ha1).2
  have Tb := (R.tag_onehot ib (c := rb) (by simp [roleCols]) hb1).2
  have Tc := (R.tag_onehot ic (c := rc) (by simp [roleCols]) hc1).2
  have Tq := (R.tag_onehot iq (c := mQM) (by simp) hq1).2
  have a_rb : (R.eF (h + 1)).trace rb = 0 := Ta rb (by simp [roleCols]) (by decide)
  have a_rx : (R.eF (h + 1)).trace rx = 0 := Ta rx (by simp [roleCols]) (by decide)
  have b_ra : (R.eF (h + 1 + ma)).trace ra = 0 := Tb ra (by simp [roleCols]) (by decide)
  have b_rx : (R.eF (h + 1 + ma)).trace rx = 0 := Tb rx (by simp [roleCols]) (by decide)
  -- the factor modes (`mS` / `mV`: not read-only, not a witness)
  have hma : R.v (h + 1) mS = 1 ∨ R.v (h + 1) mV = 1 := by
    have := operand_mode sa (Or.inl rfl) ha1
    have nR := not_mR (R := R) ia (by
      rw [Va oMul (by simp [opCols]), Va oDiv (by simp [opCols]), Va oMod (by simp [opCols]),
        show (R.eF (h + 1)).trace ra = 1 from ha1, a_rb, a_rx]
      simp [oMul, oDiv, oMod])
    rcases this with h' | h' | h'
    · exact absurd h' nR
    · exact Or.inl h'
    · exact Or.inr h'
  have hmb : R.v (h + 1 + ma) mS = 1 ∨ R.v (h + 1 + ma) mV = 1 := by
    have := operand_mode sb (Or.inr (Or.inl rfl)) hb1
    have nR := not_mR (R := R) ib (by
      rw [Vb oMul (by simp [opCols]), Vb oDiv (by simp [opCols]), Vb oMod (by simp [opCols]),
        show (R.eF (h + 1 + ma)).trace rb = 1 from hb1, b_ra, b_rx]
      simp [oMul, oDiv, oMod])
    rcases this with h' | h' | h'
    · exact absurd h' nR
    · exact Or.inl h'
    · exact Or.inr h'
  -- the latch from `ra` (`f1`) to `rb` (`f2`)
  have fa : R.v (h + 1) f1 = 1 := by
    show (R.eF (h + 1)).trace f1 = 1
    rw [f1_val ia, show (R.eF (h + 1)).trace fst = 1 from sa.fst0, show (R.eF (h + 1)).trace ra = 1 from ha1,
      a_rx, Va oMul (by simp [opCols])]
    simp
  have fb0 : R.v (h + 1 + ma) f1 = 0 := f1_of_tags ib b_ra b_rx
  have fb2 : R.v (h + 1 + ma) f2 = 1 := by
    show (R.eF (h + 1 + ma)).trace f2 = 1
    rw [f2_val ib, show (R.eF (h + 1 + ma)).trace fst = 1 from sb.fst0,
      show (R.eF (h + 1 + ma)).trace rb = 1 from hb1, Vb oMul (by simp [opCols]), Vb oDiv (by simp [opCols]),
      Vb oMod (by simp [opCols])]
    simp [oMul, oDiv, oMod]
  obtain ⟨pRL, pRO, aRL, aRO⟩ := X.latch sa sb fa (hma.imp_right Or.inl) fb0
  have LB := X.D1_f2 sb fb2 (hmb.imp_right Or.inl) aRL aRO
  -- the only `f2` row of the block is `rb`'s first row
  have hf2 : ∀ j, 1 ≤ j → j ≤ ma + mb + mc + mq → R.v (h + j) fst = 1 → R.v (h + j) f2 = 1 →
      aeval R.y (D1p X.al X.t (h + j)) = (QE.var D1).ev δ (R.eK (h + j)) (R.eF (h + j)) := by
    intro j hj1 hj2 hf hf2
    have hrb := rb_of_f2 (R := R) (by omega) hf2
    have e : h + j = h + 1 + ma := by
      by_cases c1 : h + j < h + 1 + ma
      · exact absurd hrb (by
          rw [in_tag sa (c := ra) (by simp [roleCols]) ha1 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) c1]; exact zero_ne_one)
      by_cases c2 : h + j < h + 1 + ma + mb
      · exact in_head sb (by omega) c2 hf
      by_cases c3 : h + j < h + 1 + ma + mb + mc
      · exact absurd hrb (by
          rw [in_tag sc (c := rc) (by simp [roleCols]) hc1 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) c3]; exact zero_ne_one)
      · exact absurd hrb (by
          rw [in_tag sq (c := mQM) (by simp) hq1 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) (by omega)]; exact zero_ne_one)
    rw [e]; exact LB.2
  -- the premise and the event
  have hz := hout (X.premise_of bk hf2)
  have e1 := X.D1_four sa sb sc sq bk hz
  -- the contributions
  have d0 : D1p X.al X.t h = 0 := by
    have := V (R.eF h) (fun _ _ => rfl) oLt (by simp [opCols])
    simp [D1p, onb_true X.hal hh hH, X.hal.val h hh, show (R.eF h).trace oLt = 0 by simpa [oLt, oMul] using this]
  have fna : R.v (h + 1) f2 ≠ 1 := f2_ne ia a_rb
  have fnc : R.v (h + 1 + ma + mb) f2 ≠ 1 := f2_ne ic (Tc rb (by simp [roleCols]) (by decide))
  have fnq : R.v (h + 1 + ma + mb + mc) f2 ≠ 1 := f2_ne iq (Tq rb (by simp [roleCols]) (by decide))
  have cfa : R.v (h + 1) cf1 = 0 := by
    rw [coef_val sa ha1 (c := cf1)
      (e := .sub (.sub (.add (.sub (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (cv oDiv)) (cv oMod))
      (by simp [gCoef])]
    simp only [CoeffExpr.eval, cv, Va oAdd (by simp [opCols]), Va oSub (by simp [opCols]),
      Va oLt (by simp [opCols]), Va oDiv (by simp [opCols]), Va oMod (by simp [opCols])]
    simp [oAdd, oSub, oLt, oMul, oDiv, oMod]
  have cfc : R.v (h + 1 + ma + mb) cf1 = -1 := by
    rw [coef_val sc hc1 (c := cf1) (e := .sub (.sub (cv oSub) (cv oAdd)) (cv oMul)) (by simp [gCoef])]
    simp only [CoeffExpr.eval, cv, Vc oAdd (by simp [opCols]), Vc oSub (by simp [opCols]),
      Vc oMul (by simp [opCols])]
    simp [oAdd, oSub, oMul]
  have cfq : R.v (h + 1 + ma + mb + mc) cf1 = 1 := by
    rw [coef_val sq hq1 (c := cf1) (e := .const 1) (by simp [gCoef])]; rfl
  rw [d0, (X.D_first sa fna).1, LB.1, pRL, pRO, (X.D_first sc fnc).1, (X.D_first sq fnq).1, cfa, cfc, cfq] at e1
  -- the slots' values
  have bA : AluSZChipJ9.bind (.mul (cv fst) (cv ra) : CoeffExpr Fp) kA vA ⊆ gBind := fun a ha => by
    unfold gBind; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha)))))
  have bB : AluSZChipJ9.bind (.mul (cv fst) (cv rb) : CoeffExpr Fp) kB vB ⊆ gBind := fun a ha => by
    unfold gBind; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))))
  have bE : AluSZChipJ9.bind (.mul (cv fst) (cv rc) : CoeffExpr Fp) kE vE ⊆ gBind := fun a ha => by
    unfold gBind; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha))))
  have kvA := bind_val sa (σ := .mul (cv fst) (cv ra)) (sel2 sa ha1) bA
  have kvB := bind_val sb (σ := .mul (cv fst) (cv rb)) (sel2 sb hb1) bB
  have kvE := bind_val sc (σ := .mul (cv fst) (cv rc)) (sel2 sc hc1) bE
  obtain ⟨la, ea, ea', hla, hda⟩ := X.operand_den sa (operand_mode sa (Or.inl rfl) ha1)
    (kvA.1.trans (Cs _ (by omega) (by omega) kA (by simp [Rows.constCols])))
    (kvA.2.trans (Cs _ (by omega) (by omega) vA (by simp [Rows.constCols])))
  obtain ⟨lb, eb, eb', hlb, hdb⟩ := X.operand_den sb (operand_mode sb (Or.inr (Or.inl rfl)) hb1)
    (kvB.1.trans (Cs _ (by omega) (by omega) kB (by simp [Rows.constCols])))
    (kvB.2.trans (Cs _ (by omega) (by omega) vB (by simp [Rows.constCols])))
  obtain ⟨lc, ec, -, hlc, hdc⟩ := X.operand_den sc (operand_mode sc (Or.inr (Or.inr rfl)) hc1)
    (kvE.1.trans (Cs _ (by omega) (by omega) kE (by simp [Rows.constCols])))
    (kvE.2.trans (Cs _ (by omega) (by omega) vE (by simp [Rows.constCols])))
  have hLq := sq.lane 0 (by omega)
  rw [Nat.add_zero] at hLq
  have eq := (X.Lp_mode iq hLq).2.2.2 hq1
  rw [ea', eb', X.HOp_poly sa, X.HOp_poly sb, ec, eq, X.Hp_poly sq] at e1
  simp only [map_zero, map_one, map_neg] at e1
  -- the links of the two factors and the identity
  have hlinkA := X.factor_halves bk hz sa (by omega) (by omega) (hma.imp_right Or.inl) ea
  have hlinkB := X.factor_halves bk hz sb (by omega) (by omega) (hmb.imp_right Or.inl) eb
  have hid : limbPoly la * limbPoly lb + (Polynomial.X - Polynomial.C (B : Fp)) *
      (limbPoly (lanes (laneO X.al) (h + 1) ma) * limbPoly (lanes (laneO X.al) (h + 1 + ma) mb)) - limbPoly lc =
      (Polynomial.C (B : Fp) - Polynomial.X) * limbPoly (lanes (laneL X.al) (h + 1 + ma + mb + mc) mq) := by
    rw [CB_eq]; simp only [← limbPolyQ_eq]; linear_combination e1
  have hm : ma ≤ 62 := by
    rcases hma with h' | h'
    · exact len_le sa (md := mS) (by simp) h'
    · exact len_le sa (md := mV) (by simp) h'
  have hmul := Nock.Atoms.mul_lift_gate (m := ma) (aE := lanes (laneE X.al) (h + 1) ma)
    (aO := lanes (laneO X.al) (h + 1) ma) (bE := lanes (laneE X.al) (h + 1 + ma) mb)
    (bO := lanes (laneO X.al) (h + 1 + ma) mb) hm (by rw [lanes_length]) (by rw [lanes_length])
    (lanes_bound _ fun j hj => laneE_lt X.hal (by omega)) (lanes_bound _ fun j hj => laneO_lt X.hal (by omega))
    (lanes_bound _ fun j hj => laneE_lt X.hal (by omega)) (lanes_bound _ fun j hj => laneO_lt X.hal (by omega))
    hla hlb hlc (X.qm_lt sq hq1) hlinkA hlinkB hid
  exact ⟨val la, val lb, val lc, hda, hdb, hdc, by simp [Nock.Jet.Prim.primSem, hmul]⟩

/-- **div / mod, the shared core** (block `ra rx rb ry rs mQM mQ1`): the decoded operands `a`, `d` and the quotient /
remainder `q`, `r` (one of them the result handle, the other a W-B witness) satisfy `a = q·d + r ∧ r < d`. -/
theorem divmod_core {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) {o : ℕ} (hoc : o = oDiv ∨ o = oMod)
    (hop : R.v h o = 1)
    (hout : (∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0) → ∀ P ∈ callPolys X.al X.t h, P = 0) :
    ∃ na nd nq nr, HDen X.r (R.v h kA) (R.v h vA) na ∧ HDen X.r (R.v h kB) (R.v h vB) nd ∧
      na = nq * nd + nr ∧ nr < nd ∧ (o = oDiv → HDen X.r (R.v h kE) (R.v h vE) nq) ∧
      (o = oMod → HDen X.r (R.v h kE) (R.v h vE) nr) := by
  have ho : o ∈ opCols := by rcases hoc with rfl | rfl <;> simp [opCols]
  have V := fun e he => op_vals hh hH ho hop e he
  have W : ∀ e : Env Fp, (∀ c ∈ Rows.constCols, e.trace c = R.v h c) →
      e.trace oAdd = 0 ∧ e.trace oSub = 0 ∧ e.trace oLt = 0 ∧ e.trace oMul = 0 ∧
        e.trace oDiv + e.trace oMod = 1 := by
    intro e he
    have v := V e he
    rw [v oAdd (by simp [opCols]), v oSub (by simp [opCols]), v oLt (by simp [opCols]), v oMul (by simp [opCols]),
      v oDiv (by simp [opCols]), v oMod (by simp [opCols])]
    rcases hoc with rfl | rfl <;> simp [oAdd, oSub, oLt, oMul, oDiv, oMod]
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, s1, s2, s3, s4, s5, s6, s7, t1, t2, t3, t4, t5, t6, t7, bk, hcst⟩ :=
    shape7 (R := R) hh hH (fun e he => by
      have w := W e he
      simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      exact w.2.2.2.2)
  have bl := bk.lt
  have := s1.pos; have := s2.pos; have := s3.pos; have := s4.pos; have := s5.pos; have := s6.pos; have := s7.pos
  have Cs := fun i (h1 : h ≤ i) (h2 : i ≤ h + (m1 + m2 + m3 + m4 + m5 + m6 + m7)) => cst_at hcst h1 h2
  have i1 : h + 1 < R.n := by omega
  have i2 : h + 1 + m1 < R.n := by omega
  have i3 : h + 1 + m1 + m2 < R.n := by omega
  have i4 : h + 1 + m1 + m2 + m3 < R.n := by omega
  have i5 : h + 1 + m1 + m2 + m3 + m4 < R.n := by omega
  have i6 : h + 1 + m1 + m2 + m3 + m4 + m5 < R.n := by omega
  have i7 : h + 1 + m1 + m2 + m3 + m4 + m5 + m6 < R.n := by omega
  have W1 := W _ (Cs (h + 1) (by omega) (by omega))
  have W2 := W _ (Cs (h + 1 + m1) (by omega) (by omega))
  have W3 := W _ (Cs (h + 1 + m1 + m2) (by omega) (by omega))
  have W7 := W _ (Cs (h + 1 + m1 + m2 + m3 + m4 + m5 + m6) (by omega) (by omega))
  have Wh := W (R.eF h) (fun _ _ => rfl)
  have T1 := (R.tag_onehot i1 (c := ra) (by simp [roleCols]) t1).2
  have T2 := (R.tag_onehot i2 (c := rx) (by simp [roleCols]) t2).2
  have T3 := (R.tag_onehot i3 (c := rb) (by simp [roleCols]) t3).2
  have T4 := (R.tag_onehot i4 (c := ry) (by simp [roleCols]) t4).2
  have T5 := (R.tag_onehot i5 (c := rs) (by simp [roleCols]) t5).2
  have T6 := (R.tag_onehot i6 (c := mQM) (by simp) t6).2
  have T7 := (R.tag_onehot i7 (c := mQ1) (by simp) t7).2
  have rb1 : (R.eF (h + 1)).trace rb = 0 := T1 rb (by simp [roleCols]) (by decide)
  have rb2 : (R.eF (h + 1 + m1)).trace rb = 0 := T2 rb (by simp [roleCols]) (by decide)
  have ra2 : (R.eF (h + 1 + m1)).trace ra = 0 := T2 ra (by simp [roleCols]) (by decide)
  have ra3 : (R.eF (h + 1 + m1 + m2)).trace ra = 0 := T3 ra (by simp [roleCols]) (by decide)
  have rx3 : (R.eF (h + 1 + m1 + m2)).trace rx = 0 := T3 rx (by simp [roleCols]) (by decide)
  have rb4 : (R.eF (h + 1 + m1 + m2 + m3)).trace rb = 0 := T4 rb (by simp [roleCols]) (by decide)
  have rb5 : (R.eF (h + 1 + m1 + m2 + m3 + m4)).trace rb = 0 := T5 rb (by simp [roleCols]) (by decide)
  have rb6 : (R.eF (h + 1 + m1 + m2 + m3 + m4 + m5)).trace rb = 0 := T6 rb (by simp [roleCols]) (by decide)
  have rb7 : (R.eF (h + 1 + m1 + m2 + m3 + m4 + m5 + m6)).trace rb = 0 := T7 rb (by simp [roleCols]) (by decide)
  have opv : ∀ i, h ≤ i → i ≤ h + (m1 + m2 + m3 + m4 + m5 + m6 + m7) → R.v i o = 1 := fun i h1 h2 => by
    have := V _ (Cs i h1 h2) o ho; simpa using this
  -- the bindings of the operands `a` (`ra`) and `d` (`rb`)
  have bA : AluSZChipJ9.bind (.mul (cv fst) (cv ra) : CoeffExpr Fp) kA vA ⊆ gBind := fun a ha => by
    unfold gBind; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha)))))
  have bB : AluSZChipJ9.bind (.mul (cv fst) (cv rb) : CoeffExpr Fp) kB vB ⊆ gBind := fun a ha => by
    unfold gBind; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))))
  have kvA := bind_val s1 (σ := .mul (cv fst) (cv ra)) (sel2 s1 t1) bA
  have kvB := bind_val s3 (σ := .mul (cv fst) (cv rb)) (sel2 s3 t3) bB
  obtain ⟨la, ea, -, hla, hda⟩ := X.operand_den s1 (operand_mode s1 (Or.inl rfl) t1)
    (kvA.1.trans (Cs _ (by omega) (by omega) kA (by simp [Rows.constCols])))
    (kvA.2.trans (Cs _ (by omega) (by omega) vA (by simp [Rows.constCols])))
  obtain ⟨ld, ed, ed', hld, hdd⟩ := X.operand_den s3 (operand_mode s3 (Or.inr (Or.inl rfl)) t3)
    (kvB.1.trans (Cs _ (by omega) (by omega) kB (by simp [Rows.constCols])))
    (kvB.2.trans (Cs _ (by omega) (by omega) vB (by simp [Rows.constCols])))
  -- `d` is a factor: `mS` / `mV`
  have hmd3 : R.v (h + 1 + m1 + m2) mS = 1 ∨ R.v (h + 1 + m1 + m2) mV = 1 := by
    have := operand_mode s3 (Or.inr (Or.inl rfl)) t3
    have nR := not_mR (R := R) i3 (by
      rw [W3.2.2.2.1, W3.2.2.2.2, ra3, rx3, show (R.eF (h + 1 + m1 + m2)).trace rb = 1 from t3]; ring)
    rcases this with h' | h' | h'
    · exact absurd h' nR
    · exact Or.inl h'
    · exact Or.inr h'
  -- `q` (`rx`): the result handle on `div`, a witness on `mod`
  obtain ⟨lq, eq1, eq2, hlq, hmq, hdq⟩ : ∃ lq : List ℕ, Lp X.al X.t (h + 1 + m1) = limbPolyQ lq ∧
      Lf X.al X.t (h + 1 + m1) = limbPolyQ lq ∧ (∀ x ∈ lq, x < B) ∧
      (R.v (h + 1 + m1) mS = 1 ∨ R.v (h + 1 + m1) mV = 1 ∨ R.v (h + 1 + m1) mW = 1) ∧
      (o = oDiv → HDen X.r (R.v h kE) (R.v h vE) (val lq)) := by
    have ho2 := opv (h + 1 + m1) (by omega) (by omega)
    rcases hoc with rfl | rfl
    · have nW := compat_mW0 i2 t2 ho2 (by simp [gCompat])
      have nR := not_mR (R := R) i2 (by
        rw [W2.2.2.2.1, W2.2.2.2.2, ra2, rb2, show (R.eF (h + 1 + m1)).trace rx = 1 from t2]; ring)
      have hm3 : R.v (h + 1 + m1) mS = 1 ∨ R.v (h + 1 + m1) mV = 1 := by
        rcases role_mode s2 (r := rx) (by simp [roleCols]) t2 with h' | h' | h' | h'
        · exact absurd h' nR
        · exact Or.inl h'
        · exact Or.inr h'
        · rw [nW] at h'; exact absurd h' zero_ne_one
      have bQ : AluSZChipJ9.bind (prod3 (cv fst) (cv rx) (cv oDiv) : CoeffExpr Fp) kE vE ⊆ gBind := fun a ha => by
        unfold gBind
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha))
      have kv := bind_val s2 (σ := prod3 (cv fst) (cv rx) (cv oDiv)) (by
        simp only [prod3, CoeffExpr.eval, cv]
        rw [show (R.eF (h + 1 + m1)).trace fst = 1 from s2.fst0, show (R.eF (h + 1 + m1)).trace rx = 1 from t2,
          show (R.eF (h + 1 + m1)).trace oDiv = 1 from ho2]; ring) bQ
      obtain ⟨l, e, e', hb, hd⟩ := X.operand_den s2 (Or.inr hm3)
        (kv.1.trans (Cs _ (by omega) (by omega) kE (by simp [Rows.constCols])))
        (kv.2.trans (Cs _ (by omega) (by omega) vE (by simp [Rows.constCols])))
      exact ⟨l, e, e', hb, hm3.imp_right Or.inl, fun _ => hd⟩
    · have hW := compat_mW1 i2 t2 ho2 (by simp [gCompat])
      obtain ⟨e, e', hb⟩ := X.witness s2 hW
      exact ⟨_, e, e', hb, Or.inr (Or.inr hW), fun h' => absurd h' (by decide)⟩
  -- `r` (`ry`): a witness on `div`, the result handle on `mod`
  obtain ⟨lr, er, hlr, hdr⟩ : ∃ lr : List ℕ, Lp X.al X.t (h + 1 + m1 + m2 + m3) = limbPolyQ lr ∧
      (∀ x ∈ lr, x < B) ∧ (o = oMod → HDen X.r (R.v h kE) (R.v h vE) (val lr)) := by
    have ho4 := opv (h + 1 + m1 + m2 + m3) (by omega) (by omega)
    rcases hoc with rfl | rfl
    · have hW := compat_mW1 i4 t4 ho4 (by simp [gCompat])
      obtain ⟨e, -, hb⟩ := X.witness s4 hW
      exact ⟨_, e, hb, fun h' => absurd h' (by decide)⟩
    · have nW := compat_mW0 i4 t4 ho4 (by simp [gCompat])
      have hm3 : R.v (h + 1 + m1 + m2 + m3) mR = 1 ∨ R.v (h + 1 + m1 + m2 + m3) mS = 1 ∨
          R.v (h + 1 + m1 + m2 + m3) mV = 1 := by
        rcases role_mode s4 (r := ry) (by simp [roleCols]) t4 with h' | h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
        · rw [nW] at h'; exact absurd h' zero_ne_one
      have bR : AluSZChipJ9.bind (prod3 (cv fst) (cv ry) (cv oMod) : CoeffExpr Fp) kE vE ⊆ gBind := fun a ha => by
        unfold gBind
        exact List.mem_append_left _ (List.mem_append_right _ ha)
      have kv := bind_val s4 (σ := prod3 (cv fst) (cv ry) (cv oMod)) (by
        simp only [prod3, CoeffExpr.eval, cv]
        rw [show (R.eF (h + 1 + m1 + m2 + m3)).trace fst = 1 from s4.fst0,
          show (R.eF (h + 1 + m1 + m2 + m3)).trace ry = 1 from t4,
          show (R.eF (h + 1 + m1 + m2 + m3)).trace oMod = 1 from ho4]; ring) bR
      obtain ⟨l, e, -, hb, hd⟩ := X.operand_den s4 hm3
        (kv.1.trans (Cs _ (by omega) (by omega) kE (by simp [Rows.constCols])))
        (kv.2.trans (Cs _ (by omega) (by omega) vE (by simp [Rows.constCols])))
      exact ⟨l, e, hb, fun _ => hd⟩
  -- `s` (`rs`, witness), `K` (`mQM`), `K₂` (`mQ1`)
  obtain ⟨es, -, hls⟩ := X.witness s5 (witness_mode s5 (Or.inr rfl) t5)
  have hL6 := s6.lane 0 (by omega)
  rw [Nat.add_zero] at hL6
  have ek := (X.Lp_mode i6 hL6).2.2.2 t6
  obtain ⟨ek2, hk2⟩ := X.qslot1 s7 t7
  -- the latch from `rx` (`f1`) to `rb` (`f2`)
  have fa : R.v (h + 1 + m1) f1 = 1 := by
    show (R.eF (h + 1 + m1)).trace f1 = 1
    rw [f1_val i2, show (R.eF (h + 1 + m1)).trace fst = 1 from s2.fst0, W2.2.2.2.1, W2.2.2.2.2, ra2,
      show (R.eF (h + 1 + m1)).trace rx = 1 from t2]; ring
  have fb0 : R.v (h + 1 + m1 + m2) f1 = 0 := f1_of_tags i3 ra3 rx3
  have fb2 : R.v (h + 1 + m1 + m2) f2 = 1 := by
    show (R.eF (h + 1 + m1 + m2)).trace f2 = 1
    rw [f2_val i3, show (R.eF (h + 1 + m1 + m2)).trace fst = 1 from s3.fst0,
      show (R.eF (h + 1 + m1 + m2)).trace rb = 1 from t3, W3.2.2.2.1, W3.2.2.2.2]; ring
  obtain ⟨pRL, pRO, aRL, aRO⟩ := X.latch s2 s3 fa hmq fb0
  have LB := X.D1_f2 s3 fb2 (hmd3.imp_right Or.inl) aRL aRO
  -- the only `f2` row of the block is `rb`'s first row
  have hf2 : ∀ j, 1 ≤ j → j ≤ m1 + m2 + m3 + m4 + m5 + m6 + m7 → R.v (h + j) fst = 1 → R.v (h + j) f2 = 1 →
      aeval R.y (D1p X.al X.t (h + j)) = (QE.var D1).ev δ (R.eK (h + j)) (R.eF (h + j)) := by
    intro j hj1 hj2 hf hf2
    have hrb := rb_of_f2 (R := R) (by omega) hf2
    have e : h + j = h + 1 + m1 + m2 := by
      by_cases c1 : h + j < h + 1 + m1
      · exact absurd hrb (by
          rw [in_tag s1 (c := ra) (by simp [roleCols]) t1 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) c1]; exact zero_ne_one)
      by_cases c2 : h + j < h + 1 + m1 + m2
      · exact absurd hrb (by
          rw [in_tag s2 (c := rx) (by simp [roleCols]) t2 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) c2]; exact zero_ne_one)
      by_cases c3 : h + j < h + 1 + m1 + m2 + m3
      · exact in_head s3 (by omega) c3 hf
      by_cases c4 : h + j < h + 1 + m1 + m2 + m3 + m4
      · exact absurd hrb (by
          rw [in_tag s4 (c := ry) (by simp [roleCols]) t4 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) c4]; exact zero_ne_one)
      by_cases c5 : h + j < h + 1 + m1 + m2 + m3 + m4 + m5
      · exact absurd hrb (by
          rw [in_tag s5 (c := rs) (by simp [roleCols]) t5 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) c5]; exact zero_ne_one)
      by_cases c6 : h + j < h + 1 + m1 + m2 + m3 + m4 + m5 + m6
      · exact absurd hrb (by
          rw [in_tag s6 (c := mQM) (by simp) t6 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) c6]; exact zero_ne_one)
      · exact absurd hrb (by
          rw [in_tag s7 (c := mQ1) (by simp) t7 (d := rb) (by simp [roleCols]) (by decide)
            (by omega) (by omega)]; exact zero_ne_one)
    rw [e]; exact LB.2
  -- the premise and the event
  have hz := hout (X.premise_of bk hf2)
  have e1 := X.D_seven (D1p X.al X.t) s1 s2 s3 s4 s5 s6 s7 bk (hz _ (by simp [callPolys]))
    (fun s i' he => (X.slot_sum s he).1)
  have e2 := X.D_seven (D2p X.al X.t) s1 s2 s3 s4 s5 s6 s7 bk (hz _ (by simp [callPolys]))
    (fun s i' he => (X.slot_sum s he).2)
  -- the contributions
  have d1h : D1p X.al X.t h = 0 := by
    simp [D1p, onb_true X.hal hh hH, X.hal.val h hh, Wh.2.2.1]
  have d2h : D2p X.al X.t h = Polynomial.C 1 := by
    have e : D2p X.al X.t h = Polynomial.C (cl X.al h oDiv + cl X.al h oMod) := by
      simp [D2p, onb_true X.hal hh hH]
    rw [e, X.hal.val h hh oDiv, X.hal.val h hh oMod]
    exact congrArg _ Wh.2.2.2.2
  have fn1 := f2_ne i1 rb1
  have fn2 := f2_ne i2 rb2
  have fn4 := f2_ne i4 rb4
  have fn5 := f2_ne i5 rb5
  have fn6 := f2_ne i6 rb6
  have fn7 := f2_ne i7 rb7
  have c11 : R.v (h + 1) cf1 = -1 := by
    rw [coef_val s1 t1 (c := cf1)
      (e := .sub (.sub (.add (.sub (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (cv oDiv)) (cv oMod))
      (by simp [gCoef])]
    simp only [CoeffExpr.eval, cv, W1.1, W1.2.1, W1.2.2.1]
    linear_combination -W1.2.2.2.2
  have c12 : R.v (h + 1 + m1) cf1 = 0 := by
    rw [coef_val s2 t2 (c := cf1) (e := .const 0) (by simp [gCoef])]; rfl
  have c14 : R.v (h + 1 + m1 + m2 + m3) cf1 = 1 := by
    rw [coef_val s4 t4 (c := cf1) (e := .const 1) (by simp [gCoef])]; rfl
  have c15 : R.v (h + 1 + m1 + m2 + m3 + m4) cf1 = 0 := by
    rw [coef_val s5 t5 (c := cf1) (e := .const 0) (by simp [gCoef])]; rfl
  have c16 : R.v (h + 1 + m1 + m2 + m3 + m4 + m5) cf1 = 1 := by
    rw [coef_val s6 t6 (c := cf1) (e := .const 1) (by simp [gCoef])]; rfl
  have c17 : R.v (h + 1 + m1 + m2 + m3 + m4 + m5 + m6) cf1 = 0 := by
    rw [coef_val s7 t7 (c := cf1) (e := sumC [oAdd, oSub, oLt]) (by simp [gCoef])]
    simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, W7.1, W7.2.1, W7.2.2.1]
    ring
  have c21 : R.v (h + 1) cf2 = 0 := by
    rw [coef_val s1 t1 (c := cf2) (e := .const 0) (by simp [gCoef])]; rfl
  have c22 : R.v (h + 1 + m1) cf2 = 0 := by
    rw [coef_val s2 t2 (c := cf2) (e := .const 0) (by simp [gCoef])]; rfl
  have c23 : R.v (h + 1 + m1 + m2) cf2 = -1 := by
    rw [coef_val s3 t3 (c := cf2) (e := .neg (sumC [oDiv, oMod])) (by simp [gCoef])]
    simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    linear_combination -W3.2.2.2.2
  have c24 : R.v (h + 1 + m1 + m2 + m3) cf2 = 1 := by
    rw [coef_val s4 t4 (c := cf2) (e := .const 1) (by simp [gCoef])]; rfl
  have c25 : R.v (h + 1 + m1 + m2 + m3 + m4) cf2 = 1 := by
    rw [coef_val s5 t5 (c := cf2) (e := .const 1) (by simp [gCoef])]; rfl
  have c26 : R.v (h + 1 + m1 + m2 + m3 + m4 + m5) cf2 = 0 := by
    rw [coef_val s6 t6 (c := cf2) (e := .const 0) (by simp [gCoef])]; rfl
  have c27 : R.v (h + 1 + m1 + m2 + m3 + m4 + m5 + m6) cf2 = 1 := by
    rw [coef_val s7 t7 (c := cf2) (e := sumC [oDiv, oMod]) (by simp [gCoef])]
    simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    exact W7.2.2.2.2
  rw [d1h, (X.D_first s1 fn1).1, (X.D_first s2 fn2).1, LB.1, pRL, pRO, (X.D_first s4 fn4).1,
    (X.D_first s5 fn5).1, (X.D_first s6 fn6).1, (X.D_first s7 fn7).1, c11, c12, c14, c15, c16, c17] at e1
  rw [ea, eq2, ed', X.HOp_poly s2, X.HOp_poly s3, er, ek, X.Hp_poly s6] at e1
  simp only [map_zero, map_one, map_neg] at e1
  rw [d2h, X.D2_head s1, X.D2_head s2, X.D2_head s3, X.D2_head s4, X.D2_head s5, X.D2_head s6, X.D2_head s7,
    c21, c22, c23, c24, c25, c26, c27] at e2
  rw [ed, er, es, ek2] at e2
  simp only [map_zero, map_one, map_neg] at e2
  -- the two identities, the links, `Nock.Atoms.ArithSZ`
  have h₁ : limbPoly lq * limbPoly ld + (Polynomial.X - Polynomial.C (B : Fp)) *
      (limbPoly (lanes (laneO X.al) (h + 1 + m1) m2) * limbPoly (lanes (laneO X.al) (h + 1 + m1 + m2) m3)) +
      limbPoly lr - limbPoly la =
      (Polynomial.C (B : Fp) - Polynomial.X) * limbPoly (lanes (laneL X.al) (h + 1 + m1 + m2 + m3 + m4 + m5) m6) := by
    rw [CB_eq]; simp only [← limbPolyQ_eq]; linear_combination e1
  have h₂ : limbPoly lr + limbPoly (lanes (laneL X.al) (h + 1 + m1 + m2 + m3 + m4) m5) + 1 - limbPoly ld =
      (Polynomial.C (B : Fp) - Polynomial.X) * limbPoly (packL X.al (h + 1 + m1 + m2 + m3 + m4 + m5 + m6) m7) := by
    rw [CB_eq]; simp only [← limbPolyQ_eq]; linear_combination e2
  have hlinkQ := X.factor_halves bk hz s2 (by omega) (by omega) hmq eq1
  have hlinkD := X.factor_halves bk hz s3 (by omega) (by omega) (hmd3.imp_right Or.inl) ed
  have hm : m2 ≤ 62 := by
    rcases hmq with h' | h' | h'
    · exact len_le s2 (md := mS) (by simp) h'
    · exact len_le s2 (md := mV) (by simp) h'
    · exact len_le s2 (md := mW) (by simp) h'
  have hdiv := Nock.Atoms.div_lift_gate (m := m2) (qE := lanes (laneE X.al) (h + 1 + m1) m2)
    (qO := lanes (laneO X.al) (h + 1 + m1) m2) (dE := lanes (laneE X.al) (h + 1 + m1 + m2) m3)
    (dO := lanes (laneO X.al) (h + 1 + m1 + m2) m3) hm (by rw [lanes_length]) (by rw [lanes_length])
    (lanes_bound _ fun j hj => laneE_lt X.hal (by omega)) (lanes_bound _ fun j hj => laneO_lt X.hal (by omega))
    (lanes_bound _ fun j hj => laneE_lt X.hal (by omega)) (lanes_bound _ fun j hj => laneO_lt X.hal (by omega))
    hla hld hlq hlr hls (X.qm_lt s6 t6) hk2 hlinkQ hlinkD h₁ h₂
  exact ⟨val la, val ld, val lq, val lr, hda, hdd, hdiv.1, hdiv.2, hdq, hdr⟩

/-- **`div_sound`**: an accepted `div` call block computes `primSem div` on the decoded handles (division by zero
is unsatisfiable: `r + s + 1 = d` forces `d ≥ 1`). -/
theorem div_sound {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hop : R.v h oDiv = 1)
    (hout : (∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0) → ∀ P ∈ callPolys X.al X.t h, P = 0) :
    ∃ na nb nc, HDen X.r (R.v h kA) (R.v h vA) na ∧ HDen X.r (R.v h kB) (R.v h vB) nb ∧
      HDen X.r (R.v h kE) (R.v h vE) nc ∧ Nock.Jet.Prim.primSem .div na nb = some nc := by
  obtain ⟨na, nd, nq, nr, ha, hd, e, hlt, hq, -⟩ := X.divmod_core hh hH (Or.inl rfl) hop hout
  have hpos : 0 < nd := by omega
  have hdv : na / nd = nq := by
    rw [e, show nq * nd + nr = nr + nq * nd by ring, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt,
      zero_add]
  exact ⟨na, nd, nq, ha, hd, hq rfl, by simp [Nock.Jet.Prim.primSem, hpos, hdv]⟩

/-- **`mod_sound`**: an accepted `mod` call block computes `primSem mod` on the decoded handles. -/
theorem mod_sound {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hop : R.v h oMod = 1)
    (hout : (∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0) → ∀ P ∈ callPolys X.al X.t h, P = 0) :
    ∃ na nb nc, HDen X.r (R.v h kA) (R.v h vA) na ∧ HDen X.r (R.v h kB) (R.v h vB) nb ∧
      HDen X.r (R.v h kE) (R.v h vE) nc ∧ Nock.Jet.Prim.primSem .mod na nb = some nc := by
  obtain ⟨na, nd, nq, nr, ha, hd, e, hlt, -, hr⟩ := X.divmod_core hh hH (Or.inr rfl) hop hout
  have hpos : 0 < nd := by omega
  have hmd : na % nd = nr := by
    rw [e, show nq * nd + nr = nr + nq * nd by ring, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  exact ⟨na, nd, nr, ha, hd, hr rfl, by simp [Nock.Jet.Prim.primSem, hpos, hmd]⟩

end Ctx

/-! ## 6. `op_sound6`: all six ops off the per-call event -/

section Event
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 cY1 cY2)
variable [Fintype K] [DecidableEq K] [Algebra Fp (Quad (algebraMap Fp K δ))] {R : Rows δ K}

variable {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {alu : Tr → List ALRow}
  {atom : Tr → List (CellRowB0 Nock.Atoms.p)} {C A AL : ℕ} {hC : ∀ tr, (hdrs (alu tr)).length ≤ C}
  {hA : ∀ tr, (atom tr).length ≤ A} {hAL : ∀ tr, (alu tr).length ≤ AL}
  {hc : ∀ Q, St Q → ∀ χ χ', alu (Q χ) = alu (Q χ') ∧ atom (Q χ) = atom (Q χ')}

/-- **`op_sound6`** (O-1: the six ALU ops add/sub/lt/mul/div/mod): the gates of one call block (`R`), the served
reads (`X.read`), the atom walk (`X.walk`) and the call outside the per-call arithmetic event `arithSZ` give
`primSem op (D a) (D b) = some (D c)` on the hdr's handles `(kA, vA)`, `(kB, vB)`, `(kE, vE)`. -/
theorem op_sound6 (X : Ctx R) (op : Nock.Jet.Prim.PrimOp)
    (hop6 : op = .add ∨ op = .sub ∨ op = .lt ∨ op = .mul ∨ op = .div ∨ op = .mod)
    {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hflag : R.v h (opColOf op) = 1)
    (tr : Tr) (χ : Coins frameJ8 K) (hal : X.al = alu tr) (ht : X.t = atom tr)
    (hy : R.y = Quad.mk (algebraMap Fp K δ) (χ cY1) (χ cY2))
    (hχ : ¬ (AluSZEvent.arithSZ (algebraMap Fp K δ) St alu atom C A AL hC hA hAL hc).mem tr χ) :
    ∃ na nb nc, Ctx.HDen X.r (R.v h kA) (R.v h vA) na ∧ Ctx.HDen X.r (R.v h kB) (R.v h vB) nb ∧
      Ctx.HDen X.r (R.v h kE) (R.v h vE) nc ∧ Nock.Jet.Prim.primSem op na nb = some nc := by
  have hout := hout_of_event X tr χ hal ht hy hχ hh hH
  rcases hop6 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact X.add_sound hh hH hflag hout
  · exact X.sub_sound hh hH hflag hout
  · exact X.lt_sound hh hH hflag hout
  · exact X.mul_sound hh hH hflag hout
  · exact X.div_sound hh hH hflag hout
  · exact X.mod_sound hh hH hflag hout

end Event

/-! ## Axioms (expected: `[propext, Classical.choice, Quot.sound]`) -/

#print axioms Ctx.mul_sound
#print axioms Ctx.div_sound
#print axioms Ctx.mod_sound
#print axioms Ctx.divmod_core
#print axioms op_sound6
#print axioms Ctx.len_le
#print axioms Ctx.qm_lt
#print axioms Ctx.latch
#print axioms Ctx.shape7

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps
