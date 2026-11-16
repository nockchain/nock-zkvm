/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/AxisSoundX9.lean

The axis trace is read as an `ℕ`-indexed family of row environments `E` with the row facts `AxTr`
  (every row's base gates, the next-row tie, the two masks).  The served facts are hypotheses:
  * `hL` (pass 1, Φ₀): every limb consume `(R, axK, 0, l)` meets `WalkAOK9 V combN`;
  * `hP`: every path consume (`z1a = 0`) meets `RecOK`'s `.p` clause.
  Conclusion at a closing row `r` (`cl = 1`): `∃ n, V R = some n ∧ 2^32 ≤ n ∧ (route0 → v = n) ∧
  ∃ X Y, D (1, hr) = X ∧ D hout = Y ∧ slot n X = Y` (`axisChain_sound`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RowSemChipX9
import Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AxisSoundX9

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AxRowEqs G1 G2 G3 G4 G5 G6c G6p G6p_nonhead G6p_head G6hc G6b
  G7 G8 G8_route cl_of_mu step_nonhead step_head step_route0 step_axS_nonhead step_axS_head isFT isLT head cl z1a
  route0 pw axK axS hrv hink hinv houtk houtv r0h ftk ftv mu)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN combL)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (WalkAOK9 limb_digit RecOK9 TagAxOK recClass)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (natKey mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (DenOKX9)
open Module
open scoped Polynomial

noncomputable section

section Abstract
variable {p : ℕ} [Fact p.Prime]

/-- **The axis trace's row facts**, `ℕ`-indexed: every row's base gates, the next-row tie, `isFirstT` at row `0`,
`isLastT = 0` off the last row. -/
structure AxTr (E : ℕ → Env (ZMod p)) (nX : ℕ) : Prop where
  rows : ∀ i < nX, AxRowEqs (E i)
  next : ∀ i, i + 1 < nX → ∀ j, (E i).traceNext j = (E (i + 1)).trace j
  first : 0 < nX → (E 0).trace isFT = 1
  last : ∀ i, i + 1 < nX → (E i).trace isLT = 0

variable {E : ℕ → Env (ZMod p)} {nX : ℕ}

/-- **S3 W (`chainBack`)**: a closing row `r` has a head `h < r`; the rows strictly after `h` up to `r` are
non-heads and the rows from `h` up to (not incl.) `r` are not closing. -/
theorem chainBack (A : AxTr E nX) {r : ℕ} (hr : r < nX) (hc : (E r).trace cl = 1) :
    ∃ h, h < r ∧ (E h).trace head = 1 ∧ (∀ j, h < j → j ≤ r → (E j).trace head = 0) ∧
      (∀ j, h ≤ j → j < r → (E j).trace cl = 0) := by
  classical
  have h0 : (E 0).trace head = 1 := (G6b (A.rows 0 (by omega))).2.2.2 (A.first (by omega))
  set h := Nat.findGreatest (fun j => (E j).trace head = 1) r with hh
  have hP : (E h).trace head = 1 := Nat.findGreatest_spec (P := fun j => (E j).trace head = 1) (Nat.zero_le r) h0
  have hle : h ≤ r := Nat.findGreatest_le r
  have hgt : ∀ j, h < j → j ≤ r → (E j).trace head = 0 := fun j hj hjr =>
    ((G1 (A.rows j (by omega))).1).resolve_right (Nat.findGreatest_is_greatest hj hjr)
  have hcl : ∀ j, h ≤ j → j < r → (E j).trace cl = 0 := by
    intro j hj hjr
    rcases (G1 (A.rows j (by omega))).2.1 with h1 | h1
    · exact h1
    · exfalso
      have := (G6b (A.rows j (by omega))).1 (A.last j (by omega)) h1
      rw [A.next j (by omega), hgt (j + 1) (by omega) (by omega)] at this
      exact zero_ne_one this
  have hne : h ≠ r := by
    intro he
    have := G6hc (A.rows h (by omega)) hP
    rw [he, hc] at this
    exact one_ne_zero this
  exact ⟨h, lt_of_le_of_ne hle hne, hP, hgt, hcl⟩

/-- **G6 continuity along a chain**: a column carried off `cl` is constant from the head to the closing row. -/
theorem chain_const (A : AxTr E nX) {h r : ℕ} (hr : r < nX) (hcl : ∀ j, h ≤ j → j < r → (E j).trace cl = 0)
    (c : ℕ) (hc : ∀ e : Env (ZMod p), AxRowEqs e → e.trace cl = 0 → e.traceNext c = e.trace c) :
    ∀ j, h ≤ j → j ≤ r → (E j).trace c = (E h).trace c := by
  intro j
  induction j with
  | zero => intro h0 _; rw [show h = 0 by omega]
  | succ j ih =>
    intro hj hjr
    rcases Nat.lt_or_ge j h with hjh | hjh
    · rw [show h = j + 1 by omega]
    · rw [← A.next j (by omega), hc _ (A.rows j (by omega)) (hcl j hjh (by omega))]
      exact ih hjh (by omega)

/-- `wrap62` at `ZMod p` under `hpG`. -/
theorem wrap62_zmod (hpG : p = Nock.Atoms.p) (x : ZMod p) (hx : x = 2 ^ 64 - 2) (L : List ℕ) (y : ℕ) :
    Noun.slot x.val (combL L) ≠ some (.atom y) := by
  subst hpG
  refine Nock.J9A.NounAx.wrap62 (ZMod.val_lt x) ?_ L y
  rw [ZMod.natCast_zmod_val]; exact hx

theorem hp63 (hpG : p = Nock.Atoms.p) : 2 ^ 63 < p := by
  rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]

/-- **S3 P (the backward `pw` induction)**: at distance `d` from the closing row (a non-head row),
`pw = 2^(d+2)`, `d + 2 ≤ 63`, `d + 2 ≤ |L|` and the limb is `L[d]`. -/
theorem pw_back (hpG : p = Nock.Atoms.p) (A : AxTr E nX) {h r : ℕ} (hr : r < nX)
    (hc : (E r).trace cl = 1)
    (hgt : ∀ j, h < j → j ≤ r → (E j).trace head = 0) (hcl : ∀ j, h ≤ j → j < r → (E j).trace cl = 0)
    {L : List ℕ} (hS : ∀ j, h ≤ j → j ≤ r →
      Noun.slot ((E j).trace axK).val (combL L) = some (.atom ((E j).trace AxisChipJ9.l).val)) :
    ∀ d, h < r - d → (E (r - d)).trace pw = (2 : ZMod p) ^ (d + 2) ∧ d + 2 ≤ 63 ∧ d + 2 ≤ L.length ∧
      ((E (r - d)).trace AxisChipJ9.l).val = L[d]! := by
  have hp := hp63 hpG
  intro d
  induction d with
  | zero =>
    intro hd
    have H := A.rows r hr
    have hpw : (E r).trace pw = (2 : ZMod p) ^ (0 + 2) := by rw [(G6p H).2 hc]; norm_num
    obtain ⟨-, h2, h3⟩ := step_nonhead hp H (hgt r (by omega) le_rfl) 0 (by norm_num) hpw (hS r (by omega) le_rfl)
    exact ⟨hpw, by norm_num, h2, h3⟩
  | succ d ih =>
    intro hd
    obtain ⟨ipw, i63, -, -⟩ := ih (by omega)
    set j := r - (d + 1) with hjdef
    have hj1 : j + 1 = r - d := by omega
    have H := A.rows j (by omega)
    have hhj := hgt j (by omega) (by omega)
    have hpw : (E j).trace pw = (2 : ZMod p) ^ (d + 1 + 2) := by
      rw [G6p_nonhead H (hcl j (by omega) (by omega)) hhj, A.next j (by omega), hj1, ipw]; ring
    rcases Nat.lt_or_ge (d + 2) 63 with hlt | hge
    · obtain ⟨-, h2, h3⟩ := step_nonhead hp H hhj (d + 1) (by omega) hpw (hS j (by omega) (by omega))
      exact ⟨hpw, by omega, h2, h3⟩
    · exfalso
      have hd62 : d + 1 + 2 = 64 := by omega
      have hax : (E j).trace axK = 2 ^ 64 - 2 := by rw [(G2 H).2 hhj, hpw, hd62]
      exact wrap62_zmod hpG _ hax L _ (hS j (by omega) (by omega))

theorem getLast!_eq {L : List ℕ} (hL : L ≠ []) : L.getLast! = L[L.length - 1]! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?]
  have : L.length - 1 < L.length := by
    rcases L with _ | ⟨a, t⟩
    · exact absurd rfl hL
    · simp
  rw [List.getElem!_eq_getElem?_getD]

/-- `B^(k−1) ≤ n` and `n < B^k` for the digit count `k` of `n ≠ 0`, in powers of `2`. -/
theorem digits_bounds {n : ℕ} (hn : n ≠ 0) :
    2 ^ (32 * ((Nat.digits Nock.Atoms.B n).length - 1)) ≤ n ∧
      n < 2 ^ (32 * (Nat.digits Nock.Atoms.B n).length) := by
  have hb : 1 < Nock.Atoms.B := Nock.Atoms.one_lt_B
  have hB : Nock.Atoms.B = 2 ^ 32 := rfl
  set k := (Nat.digits Nock.Atoms.B n).length with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (List.length_eq_zero_iff.mp h0) (Nat.digits_ne_nil_iff_ne_zero.mpr hn)
    · exact h0
  refine ⟨?_, ?_⟩
  · have h1 := Nat.base_pow_length_digits_le Nock.Atoms.B n hb hn
    rw [← hk] at h1
    have h2 : Nock.Atoms.B ^ k = Nock.Atoms.B * Nock.Atoms.B ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2] at h1
    have h3 : Nock.Atoms.B ^ (k - 1) ≤ n := Nat.le_of_mul_le_mul_left h1 (by omega)
    rwa [hB, ← pow_mul] at h3
  · have := Nat.lt_base_pow_length_digits (b := Nock.Atoms.B) (m := n) hb
    rwa [← hk, hB, ← pow_mul] at this

/-- The digit identity: `n / 2^(32m) = n / 2^(32(m+1)) · 2^32 + n / 2^(32m) % 2^32`. -/
theorem div_step (n m : ℕ) : n / 2 ^ (32 * m) = n / 2 ^ (32 * (m + 1)) * 2 ^ 32 + n / 2 ^ (32 * m) % 2 ^ 32 := by
  have e : n / 2 ^ (32 * (m + 1)) = n / 2 ^ (32 * m) / 2 ^ 32 := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf
  rw [e, Nat.div_add_mod']

/-- **S3 `axisChain_sound`** (abstract rows): an accepted axis chain closing at `r`, with every limb consume
genuine at `WalkAOK9 V combN` and every path consume genuine at `RecOK`'s `.p` clause, provides a genuine
`TAG_ax` fact: `V R = some n`, `2^32 ≤ n`, the route0 value is `n`, and `slot n (D (1, hr)) = D hout`. -/
theorem axisChain_sound (hpG : p = Nock.Atoms.p) (A : AxTr E nX) {V : ℕ → Option ℕ}
    {D : LocalVSX.HX → Option Noun}
    (hL : ∀ i < nX, WalkAOK9 V combN [((E i).trace AxisChipJ9.R).val, ((E i).trace axK).val, 0,
      ((E i).trace AxisChipJ9.l).val])
    (hP : ∀ i < nX, (E i).trace z1a = 0 → ∃ Rt C, D (1, ((E i).trace hinv).val) = some Rt ∧
      D (((E i).trace houtk).val, ((E i).trace houtv).val) = some C ∧ Noun.slot ((E i).trace axS).val Rt = some C)
    {r : ℕ} (hr : r < nX) (hc : (E r).trace cl = 1) :
    ∃ n, V ((E r).trace AxisChipJ9.R).val = some n ∧ 2 ^ 32 ≤ n ∧
      ((E r).trace route0 = 1 → ((E r).trace AxisChipJ9.v).val = n) ∧
      ∃ X Y, D (1, ((E r).trace hrv).val) = some X ∧
        D (((E r).trace houtk).val, ((E r).trace houtv).val) = some Y ∧ Noun.slot n X = some Y := by
  have hp := hp63 hpG
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have := congrArg ZMod.val h0
    rw [ZMod.val_zero, show ((2 : ZMod p)) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  obtain ⟨h, hhr, hH, hgt, hcl⟩ := chainBack A hr hc
  have cR := chain_const A hr hcl AxisChipJ9.R (fun e He hc => (G6c He hc).2.2.1)
  have cHr := chain_const A hr hcl hrv (fun e He hc => (G6c He hc).2.2.2.1)
  have cR0 := chain_const A hr hcl route0 (fun e He hc => (G6c He hc).2.2.2.2.1)
  have cV := chain_const A hr hcl AxisChipJ9.v (fun e He hc => (G6c He hc).2.2.2.2.2)
  obtain ⟨n, hVn, -, -⟩ := hL r hr
  set L := Nat.digits Nock.Atoms.B n with hLdef
  have hS : ∀ j, h ≤ j → j ≤ r →
      Noun.slot ((E j).trace axK).val (combL L) = some (.atom ((E j).trace AxisChipJ9.l).val) := by
    intro j hj hjr
    obtain ⟨n', hn', h0', -⟩ := hL j (by omega)
    rw [cR j hj hjr, ← cR r hhr.le le_rfl, hVn] at hn'
    cases hn'
    exact h0' rfl
  have hpb := pw_back hpG A hr hc hgt hcl hS
  -- the head
  have HH := A.rows h (by omega)
  have hclh := hcl h le_rfl hhr
  obtain ⟨ipw, i63, -, -⟩ := hpb (r - (h + 1)) (by omega)
  rw [show r - (r - (h + 1)) = h + 1 by omega] at ipw
  have hpwh : (E h).trace pw = (2 : ZMod p) ^ (r - (h + 1) + 2) := by
    rw [G6p_head HH h2 hclh hH, A.next h (by omega), ipw]
  obtain ⟨-, hk, hlh⟩ := step_head hp HH hH (r - (h + 1) + 2) (by omega) i63 hpwh (hS h le_rfl hhr.le)
  have hLne : L ≠ [] := by intro h0; rw [h0] at hk; simp at hk
  have hn0 : n ≠ 0 := by intro h0; apply hLne; rw [hLdef, h0]; simp
  have hklen : L.length = r - h + 1 := by omega
  obtain ⟨hlo_n, hhi_n⟩ := digits_bounds hn0
  rw [← hLdef, hklen, show r - h + 1 - 1 = r - h by omega] at hlo_n
  rw [← hLdef, hklen] at hhi_n
  -- limbs
  have hlimb : ∀ j, h ≤ j → j ≤ r → ((E j).trace AxisChipJ9.l).val = n / 2 ^ (32 * (r - j)) % 2 ^ 32 := by
    intro j hj hjr
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · rw [hlh, getLast!_eq hLne, hklen, show r - h + 1 - 1 = r - h by omega, hLdef, limb_digit]
    · obtain ⟨-, -, -, hl⟩ := hpb (r - j) (by omega)
      rw [show r - (r - j) = j by omega] at hl
      rw [hl, hLdef, limb_digit]
  have hlB : ∀ j, h ≤ j → j ≤ r → ((E j).trace AxisChipJ9.l).val < Nock.Atoms.B := by
    intro j hj hjr; rw [hlimb j hj hjr]; exact Nat.mod_lt _ (by norm_num)
  have htop : n / 2 ^ (32 * (r - h)) = ((E h).trace AxisChipJ9.l).val := by
    rw [hlimb h le_rfl hhr.le, Nat.mod_eq_of_lt]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    rw [show 32 + 32 * (r - h) = 32 * (r - h + 1) by ring]; exact hhi_n
  have hB2 : 2 ^ 32 ≤ n := by
    calc 2 ^ 32 = 2 ^ (32 * 1) := rfl
      _ ≤ 2 ^ (32 * (r - h)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := hlo_n
  -- the root `X`
  have HG5 := (G5 HH).1 hH
  have hz1 : ∀ j, h < j → j ≤ r → (E j).trace z1a = 0 := by
    intro j hj hjr
    rcases (G1 (A.rows j (by omega))).2.2.1 with hz | hz
    · exact hz
    · exfalso
      have := (G4 (A.rows j (by omega)) hz).1
      rw [hgt j hj hjr] at this
      exact zero_ne_one this
  obtain ⟨X, hX⟩ : ∃ X, D (1, ((E h).trace hrv).val) = some X := by
    rcases (G1 HH).2.2.1 with hz | hz
    · obtain ⟨Rt, C, hRt, -, -⟩ := hP h (by omega) hz
      exact ⟨Rt, by rw [← HG5.1]; exact hRt⟩
    · obtain ⟨Rt, C, hRt, -, -⟩ := hP (h + 1) (by omega) (hz1 (h + 1) (by omega) (by omega))
      refine ⟨Rt, ?_⟩
      have e1 : (E (h + 1)).trace hinv = (E h).trace hrv := by
        rw [← A.next h (by omega), (G6c HH hclh).2.1, (G4 HH hz).2.2.2, HG5.1]
      rw [← e1]; exact hRt
  -- the forward composition
  have hfwd : ∀ t, t ≤ r - h → ∃ Y, D (((E (h + t)).trace houtk).val, ((E (h + t)).trace houtv).val) = some Y ∧
      Noun.slot (n / 2 ^ (32 * (r - h - t))) X = some Y := by
    intro t
    induction t with
    | zero =>
      intro _
      simp only [Nat.add_zero, Nat.sub_zero]
      rw [htop]
      rcases (G1 HH).2.2.1 with hz | hz
      · obtain ⟨Rt, C, hRt, hC, hsl⟩ := hP h (by omega) hz
        rw [HG5.1, hX] at hRt
        cases hRt
        refine ⟨C, hC, ?_⟩
        rw [← step_axS_head HH hH]; exact hsl
      · obtain ⟨-, hl1, hk1, hv1⟩ := G4 HH hz
        refine ⟨X, ?_, ?_⟩
        · rw [hk1, hv1, HG5.2, HG5.1, RowSemChipX.val_one']; exact hX
        · rw [hl1, RowSemChipX.val_one']; simp [Noun.slot]
    | succ t ih =>
      intro ht
      obtain ⟨Y, hY, hsl⟩ := ih (by omega)
      set j := h + (t + 1) with hjdef
      have hj' : h + t + 1 = j := by omega
      have Hj := A.rows j (by omega)
      have Ht := A.rows (h + t) (by omega)
      have hclt := hcl (h + t) (by omega) (by omega)
      have hzj := hz1 j (by omega) (by omega)
      have hhj := hgt j (by omega) (by omega)
      have hkj := (G5 Hj).2 hzj
      obtain ⟨ek, ev, -⟩ := G6c Ht hclt
      rw [A.next (h + t) (by omega), hj'] at ek ev
      obtain ⟨Rt, C, hRt, hC, hslj⟩ := hP j (by omega) hzj
      have hk1 : (E (h + t)).trace houtk = 1 := ek.symm.trans hkj
      rw [hk1, RowSemChipX.val_one'] at hY
      rw [ev] at hRt
      rw [hY] at hRt
      cases hRt
      refine ⟨C, hC, ?_⟩
      have hm : r - h - t = r - h - (t + 1) + 1 := by omega
      rw [hm] at hsl
      rw [div_step n (r - h - (t + 1)), Nock.J9A.NounComp.slot_comp _ _ _ _ ?_ (Nat.mod_lt _ (by norm_num)), hsl]
      · show Noun.slot (2 ^ 32 + n / 2 ^ (32 * (r - h - (t + 1))) % 2 ^ 32) Y = some C
        rw [← hslj, step_axS_nonhead hpG Hj hhj (hlB j (by omega) (by omega)), hlimb j (by omega) (by omega),
          show r - j = r - h - (t + 1) by omega]
        rfl
      · refine Nat.div_pos ?_ (Nat.two_pow_pos _)
        calc 2 ^ (32 * (r - h - (t + 1) + 1)) ≤ 2 ^ (32 * (r - h)) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ n := hlo_n
  obtain ⟨Y, hY, hsl⟩ := hfwd (r - h) le_rfl
  rw [show h + (r - h) = r by omega] at hY
  rw [Nat.sub_self, Nat.mul_zero, pow_zero, Nat.div_one] at hsl
  refine ⟨n, hVn, hB2, ?_, X, Y, ?_, hY, hsl⟩
  · -- route0
    intro h0
    have h0h : (E h).trace route0 = 1 := by rw [← cR0 r hhr.le le_rfl]; exact h0
    have hr0 : (E h).trace r0h = 1 := by rw [(G7 HH).1, h0h, hH, one_mul]
    have hlo' : ((E h).traceNext AxisChipJ9.l).val < Nock.Atoms.B := by
      rw [A.next h (by omega)]; exact hlB (h + 1) (by omega) (by omega)
    obtain ⟨hnc, hv, -⟩ := step_route0 hpG HH hr0 (hlB h le_rfl hhr.le) hlo'
    rw [A.next h (by omega)] at hnc hv
    have hrh : h + 1 = r := by
      by_contra hne
      have := hcl (h + 1) (by omega) (by omega)
      rw [hnc] at this; exact one_ne_zero this
    rw [cV r hhr.le le_rfl, hv, ← htop, hlimb (h + 1) (by omega) (by omega)]
    rw [← hrh, Nat.add_sub_cancel_left, Nat.sub_self, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mul_one,
      show Nock.Atoms.B = 2 ^ 32 from rfl]
    exact Nat.div_add_mod' n _
  · rw [cHr r hhr.le le_rfl]; exact hX

end Abstract

/-! ## Service pass 1: the weak obligation `Φ₀` -/

/-- **`Φ₀`**: a 4-entry service record meets `WalkAOK9 V combN`. -/
def Phi0 (V : ℕ → Option ℕ) : List ℕ × Bal → Prop := fun r => r.2 = .s → r.1.length = 4 → WalkAOK9 V combN r.1

/-- `RecOK9I` implies `Φ₀` (a 4-entry service record is class `2`, so its `PreI9` is vacuous). -/
theorem phi0_of_recOK9I {D : LocalVSX.HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry}
    {r : List ℕ × Bal} (h : RowSemChipX9.RecOK9I D V Rg combN r) : Phi0 V r := by
  obtain ⟨l, bl⟩ := r
  intro hs h4
  simp only at hs h4
  subst hs
  have hc : recClass (l, Bal.s) = 2 := by simp [recClass, h4]
  have := h (RowSemChipX9.pre9_cls (by rw [hc]; omega))
  unfold RecOK9 at this
  rw [if_neg (by rw [hc]; omega), if_pos hc] at this
  exact this

theorem provP_phi0_of_I {D : LocalVSX.HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry}
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {bl : Bal} {provs : List ((Fin (mOf bl) → K) × K)}
    (h : ProvP (p := p) (K := K) (RowSemChipX9.RecOK9I D V Rg combN) bl provs) :
    ProvP (p := p) (K := K) (Phi0 V) bl provs :=
  fun q hq l hl hlt hk => phi0_of_recOK9I (h q hq l hl hlt hk)

theorem provP_phi0_of_9 {D : LocalVSX.HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry}
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {bl : Bal} {provs : List ((Fin (mOf bl) → K) × K)}
    (h : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) bl provs) :
    ProvP (p := p) (K := K) (Phi0 V) bl provs :=
  fun q hq l hl hlt hk => phi0_of_recOK9I (fun _ => h q hq l hl hlt hk)

/-- **A key with a nonzero entry at `c ≥ 4` is never the key of a 4-entry list**, so `Φ₀` holds vacuously. -/
theorem provP_phi0_wide {V : ℕ → Option ℕ} {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {provs : List ((Fin (mOf .s) → K) × K)}
    (hw : ∀ q ∈ provs, ∃ c : Fin (mOf .s), 4 ≤ (c : ℕ) ∧ q.1 c ≠ 0) :
    ProvP (p := p) (K := K) (Phi0 V) .s provs := by
  intro q hq l hl hlt hk _ h4
  obtain ⟨c, hc4, hne⟩ := hw q hq
  exfalso
  apply hne
  rw [← hk]
  simp only [natKey]
  rw [List.getD_eq_default _ _ (by simp only at h4; omega)]
  simp

/-! ## The concrete axis chip -/

section Chip
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))]
  (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

/-- The axis rows, `ℕ`-indexed (row `0` past the end). -/
def axE : ℕ → Env (ZMod p) := fun i =>
  if hi : i < n then AxisChipJ9.axEF b nodes orbit chals pubs Q ⟨i, hi⟩
  else AxisChipJ9.axEF b nodes orbit chals pubs Q ⟨0, hn⟩

theorem axE_of_lt (i : ℕ) (hi : i < n) :
    axE δF b hn nodes orbit chals pubs Q i = AxisChipJ9.axEF b nodes orbit chals pubs Q ⟨i, hi⟩ := dif_pos hi

theorem axTr (hsat : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    AxTr (axE δF b hn nodes orbit chals pubs Q) n where
  rows := fun i hi => by
    rw [axE_of_lt δF b hn nodes orbit chals pubs Q i hi]
    exact AxisChipJ9.ax_rowEqs δF b hn nodes orbit chals pubs Q hsat ⟨i, hi⟩
  next := fun i hi j => by
    rw [axE_of_lt δF b hn nodes orbit chals pubs Q i (by omega), axE_of_lt δF b hn nodes orbit chals pubs Q (i + 1) hi]
    exact AxisChipJ9.axEF_next δF b hn nodes orbit chals pubs Q hadj ⟨i, by omega⟩ hi j
  first := fun h0 => by
    rw [axE_of_lt δF b hn nodes orbit chals pubs Q 0 h0]
    have := (AxisChipJ9.ax_masks δF b hn nodes orbit chals pubs Q hbind hinj ⟨0, h0⟩).1
    simpa using this
  last := fun i hi => by
    rw [axE_of_lt δF b hn nodes orbit chals pubs Q i (by omega)]
    have := (AxisChipJ9.ax_masks δF b hn nodes orbit chals pubs Q hbind hinj ⟨i, by omega⟩).2
    rw [this, if_neg (by simp only; omega)]

/-- The limb consume's `ℕ` record. -/
def limbNat (e : Env (ZMod p)) : List ℕ :=
  [(e.trace AxisChipJ9.R).val, (e.trace axK).val, 0, (e.trace AxisChipJ9.l).val]

/-- The path consume's `ℕ` record. -/
def pathNat (e : Env (ZMod p)) : List ℕ :=
  [(e.trace hinv).val, (e.trace axS).val, (e.trace houtk).val, (e.trace houtv).val]

/-- The `TAG_ax` provide's `ℕ` record. -/
def tagNat (e : Env (ZMod p)) : List ℕ :=
  [(e.trace hrv).val, (e.trace ftk).val, (e.trace ftv).val, (e.trace houtk).val, (e.trace houtv).val,
    (e.trace AxisChipJ9.R).val, 0, 5]

theorem limb_natKey (e : Env (ZMod p)) :
    natKey (p := p) (K := K) 8 (limbNat e) = AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey e := by
  funext c
  fin_cases c <;> simp [natKey, AxisChipJ9.keyVecL, AxisChipJ9.limbKey, limbNat, CoeffExpr.eval, cv]

theorem path_natKey (e : Env (ZMod p)) :
    natKey (p := p) (K := K) 5 (pathNat e) = AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey e := by
  funext c
  fin_cases c <;> simp [natKey, AxisChipJ9.keyVecL, AxisChipJ9.pathKey, pathNat, CoeffExpr.eval, cv]

theorem vals_lt {l : List (ZMod p)} : ∀ x ∈ l.map ZMod.val, x < p := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  exact ZMod.val_lt y

/-- Every row's limb key is in `axLimbReqs` (at any `chals'`/`pubs'` and the same trace). -/
theorem limbKey_mem (i : Fin n) :
    AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodes orbit chals pubs Q i) ∈
      AxisChipJ9.axLimbReqs b nodes orbit chals pubs Q :=
  List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- Every `z1a = 0` row's path key is in `axPathReqs`. -/
theorem pathKey_mem [DecidableEq (ZMod p)] (i : Fin n)
    (hz : (AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace z1a = 0) :
    AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodes orbit chals pubs Q i) ∈
      AxisChipJ9.axPathReqs b nodes orbit chals pubs Q := by
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
  rw [if_neg (by rw [hz, sub_zero]; exact one_ne_zero)]
  exact List.mem_singleton_self _

/-- **S1a (generic)**: a served ext key meets `Φ`. -/
theorem extP_of_served {bl : Bal} {provs : List ((Fin (mOf bl) → K) × K)} {ext : List (Fin (mOf bl) → K)}
    (hsv : ∀ c ∈ ext, c ∈ provs.map Prod.fst) {Φ : List ℕ × Bal → Prop}
    (hprov : ProvP (p := p) (K := K) Φ bl provs) :
    ∀ c ∈ ext, ∀ l : List ℕ, l.length ≤ mOf bl → (∀ e ∈ l, e < p) → natKey (p := p) (K := K) (mOf bl) l = c →
      Φ (l, bl) := by
  intro c hc l hl hlt hk
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hsv c hc)
  exact hprov q hq l hl hlt hk

/-- **S1 `served_limb_cons`**: if every limb consume key is a served ext key and the service providers meet `Φ`,
which implies `WalkAOK9` on 4-entry service records, every row's limb record meets `WalkAOK9`. -/
theorem served_limb_cons {V : ℕ → Option ℕ} {Φ : List ℕ × Bal → Prop}
    (hΦ : ∀ a b c d, Φ ([a, b, c, d], .s) → WalkAOK9 V combN [a, b, c, d])
    {provs : List ((Fin (mOf .s) → K) × K)} {ext : List (Fin (mOf .s) → K)}
    (hsv : ∀ c ∈ ext, c ∈ provs.map Prod.fst)
    (hsub : ∀ i : Fin n,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodes orbit chals pubs Q i) ∈ ext)
    (hprov : ProvP (p := p) (K := K) Φ .s provs) :
    ∀ i : Fin n, WalkAOK9 V combN (limbNat (AxisChipJ9.axEF b nodes orbit chals pubs Q i)) := by
  intro i
  set e := AxisChipJ9.axEF b nodes orbit chals pubs Q i
  have hc : AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey e ∈ ext := hsub i
  have := extP_of_served hsv hprov _ hc (limbNat e) (by simp [limbNat, mOf])
    (by intro x hx; simp only [limbNat, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> first | exact ZMod.val_lt _ | exact (Fact.out : p.Prime).pos)
    (limb_natKey e)
  exact hΦ _ _ _ _ this

/-- **S1 `served_path_cons`**: the path twin (activity `1 − z1a`). -/
theorem served_path_cons [DecidableEq (ZMod p)] {D : LocalVSX.HX → Option Noun} {Φ : List ℕ × Bal → Prop}
    (hΦ : ∀ a b c d, Φ ([a, b, c, d], .p) →
      ∃ Rt C, D (1, a) = some Rt ∧ D (c, d) = some C ∧ Noun.slot b Rt = some C)
    {provs : List ((Fin (mOf .p) → K) × K)} {ext : List (Fin (mOf .p) → K)}
    (hsv : ∀ c ∈ ext, c ∈ provs.map Prod.fst)
    (hsub : ∀ i : Fin n, (AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodes orbit chals pubs Q i) ∈ ext)
    (hprov : ProvP (p := p) (K := K) Φ .p provs) :
    ∀ i : Fin n, (AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace z1a = 0 →
      ∃ Rt C, D (1, ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace hinv).val) = some Rt ∧
        D (((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace houtk).val,
          ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace houtv).val) = some C ∧
        Noun.slot ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace axS).val Rt = some C := by
  intro i hz
  set e := AxisChipJ9.axEF b nodes orbit chals pubs Q i
  have hc : AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey e ∈ ext := hsub i hz
  have := extP_of_served hsv hprov _ hc (pathNat e) (by simp [pathNat, mOf])
    (by intro x hx; simp only [pathNat, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> exact ZMod.val_lt _)
    (path_natKey e)
  exact hΦ _ _ _ _ this

/-- **S3 at the chip**: `axisChain_sound` on the accepted axis trace. -/
theorem axisChain_sound_chip (hpG : p = Nock.Atoms.p)
    (hsat : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    {V : ℕ → Option ℕ} {D : LocalVSX.HX → Option Noun}
    (hL : ∀ i : Fin n, WalkAOK9 V combN (limbNat (AxisChipJ9.axEF b nodes orbit chals pubs Q i)))
    (hP : ∀ i : Fin n, (AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace z1a = 0 →
      ∃ Rt C, D (1, ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace hinv).val) = some Rt ∧
        D (((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace houtk).val,
          ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace houtv).val) = some C ∧
        Noun.slot ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace axS).val Rt = some C)
    (r : Fin n) (hc : (AxisChipJ9.axEF b nodes orbit chals pubs Q r).trace cl = 1) :
    ∃ n', V ((AxisChipJ9.axEF b nodes orbit chals pubs Q r).trace AxisChipJ9.R).val = some n' ∧ 2 ^ 32 ≤ n' ∧
      ((AxisChipJ9.axEF b nodes orbit chals pubs Q r).trace route0 = 1 →
        ((AxisChipJ9.axEF b nodes orbit chals pubs Q r).trace AxisChipJ9.v).val = n') ∧
      ∃ X Y, D (1, ((AxisChipJ9.axEF b nodes orbit chals pubs Q r).trace hrv).val) = some X ∧
        D (((AxisChipJ9.axEF b nodes orbit chals pubs Q r).trace houtk).val,
          ((AxisChipJ9.axEF b nodes orbit chals pubs Q r).trace houtv).val) = some Y ∧ Noun.slot n' X = some Y := by
  have A := axTr δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj
  have e := axE_of_lt δF b hn nodes orbit chals pubs Q r r.2
  have hL' : ∀ i < n, WalkAOK9 V combN [((axE δF b hn nodes orbit chals pubs Q i).trace AxisChipJ9.R).val,
      ((axE δF b hn nodes orbit chals pubs Q i).trace axK).val, 0,
      ((axE δF b hn nodes orbit chals pubs Q i).trace AxisChipJ9.l).val] := by
    intro i hi; rw [axE_of_lt δF b hn nodes orbit chals pubs Q i hi]; exact hL ⟨i, hi⟩
  have hP' : ∀ i < n, (axE δF b hn nodes orbit chals pubs Q i).trace z1a = 0 →
      ∃ Rt C, D (1, ((axE δF b hn nodes orbit chals pubs Q i).trace hinv).val) = some Rt ∧
        D (((axE δF b hn nodes orbit chals pubs Q i).trace houtk).val,
          ((axE δF b hn nodes orbit chals pubs Q i).trace houtv).val) = some C ∧
        Noun.slot ((axE δF b hn nodes orbit chals pubs Q i).trace axS).val Rt = some C := by
    intro i hi; rw [axE_of_lt δF b hn nodes orbit chals pubs Q i hi]; exact hP ⟨i, hi⟩
  have := axisChain_sound hpG A hL' hP' r.2 (by rw [e]; exact hc)
  rw [e] at this
  exact this

/-- **S4 `provP_TAGax`**: every `TAG_ax` provide meets `RecOK9` (the design's cond. 4 `TagAxOK`), from S3 and
`DenOKX9`'s `atom` / `k2` clauses (the `hden2` fact is not needed: `k2` is `hagree`). -/
theorem provP_TAGax [DecidableEq (ZMod p)] (hpG : p = Nock.Atoms.p)
    (hsat : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    {V : ℕ → Option ℕ} {D : LocalVSX.HX → Option Noun} (Rg : Nock.Jet.Registry) (hD : DenOKX9 p D V)
    (hL : ∀ i : Fin n, WalkAOK9 V combN (limbNat (AxisChipJ9.axEF b nodes orbit chals pubs Q i)))
    (hP : ∀ i : Fin n, (AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace z1a = 0 →
      ∃ Rt C, D (1, ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace hinv).val) = some Rt ∧
        D (((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace houtk).val,
          ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace houtv).val) = some C ∧
        Noun.slot ((AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace axS).val Rt = some C) :
    ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s (AxisChipJ9.axTagProvs b nodes orbit chals pubs Q) := by
  intro q hq l hlen hlt hkey
  obtain ⟨i, hmu, rfl⟩ := AxisChipJ9.axTagProvs_mu b nodes orbit chals pubs Q q hq
  set e := AxisChipJ9.axEF b nodes orbit chals pubs Q i with he
  have H := AxisChipJ9.ax_rowEqs δF b hn nodes orbit chals pubs Q hsat i
  have hcl := cl_of_mu H hmu
  have hp5 : 5 < p := by have := hp63 hpG; omega
  -- the key, entrywise
  have hent : ∀ c : Fin 8, ((l.getD c 0 : ℕ) : ZMod p) = ((tagNat e).getD c 0 : ℕ) := by
    intro c
    have h1 := congrFun hkey c
    simp only [natKey] at h1
    have h2 := (algebraMap (ZMod p) K).injective h1
    rw [h2]
    fin_cases c <;> simp [AxisChipJ9.keyVecL, AxisChipJ9.tagKey, tagNat, CoeffExpr.eval, cv, AxisChipJ9.tagAx]
  have hgetD : ∀ c : Fin 8, l.getD c 0 = (tagNat e).getD c 0 := by
    intro c
    have hl : l.getD c 0 < p := by
      rcases Nat.lt_or_ge (c : ℕ) l.length with hcl | hcl
      · rw [List.getD_eq_getElem _ _ hcl]; exact hlt _ (List.getElem_mem hcl)
      · rw [List.getD_eq_default _ _ hcl]; exact (Fact.out : p.Prime).pos
    have hr : (tagNat e).getD c 0 < p := by
      fin_cases c <;> simp [tagNat] <;> first | exact ZMod.val_lt _ | omega
    have := hent c
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] at this
    exact this
  have hl8 : l.length = 8 := by
    by_contra hne
    have h7 := hgetD 7
    rw [List.getD_eq_default _ _ (by simp only [DenXJ8.mOf] at hlen; omega)] at h7
    simp [tagNat] at h7
  have hlE : l = tagNat e := by
    apply List.ext_getElem (by rw [hl8]; rfl)
    intro j hj1 hj2
    have := hgetD ⟨j, by omega⟩
    simp only at this
    rwa [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hj2] at this
  subst hlE
  -- S3 at row `i`
  obtain ⟨n', hVn, hB, hr0, X, Y, hX, hY, hsl⟩ :=
    axisChain_sound_chip δF b hn nodes orbit chals pubs Q hpG hsat hbind hinj hadj hL hP i hcl
  have hc1 : recClass (tagNat e, Bal.s) = 1 := by simp [recClass, tagNat]
  unfold RecOK9
  rw [if_pos hc1]
  show ∀ m, D ((e.trace ftk).val, (e.trace ftv).val) = some (.atom m) →
      V (e.trace AxisChipJ9.R).val = some m ∧ 2 ^ 32 ≤ m ∧
        ∃ X Y, D (1, (e.trace hrv).val) = some X ∧ D ((e.trace houtk).val, (e.trace houtv).val) = some Y ∧
          Noun.slot m X = some Y
  intro m hm
  have hmn : m = n' := by
    rcases (G1 H).2.2.2 with h0 | h1
    · obtain ⟨hk, hv⟩ := (G8_route H).2 h0
      rw [hk, hv, RowSemChipX9.val_two (by omega)] at hm
      have := hD.k2 _ _ hm
      rw [hVn] at this
      exact (Option.some.inj this).symm
    · obtain ⟨hk, hv⟩ := (G8_route H).1 h1
      rw [hk, hv, ZMod.val_zero, hD.base.atom] at hm
      have := Option.some.inj hm
      cases this
      exact hr0 h1
  subst hmn
  exact ⟨hVn, hB, X, Y, hX, hY, hsl⟩

/-- **Service pass 1 for `TAG_ax`**: the tag entry `5` makes `Φ₀` vacuous. -/
theorem provP_phi0_TAGax [DecidableEq (ZMod p)] (hp5 : 5 < p) {V : ℕ → Option ℕ} :
    ProvP (p := p) (K := K) (Phi0 V) .s (AxisChipJ9.axTagProvs b nodes orbit chals pubs Q) := by
  refine provP_phi0_wide fun q hq => ?_
  obtain ⟨i, -, rfl⟩ := AxisChipJ9.axTagProvs_mu b nodes orbit chals pubs Q q hq
  refine ⟨⟨7, by simp [mOf]⟩, by simp, ?_⟩
  simp only [AxisChipJ9.keyVecL, AxisChipJ9.tagKey, AxisChipJ9.tagAx]
  simp only [List.getD_cons_succ, List.getD_cons_zero, CoeffExpr.eval, ne_eq, map_eq_zero]
  intro h0
  have := congrArg ZMod.val h0
  rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hp5] at this
  omega

/-- **The two-pass service assembly at the axis chip.** The `.s` provider list
`jet ++ inc ++ walk ++ TAG_ax ++ split`: the J-8 providers at `RecOK9I` (J-9 B's obligations), the atom walk and
the split at `RecOK9` (`ProvNewX9.provP_walkV9`, `provP_split`).  Pass 1 (`Φ₀`): every limb consume is genuine
(`served_limb_cons`); with the path consumes (`served_path_cons`), S3 and S4 make `TAG_ax` genuine; pass 2: the
whole list meets `RecOK9I`. -/
theorem provP_service9 [DecidableEq (ZMod p)] (hpG : p = Nock.Atoms.p)
    (hsat : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    {V : ℕ → Option ℕ} {D : LocalVSX.HX → Option Noun} (Rg : Nock.Jet.Registry) (hD : DenOKX9 p D V)
    {pJ pI pW pS : List ((Fin 8 → K) × K)}
    (hJ : ProvP (p := p) (K := K) (RowSemChipX9.RecOK9I D V Rg combN) .s pJ)
    (hI : ProvP (p := p) (K := K) (RowSemChipX9.RecOK9I D V Rg combN) .s pI)
    (hW : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    {extS : List (Fin 8 → K)}
    (hsvS : ∀ c ∈ extS, c ∈ (pJ ++ pI ++ pW ++ AxisChipJ9.axTagProvs b nodes orbit chals pubs Q ++ pS).map Prod.fst)
    (hsubS : ∀ i : Fin n,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodes orbit chals pubs Q i) ∈ extS)
    {Φp : List ℕ × Bal → Prop}
    (hΦp : ∀ a b c d, Φp ([a, b, c, d], .p) →
      ∃ Rt C, D (1, a) = some Rt ∧ D (c, d) = some C ∧ Noun.slot b Rt = some C)
    {pP : List ((Fin (mOf .p) → K) × K)} {extP : List (Fin (mOf .p) → K)}
    (hsvP : ∀ c ∈ extP, c ∈ pP.map Prod.fst)
    (hsubP : ∀ i : Fin n, (AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodes orbit chals pubs Q i) ∈ extP)
    (hP : ProvP (p := p) (K := K) Φp .p pP) :
    ProvP (p := p) (K := K) (RowSemChipX9.RecOK9I D V Rg combN) .s
      (pJ ++ pI ++ pW ++ AxisChipJ9.axTagProvs b nodes orbit chals pubs Q ++ pS) := by
  have hp5 : 5 < p := by have := hp63 hpG; omega
  -- pass 1
  have h0 : ProvP (p := p) (K := K) (Phi0 V) .s
      (pJ ++ pI ++ pW ++ AxisChipJ9.axTagProvs b nodes orbit chals pubs Q ++ pS) := by
    refine ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr
      ⟨ServiceJ8.provP_append.mpr ⟨provP_phi0_of_I hJ, provP_phi0_of_I hI⟩, provP_phi0_of_9 hW⟩,
      provP_phi0_TAGax δF b hn nodes orbit chals pubs Q hp5⟩, provP_phi0_of_9 hS⟩
  have hL := served_limb_cons δF b hn nodes orbit chals pubs Q
    (fun a b c d h => h rfl rfl) hsvS hsubS h0
  have hPP := served_path_cons δF b hn nodes orbit chals pubs Q hΦp hsvP hsubP hP
  have hT := provP_TAGax δF b hn nodes orbit chals pubs Q hpG hsat hbind hinj hadj Rg hD hL hPP
  -- pass 2
  have hI9 : ∀ {pl : List ((Fin 8 → K) × K)}, ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pl →
      ProvP (p := p) (K := K) (RowSemChipX9.RecOK9I D V Rg combN) .s pl :=
    fun h q hq l hl hlt hk _ => h q hq l hl hlt hk
  exact ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr
    ⟨ServiceJ8.provP_append.mpr ⟨hJ, hI⟩, hI9 hW⟩, hI9 hT⟩, hI9 hS⟩

end Chip

#print axioms chainBack
#print axioms pw_back
#print axioms axisChain_sound
#print axioms axisChain_sound_chip
#print axioms served_limb_cons
#print axioms served_path_cons
#print axioms provP_TAGax
#print axioms provP_phi0_TAGax
#print axioms provP_service9

end

end Nock.NockVMROM.Thm54.VclL.Handle.AxisSoundX9
