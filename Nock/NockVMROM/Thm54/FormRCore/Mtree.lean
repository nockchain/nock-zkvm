/-
  Nock/NockVMROM/Thm54/FormRCore/Mtree.lean

  Same names
  (`Nock.RedTeam.Batch575.*`): `Y`, `scale`, `Tpoly`, `C'poly`, `formRPw`, `formRCounts`,
  `UniqueExponents`, `Paired`, `Padding`, the path / coefficient lemmas (S1),
  `formR_counts_zero_iff` (S2's identity) and S3 (`degY_le`, `formR_event_card`,
  `formR_work_vs_majorant`).
-/
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.NockVMROM.Thm54.FormRCore.PwFunctional
import Nock.NockVMROM.Thm54.FormRCore.PwEvent
import Nock.NockVMROM.Thm54.FormRCore.Majorant

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch575

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch554
  (vpaths rpaths addrP addrPFrom addrP_append addrP_nil addrP_ne_zero addrP_coeff_length
    bitsOf bitsOf_length Cpoly bracket bracket_zero_iff bracket_zero_prefix
    cross_root_both_nonzero bit honestTree honestTree_paths place)
open Polynomial

variable {K : Type*} [Field K]

/-! ## Form R accumulators on `MTree` -/

noncomputable def Y : Polynomial K := X
noncomputable def scale (n : ℕ) : Polynomial K := Y ^ (n - 1)
noncomputable def Tpoly (m : ℕ) : Polynomial K := Y ^ m
noncomputable def C'poly (n : ℕ) (c : ℕ → Bool) : Polynomial K := Cpoly (n - 1) c

noncomputable def formRPw (n : ℕ) (mm : ℕ → ℕ) : MTree K → (Polynomial K)[X]
  | .halt => 0
  | .decompose L R => C Y * (formRPw n mm L + formRPw n mm R)
  | .read e ch => formRPw n mm ch - C (scale n * Tpoly (mm e)) * X ^ e
  | .verify e _ ch => formRPw n mm ch + C (scale n) * X ^ e

noncomputable def formRCounts (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) : MTree K → (Polynomial K)[X]
  | .halt => 0
  | .decompose L R =>
      formRCounts n mm cc L + formRCounts n mm cc R
        + C (Y - 1) * (formRPw n mm L + formRPw n mm R) + formRPw n mm R
  | .read e ch => formRCounts n mm cc ch - C (Tpoly (mm e) * C'poly n (cc e)) * X ^ e
  | .verify e _ ch => formRCounts n mm cc ch + C (scale n) * X ^ e

omit [Field K] in
def UniqueExponents {K : Type*} (t : MTree K) : Prop :=
  ∀ e, readCount e t ≤ 1 ∧ verifyCount e t ≤ 1

omit [Field K] in
def Paired {K : Type*} (e : ℕ) (t : MTree K) : Prop :=
  readCount e t = 1 ∧ verifyCount e t = 1

def Padding (n m : ℕ) (c : ℕ → Bool) : Prop :=
  ∀ j, m < j → j ≤ n - 1 → c j = false

theorem Cpoly_false (n : ℕ) : Cpoly (K := K) n (fun _ => false) = (X : Polynomial K) ^ n := by
  unfold Cpoly
  have h0 :
      ∑ j ∈ Finset.range n,
          C (bit (K := K) false) * (X : Polynomial K) ^ (n - (j + 1)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j _
    simp [bit]
  rw [h0, add_zero]

omit [Field K] in
theorem list_length_eq_one {α : Type*} {l : List α} (h : l.length = 1) : ∃ x, l = [x] := by
  cases l with
  | nil => simp at h
  | cons x xs =>
      cases xs with
      | nil => exact ⟨x, rfl⟩
      | cons _ _ => simp at h

/-! ## Paths -/

omit [Field K] in
theorem vpaths_length (e : ℕ) : ∀ t : MTree K, (vpaths e t).length = verifyCount e t
  | .halt => rfl
  | .decompose L R => by
      simp [vpaths, verifyCount, vpaths_length e L, vpaths_length e R, List.length_map]
  | .read _ ch => by simp [vpaths, verifyCount, vpaths_length e ch]
  | .verify e' _ ch => by
      simp [vpaths, verifyCount, vpaths_length e ch]
      split_ifs <;> simp

omit [Field K] in
theorem rpaths_length (e : ℕ) : ∀ t : MTree K, (rpaths e t).length = readCount e t
  | .halt => rfl
  | .decompose L R => by
      simp [rpaths, readCount, rpaths_length e L, rpaths_length e R, List.length_map]
  | .read e' ch => by
      simp [rpaths, readCount, rpaths_length e ch]
      split_ifs <;> simp
  | .verify _ _ ch => by simp [rpaths, readCount, rpaths_length e ch]

omit [Field K] in
theorem vpaths_eq_nil (e : ℕ) (t : MTree K) (h : verifyCount e t = 0) : vpaths e t = [] :=
  List.eq_nil_of_length_eq_zero (by rw [vpaths_length, h])

omit [Field K] in
theorem rpaths_eq_nil (e : ℕ) (t : MTree K) (h : readCount e t = 0) : rpaths e t = [] :=
  List.eq_nil_of_length_eq_zero (by rw [rpaths_length, h])

omit [Field K] in
theorem vpaths_singleton (e : ℕ) (t : MTree K) (h : verifyCount e t = 1) :
    ∃ v, vpaths e t = [v] :=
  list_length_eq_one (by rw [vpaths_length, h])

omit [Field K] in
theorem rpaths_singleton (e : ℕ) (t : MTree K) (h : readCount e t = 1) :
    ∃ r, rpaths e t = [r] :=
  list_length_eq_one (by rw [rpaths_length, h])

/-! ## Path-sum algebra at `Y` -/

noncomputable def sumAddrP (L : List (List Bool)) : Polynomial K := (L.map addrP).sum
noncomputable def sumPowP (L : List (List Bool)) : Polynomial K := (L.map fun p => Y ^ p.length).sum

theorem addrP_cons (b : Bool) (p : List Bool) :
    addrP (K := K) (b :: p)
      = addrP p + (X : K[X]) ^ p.length * (X - 1 + C (bit b)) := by
  rw [show b :: p = [b] ++ p from rfl, addrP_append]
  have hb : addrP (K := K) [b] = X + C (bit b) := by
    simp [addrP, addrPFrom]
  rw [hb]; ring

theorem sumAddrP_shift (b : Bool) (L : List (List Bool)) :
    sumAddrP (K := K) (L.map (b :: ·))
      = sumAddrP L + (Y - 1 + C (bit b)) * sumPowP L := by
  induction L with
  | nil => simp [sumAddrP, sumPowP]
  | cons p L ih =>
      simp only [List.map_cons, sumAddrP, sumPowP, List.sum_cons] at ih ⊢
      rw [addrP_cons, ih, Y]; ring

theorem sumPowP_shift (b : Bool) (L : List (List Bool)) :
    sumPowP (K := K) (L.map (b :: ·)) = Y * sumPowP L := by
  induction L with
  | nil => simp [sumPowP]
  | cons p L ih =>
      simp only [List.map_cons, sumPowP, List.sum_cons, List.length_cons, pow_succ, Y] at ih ⊢
      rw [ih]; ring

theorem sumAddrP_append (L L' : List (List Bool)) :
    sumAddrP (K := K) (L ++ L') = sumAddrP L + sumAddrP L' := by simp [sumAddrP]
theorem sumPowP_append (L L' : List (List Bool)) :
    sumPowP (K := K) (L ++ L') = sumPowP L + sumPowP L' := by simp [sumPowP]

/-! ## S1 — per-exponent coefficients -/

theorem coeff_const_X_pow (a : Polynomial K) (e k : ℕ) :
    ((C a * (X : (Polynomial K)[X]) ^ e).coeff k) = if k = e then a else 0 := by
  simp [coeff_C_mul, coeff_X_pow]

theorem coeff_formR (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e : ℕ) :
    ∀ t : MTree K,
      (formRPw n mm t).coeff e
          = scale n * sumPowP (vpaths e t)
            - scale n * Tpoly (mm e) * sumPowP (rpaths e t)
      ∧ (formRCounts n mm cc t).coeff e
          = scale n * sumAddrP (vpaths e t)
            - (Tpoly (mm e) * C'poly n (cc e) * ((rpaths e t).length : Polynomial K)
              + scale n * Tpoly (mm e)
                * (sumAddrP (rpaths e t) - ((rpaths e t).length : Polynomial K))) := by
  intro t
  induction t with
  | halt =>
      simp only [formRPw, formRCounts, vpaths, rpaths, sumAddrP, sumPowP, coeff_zero,
        List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, mul_zero, add_zero,
        sub_zero]
      constructor <;> trivial
  | decompose L R ihl ihr =>
      obtain ⟨hpl, hcl⟩ := ihl
      obtain ⟨hpr, hcr⟩ := ihr
      have hp : (formRPw n mm (.decompose L R)).coeff e
          = Y * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e) := by
        simp only [formRPw, coeff_C_mul, coeff_add]
      have hc : (formRCounts n mm cc (.decompose L R)).coeff e
          = (formRCounts n mm cc L).coeff e + (formRCounts n mm cc R).coeff e
            + (Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e)
            + (formRPw n mm R).coeff e := by
        simp only [formRCounts, coeff_add, coeff_C_mul]
      rw [hp, hc, hpl, hcl, hpr, hcr]
      simp only [vpaths, rpaths, sumAddrP_append, sumPowP_append, sumAddrP_shift, sumPowP_shift,
        List.length_append, List.length_map, bit]
      simp [C_0, C_1]
      push_cast
      constructor <;> ring
  | read e' ch ih =>
      obtain ⟨hp, hc⟩ := ih
      have hp' : (formRPw n mm (.read e' ch)).coeff e
          = (formRPw n mm ch).coeff e
            - if e = e' then scale n * Tpoly (mm e') else 0 := by
        simp only [formRPw, coeff_sub, coeff_const_X_pow]
      have hc' : (formRCounts n mm cc (.read e' ch)).coeff e
          = (formRCounts n mm cc ch).coeff e
            - if e = e' then Tpoly (mm e') * C'poly n (cc e') else 0 := by
        simp only [formRCounts, coeff_sub, coeff_const_X_pow]
      rw [hp', hc', hp, hc]
      by_cases h : e' = e
      · subst h
        simp [rpaths, vpaths, sumAddrP, sumPowP, addrP_nil, Y]
        constructor <;> ring
      · simp [rpaths, vpaths, h, Ne.symm h]
  | verify e' a ch ih =>
      obtain ⟨hp, hc⟩ := ih
      have hp' : (formRPw n mm (.verify e' a ch)).coeff e
          = (formRPw n mm ch).coeff e + if e = e' then scale n else 0 := by
        simp only [formRPw, coeff_add, coeff_const_X_pow]
      have hc' : (formRCounts n mm cc (.verify e' a ch)).coeff e
          = (formRCounts n mm cc ch).coeff e + if e = e' then scale n else 0 := by
        simp only [formRCounts, coeff_add, coeff_const_X_pow]
      rw [hp', hc', hp, hc]
      by_cases h : e' = e
      · subst h
        simp [rpaths, vpaths, sumAddrP, sumPowP, addrP_nil, Y]
        constructor <;> ring
      · simp [rpaths, vpaths, h, Ne.symm h]

theorem paired_bracket (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e : ℕ)
    (t : MTree K) (v r : List Bool)
    (hv : vpaths e t = [v]) (hr : rpaths e t = [r]) :
    (formRCounts n mm cc t).coeff e = bracket (n - 1) (mm e) (cc e) v r := by
  rw [(coeff_formR n mm cc e t).2, hv, hr]
  simp only [sumAddrP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.length_singleton, Nat.cast_one]
  unfold bracket C'poly scale Tpoly Y
  ring

theorem unpaired_verify_coeff (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e : ℕ)
    (t : MTree K) (v : List Bool) (hv : vpaths e t = [v]) (hr : rpaths e t = []) :
    (formRCounts n mm cc t).coeff e = scale n * addrP v := by
  rw [(coeff_formR n mm cc e t).2, hv, hr]
  simp [sumAddrP]

theorem unpaired_verify_ne (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e : ℕ)
    (t : MTree K) (v : List Bool) (hv : vpaths e t = [v]) (hr : rpaths e t = []) :
    (formRCounts n mm cc t).coeff e ≠ 0 := by
  rw [unpaired_verify_coeff n mm cc e t v hv hr]
  exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (addrP_ne_zero v)

theorem unpaired_read_coeff (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e : ℕ)
    (t : MTree K) (r : List Bool) (hv : vpaths e t = []) (hr : rpaths e t = [r]) :
    (formRCounts n mm cc t).coeff e
      = -(Tpoly (mm e) * (C'poly n (cc e) + scale n * (addrP r - 1))) := by
  rw [(coeff_formR n mm cc e t).2, hv, hr]
  simp only [sumAddrP, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, List.sum_nil,
    add_zero, List.length_singleton, Nat.cast_one]
  ring

theorem unpaired_read_ne (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e : ℕ)
    (t : MTree K) (r : List Bool) (hv : vpaths e t = []) (hr : rpaths e t = [r]) :
    (formRCounts n mm cc t).coeff e ≠ 0 := by
  rw [unpaired_read_coeff n mm cc e t r hv hr]
  simpa [Tpoly, C'poly, scale, Y] using
    (cross_root_both_nonzero (K := K) (n - 1) (mm e) (cc e) r []).1

theorem absent_coeff (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e : ℕ) (t : MTree K)
    (hr : readCount e t = 0) (hv : verifyCount e t = 0) :
    (formRCounts n mm cc t).coeff e = 0 := by
  rw [(coeff_formR n mm cc e t).2, vpaths_eq_nil e t hv, rpaths_eq_nil e t hr]
  simp [sumAddrP]

/-- **S1.** Under uniqueness, `B_e` is the bracket of the unique pair, or a nonzero
unpaired monomial, or `0` if `e` is absent. -/
theorem formR_coeff_cases (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e : ℕ)
    (t : MTree K) (hU : UniqueExponents t) :
    (readCount e t = 0 ∧ verifyCount e t = 0 ∧ (formRCounts n mm cc t).coeff e = 0)
    ∨ (readCount e t = 1 ∧ verifyCount e t = 1 ∧
        ∃ v r, vpaths e t = [v] ∧ rpaths e t = [r]
          ∧ (formRCounts n mm cc t).coeff e = bracket (n - 1) (mm e) (cc e) v r)
    ∨ (readCount e t = 0 ∧ verifyCount e t = 1 ∧ (formRCounts n mm cc t).coeff e ≠ 0)
    ∨ (readCount e t = 1 ∧ verifyCount e t = 0 ∧ (formRCounts n mm cc t).coeff e ≠ 0) := by
  have hr01 := Nat.le_one_iff_eq_zero_or_eq_one.mp (hU e).1
  have hv01 := Nat.le_one_iff_eq_zero_or_eq_one.mp (hU e).2
  rcases hr01 with hr0 | hr1
  · rcases hv01 with hv0 | hv1
    · exact Or.inl ⟨hr0, hv0, absent_coeff n mm cc e t hr0 hv0⟩
    · obtain ⟨v, hv'⟩ := vpaths_singleton e t hv1
      exact Or.inr (Or.inr (Or.inl ⟨hr0, hv1,
        unpaired_verify_ne n mm cc e t v hv' (rpaths_eq_nil e t hr0)⟩))
  · rcases hv01 with hv0 | hv1
    · obtain ⟨r, hr'⟩ := rpaths_singleton e t hr1
      exact Or.inr (Or.inr (Or.inr ⟨hr1, hv0,
        unpaired_read_ne n mm cc e t r (vpaths_eq_nil e t hv0) hr'⟩))
    · obtain ⟨v, hv'⟩ := vpaths_singleton e t hv1
      obtain ⟨r, hr'⟩ := rpaths_singleton e t hr1
      exact Or.inr (Or.inl ⟨hr1, hv1, v, r, hv', hr',
        paired_bracket n mm cc e t v r hv' hr'⟩)

/-! ## S2 — the identity that holds, and the Nested conjunct that does not -/

theorem counts_zero_iff_coeffs (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (t : MTree K) :
    formRCounts n mm cc t = 0 ↔ ∀ e, (formRCounts n mm cc t).coeff e = 0 := by
  constructor
  · intro h e; simp [h]
  · intro h; ext e; simp [h]

/-- The algebraic S2: `counts = 0` iff every *paired* exponent has padding and
`V = R ++ bitsOf`, and there are no unpaired reads/verifies.  **No `Nested` conjunct.**
`hm` is the certificate range `m_e ≤ n−1`. -/
theorem formR_counts_zero_iff (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool)
    (t : MTree K) (hU : UniqueExponents t) (hm : ∀ e, mm e ≤ n - 1) :
    formRCounts n mm cc t = 0
      ↔ (∀ e, readCount e t = verifyCount e t)
        ∧ ∀ e, Paired e t →
            Padding n (mm e) (cc e)
            ∧ ∃ r, rpaths e t = [r] ∧ vpaths e t = [r ++ bitsOf (mm e) (cc e)] := by
  constructor
  · intro hz
    have hB : ∀ e, (formRCounts n mm cc t).coeff e = 0 :=
      (counts_zero_iff_coeffs n mm cc t).mp hz
    constructor
    · intro e
      rcases formR_coeff_cases n mm cc e t hU with h | h | h | h
      · omega
      · omega
      · exact absurd (hB e) h.2.2
      · exact absurd (hB e) h.2.2
    · intro e ⟨hr, hv⟩
      obtain ⟨v, hv'⟩ := vpaths_singleton e t hv
      obtain ⟨r, hr'⟩ := rpaths_singleton e t hr
      have hbr : bracket (K := K) (n - 1) (mm e) (cc e) v r = 0 := by
        have hpe :
            (formRCounts n mm cc t).coeff e
              = bracket (K := K) (n - 1) (mm e) (cc e) v r :=
          paired_bracket (K := K) n mm cc e t v r hv' hr'
        rw [hB e] at hpe
        exact hpe.symm
      obtain ⟨hpad, hpath⟩ := (bracket_zero_iff (n - 1) (mm e) (cc e) v r (hm e)).mp hbr
      exact ⟨hpad, r, hr', by rw [hv', hpath]⟩
  · intro ⟨hbal, hpair⟩
    apply (counts_zero_iff_coeffs n mm cc t).mpr
    intro e
    rcases formR_coeff_cases n mm cc e t hU with h | h | h | h
    · exact h.2.2
    · obtain ⟨v, r, hv', hr', hbr⟩ := h.2.2
      obtain ⟨hpad, r', hr2, hv2⟩ := hpair e ⟨h.1, h.2.1⟩
      have hrq : r' = r := by
        rw [hr'] at hr2
        exact (List.cons.inj hr2).1.symm
      have hvq : v = r ++ bitsOf (mm e) (cc e) := by
        rw [hv'] at hv2; rw [hrq] at hv2
        exact (List.cons.inj hv2).1
      rw [hbr]
      exact (bracket_zero_iff (n - 1) (mm e) (cc e) v r (hm e)).mpr ⟨hpad, hvq⟩
    · have : readCount e t = verifyCount e t := hbal e
      omega
    · have : readCount e t = verifyCount e t := hbal e
      omega

/-! ## S3 — degree and the bivariate event (honest form) -/

def decompCount : MTree K → ℕ
  | .halt => 0
  | .decompose L R => decompCount L + decompCount R + 1
  | .read _ ch => decompCount ch
  | .verify _ _ ch => decompCount ch

def nodeCount : MTree K → ℕ
  | .halt => 1
  | .decompose L R => nodeCount L + nodeCount R + 1
  | .read _ ch => nodeCount ch + 1
  | .verify _ _ ch => nodeCount ch + 1

theorem decompCount_le_nodeCount : ∀ t : MTree K, decompCount t ≤ nodeCount t
  | .halt => by simp [decompCount, nodeCount]
  | .decompose L R => by
      have := decompCount_le_nodeCount L
      have := decompCount_le_nodeCount R
      simp [decompCount, nodeCount]; omega
  | .read _ ch => by
      have := decompCount_le_nodeCount ch
      simp [decompCount, nodeCount]; omega
  | .verify _ _ ch => by
      have := decompCount_le_nodeCount ch
      simp [decompCount, nodeCount]; omega

theorem natDegree_scale (n : ℕ) : (scale (K := K) n).natDegree ≤ n - 1 := by
  simpa [scale, Y] using natDegree_X_pow_le (n - 1)

theorem natDegree_Tpoly (mm : ℕ) : (Tpoly (K := K) mm).natDegree ≤ mm := by
  simpa [Tpoly, Y] using natDegree_X_pow_le mm

theorem natDegree_C'poly (n : ℕ) (c : ℕ → Bool) :
    (C'poly (K := K) n c).natDegree ≤ n - 1 := by
  unfold C'poly Cpoly
  refine (natDegree_add_le _ _).trans ?_
  refine max_le (natDegree_X_pow_le (n - 1)) ?_
  refine (natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le fun j _ =>
    (natDegree_C_mul_le _ _).trans <|
      (natDegree_X_pow_le (n - 1 - (j + 1))).trans (by omega)

theorem natDegree_formRPw_coeff (n : ℕ) (mm : ℕ → ℕ) (hmm : ∀ e, mm e ≤ n - 1) (e : ℕ) :
    ∀ t : MTree K, ((formRPw n mm t).coeff e).natDegree ≤ decompCount t + 2 * (n - 1) := by
  intro t
  induction t with
  | halt => simp [formRPw]
  | decompose L R ihl ihr =>
      have hp : (formRPw n mm (.decompose L R)).coeff e
          = Y * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e) := by
        simp only [formRPw, coeff_C_mul, coeff_add]
      rw [hp]
      have hadd := natDegree_add_le ((formRPw n mm L).coeff e) ((formRPw n mm R).coeff e)
      have hmul := natDegree_mul_le (p := (X : Polynomial K))
        (q := (formRPw n mm L).coeff e + (formRPw n mm R).coeff e)
      simp only [decompCount, Y, natDegree_X] at hmul ⊢
      omega
  | read e' ch ih =>
      have hp : (formRPw n mm (.read e' ch)).coeff e
          = (formRPw n mm ch).coeff e
            - if e = e' then scale n * Tpoly (mm e') else 0 := by
        simp only [formRPw, coeff_sub, coeff_const_X_pow]
      rw [hp]
      refine (natDegree_sub_le _ _).trans ?_
      simp only [decompCount]
      split_ifs with _he
      · have hs : (scale n * Tpoly (mm e')).natDegree ≤ 2 * (n - 1) :=
          (natDegree_mul_le (p := scale n) (q := Tpoly (mm e'))).trans (by
            have := natDegree_scale (K := K) n
            have := natDegree_Tpoly (K := K) (mm e')
            have := hmm e'
            omega)
        omega
      · simp; omega
  | verify e' a ch ih =>
      have hp : (formRPw n mm (.verify e' a ch)).coeff e
          = (formRPw n mm ch).coeff e + if e = e' then scale n else 0 := by
        simp only [formRPw, coeff_add, coeff_const_X_pow]
      rw [hp]
      refine (natDegree_add_le _ _).trans ?_
      simp [decompCount]
      split_ifs
      · have := natDegree_scale (K := K) n; omega
      · simp; omega

theorem natDegree_formRCounts_coeff (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool)
    (hmm : ∀ e, mm e ≤ n - 1) (e : ℕ) :
    ∀ t : MTree K,
      ((formRCounts n mm cc t).coeff e).natDegree ≤ decompCount t + 2 * (n - 1) := by
  intro t
  induction t with
  | halt => simp [formRCounts]
  | decompose L R ihl ihr =>
      have hc : (formRCounts n mm cc (.decompose L R)).coeff e
          = (formRCounts n mm cc L).coeff e + (formRCounts n mm cc R).coeff e
            + (Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e)
            + (formRPw n mm R).coeff e := by
        simp only [formRCounts, coeff_add, coeff_C_mul]
      rw [hc]
      have hpwL := natDegree_formRPw_coeff n mm hmm e L
      have hpwR := natDegree_formRPw_coeff n mm hmm e R
      have hY : (Y - 1 : Polynomial K).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (by simp [Y, natDegree_X, natDegree_one])
      have hmul : ((Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e)).natDegree
          ≤ 1 + max (decompCount L + 2 * (n - 1)) (decompCount R + 2 * (n - 1)) := by
        refine (natDegree_mul_le (p := Y - 1)
          (q := (formRPw n mm L).coeff e + (formRPw n mm R).coeff e)).trans ?_
        have := natDegree_add_le ((formRPw n mm L).coeff e) ((formRPw n mm R).coeff e)
        omega
      have h1 := natDegree_add_le
        ((formRCounts n mm cc L).coeff e + (formRCounts n mm cc R).coeff e
          + (Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e))
        ((formRPw n mm R).coeff e)
      have h2 := natDegree_add_le
        ((formRCounts n mm cc L).coeff e + (formRCounts n mm cc R).coeff e)
        ((Y - 1) * ((formRPw n mm L).coeff e + (formRPw n mm R).coeff e))
      have h3 := natDegree_add_le
        ((formRCounts n mm cc L).coeff e) ((formRCounts n mm cc R).coeff e)
      simp [decompCount] at ihl ihr hpwL hpwR hmul h1 h2 h3 ⊢
      omega
  | read e' ch ih =>
      have hc : (formRCounts n mm cc (.read e' ch)).coeff e
          = (formRCounts n mm cc ch).coeff e
            - if e = e' then Tpoly (mm e') * C'poly n (cc e') else 0 := by
        simp only [formRCounts, coeff_sub, coeff_const_X_pow]
      rw [hc]
      refine (natDegree_sub_le _ _).trans ?_
      simp [decompCount]
      split_ifs
      · have : (Tpoly (mm e') * C'poly n (cc e')).natDegree ≤ 2 * (n - 1) :=
          (natDegree_mul_le (p := Tpoly (mm e')) (q := C'poly n (cc e'))).trans (by
            have := natDegree_Tpoly (K := K) (mm e')
            have := natDegree_C'poly (K := K) n (cc e')
            have := hmm e'
            omega)
        omega
      · simp; omega
  | verify e' a ch ih =>
      have hc : (formRCounts n mm cc (.verify e' a ch)).coeff e
          = (formRCounts n mm cc ch).coeff e + if e = e' then scale n else 0 := by
        simp only [formRCounts, coeff_add, coeff_const_X_pow]
      rw [hc]
      refine (natDegree_add_le _ _).trans ?_
      simp [decompCount]
      split_ifs
      · have := natDegree_scale (K := K) n; omega
      · simp; omega

/-- Honest `deg_Y B_e` bound: `decompCount + 2(n−1)`, and `decompCount ≤ nodeCount`
so the authority's `2(n−1)+M` majorises this when `M` counts memory rows. -/
theorem degY_le (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool)
    (hmm : ∀ e, mm e ≤ n - 1) (e : ℕ) (t : MTree K) :
    ((formRCounts n mm cc t).coeff e).natDegree ≤ 2 * (n - 1) + nodeCount t := by
  have := natDegree_formRCounts_coeff n mm cc hmm e t
  have := decompCount_le_nodeCount t
  omega

/-- **S3, honest event form.**  For nonzero `counts`, pick any nonzero coefficient
`B_{e₀}`; then
`#{(α,λ) : F_E(α,λ)=0} ≤ |K| · (deg_Y B_{e₀} + E)`
where `F_E = Σ_{k≤E} α^k B_k(λ)` is the degree-`E` envelope of `counts`
(authority: `E ≤ 3N+3`) and `deg_Y B_{e₀} ≤ 2(n−1)+M` (`M = nodeCount`).
The majorant
`pwAccountingWork' = M+3N+2(n−1)+4` is `deg_Y + E` plus one spare; we do not
fit the number. -/
theorem formR_event_card [Fintype K] [DecidableEq K]
    (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (t : MTree K)
    (e₀ : ℕ) (hB : (formRCounts n mm cc t).coeff e₀ ≠ 0) (E : ℕ)
    (hE0 : e₀ ≤ E) :
    (Finset.univ.filter fun p : K × K =>
        Batch556.F (Finset.range (E + 1)) id
          (fun e => (formRCounts n mm cc t).coeff e) p.1 p.2 = 0).card
      ≤ Fintype.card K * (((formRCounts n mm cc t).coeff e₀).natDegree + E) := by
  let s : Finset ℕ := Finset.range (E + 1)
  let Q : ℕ → Polynomial K := fun e => (formRCounts n mm cc t).coeff e
  have hinj : Set.InjOn (id : ℕ → ℕ) s := fun _ _ _ _ h => h
  have hE' : ∀ k ∈ s, id k ≤ E :=
    fun k hk => Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk₀ : e₀ ∈ s := Finset.mem_range.mpr (Nat.lt_succ_of_le hE0)
  exact Batch556.bivariate_bad_card_le (K := K) s id Q E hinj hE' e₀ hk₀ hB

theorem formR_support_le_envelope (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool)
    (t : MTree K) (E : ℕ) (hE : (formRCounts n mm cc t).natDegree ≤ E) :
    (formRCounts n mm cc t).support ⊆ Finset.range (E + 1) := by
  intro k hk
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_natDegree_of_mem_supp k hk).trans hE))

/-- Compare the honest numerator to `pwAccountingWork'`.  Slack of `1` is disclosed,
not absorbed. -/
theorem formR_work_vs_majorant (n N M dQ E : ℕ)
    (hd : dQ ≤ 2 * (n - 1) + M) (hE : E ≤ 3 * N + 3) :
    dQ + E ≤ Batch557.pwAccountingWork' n N M
    ∧ dQ + E + 1 ≤ Batch557.pwAccountingWork' n N M := by
  constructor
  · unfold Batch557.pwAccountingWork'; omega
  · exact Batch557.pwAccountingWork'_majorises n N M dQ E hd hE

end Nock.RedTeam.Batch575
