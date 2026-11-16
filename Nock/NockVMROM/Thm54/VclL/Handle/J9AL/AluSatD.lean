/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSatD.lean

  **The honest ALU gate satisfaction for `div` / `mod`.**
  Part A: pure list math (evaluation of the coefficient lists, coefficient formulas,
  carry bounds with a position-aware head).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluHonestRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSatD

open Nock Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.Jet.Prim (PrimOp)

/-! ## A. List math -/

theorem evB_eq_evR (B : ℤ) : ∀ l : List ℤ, evB B l = evR B l
  | [] => by simp [evB, evR]
  | d :: ds => by simp [evB, evR, evB_eq_evR B ds]

theorem evR_map_mul {R : Type} [CommRing R] (y : R) (a : ℤ) :
    ∀ l : List ℤ, evR y (l.map (a * ·)) = (a : R) * evR y l
  | [] => by simp [evR]
  | d :: ds => by simp [evR, evR_map_mul y a ds]; ring

theorem evR_mulL {R : Type} [CommRing R] (y : R) :
    ∀ as bs : List ℤ, evR y (mulL as bs) = evR y as * evR y bs
  | [], bs => by simp [mulL, evR]
  | a :: as, bs => by
    simp only [mulL, evR_addL, evR_map_mul, evR, evR_mulL y as bs]
    push_cast; ring

theorem evR_wL {R : Type} [CommRing R] (y : R) (A Bs : List ℕ) :
    evR y (wL A Bs) = evR y (zl A) * evR y (zl Bs) +
      (y - ((Bn : ℤ) : R)) * (evR y (zl (hiL A)) * evR y (zl (hiL Bs))) := by
  simp only [wL, evR_addL, evR_mulL]
  simp [evR]; ring

theorem addL_getD : ∀ (as bs : List ℤ) (k : ℕ),
    (addL as bs).getD k 0 = as.getD k 0 + bs.getD k 0
  | [], bs, k => by simp [addL]
  | a :: as, [], k => by simp [addL]
  | a :: as, b :: bs, 0 => by simp only [addL, List.getD_cons_zero]
  | a :: as, b :: bs, k + 1 => by
    simp only [addL, List.getD_cons_succ]; exact addL_getD as bs k

theorem negL_getD : ∀ (as : List ℤ) (k : ℕ), (negL as).getD k 0 = -as.getD k 0
  | [], k => by simp [negL]
  | a :: as, 0 => by simp [negL]
  | a :: as, k + 1 => by
    have := negL_getD as k
    simpa [negL] using this

theorem map_mul_getD (a : ℤ) : ∀ (bs : List ℤ) (k : ℕ), (bs.map (a * ·)).getD k 0 = a * bs.getD k 0
  | [], k => by simp
  | b :: bs, 0 => by simp
  | b :: bs, k + 1 => by
    have := map_mul_getD a bs k
    simpa using this

theorem mulL_getD : ∀ (as bs : List ℤ) (k : ℕ),
    (mulL as bs).getD k 0 = ∑ i ∈ Finset.range (k + 1), as.getD i 0 * bs.getD (k - i) 0
  | [], bs, k => by simp [mulL]
  | a :: as, bs, 0 => by
    simp only [mulL]; rw [addL_getD, map_mul_getD]; simp
  | a :: as, bs, k + 1 => by
    simp only [mulL, addL_getD, map_mul_getD]
    rw [Finset.sum_range_succ' _ (k + 1)]
    have ih := mulL_getD as bs k
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_sub_add_right, Nat.sub_zero]
    rw [← ih]
    simp [add_comm]

theorem mulX_getD (B : ℤ) (P : List ℤ) (k : ℕ) :
    (mulL [-B, 1] P).getD k 0 = -B * P.getD k 0 + (if k = 0 then 0 else P.getD (k - 1) 0) := by
  have h1 : mulL [1] P = addL (P.map (1 * ·)) [0] := by simp [mulL]
  have h2 : mulL [-B, 1] P = addL (P.map (-B * ·)) (0 :: addL (P.map (1 * ·)) [0]) := by
    simp [mulL, h1]
  rw [h2, addL_getD, map_mul_getD]
  rcases k with _ | k
  · simp
  · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [addL_getD, map_mul_getD]
    have : ([0] : List ℤ).getD k 0 = 0 := by
      cases k <;> simp
    rw [this]; ring

theorem zl_getD : ∀ (l : List ℕ) (k : ℕ), (zl l).getD k 0 = ((l.getD k 0 : ℕ) : ℤ)
  | [], k => by simp [zl]
  | a :: as, 0 => by simp [zl]
  | a :: as, k + 1 => by
    have := zl_getD as k
    simpa [zl] using this

theorem hiL_getD (l : List ℕ) (k : ℕ) : (hiL l).getD k 0 = l.getD k 0 / 2 ^ 16 := by
  induction l generalizing k with
  | nil => simp [hiL]
  | cons a as ih =>
    cases k with
    | zero => simp [hiL]
    | succ k => simpa [hiL] using ih k

/-! ### Coefficients of `wL` and their bounds -/

def aI (A : List ℕ) (i : ℕ) : ℤ := ((A.getD i 0 : ℕ) : ℤ)
def hI (A : List ℕ) (i : ℕ) : ℤ := ((A.getD i 0 / 2 ^ 16 : ℕ) : ℤ)

theorem wL_getD (A Bs : List ℕ) (k : ℕ) :
    (wL A Bs).getD k 0 =
      (∑ i ∈ Finset.range (k + 1), (aI A i * aI Bs (k - i) - (Bn : ℤ) * (hI A i * hI Bs (k - i)))) +
        (if k = 0 then 0 else ∑ i ∈ Finset.range k, hI A i * hI Bs (k - 1 - i)) := by
  have hP : ∀ m, (mulL (zl (hiL A)) (zl (hiL Bs))).getD m 0 =
      ∑ i ∈ Finset.range (m + 1), hI A i * hI Bs (m - i) := by
    intro m; rw [mulL_getD]; simp only [zl_getD, hiL_getD, hI]
  have hQ : (mulL (zl A) (zl Bs)).getD k 0 = ∑ i ∈ Finset.range (k + 1), aI A i * aI Bs (k - i) := by
    rw [mulL_getD]; simp only [zl_getD, aI]
  simp only [wL]
  rw [addL_getD, mulX_getD, hQ, hP, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rcases k with _ | k
  · simp; ring
  · rw [hP (k + 1 - 1)]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]; ring

theorem getD_lt_of_forall (A : List ℕ) (hA : ∀ w ∈ A, w < 2 ^ 32) (i : ℕ) : A.getD i 0 < 2 ^ 32 := by
  by_cases h : i < A.length
  · rw [List.getD_eq_getElem _ _ h]; exact hA _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; norm_num

theorem term_bound (x y : ℕ) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    0 ≤ (x : ℤ) * y - (Bn : ℤ) * (((x / 2 ^ 16 : ℕ) : ℤ) * ((y / 2 ^ 16 : ℕ) : ℤ)) ∧
    (x : ℤ) * y - (Bn : ℤ) * (((x / 2 ^ 16 : ℕ) : ℤ) * ((y / 2 ^ 16 : ℕ) : ℤ)) ≤ 2 ^ 49 := by
  have hBn : ((Bn : ℕ) : ℤ) = 2 ^ 32 := by norm_num [Bn]
  rw [hBn]
  have hx' := Nat.div_add_mod x (2 ^ 16)
  have hy' := Nat.div_add_mod y (2 ^ 16)
  have hxl := Nat.mod_lt x (show 0 < 2 ^ 16 by norm_num)
  have hyl := Nat.mod_lt y (show 0 < 2 ^ 16 by norm_num)
  have hxh : x / 2 ^ 16 < 2 ^ 16 := by omega
  have hyh : y / 2 ^ 16 < 2 ^ 16 := by omega
  generalize x / 2 ^ 16 = h at *
  generalize y / 2 ^ 16 = h' at *
  generalize x % 2 ^ 16 = l at *
  generalize y % 2 ^ 16 = l' at *
  have ex : (x : ℤ) = 65536 * h + l := by exact_mod_cast hx'.symm
  have ey : (y : ℤ) = 65536 * h' + l' := by exact_mod_cast hy'.symm
  have e : (x : ℤ) * y - 2 ^ 32 * ((h : ℤ) * h') = 65536 * (h * l' + l * h') + l * l' := by
    rw [ex, ey]; ring
  rw [e]
  have h1 : (h : ℤ) ≤ 65535 := by omega
  have h2 : (h' : ℤ) ≤ 65535 := by omega
  have h3 : (l : ℤ) ≤ 65535 := by omega
  have h4 : (l' : ℤ) ≤ 65535 := by omega
  have p1 : (h : ℤ) * l' ≤ 65535 * 65535 := mul_le_mul h1 h4 (by positivity) (by norm_num)
  have p2 : (l : ℤ) * h' ≤ 65535 * 65535 := mul_le_mul h3 h2 (by positivity) (by norm_num)
  have p3 : (l : ℤ) * l' ≤ 65535 * 65535 := mul_le_mul h3 h4 (by positivity) (by norm_num)
  constructor
  · positivity
  · nlinarith

theorem sum_cut {g : ℕ → ℤ} {cap : ℤ} (n : ℕ) (h0 : ∀ i, 0 ≤ g i ∧ g i ≤ cap)
    (hz : ∀ i, 62 ≤ i → g i = 0) :
    0 ≤ ∑ i ∈ Finset.range n, g i ∧ ∑ i ∈ Finset.range n, g i ≤ 62 * cap := by
  refine ⟨Finset.sum_nonneg fun i _ => (h0 i).1, ?_⟩
  have hcap : 0 ≤ cap := le_trans (h0 0).1 (h0 0).2
  calc ∑ i ∈ Finset.range n, g i
      = ∑ i ∈ (Finset.range n).filter (· < 62), g i :=
        (Finset.sum_filter_of_ne (fun i _ hi => by
          by_contra h; exact hi (hz i (by omega)))).symm
    _ ≤ ((Finset.range n).filter (· < 62)).card • cap :=
        Finset.sum_le_card_nsmul _ _ _ (fun i _ => (h0 i).2)
    _ ≤ 62 * cap := by
        have hc : ((Finset.range n).filter (· < 62)).card ≤ 62 := by
          calc ((Finset.range n).filter (· < 62)).card ≤ (Finset.range 62).card :=
                Finset.card_le_card (fun i hi => by
                  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; exact hi.2)
            _ = 62 := Finset.card_range 62
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hcap

theorem wL_coef_bound (A Bs : List ℕ) (hA : ∀ w ∈ A, w < 2 ^ 32) (hB : ∀ w ∈ Bs, w < 2 ^ 32)
    (hl : A.length ≤ 62) (k : ℕ) :
    0 ≤ (wL A Bs).getD k 0 ∧ (wL A Bs).getD k 0 ≤ 62 * 2 ^ 49 + 62 * 2 ^ 32 := by
  have hz : ∀ i, 62 ≤ i → A.getD i 0 = 0 := fun i hi => List.getD_eq_default _ _ (by omega)
  have s1 := sum_cut (g := fun i => aI A i * aI Bs (k - i) - (Bn : ℤ) * (hI A i * hI Bs (k - i)))
    (cap := 2 ^ 49) (k + 1)
    (fun i => by simpa [aI, hI] using term_bound _ _ (getD_lt_of_forall A hA i) (getD_lt_of_forall Bs hB (k - i)))
    (fun i hi => by simp only [aI, hI, hz i hi]; simp)
  have s2 : 0 ≤ (if k = 0 then 0 else ∑ i ∈ Finset.range k, hI A i * hI Bs (k - 1 - i)) ∧
      (if k = 0 then 0 else ∑ i ∈ Finset.range k, hI A i * hI Bs (k - 1 - i)) ≤ 62 * 2 ^ 32 := by
    split_ifs
    · norm_num
    · have := sum_cut (g := fun i => hI A i * hI Bs (k - 1 - i)) (cap := 2 ^ 32) k
        (fun i => by
          have a1 : A.getD i 0 / 2 ^ 16 < 2 ^ 16 := by
            have := getD_lt_of_forall A hA i; omega
          have b1 : Bs.getD (k - 1 - i) 0 / 2 ^ 16 < 2 ^ 16 := by
            have := getD_lt_of_forall Bs hB (k - 1 - i); omega
          have : (hI A i) * (hI Bs (k - 1 - i)) ≤ 2 ^ 16 * 2 ^ 16 := by
            unfold hI
            have c1 : (((A.getD i 0 / 2 ^ 16 : ℕ)) : ℤ) ≤ 2 ^ 16 := by exact_mod_cast a1.le
            have c2 : (((Bs.getD (k - 1 - i) 0 / 2 ^ 16 : ℕ)) : ℤ) ≤ 2 ^ 16 := by exact_mod_cast b1.le
            exact mul_le_mul c1 c2 (by positivity) (by norm_num)
          refine ⟨by unfold hI; positivity, by norm_num at this ⊢; linarith⟩)
        (fun i hi => by simp only [hI, hz i hi]; simp)
      exact this
  rw [wL_getD]
  constructor
  · linarith [s1.1, s2.1]
  · linarith [s1.2, s2.2]

/-! ### Carries with a position-aware head -/

theorem mem_exists_getD (l : List ℤ) (d : ℤ) (h : d ∈ l) : ∃ k, d = l.getD k 0 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨k, by rw [List.getD_eq_getElem _ _ hk]⟩

theorem carr_bound_pos {B M : ℤ} (hB : 0 < B) (d0 : ℤ) (ds : List ℤ)
    (h : evB B (d0 :: ds) = 0) (h0 : -B < d0 ∧ d0 < B * (M + 1))
    (hd : ∀ d ∈ ds, -B < d ∧ d + M < B * (M + 1)) : ∀ q ∈ carr B 0 (d0 :: ds), 0 ≤ q ∧ q ≤ M := by
  have h' : 0 + evB B (d0 :: ds) = 0 := by simpa using h
  obtain ⟨hcd, hrest⟩ := carr_step hB.ne' h'
  have hq0 : 0 ≤ (0 + d0) / B := by
    by_contra hneg
    replace hneg := not_le.mp hneg
    have : B * ((0 + d0) / B) ≤ B * (-1) := mul_le_mul_of_nonneg_left (by omega) hB.le
    linarith
  have hqM : (0 + d0) / B ≤ M := by
    by_contra hbig
    replace hbig := not_le.mp hbig
    have : B * (M + 1) ≤ B * ((0 + d0) / B) := mul_le_mul_of_nonneg_left (by omega) hB.le
    linarith
  intro q hq
  simp only [carr, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact ⟨hq0, hqM⟩
  · exact carr_bound hB ds _ hrest hq0 hqM hd q hq

theorem carr_bound_pos' {B M : ℤ} (hB : 0 < B) (ds : List ℤ) (h : evB B ds = 0)
    (h0 : -B < ds.getD 0 0 ∧ ds.getD 0 0 < B * (M + 1))
    (hd : ∀ k, 1 ≤ k → -B < ds.getD k 0 ∧ ds.getD k 0 + M < B * (M + 1)) :
    ∀ q ∈ carr B 0 ds, 0 ≤ q ∧ q ≤ M := by
  cases ds with
  | nil => intro q hq; simp [carr] at hq
  | cons d0 ds =>
    refine carr_bound_pos hB d0 ds h (by simpa using h0) ?_
    intro d hd'
    obtain ⟨k, rfl⟩ := mem_exists_getD ds d hd'
    simpa using hd (k + 1) (by omega)

/-! ### Values of limb lists -/

theorem evB_zl : ∀ l : List ℕ, evB (Bn : ℤ) (zl l) = ((Nock.Atoms.val l : ℕ) : ℤ)
  | [] => by simp [zl, evB]
  | a :: l => by
    have := evB_zl l
    simp only [zl, List.map_cons, evB] at this ⊢
    rw [this, Nock.Atoms.val_cons]
    simp [Nock.Atoms.B, Bn]

theorem evB_wL (A Bs : List ℕ) :
    evB (Bn : ℤ) (wL A Bs) = ((Nock.Atoms.val A * Nock.Atoms.val Bs : ℕ) : ℤ) := by
  rw [evB_eq_evR, evR_wL]
  have h1 : evR ((Bn : ℤ)) (zl A) = evB (Bn : ℤ) (zl A) := (evB_eq_evR _ _).symm
  have h2 : evR ((Bn : ℤ)) (zl Bs) = evB (Bn : ℤ) (zl Bs) := (evB_eq_evR _ _).symm
  rw [h1, h2, evB_zl, evB_zl]
  simp

theorem evB_ds1 (X Bv Y A : List ℕ) :
    evB (Bn : ℤ) (addL (addL (wL X Bv) (zl Y)) (negL (zl A))) =
      ((Nock.Atoms.val X * Nock.Atoms.val Bv : ℕ) : ℤ) + (Nock.Atoms.val Y : ℤ) - (Nock.Atoms.val A : ℤ) := by
  rw [evB_addL, evB_addL, evB_negL, evB_wL, evB_zl, evB_zl]; ring

theorem evB_ds2 (Y S Bv : List ℕ) :
    evB (Bn : ℤ) (addL (addL (addL (zl Y) (zl S)) [1]) (negL (zl Bv))) =
      (Nock.Atoms.val Y : ℤ) + (Nock.Atoms.val S : ℤ) + 1 - (Nock.Atoms.val Bv : ℤ) := by
  rw [evB_addL, evB_addL, evB_addL, evB_negL, evB_zl, evB_zl, evB_zl]
  simp [evB]; ring

/-- The carries of the `S1` identity (K at 25 bits) are in `[0, 2^25 − 1]`. -/
theorem ds1_carries (X Bv Y A : List ℕ) (hX : ∀ w ∈ X, w < 2 ^ 32) (hB : ∀ w ∈ Bv, w < 2 ^ 32)
    (hY : ∀ w ∈ Y, w < 2 ^ 32) (hA : ∀ w ∈ A, w < 2 ^ 32) (hl : X.length ≤ 62)
    (hv : Nock.Atoms.val X * Nock.Atoms.val Bv + Nock.Atoms.val Y = Nock.Atoms.val A) :
    ∀ q ∈ carr (Bn : ℤ) 0 (addL (addL (wL X Bv) (zl Y)) (negL (zl A))), 0 ≤ q ∧ q ≤ 2 ^ 25 - 1 := by
  have hBn : ((Bn : ℕ) : ℤ) = 2 ^ 32 := by norm_num [Bn]
  refine carr_bound0 (by rw [hBn]; norm_num) (by norm_num) _ ?_ ?_
  · rw [evB_ds1]; have h := congrArg (Nat.cast : ℕ → ℤ) hv; push_cast at h ⊢; linarith
  · intro d hd
    obtain ⟨k, rfl⟩ := mem_exists_getD _ d hd
    rw [addL_getD, addL_getD, negL_getD, zl_getD, zl_getD]
    have b1 := wL_coef_bound X Bv hX hB hl k
    have b2 := getD_lt_of_forall Y hY k
    have b3 := getD_lt_of_forall A hA k
    rw [hBn]
    have c2 : ((Y.getD k 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast b2
    have c3 : ((A.getD k 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast b3
    have c2' : (0 : ℤ) ≤ ((Y.getD k 0 : ℕ) : ℤ) := by positivity
    have c3' : (0 : ℤ) ≤ ((A.getD k 0 : ℕ) : ℤ) := by positivity
    constructor <;> nlinarith [b1.1, b1.2]

/-- The carries of the `S2` identity (K₂ at 1 bit), with the `+[1]` at `k = 0`: position-aware. -/
theorem ds2_carries (Y S Bv : List ℕ) (hY : ∀ w ∈ Y, w < 2 ^ 32) (hS : ∀ w ∈ S, w < 2 ^ 32)
    (hB : ∀ w ∈ Bv, w < 2 ^ 32)
    (hv : Nock.Atoms.val Y + Nock.Atoms.val S + 1 = Nock.Atoms.val Bv) :
    ∀ q ∈ carr (Bn : ℤ) 0 (addL (addL (addL (zl Y) (zl S)) [1]) (negL (zl Bv))), 0 ≤ q ∧ q ≤ 1 := by
  have hBn : ((Bn : ℕ) : ℤ) = 2 ^ 32 := by norm_num [Bn]
  have hget : ∀ k, (addL (addL (addL (zl Y) (zl S)) [1]) (negL (zl Bv))).getD k 0 =
      ((Y.getD k 0 : ℕ) : ℤ) + ((S.getD k 0 : ℕ) : ℤ) + (if k = 0 then 1 else 0) - ((Bv.getD k 0 : ℕ) : ℤ) := by
    intro k
    rw [addL_getD, addL_getD, addL_getD, negL_getD, zl_getD, zl_getD, zl_getD]
    have : ([1] : List ℤ).getD k 0 = if k = 0 then 1 else 0 := by
      cases k <;> simp
    rw [this]; ring
  refine carr_bound_pos' (by rw [hBn]; norm_num) _ ?_ ?_ ?_
  · rw [evB_ds2]; have h := congrArg (Nat.cast : ℕ → ℤ) hv; push_cast at h ⊢; linarith
  · rw [hget, hBn]
    have b1 := getD_lt_of_forall Y hY 0
    have b2 := getD_lt_of_forall S hS 0
    have b3 := getD_lt_of_forall Bv hB 0
    have : ((Y.getD 0 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast b1
    have : ((S.getD 0 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast b2
    have : ((Bv.getD 0 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast b3
    rw [if_pos rfl]
    constructor <;> omega
  · intro k hk
    rw [hget, hBn]
    have b1 := getD_lt_of_forall Y hY k
    have b2 := getD_lt_of_forall S hS k
    have b3 := getD_lt_of_forall Bv hB k
    have : ((Y.getD k 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast b1
    have : ((S.getD k 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast b2
    have : ((Bv.getD k 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast b3
    have hk0 : k ≠ 0 := by omega
    simp only [hk0, if_false]
    constructor <;> omega

/-! ## B. The slots of a div/mod call -/

theorem val_wordsOf (v : ℕ) : Nock.Atoms.val (wordsOf v) = v := by
  unfold wordsOf; split_ifs with h
  · simp [h]
  · exact Nock.Atoms.val_limbs v

theorem wordsOf_lt (v : ℕ) : ∀ w ∈ wordsOf v, w < 2 ^ 32 := by
  unfold wordsOf; split_ifs
  · simp
  · intro w hw; exact (Nock.Atoms.limbs_canonical v).1 w hw

theorem wordsOf_ne_nil (v : ℕ) : wordsOf v ≠ [] := by
  unfold wordsOf; split_ifs with h
  · simp
  · exact Nat.digits_ne_nil_iff_ne_zero.mpr h

theorem val_splitOf (v : ℕ) : Nock.Atoms.val (splitOf v) = v := by
  simp only [splitOf, Nock.Atoms.val_cons, Nock.Atoms.val_nil]
  have : Nock.Atoms.B = Bn := rfl
  rw [this]; simpa using Nat.mod_add_div v Bn

theorem splitOf_lt (v : ℕ) (hv : v < Bn * Bn) : ∀ w ∈ splitOf v, w < 2 ^ 32 := by
  intro w hw
  simp only [splitOf, List.mem_cons, List.not_mem_nil, or_false] at hw
  have hB : Bn = 2 ^ 32 := rfl
  rcases hw with rfl | rfl
  · rw [← hB]; exact Nat.mod_lt _ (by norm_num [Bn])
  · rw [← hB]; exact (Nat.div_lt_iff_lt_mul (by norm_num [Bn])).mpr hv

/-- The facts about one slot used by this module. -/
structure SlotOK (s : SlotL) (r : ℕ) (v : ℕ) (cf : ℤ × ℤ) : Prop where
  role : s.role = some r
  cf1 : s.cf1 = cf.1
  cf2 : s.cf2 = cf.2
  vwlt : ∀ w ∈ s.vw, w < 2 ^ 32
  val : Nock.Atoms.val s.vw = v
  mode_le : s.mode ≤ 3
  ne : s.words ≠ []
  eqw : s.mode ≠ 0 → s.vw = s.words

theorem SlotOK.cast {s : SlotL} {r v v' : ℕ} {cf : ℤ × ℤ} (h : SlotOK s r v cf) (e : v = v') :
    SlotOK s r v' cf := e ▸ h

theorem handleSlot_ok (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) (hp : p ≤ Bn * Bn) (hp0 : 0 < p) :
    SlotOK (handleSlot p o lb r v k s) r v (coefOf o lb (some r)) ∧
      (isFactor o r = true → (handleSlot p o lb r v k s).mode ≠ 0) := by
  unfold handleSlot
  split_ifs with h1 h2
  · refine ⟨⟨rfl, rfl, rfl, splitOf_lt v (by omega), val_splitOf v, by simp, by simp [splitOf], fun _ => rfl⟩,
      fun _ => by simp⟩
  · refine ⟨⟨rfl, rfl, rfl, fun w hw => (Nock.Atoms.limbs_canonical v).1 w hw, Nock.Atoms.val_limbs v,
      by simp, ?_, fun _ => rfl⟩, fun _ => by simp⟩
    show Nock.Atoms.limbs v ≠ []
    exact Nat.digits_ne_nil_iff_ne_zero.mpr (show v ≠ 0 by omega)
  · refine ⟨⟨rfl, rfl, rfl, fun w hw => (Nock.Atoms.limbs_canonical v).1 w hw, Nock.Atoms.val_limbs v,
      by simp, by simp, fun h => absurd rfl h⟩, fun h => by simp_all⟩

theorem witSlot_ok (o : PrimOp) (lb r w : ℕ) :
    SlotOK (witSlot o lb r w) r w (coefOf o lb (some r)) ∧ (witSlot o lb r w).mode = 3 ∧
      (witSlot o lb r w).vw = (witSlot o lb r w).words := by
  refine ⟨⟨rfl, rfl, rfl, wordsOf_lt w, val_wordsOf w, by simp [witSlot], wordsOf_ne_nil w, fun _ => rfl⟩,
    rfl, rfl⟩

/-- The two honest coefficient lists. -/
def dsS1 (sX sB sY sA : SlotL) : List ℤ :=
  addL (addL (wL sX.vw sB.vw) (zl sY.vw)) (negL (zl sA.vw))
def dsS2 (sY sS sB : SlotL) : List ℤ :=
  addL (addL (addL (zl sY.vw) (zl sS.vw)) [1]) (negL (zl sB.vw))

/-- **The slots of a div/mod call**. -/
theorem dm_slots (p : ℕ) (cl : CallL) (hcl : CallOK p cl) (hop : cl.op = .div ∨ cl.op = .mod)
    (hp : p ≤ Bn * Bn) :
    ∃ sA sX sB sY sS : SlotL,
      slotsOf p cl = [sA, sX, sB, sY, sS, qSlot cl.op false (carr (Bn : ℤ) 0 (dsS1 sX sB sY sA)),
        qSlot cl.op true (carr (Bn : ℤ) 0 (dsS2 sY sS sB))] ∧
      SlotOK sA 0 cl.a (-1, 0) ∧ SlotOK sX 4 (cl.a / cl.b) (0, 0) ∧ SlotOK sB 1 cl.b (0, -1) ∧
      SlotOK sY 5 (cl.a % cl.b) (1, 1) ∧ SlotOK sS 6 (cl.b - cl.a % cl.b - 1) (0, 1) ∧
      (sX.mode = 1 ∨ sX.mode = 2 ∨ sX.mode = 3) ∧ (sB.mode = 1 ∨ sB.mode = 2 ∨ sB.mode = 3) ∧
      sS.mode = 3 ∧ sS.vw = sS.words ∧ 0 < cl.b := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num [Bn]) (le_of_lt hcl.hp)
  have hsem := hcl.sem
  have hAok := (handleSlot_ok p cl.op cl.lbv 0 cl.a cl.kA cl.vA hp hp0)
  have hBok := (handleSlot_ok p cl.op cl.lbv 1 cl.b cl.kB cl.vB hp hp0)
  have hlbv : cl.lbv = 0 := by
    unfold CallL.lbv; rcases hop with h | h <;> simp [h]
  have hSok := witSlot_ok cl.op cl.lbv 6 (cl.b - cl.a % cl.b - 1)
  have hfacB : (handleSlot p cl.op cl.lbv 1 cl.b cl.kB cl.vB).mode ≠ 0 := by
    apply hBok.2; rcases hop with h | h <;> simp [isFactor, h]
  have hSA : SlotOK (handleSlot p cl.op cl.lbv 0 cl.a cl.kA cl.vA) 0 cl.a (-1, 0) := by
    have := hAok.1; rcases hop with h | h <;> simpa [coefOf, h, hlbv] using this
  have hSB : SlotOK (handleSlot p cl.op cl.lbv 1 cl.b cl.kB cl.vB) 1 cl.b (0, -1) := by
    have := hBok.1; rcases hop with h | h <;> simpa [coefOf, h, hlbv] using this
  have hSS : SlotOK (witSlot cl.op cl.lbv 6 (cl.b - cl.a % cl.b - 1)) 6 (cl.b - cl.a % cl.b - 1) (0, 1) := by
    have := hSok.1; simpa [coefOf] using this
  rcases hop with h | h
  · -- div
    have hb : 0 < cl.b ∧ cl.a / cl.b = cl.c := by
      by_cases hb : 0 < cl.b
      · simp only [Nock.Jet.Prim.primSem, h, hb, if_true] at hsem
        exact ⟨hb, Option.some.inj hsem⟩
      · simp [Nock.Jet.Prim.primSem, h, hb] at hsem
    have hXok := handleSlot_ok p cl.op cl.lbv 4 cl.c cl.kE cl.vE hp hp0
    have hYok := witSlot_ok cl.op cl.lbv 5 (cl.a % cl.b)
    have hfacX : (handleSlot p cl.op cl.lbv 4 cl.c cl.kE cl.vE).mode ≠ 0 := by
      apply hXok.2; simp [isFactor, h]
    refine ⟨handleSlot p cl.op cl.lbv 0 cl.a cl.kA cl.vA, handleSlot p cl.op cl.lbv 4 cl.c cl.kE cl.vE,
      handleSlot p cl.op cl.lbv 1 cl.b cl.kB cl.vB, witSlot cl.op cl.lbv 5 (cl.a % cl.b),
      witSlot cl.op cl.lbv 6 (cl.b - cl.a % cl.b - 1), ?_, hSA, ?_, hSB, ?_, hSS, ?_, ?_, hSok.2.1, hSok.2.2, hb.1⟩
    · simp only [slotsOf, h, dsS1, dsS2]
    · have := hXok.1.cast hb.2.symm
      simpa [coefOf, h, hlbv] using this
    · have := hYok.1; simpa [coefOf, h, hlbv] using this
    · have := hXok.1.mode_le; omega
    · have := hBok.1.mode_le; omega
  · -- mod
    have hb : 0 < cl.b ∧ cl.a % cl.b = cl.c := by
      by_cases hb : 0 < cl.b
      · simp only [Nock.Jet.Prim.primSem, h, hb, if_true] at hsem
        exact ⟨hb, Option.some.inj hsem⟩
      · simp [Nock.Jet.Prim.primSem, h, hb] at hsem
    have hXok := witSlot_ok cl.op cl.lbv 4 (cl.a / cl.b)
    have hYok := handleSlot_ok p cl.op cl.lbv 5 cl.c cl.kE cl.vE hp hp0
    have hfacY : (handleSlot p cl.op cl.lbv 5 cl.c cl.kE cl.vE).mode ≠ 0 ∨ True := Or.inr trivial
    refine ⟨handleSlot p cl.op cl.lbv 0 cl.a cl.kA cl.vA, witSlot cl.op cl.lbv 4 (cl.a / cl.b),
      handleSlot p cl.op cl.lbv 1 cl.b cl.kB cl.vB, handleSlot p cl.op cl.lbv 5 cl.c cl.kE cl.vE,
      witSlot cl.op cl.lbv 6 (cl.b - cl.a % cl.b - 1), ?_, hSA, ?_, hSB, ?_, hSS, ?_, ?_, hSok.2.1, hSok.2.2, hb.1⟩
    · simp only [slotsOf, h, dsS1, dsS2, ← hb.2]
    · have := hXok.1; simpa [coefOf, h, hlbv] using this
    · have := hYok.1.cast hb.2.symm
      simpa [coefOf, h, hlbv] using this
    · right; right; exact hXok.2.1
    · have := hBok.1.mode_le; omega

/-! ## C. Row-level gate evaluation -/

section Rows
variable {F : Type} [Field F]

def rowsS (p : ℕ) (cl : CallL) (ss : List SlotL) : List (BRow F) := ss.flatMap (slotRows p cl)

theorem slotRows_length (p : ℕ) (cl : CallL) (s : SlotL) : (slotRows (F := F) p cl s).length = s.words.length := by
  simp [slotRows]

theorem slotRows_getD (p : ℕ) (cl : CallL) (s : SlotL) (j : ℕ) (hj : j < s.words.length) :
    (slotRows (F := F) p cl s).getD j BRow.zero = slotRow p cl s j := by
  rw [List.getD_eq_getElem _ _ (by simpa [slotRows_length] using hj)]
  simp [slotRows]

theorem rowsS_info (p : ℕ) (cl : CallL) : ∀ (ss : List SlotL), (∀ s ∈ ss, s.words ≠ []) →
    ∀ j, j < (rowsS (F := F) p cl ss).length →
    ∃ s ∈ ss, ∃ i, i < s.words.length ∧ (rowsS (F := F) p cl ss).getD j BRow.zero = slotRow p cl s i ∧
      (i + 1 < s.words.length → (rowsS (F := F) p cl ss).getD (j + 1) BRow.zero = slotRow p cl s (i + 1)) ∧
      (i + 1 = s.words.length →
        (j + 1 < (rowsS (F := F) p cl ss).length →
          ∃ s', (s, s') ∈ ss.zip ss.tail ∧ (rowsS (F := F) p cl ss).getD (j + 1) BRow.zero = slotRow p cl s' 0) ∧
        ((rowsS (F := F) p cl ss).length ≤ j + 1 → ss.getLast? = some s))
  | [], _, j, hj => by simp [rowsS] at hj
  | s :: rest, hne, j, hj => by
    have hn : 0 < s.words.length := List.length_pos_iff.mpr (hne s (List.mem_cons_self ..))
    have hrest : ∀ s ∈ rest, s.words ≠ [] := fun s' h => hne s' (List.mem_cons_of_mem _ h)
    have hlen : (rowsS (F := F) p cl (s :: rest)).length = s.words.length + (rowsS (F := F) p cl rest).length := by
      simp [rowsS, slotRows_length]
    have happ : rowsS (F := F) p cl (s :: rest) = slotRows p cl s ++ rowsS p cl rest := by simp [rowsS]
    by_cases hjn : j < s.words.length
    · refine ⟨s, List.mem_cons_self .., j, hjn, ?_, ?_, ?_⟩
      · rw [happ, List.getD_append _ _ _ _ (by simpa [slotRows_length] using hjn), slotRows_getD _ _ _ _ hjn]
      · intro h
        rw [happ, List.getD_append _ _ _ _ (by simpa [slotRows_length] using h), slotRows_getD _ _ _ _ h]
      · intro h
        cases rest with
        | nil =>
          refine ⟨fun h' => ?_, fun _ => by simp⟩
          rw [hlen] at h'; simp [rowsS] at h'; omega
        | cons s' rest' =>
          have hn' : 0 < s'.words.length := List.length_pos_iff.mpr (hne s' (by simp))
          refine ⟨fun _ => ⟨s', by simp, ?_⟩, fun h' => ?_⟩
          · rw [happ, List.getD_append_right _ _ _ _ (by simp [slotRows_length]; omega)]
            simp only [slotRows_length]
            rw [show j + 1 - s.words.length = 0 by omega]
            have : rowsS (F := F) p cl (s' :: rest') = slotRows p cl s' ++ rowsS p cl rest' := by simp [rowsS]
            rw [this, List.getD_append _ _ _ _ (by simpa [slotRows_length] using hn'), slotRows_getD _ _ _ _ hn']
          · exfalso; rw [hlen] at h'
            have : 0 < (rowsS (F := F) p cl (s' :: rest')).length := by
              rw [show rowsS (F := F) p cl (s' :: rest') = slotRows p cl s' ++ rowsS p cl rest' by simp [rowsS]]
              simp [slotRows_length]; omega
            omega
    · have hj' : j - s.words.length < (rowsS (F := F) p cl rest).length := by rw [hlen] at hj; omega
      obtain ⟨s0, hs0, i, hi, hrow, hnext, hlast⟩ := rowsS_info p cl rest hrest (j - s.words.length) hj'
      have hrestne : rest ≠ [] := by rintro rfl; simp at hs0
      refine ⟨s0, List.mem_cons_of_mem _ hs0, i, hi, ?_, ?_, ?_⟩
      · rw [happ, List.getD_append_right _ _ _ _ (by simp [slotRows_length]; omega)]
        simpa [slotRows_length] using hrow
      · intro h
        have := hnext h
        rw [happ, List.getD_append_right _ _ _ _ (by simp [slotRows_length]; omega)]
        simp only [slotRows_length]
        rw [show j + 1 - s.words.length = j - s.words.length + 1 by omega]; exact this
      · intro h
        obtain ⟨h1, h2⟩ := hlast h
        refine ⟨fun hlt => ?_, fun hle => ?_⟩
        · rw [hlen] at hlt
          obtain ⟨s', hs', hrw⟩ := h1 (by omega)
          refine ⟨s', ?_, ?_⟩
          · cases rest with
            | nil => exact absurd rfl hrestne
            | cons r0 rest'' =>
              simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
              right; simpa using hs'
          · rw [happ, List.getD_append_right _ _ _ _ (by simp [slotRows_length]; omega)]
            simp only [slotRows_length]
            rw [show j + 1 - s.words.length = j - s.words.length + 1 by omega]; exact hrw
        · rw [hlen] at hle
          have := h2 (by omega)
          cases rest with
          | nil => exact absurd rfl hrestne
          | cons r0 rest'' => simpa [List.getLast?_cons_cons] using this

def KShape (s : SlotL) : ℕ → Prop
  | 0 => s.role = some 0 ∧ s.mode ≤ 3
  | 1 => s.role = some 4 ∧ s.mode ≤ 3
  | 2 => s.role = some 1 ∧ s.mode ≤ 3
  | 3 => s.role = some 5 ∧ s.mode ≤ 3
  | 4 => s.role = some 6 ∧ s.mode ≤ 3
  | 5 => s.role = none ∧ s.mode = 5
  | _ => s.role = none ∧ s.mode = 4


theorem gSeq_pair0 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod)
    (s s' : SlotL) (hs : KShape s 0) (hs' : KShape s' (0 + 1)) (i : ℕ) (hi : i + 1 = s.words.length) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col (slotRow (F := F) p cl s' 0).col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm⟩ := hs
  obtain ⟨hr', hm'⟩ := hs'
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  have hn4 : (4 : ℕ) ≠ s'.mode := by omega
  have hn5 : (5 : ℕ) ≠ s'.mode := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hop with hop | hop <;>
    simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, notE, hop, opIx, hr, hr', hi, hm4, hm5, hn4, hn5]

theorem gSeq_pair1 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod)
    (s s' : SlotL) (hs : KShape s 1) (hs' : KShape s' (1 + 1)) (i : ℕ) (hi : i + 1 = s.words.length) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col (slotRow (F := F) p cl s' 0).col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm⟩ := hs
  obtain ⟨hr', hm'⟩ := hs'
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  have hn4 : (4 : ℕ) ≠ s'.mode := by omega
  have hn5 : (5 : ℕ) ≠ s'.mode := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hop with hop | hop <;>
    simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, notE, hop, opIx, hr, hr', hi, hm4, hm5, hn4, hn5]

theorem gSeq_pair2 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod)
    (s s' : SlotL) (hs : KShape s 2) (hs' : KShape s' (2 + 1)) (i : ℕ) (hi : i + 1 = s.words.length) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col (slotRow (F := F) p cl s' 0).col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm⟩ := hs
  obtain ⟨hr', hm'⟩ := hs'
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  have hn4 : (4 : ℕ) ≠ s'.mode := by omega
  have hn5 : (5 : ℕ) ≠ s'.mode := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hop with hop | hop <;>
    simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, notE, hop, opIx, hr, hr', hi, hm4, hm5, hn4, hn5]

theorem gSeq_pair3 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod)
    (s s' : SlotL) (hs : KShape s 3) (hs' : KShape s' (3 + 1)) (i : ℕ) (hi : i + 1 = s.words.length) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col (slotRow (F := F) p cl s' 0).col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm⟩ := hs
  obtain ⟨hr', hm'⟩ := hs'
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  have hn4 : (4 : ℕ) ≠ s'.mode := by omega
  have hn5 : (5 : ℕ) ≠ s'.mode := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hop with hop | hop <;>
    simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, notE, hop, opIx, hr, hr', hi, hm4, hm5, hn4, hn5]

theorem gSeq_pair4 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod)
    (s s' : SlotL) (hs : KShape s 4) (hs' : KShape s' (4 + 1)) (i : ℕ) (hi : i + 1 = s.words.length) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col (slotRow (F := F) p cl s' 0).col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm⟩ := hs
  obtain ⟨hr', hm'⟩ := hs'
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hop with hop | hop <;>
    simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, notE, hop, opIx, hr, hr', hi, hm4, hm5, hm']

theorem gSeq_pair5 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod)
    (s s' : SlotL) (hs : KShape s 5) (hs' : KShape s' (5 + 1)) (i : ℕ) (hi : i + 1 = s.words.length) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col (slotRow (F := F) p cl s' 0).col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm⟩ := hs
  obtain ⟨hr', hm'⟩ := hs'

  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hop with hop | hop <;>
    simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, notE, hop, opIx, hr, hr', hi, hm, hm']

theorem gSeq_pair (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (k : ℕ) (hk : k < 6)
    (s s' : SlotL) (hs : KShape s k) (hs' : KShape s' (k + 1)) (i : ℕ) (hi : i + 1 = s.words.length) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col (slotRow (F := F) p cl s' 0).col) = 0 := by
  interval_cases k
  · exact gSeq_pair0 p cl hop s s' hs hs' i hi
  · exact gSeq_pair1 p cl hop s s' hs hs' i hi
  · exact gSeq_pair2 p cl hop s s' hs hs' i hi
  · exact gSeq_pair3 p cl hop s s' hs hs' i hi
  · exact gSeq_pair4 p cl hop s s' hs hs' i hi
  · exact gSeq_pair5 p cl hop s s' hs hs' i hi

theorem gSeq_noeos (nxt cur : BRow F) (he : cur.eos = 0) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB cur.col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, he]

theorem gSeq_last (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (s : SlotL) (hs : KShape s 6)
    (i : ℕ) (hi : i + 1 = s.words.length) (nxt : BRow F) (hn : nxt.sL = 0) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm⟩ := hs
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hop with hop | hop <;>
    simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, notE, hop, opIx, hr, hi, hm, hn]

theorem gCoef_shape0 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (s : SlotL)
    (hs : s.role = some 0 ∧ s.cf1 = -1 ∧ s.cf2 = 0 ∧ s.mode ≤ 3) (i : ℕ) (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, h1, h2, hm⟩ := hs
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  by_cases hi : i = 0
  · subst hi
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hop with hop | hop <;>
      simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, AluSZChipJ9.sgnLt, notE, hop, opIx, hr, h1, h2, hm4, hm5]
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, hi]

theorem gCoef_shape1 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (s : SlotL)
    (hs : s.role = some 1 ∧ s.cf1 = 0 ∧ s.cf2 = -1 ∧ s.mode ≤ 3) (i : ℕ) (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, h1, h2, hm⟩ := hs
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  by_cases hi : i = 0
  · subst hi
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hop with hop | hop <;>
      simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, AluSZChipJ9.sgnLt, notE, hop, opIx, hr, h1, h2, hm4, hm5]
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, hi]

theorem gCoef_shape2 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (s : SlotL)
    (hs : s.role = some 4 ∧ s.cf1 = 0 ∧ s.cf2 = 0 ∧ s.mode ≤ 3) (i : ℕ) (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, h1, h2, hm⟩ := hs
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  by_cases hi : i = 0
  · subst hi
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hop with hop | hop <;>
      simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, AluSZChipJ9.sgnLt, notE, hop, opIx, hr, h1, h2, hm4, hm5]
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, hi]

theorem gCoef_shape3 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (s : SlotL)
    (hs : s.role = some 5 ∧ s.cf1 = 1 ∧ s.cf2 = 1 ∧ s.mode ≤ 3) (i : ℕ) (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, h1, h2, hm⟩ := hs
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  by_cases hi : i = 0
  · subst hi
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hop with hop | hop <;>
      simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, AluSZChipJ9.sgnLt, notE, hop, opIx, hr, h1, h2, hm4, hm5]
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, hi]

theorem gCoef_shape4 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (s : SlotL)
    (hs : s.role = some 6 ∧ s.cf1 = 0 ∧ s.cf2 = 1 ∧ s.mode ≤ 3) (i : ℕ) (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, h1, h2, hm⟩ := hs
  have hm4 : (4 : ℕ) ≠ s.mode := by omega
  have hm5 : (5 : ℕ) ≠ s.mode := by omega
  by_cases hi : i = 0
  · subst hi
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hop with hop | hop <;>
      simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, AluSZChipJ9.sgnLt, notE, hop, opIx, hr, h1, h2, hm4, hm5]
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, hi]

theorem gCoef_shape5 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (s : SlotL)
    (hs : s.role = none ∧ s.mode = 4 ∧ s.cf1 = 0 ∧ s.cf2 = 1) (i : ℕ) (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm, h1, h2⟩ := hs
  by_cases hi : i = 0
  · subst hi
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hop with hop | hop <;>
      simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, AluSZChipJ9.sgnLt, notE, hop, opIx, hr, hm, h1, h2]
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, hi]

theorem gCoef_shape6 (p : ℕ) (cl : CallL) (hop : cl.op = .div ∨ cl.op = .mod) (s : SlotL)
    (hs : s.role = none ∧ s.mode = 5 ∧ s.cf1 = 1 ∧ s.cf2 = 0) (i : ℕ) (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨hr, hm, h1, h2⟩ := hs
  by_cases hi : i = 0
  · subst hi
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hop with hop | hop <;>
      simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, AluSZChipJ9.sgnLt, notE, hop, opIx, hr, hm, h1, h2]
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval, AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, slotRow, hdrRow, ind, hi]


/-- The `mQM` part of `gBits`: `mQM·b_{25+t} = 0`, `t < 7`. -/
def gBitsM : List (AxisChipJ9.AG F) :=
  (List.range 7).map (fun t => AluSZChipJ9.ar (.mul (cv AluSZChipJ9.mQM) (cv (AluSZChipJ9.bt0 + 25 + t))))

theorem gBits_split : (AluSZChipJ9.gBits : List (AxisChipJ9.AG F)) =
    (List.range 32).map (fun t => AluSZChipJ9.ar (boolE (cv (AluSZChipJ9.bt0 + t)))) ++ gBitsM := rfl

theorem gBitsM_slotRow (p : ℕ) (cl : CallL) (s : SlotL) (hs : s.mode ≠ 5 ∨ ∀ w ∈ s.words, w < 2 ^ 25)
    (i : ℕ) (nxt : BRow F) :
    ∀ a ∈ (gBitsM : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (slotRow (F := F) p cl s i).col nxt.col) = 0 := by
  intro a ha
  simp only [gBitsM, List.mem_map, List.mem_range] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  simp only [AluSZChipJ9.ar, AxisChipJ9.AG.gate, CoeffExpr.eval, envB]
  rw [show AluSZChipJ9.bt0 + 25 + t = AluSZChipJ9.bt0 + (25 + t) by omega, BRow.col_bit _ _ (by omega)]
  by_cases hm : s.mode = 5
  · have hw : ∀ w ∈ s.words, w < 2 ^ 25 := hs.resolve_left (by simpa using hm)
    have hb : bitOf (s.words.getD i 0) (25 + t) = 0 := by
      unfold bitOf
      have : s.words.getD i 0 < 2 ^ 25 := by
        by_cases hi : i < s.words.length
        · rw [List.getD_eq_getElem _ _ hi]; exact hw _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]; positivity
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    have hb' : bitOf (s.words[i]?.getD 0) (25 + t) = 0 := by simpa using hb
    simp [slotRow, ind, hb']
  · simp [slotRow, ind, hm, Ne.symm hm]

end Rows

/-! ## D. The group theorems -/

theorem packQ1_ne : ∀ ws : List ℕ, ws ≠ [] → packQ1 ws ≠ []
  | [], h => absurd rfl h
  | q :: qs, _ => by rw [packQ1]; simp

theorem p_le_BnBn : Nock.Atoms.p ≤ Bn * Bn := by
  have := Nock.Atoms.p_eq_limbs
  have h2 : Nock.Atoms.B = Bn := rfl
  rw [h2] at this
  have hB : 1 ≤ Bn := by norm_num [Bn]
  have : Bn * (Bn - 1) + 1 ≤ Bn * Bn := by
    have : Bn * (Bn - 1) + Bn = Bn * Bn := by
      cases Bn with
      | zero => omega
      | succ n => simp [Nat.mul_succ]
    omega
  omega

theorem qSlot_false_facts (o : PrimOp) (qs : List ℤ) :
    (qSlot o false qs).role = none ∧ (qSlot o false qs).mode = 5 ∧ (qSlot o false qs).cf1 = 1 ∧
      (qSlot o false qs).cf2 = 0 ∧ (qSlot o false qs).words ≠ [] ∧
      ((∀ q ∈ qs, 0 ≤ q ∧ q ≤ 2 ^ 25 - 1) → ∀ w ∈ (qSlot o false qs).words, w < 2 ^ 25) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [qSlot, Bool.false_eq_true, if_false]; split_ifs with h
    · simp
    · exact h
  · intro hq w hw
    simp only [qSlot, Bool.false_eq_true, if_false] at hw
    split_ifs at hw with h
    · simp at hw; subst hw; norm_num
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hw
      have := hq q hq'
      omega

theorem qSlot_true_facts (o : PrimOp) (qs : List ℤ) :
    (qSlot o true qs).role = none ∧ (qSlot o true qs).mode = 4 ∧ (qSlot o true qs).cf1 = (coefQ1 o).1 ∧
      (qSlot o true qs).cf2 = (coefQ1 o).2 ∧ (qSlot o true qs).words ≠ [] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only [qSlot, if_true]
  split_ifs with h
  · simp
  · exact packQ1_ne _ h

/-- **Everything the gate groups need to know about the slots of a div/mod call.** -/
theorem dm_shapes (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hcl : CallOK p cl)
    (hop : cl.op = .div ∨ cl.op = .mod) :
    ∃ sA sX sB sY sS qM q1 : SlotL,
      slotsOf p cl = [sA, sX, sB, sY, sS, qM, q1] ∧
      KShape sA 0 ∧ KShape sX 1 ∧ KShape sB 2 ∧ KShape sY 3 ∧ KShape sS 4 ∧ KShape qM 5 ∧ KShape q1 6 ∧
      (∀ s ∈ [sA, sX, sB, sY, sS, qM, q1], s.words ≠ []) ∧
      (sA.cf1 = -1 ∧ sA.cf2 = 0) ∧ (sB.cf1 = 0 ∧ sB.cf2 = -1) ∧ (sX.cf1 = 0 ∧ sX.cf2 = 0) ∧
      (sY.cf1 = 1 ∧ sY.cf2 = 1) ∧ (sS.cf1 = 0 ∧ sS.cf2 = 1) ∧ (qM.cf1 = 1 ∧ qM.cf2 = 0) ∧
      (q1.cf1 = 0 ∧ q1.cf2 = 1) ∧
      (∀ s ∈ [sA, sX, sB, sY, sS, qM, q1], s.mode ≠ 5 ∨ ∀ w ∈ s.words, w < 2 ^ 25) := by
  have hp : p ≤ Bn * Bn := hpG ▸ p_le_BnBn
  obtain ⟨sA, sX, sB, sY, sS, heq, hA, hX, hB, hY, hS, mX, mB, mS, hvwS, hb⟩ := dm_slots p cl hcl hop hp
  have hlen : sX.words.length ≤ 62 := hcl.limbs62 sX (by rw [heq]; simp) mX
  have hXw : sX.vw = sX.words := hX.eqw (by omega)
  have hv1 : Nock.Atoms.val sX.vw * Nock.Atoms.val sB.vw + Nock.Atoms.val sY.vw = Nock.Atoms.val sA.vw := by
    rw [hX.val, hB.val, hY.val, hA.val, mul_comm]; exact Nat.div_add_mod cl.a cl.b
  have hv2 : Nock.Atoms.val sY.vw + Nock.Atoms.val sS.vw + 1 = Nock.Atoms.val sB.vw := by
    rw [hY.val, hS.val, hB.val]; have := Nat.mod_lt cl.a hb; omega
  have h1 := ds1_carries sX.vw sB.vw sY.vw sA.vw hX.vwlt hB.vwlt hY.vwlt hA.vwlt (by rw [hXw]; exact hlen) hv1
  have h2 := ds2_carries sY.vw sS.vw sB.vw hY.vwlt hS.vwlt hB.vwlt hv2
  have fM := qSlot_false_facts cl.op (carr (Bn : ℤ) 0 (dsS1 sX sB sY sA))
  have fQ := qSlot_true_facts cl.op (carr (Bn : ℤ) 0 (dsS2 sY sS sB))
  have hc1 : (coefQ1 cl.op).1 = 0 ∧ (coefQ1 cl.op).2 = 1 := by
    rcases hop with h | h <;> simp [coefQ1, h]
  refine ⟨sA, sX, sB, sY, sS, qSlot cl.op false (carr (Bn : ℤ) 0 (dsS1 sX sB sY sA)),
    qSlot cl.op true (carr (Bn : ℤ) 0 (dsS2 sY sS sB)), heq, ⟨hA.role, hA.mode_le⟩, ⟨hX.role, hX.mode_le⟩,
    ⟨hB.role, hB.mode_le⟩, ⟨hY.role, hY.mode_le⟩, ⟨hS.role, hS.mode_le⟩, ⟨fM.1, fM.2.1⟩, ⟨fQ.1, fQ.2.1⟩, ?_,
    ⟨by simpa using hA.cf1, by simpa using hA.cf2⟩, ⟨by simpa using hB.cf1, by simpa using hB.cf2⟩,
    ⟨by simpa using hX.cf1, by simpa using hX.cf2⟩, ⟨by simpa using hY.cf1, by simpa using hY.cf2⟩,
    ⟨by simpa using hS.cf1, by simpa using hS.cf2⟩, ⟨fM.2.2.1, fM.2.2.2.1⟩,
    ⟨by rw [fQ.2.2.1]; exact hc1.1, by rw [fQ.2.2.2.1]; exact hc1.2⟩, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hA.ne
    · exact hX.ne
    · exact hB.ne
    · exact hY.ne
    · exact hS.ne
    · exact fM.2.2.2.2.1
    · exact fQ.2.2.2.2
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; have := hA.mode_le; omega
    · left; have := hX.mode_le; omega
    · left; have := hB.mode_le; omega
    · left; have := hY.mode_le; omega
    · left; have := hS.mode_le; omega
    · right; exact fM.2.2.2.2.2 h1
    · left; rw [fQ.2.1]; omega

section Groups
variable {F : Type} [Field F]

theorem blockB_def (p : ℕ) (cl : CallL) :
    blockB (F := F) p cl = hdrRow cl :: rowsS p cl (slotsOf p cl) := rfl

theorem blockB_len (p : ℕ) (cl : CallL) :
    (blockB (F := F) p cl).length = (rowsS (F := F) p cl (slotsOf p cl)).length + 1 := by
  rw [blockB_def]; simp

/-- Every block row is the hdr or a lane row of a slot. -/
theorem blockB_cur (p : ℕ) (cl : CallL) (hne : ∀ s ∈ slotsOf p cl, s.words ≠ []) (j : ℕ)
    (hj : j < (blockB (F := F) p cl).length) :
    (blockB (F := F) p cl).getD j BRow.zero = hdrRow cl ∨
      ∃ s ∈ slotsOf p cl, ∃ i < s.words.length, (blockB (F := F) p cl).getD j BRow.zero = slotRow p cl s i := by
  rcases j with _ | j
  · left; rw [blockB_def]; rfl
  · right
    rw [blockB_len] at hj
    obtain ⟨s, hs, i, hi, hrow, -⟩ := rowsS_info (F := F) p cl (slotsOf p cl) hne j (by omega)
    exact ⟨s, hs, i, hi, by rw [blockB_def]; simpa using hrow⟩

theorem gCoef_hdr (cl : CallL) (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (hdrRow (F := F) cl).col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.sumC, CoeffExpr.sumList, CoeffExpr.eval,
    AxisChipJ9.AG.gate, envB, AluSZChipJ9.ar, hdrRow, BRow.zero]

theorem gBitsM_hdr (cl : CallL) (nxt : BRow F) :
    ∀ a ∈ (gBitsM : List (AxisChipJ9.AG F)),
      (AxisChipJ9.AG.gate a).eval (envB (hdrRow (F := F) cl).col nxt.col) = 0 := by
  intro a ha
  simp only [gBitsM, List.mem_map, List.mem_range] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  simp [AluSZChipJ9.ar, AxisChipJ9.AG.gate, CoeffExpr.eval, envB, hdrRow, BRow.zero]

/-- **`GroupSat gCoef` for div/mod.** -/
theorem gCoef_sat (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hcl : CallOK p cl)
    (hop : cl.op = .div ∨ cl.op = .mod) :
    GroupSat (F := F) p cl AluSZChipJ9.gCoef := by
  intro j hj nxt hn a ha
  obtain ⟨sA, sX, sB, sY, sS, qM, q1, heq, kA, kX, kB, kY, kS, kM, kQ, hne, cA, cB, cX, cY, cS, cM, cQ, hmode⟩ :=
    dm_shapes p cl hpG hcl hop
  rcases blockB_cur (F := F) p cl (by rw [heq]; exact hne) j hj with h | ⟨s, hs, i, hi, h⟩
  · rw [h]; exact gCoef_hdr cl nxt a ha
  · rw [h]
    rw [heq] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gCoef_shape0 p cl hop _ ⟨kA.1, cA.1, cA.2, kA.2⟩ i nxt a ha
    · exact gCoef_shape2 p cl hop _ ⟨kX.1, cX.1, cX.2, kX.2⟩ i nxt a ha
    · exact gCoef_shape1 p cl hop _ ⟨kB.1, cB.1, cB.2, kB.2⟩ i nxt a ha
    · exact gCoef_shape3 p cl hop _ ⟨kY.1, cY.1, cY.2, kY.2⟩ i nxt a ha
    · exact gCoef_shape4 p cl hop _ ⟨kS.1, cS.1, cS.2, kS.2⟩ i nxt a ha
    · exact gCoef_shape6 p cl hop _ ⟨kM.1, kM.2, cM.1, cM.2⟩ i nxt a ha
    · exact gCoef_shape5 p cl hop _ ⟨kQ.1, kQ.2, cQ.1, cQ.2⟩ i nxt a ha

/-- **The `mQM` part of `gBits`** (`mQM·b_{25+t} = 0`) for div/mod. -/
theorem gBitsM_sat (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hcl : CallOK p cl)
    (hop : cl.op = .div ∨ cl.op = .mod) :
    GroupSat (F := F) p cl (gBitsM : List (AxisChipJ9.AG F)) := by
  intro j hj nxt hn a ha
  obtain ⟨sA, sX, sB, sY, sS, qM, q1, heq, kA, kX, kB, kY, kS, kM, kQ, hne, cA, cB, cX, cY, cS, cM, cQ, hmode⟩ :=
    dm_shapes p cl hpG hcl hop
  rcases blockB_cur (F := F) p cl (by rw [heq]; exact hne) j hj with h | ⟨s, hs, i, hi, h⟩
  · rw [h]; exact gBitsM_hdr cl nxt a ha
  · rw [h]
    rw [heq] at hs
    exact gBitsM_slotRow p cl s (hmode s hs) i nxt a ha

/-- **`GroupSat gSeq` for div/mod.** -/
theorem gSeq_sat (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hcl : CallOK p cl)
    (hop : cl.op = .div ∨ cl.op = .mod) :
    GroupSat (F := F) p cl AluSZChipJ9.gSeq := by
  intro j hj nxt hn a ha
  obtain ⟨sA, sX, sB, sY, sS, qM, q1, heq, kA, kX, kB, kY, kS, kM, kQ, hne, cA, cB, cX, cY, cS, cM, cQ, hmode⟩ :=
    dm_shapes p cl hpG hcl hop
  have hne' : ∀ s ∈ slotsOf p cl, s.words ≠ [] := by rw [heq]; exact hne
  rcases j with _ | j
  · have : (blockB (F := F) p cl).getD 0 BRow.zero = hdrRow cl := by rw [blockB_def]; rfl
    rw [this]
    exact gSeq_noeos nxt _ (by simp [hdrRow, BRow.zero]) a ha
  · have hlen := blockB_len (F := F) p cl
    obtain ⟨s, hs, i, hi, hrow, hnext, hlast⟩ :=
      rowsS_info (F := F) p cl (slotsOf p cl) hne' j (by omega)
    have hcur : (blockB (F := F) p cl).getD (j + 1) BRow.zero = slotRow p cl s i := by
      rw [blockB_def]; simpa using hrow
    rw [hcur]
    by_cases hlt : i + 1 < s.words.length
    · exact gSeq_noeos nxt _ (by simp [slotRow, ind, BRow.zero, hdrRow]; omega) a ha
    · have hieq : i + 1 = s.words.length := by omega
      by_cases hnx : j + 1 + 1 < (blockB (F := F) p cl).length
      · obtain ⟨s', hpair, hnrow⟩ := (hlast hieq).1 (by omega)
        have hnxt : nxt = slotRow p cl s' 0 := by
          have := hn.1 hnx
          rw [this, blockB_def]; simpa using hnrow
        rw [hnxt]
        rw [heq] at hpair
        simp [List.zip] at hpair
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact gSeq_pair p cl hop 0 (by norm_num) _ _ kA kX i hieq a ha
        · exact gSeq_pair p cl hop 1 (by norm_num) _ _ kX kB i hieq a ha
        · exact gSeq_pair p cl hop 2 (by norm_num) _ _ kB kY i hieq a ha
        · exact gSeq_pair p cl hop 3 (by norm_num) _ _ kY kS i hieq a ha
        · exact gSeq_pair p cl hop 4 (by norm_num) _ _ kS kM i hieq a ha
        · exact gSeq_pair p cl hop 5 (by norm_num) _ _ kM kQ i hieq a ha
      · have hnl := hn.2 (by omega)
        have hg := (hlast hieq).2 (by omega)
        rw [heq] at hg
        simp at hg
        subst hg
        exact gSeq_last p cl hop _ kQ i hieq nxt hnl.1 a ha

end Groups

/-! ## E. The terminal `S1 = S2 = 0` -/

/-! ### E1. Packed carries: `hornerQ1 y (packQ1 ws) = evR y ws` for `0/1` carries -/

def val2 : List ℕ → ℕ
  | [] => 0
  | a :: xs => a + 2 * val2 xs

theorem zipIdx_sum (l : List ℕ) :
    ∀ k : ℕ, ((l.zipIdx k).map fun x => x.1 * 2 ^ x.2).sum = 2 ^ k * val2 l := by
  induction l with
  | nil => intro k; simp [val2]
  | cons a l ih => intro k; simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (k + 1), val2, pow_succ]; ring

theorem bitOf_val2 : ∀ (x : List ℕ), (∀ a ∈ x, a ≤ 1) → ∀ t, bitOf (val2 x) t = x.getD t 0
  | [], _, t => by simp [val2, bitOf]
  | a :: xs, h, 0 => by
    have ha := h a (by simp)
    simp only [bitOf, val2, pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | a :: xs, h, t + 1 => by
    have ha := h a (by simp)
    have ih := bitOf_val2 xs (fun b hb => h b (by simp [hb])) t
    simp only [bitOf, val2, List.getD_cons_succ] at ih ⊢
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have : (a + 2 * val2 xs) / 2 = val2 xs := by omega
    rw [this, ih]

section Ring
variable {Q : Type} [CommRing Q]

theorem rsum_eq (y : Q) : ∀ (x : List ℕ) (m : ℕ), x.length ≤ m →
    ((List.range m).map fun t => ((x.getD t 0 : ℕ) : Q) * y ^ t).sum = evR y (zl x)
  | [], m, _ => by simp [evR, zl]
  | a :: x, 0, h => by simp at h
  | a :: x, m + 1, h => by
    have ih := rsum_eq y x m (by simpa using h)
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have hf : ((fun t => ((((a :: x).getD t 0 : ℕ) : Q)) * y ^ t) ∘ Nat.succ) =
        fun t => y * (((x.getD t 0 : ℕ) : Q) * y ^ t) := by
      funext t; simp only [Function.comp, List.getD_cons_succ, Nat.succ_eq_add_one]; ring
    rw [hf, List.sum_map_mul_left, ih]
    simp [evR, zl]

theorem evR_zl_append (y : Q) : ∀ (a b : List ℕ),
    evR y (zl (a ++ b)) = evR y (zl a) + y ^ a.length * evR y (zl b)
  | [], b => by simp [zl, evR]
  | x :: a, b => by
    have ih := evR_zl_append y a b
    simp only [zl, List.cons_append, List.map_cons, evR, List.length_cons, pow_succ] at ih ⊢
    rw [ih]; ring

theorem evR_take_drop (y : Q) (ws : List ℕ) :
    evR y (zl ws) = evR y (zl (ws.take 32)) + y ^ 32 * evR y (zl (ws.drop 32)) := by
  by_cases h : 32 ≤ ws.length
  · conv_lhs => rw [← List.take_append_drop 32 ws]
    rw [evR_zl_append, List.length_take, min_eq_left h]
  · have : ws.drop 32 = [] := List.drop_eq_nil_of_le (by omega)
    rw [this, List.take_of_length_le (by omega)]
    simp [zl, evR]

theorem packV_val2 (y : Q) (x : List ℕ) (h1 : ∀ a ∈ x, a ≤ 1) (hl : x.length ≤ 32) :
    packV y (val2 x) = evR y (zl x) := by
  unfold packV
  have : ∀ t ∈ List.range 32, ((bitOf (val2 x) t : ℕ) : Q) * y ^ t = ((x.getD t 0 : ℕ) : Q) * y ^ t := by
    intro t _; rw [bitOf_val2 x h1 t]
  rw [List.map_congr_left this]
  exact rsum_eq y x 32 hl

theorem hornerQ1_packQ1 (y : Q) : ∀ (n : ℕ) (ws : List ℕ), ws.length ≤ n → (∀ a ∈ ws, a ≤ 1) →
    hornerQ1 y (packQ1 ws) = evR y (zl ws)
  | 0, ws, hl, _ => by
    have : ws = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp [packQ1, hornerQ1, evR, zl]
  | n + 1, ws, hl, h1 => by
    cases ws with
    | nil => simp [packQ1, hornerQ1, evR, zl]
    | cons q qs =>
      rw [packQ1.eq_def]
      dsimp only
      rw [hornerQ1]
      have hz := zipIdx_sum ((q :: qs).take 32) 0
      simp only [pow_zero, one_mul] at hz
      rw [hz]
      have hlt : ((q :: qs).take 32).length ≤ 32 := by simp
      have hle : ∀ a ∈ (q :: qs).take 32, a ≤ 1 := fun a ha => h1 a (List.mem_of_mem_take ha)
      rw [packV_val2 y _ hle hlt]
      have ih := hornerQ1_packQ1 y n ((q :: qs).drop 32) (by simp at hl ⊢; omega)
        (fun a ha => h1 a (List.mem_of_mem_drop ha))
      rw [ih, evR_take_drop y (q :: qs)]

theorem zl_toNat (cs : List ℤ) (hb : ∀ q ∈ cs, 0 ≤ q) : zl (cs.map Int.toNat) = cs := by
  unfold zl
  rw [List.map_map]
  conv_rhs => rw [← List.map_id cs]
  apply List.map_congr_left
  intro q hq
  simp [Int.toNat_of_nonneg (hb q hq)]

/-- The packed `mQ1` block evaluates to the carries. -/
theorem qSlot_true_H (y : Q) (o : PrimOp) (cs : List ℤ) (hb : ∀ q ∈ cs, 0 ≤ q ∧ q ≤ 1) :
    hornerQ1 y (qSlot o true cs).words = evR y cs := by
  have hws := zl_toNat cs (fun q hq => (hb q hq).1)
  have hb' : ∀ a ∈ cs.map Int.toNat, a ≤ 1 := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    have := hb q hq
    omega
  simp only [qSlot, if_true]
  split_ifs with h
  · have : cs = [] := List.map_eq_nil_iff.mp h
    subst this
    simp [hornerQ1, packV, bitOf, evR]
  · rw [hornerQ1_packQ1 y _ (cs.map Int.toNat) le_rfl hb', hws]

/-- The `mQM` block (one carry per row) evaluates to the carries. -/
theorem qSlot_false_H (y : Q) (o : PrimOp) (cs : List ℤ) (hb : ∀ q ∈ cs, 0 ≤ q) :
    slotH y (qSlot o false cs) 0 = evR y cs := by
  have hws := zl_toNat cs hb
  unfold slotH hornerFrom horner
  have hm : (qSlot o false cs).mode = 5 := rfl
  rw [if_neg (by rw [hm]; omega), if_neg (by rw [hm]; omega)]
  simp only [qSlot, Bool.false_eq_true, if_false, List.drop_zero]
  split_ifs with h
  · have : cs = [] := List.map_eq_nil_iff.mp h
    subst this
    simp [evR, zl]
  · rw [hws]

theorem slotL_of_mode_le (y : Q) (s : SlotL) (h : s.mode ≤ 3) : slotL y s = evR y (zl s.vw) := by
  unfold slotL
  rw [if_neg (by omega)]
  rfl

theorem slotL_q1 (y : Q) (o : PrimOp) (cs : List ℤ) :
    slotL y (qSlot o true cs) = (y - (Bn : Q)) * hornerQ1 y (qSlot o true cs).words := by
  unfold slotL slotH
  have : (qSlot o true cs).mode = 4 := by simp [qSlot]
  simp [this]

theorem slotL_qM (y : Q) (o : PrimOp) (cs : List ℤ) :
    slotL y (qSlot o false cs) = (y - (Bn : Q)) * slotH y (qSlot o false cs) 0 := by
  unfold slotL
  have : (qSlot o false cs).mode = 5 := rfl
  rw [if_pos (by omega)]

theorem slotHO_vw (y : Q) (s : SlotL) (h0 : s.mode ≠ 0) (h4 : s.mode ≠ 4) (hw : s.vw = s.words) :
    slotHO y s 0 = evR y (zl (hiL s.vw)) := by
  unfold slotHO hornerFrom horner
  rw [if_neg (by omega), hw]; rfl

theorem evR_single (y : Q) (e : ℤ) : evR y [e] = (e : Q) := by simp [evR]

end Ring

/-! ### E2. The last `𝕂′` row of a block -/

/-- The slot rows of a slot list under a row constructor `f`. -/
def rowsOf {X : Type} (f : SlotL → ℕ → X) (ss : List SlotL) : List X :=
  ss.flatMap fun s => (List.range s.words.length).map (f s)

theorem rowsOf_cons {X : Type} (f : SlotL → ℕ → X) (s : SlotL) (rest : List SlotL) :
    rowsOf f (s :: rest) = (List.range s.words.length).map (f s) ++ rowsOf f rest := by
  simp [rowsOf]

theorem rowsOf_length {X : Type} (f : SlotL → ℕ → X) (ss : List SlotL) :
    (rowsOf f ss).length = (ss.map (·.words.length)).sum := by
  induction ss with
  | nil => simp [rowsOf]
  | cons s rest ih => rw [rowsOf_cons, List.length_append, ih]; simp

section QRows
variable {Q : Type} [CommRing Q]

theorem runSums_length (acc : Q × Q) (ds : List (Q × Q)) : (runSums acc ds).length = ds.length := by
  induction ds generalizing acc with
  | nil => simp [runSums]
  | cons d ds ih => simp [runSums, ih]

theorem runSums_getD : ∀ (ds : List (Q × Q)) (acc : Q × Q) (k : ℕ), k < ds.length →
    (runSums acc ds).getD k (0, 0) =
      (acc.1 + ((ds.take (k + 1)).map Prod.fst).sum, acc.2 + ((ds.take (k + 1)).map Prod.snd).sum)
  | [], _, _, h => by simp at h
  | d :: ds, acc, 0, _ => by
    simp [runSums]
  | d :: ds, acc, k + 1, h => by
    have ih := runSums_getD ds (acc.1 + d.1, acc.2 + d.2) k (by simpa using h)
    simp only [runSums, List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ext <;> simp <;> ring

theorem laneD_eq (p : ℕ) (y : Q) (cl : CallL) :
    laneD p y cl = rowsOf (fun s i => if i = 0 then AluHonestRows.slotD p y cl s else (0, 0)) (slotsOf p cl) := rfl

theorem laneHL_eq (p : ℕ) (y : Q) (cl : CallL) :
    laneHL y cl p = rowsOf (fun s i => (slotH y s i, slotHO y s i, if i = 0 then slotL y s else 0)) (slotsOf p cl) :=
  rfl

theorem sum_rowsOf_first (x : SlotL → Q × Q) : ∀ (ss : List SlotL), (∀ s ∈ ss, 0 < s.words.length) →
    ((rowsOf (fun s i => if i = 0 then x s else (0, 0)) ss).map Prod.fst).sum = (ss.map fun s => (x s).1).sum ∧
    ((rowsOf (fun s i => if i = 0 then x s else (0, 0)) ss).map Prod.snd).sum = (ss.map fun s => (x s).2).sum
  | [], _ => by simp [rowsOf]
  | s :: rest, h => by
    have hn : 0 < s.words.length := h s (by simp)
    have ih := sum_rowsOf_first x rest (fun s' hs' => h s' (by simp [hs']))
    rw [rowsOf_cons]
    obtain ⟨m, hm⟩ : ∃ m, s.words.length = m + 1 := ⟨s.words.length - 1, by omega⟩
    rw [hm, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def, ih.1, ih.2]

theorem blockQ_getD_last (p : ℕ) (y : Q) (cl : CallL) (hs : ∀ s ∈ slotsOf p cl, 0 < s.words.length)
    (hN : 0 < ((slotsOf p cl).map (·.words.length)).sum) :
    ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).S1 =
        (hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum ∧
    ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).S2 =
        (hdrD (Q := Q) cl).2 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).2).sum := by
  set N := ((slotsOf p cl).map (·.words.length)).sum with hNdef
  have hHL : (laneHL y cl p).length = N := by rw [laneHL_eq, rowsOf_length]
  have hD : (laneD p y cl).length = N := by rw [laneD_eq, rowsOf_length]
  have hSS : (runSums (hdrD (Q := Q) cl) (laneD p y cl)).length = N := by rw [runSums_length, hD]
  obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hsums := sum_rowsOf_first (fun s => AluHonestRows.slotD p y cl s) (slotsOf p cl) hs
  have hkey := runSums_getD (laneD p y cl) (hdrD (Q := Q) cl) N' (by omega)
  have htake : (laneD p y cl).take (N' + 1) = laneD p y cl := List.take_of_length_le (by omega)
  rw [htake] at hkey
  rw [laneD_eq] at hkey
  rw [hsums.1, hsums.2] at hkey
  simp only [blockQ]
  rw [hN', List.getD_cons_succ]
  have hlt : N' < (List.map (fun x => (⟨x.1.1, x.1.2.1, x.1.2.2, x.2.1.1, x.2.1.2, x.2.2.1, x.2.2.2,
      (latchOf p y cl).1, (latchOf p y cl).2⟩ : QRow Q))
      ((laneHL y cl p).zip ((laneD p y cl).zip (runSums (hdrD (Q := Q) cl) (laneD p y cl))))).length := by
    simp [List.length_zip, hHL, hD, hSS]; omega
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_zip, List.getElem_zip]
  have hgd : (runSums (hdrD (Q := Q) cl) (laneD p y cl))[N']'(by omega) =
      ((hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum,
        (hdrD (Q := Q) cl).2 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).2).sum) := by
    rw [← List.getD_eq_getElem _ (0, 0) _]; exact hkey
  refine ⟨?_, ?_⟩ <;> dsimp only <;> rw [hgd]

end QRows

/-! ### E3. The two totals vanish -/

section Terminal
variable {Q : Type} [CommRing Q]

theorem qM_role (o : PrimOp) (qs : List ℤ) : (qSlot o false qs).role = none := rfl
theorem qM_cf1 (o : PrimOp) (qs : List ℤ) : (qSlot o false qs).cf1 = 1 := rfl
theorem qM_cf2 (o : PrimOp) (qs : List ℤ) : (qSlot o false qs).cf2 = 0 := rfl
theorem q1_role (o : PrimOp) (qs : List ℤ) : (qSlot o true qs).role = none := rfl
theorem q1_cf1 (o : PrimOp) (qs : List ℤ) : (qSlot o true qs).cf1 = (coefQ1 o).1 := rfl
theorem q1_cf2 (o : PrimOp) (qs : List ℤ) : (qSlot o true qs).cf2 = (coefQ1 o).2 := rfl

/-- **The terminal sums vanish** for `div` / `mod`: the hdr contribution plus the slots' contributions
(`carry_id` on the two honest identities). -/
theorem dm_terminal (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hcl : CallOK p cl)
    (hop : cl.op = .div ∨ cl.op = .mod) (y : Q) :
    (hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum = 0 ∧
    (hdrD (Q := Q) cl).2 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).2).sum = 0 := by
  have hp : p ≤ Bn * Bn := hpG ▸ p_le_BnBn
  obtain ⟨sA, sX, sB, sY, sS, heq, hA, hX, hB, hY, hS, mX, mB, mS, hvwS, hb⟩ := dm_slots p cl hcl hop hp
  have hlen : sX.words.length ≤ 62 := hcl.limbs62 sX (by rw [heq]; simp) mX
  have hXw : sX.vw = sX.words := hX.eqw (by omega)
  have hBw : sB.vw = sB.words := hB.eqw (by omega)
  have hv1 : Nock.Atoms.val sX.vw * Nock.Atoms.val sB.vw + Nock.Atoms.val sY.vw = Nock.Atoms.val sA.vw := by
    rw [hX.val, hB.val, hY.val, hA.val, mul_comm]; exact Nat.div_add_mod cl.a cl.b
  have hv2 : Nock.Atoms.val sY.vw + Nock.Atoms.val sS.vw + 1 = Nock.Atoms.val sB.vw := by
    rw [hY.val, hS.val, hB.val]; have := Nat.mod_lt cl.a hb; omega
  have h1 := ds1_carries sX.vw sB.vw sY.vw sA.vw hX.vwlt hB.vwlt hY.vwlt hA.vwlt (by rw [hXw]; exact hlen) hv1
  have h2 := ds2_carries sY.vw sS.vw sB.vw hY.vwlt hS.vwlt hB.vwlt hv2
  have e1 : evB (Bn : ℤ) (dsS1 sX sB sY sA) = 0 := by
    unfold dsS1; rw [evB_ds1]; have h := congrArg (Nat.cast : ℕ → ℤ) hv1; push_cast at h ⊢; linarith
  have e2 : evB (Bn : ℤ) (dsS2 sY sS sB) = 0 := by
    unfold dsS2; rw [evB_ds2]; have h := congrArg (Nat.cast : ℕ → ℤ) hv2; push_cast at h ⊢; linarith
  have c1 := carry_id (R := Q) (B := (Bn : ℤ)) (by norm_num [Bn]) y (dsS1 sX sB sY sA) e1
  have c2 := carry_id (R := Q) (B := (Bn : ℤ)) (by norm_num [Bn]) y (dsS2 sY sS sB) e2
  have hq1 := qSlot_true_H y cl.op (carr (Bn : ℤ) 0 (dsS2 sY sS sB)) h2
  have hqM := qSlot_false_H y cl.op (carr (Bn : ℤ) 0 (dsS1 sX sB sY sA)) (fun q hq => (h1 q hq).1)
  have fM := qSlot_false_facts cl.op (carr (Bn : ℤ) 0 (dsS1 sX sB sY sA))
  have fQ := qSlot_true_facts cl.op (carr (Bn : ℤ) 0 (dsS2 sY sS sB))
  have hc1 : (coefQ1 cl.op).1 = 0 ∧ (coefQ1 cl.op).2 = 1 := by
    rcases hop with h | h <;> simp [coefQ1, h]
  have hlat : latchOf p y cl = (slotL y sX, slotHO y sX 0) := by
    unfold latchOf; rw [heq]
    simp [List.find?, isF1, hA.role, hX.role]
    rcases hop with h | h <;> simp [h]
  have hd : (hdrD (Q := Q) cl).1 = 0 ∧ (hdrD (Q := Q) cl).2 = 1 := by
    rcases hop with h | h <;> simp [hdrD, h]
  have dA : AluHonestRows.slotD p y cl sA = (-(slotL y sA), 0) := by
    unfold AluHonestRows.slotD; rw [hlat]; simp [isF2, hA.role, hA.cf1, hA.cf2]
  have dX : AluHonestRows.slotD p y cl sX = (0, 0) := by
    unfold AluHonestRows.slotD; rw [hlat]; simp [isF2, hX.role, hX.cf1, hX.cf2]
  have dB : AluHonestRows.slotD p y cl sB = (slotL y sX * slotL y sB + (y - (Bn : Q)) * (slotHO y sX 0 * slotHO y sB 0),
      -(slotL y sB)) := by
    unfold AluHonestRows.slotD; rw [hlat]; simp [isF2, hB.role, hB.cf1, hB.cf2]
    rcases hop with h | h <;> simp [h]
  have dY : AluHonestRows.slotD p y cl sY = (slotL y sY, slotL y sY) := by
    unfold AluHonestRows.slotD; rw [hlat]; simp [isF2, hY.role, hY.cf1, hY.cf2]
  have dS : AluHonestRows.slotD p y cl sS = (0, slotL y sS) := by
    unfold AluHonestRows.slotD; rw [hlat]; simp [isF2, hS.role, hS.cf1, hS.cf2]
  have dM : AluHonestRows.slotD p y cl (qSlot cl.op false (carr (Bn : ℤ) 0 (dsS1 sX sB sY sA))) = (slotL y (qSlot cl.op false (carr (Bn : ℤ) 0 (dsS1 sX sB sY sA))), 0) := by
    unfold AluHonestRows.slotD; rw [hlat]; simp [isF2, qM_role, qM_cf1, qM_cf2]
  have dQ : AluHonestRows.slotD p y cl (qSlot cl.op true (carr (Bn : ℤ) 0 (dsS2 sY sS sB))) = (0, slotL y (qSlot cl.op true (carr (Bn : ℤ) 0 (dsS2 sY sS sB)))) := by
    unfold AluHonestRows.slotD; rw [hlat]; simp [isF2, q1_role, q1_cf1, q1_cf2, hc1.1, hc1.2]
  rw [heq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [dA, dX, dB, dY, dS, dM, dQ, slotL_qM, slotL_q1, hqM, hq1]
  rw [slotL_of_mode_le y sA hA.mode_le, slotL_of_mode_le y sX hX.mode_le, slotL_of_mode_le y sB hB.mode_le,
    slotL_of_mode_le y sY hY.mode_le, slotL_of_mode_le y sS hS.mode_le,
    slotHO_vw y sX (by omega) (by omega) hXw, slotHO_vw y sB (by omega) (by omega) hBw]
  have hB' : ((Bn : ℤ) : Q) = (Bn : Q) := Int.cast_natCast Bn
  have x1 : evR y (dsS1 sX sB sY sA) = evR y (zl sX.vw) * evR y (zl sB.vw) +
      (y - (Bn : Q)) * (evR y (zl (hiL sX.vw)) * evR y (zl (hiL sB.vw))) + evR y (zl sY.vw) - evR y (zl sA.vw) := by
    unfold dsS1; rw [evR_addL, evR_addL, evR_negL, evR_wL, hB']; ring
  have x2 : evR y (dsS2 sY sS sB) = evR y (zl sY.vw) + evR y (zl sS.vw) + 1 - evR y (zl sB.vw) := by
    unfold dsS2; rw [evR_addL, evR_addL, evR_addL, evR_negL, evR_single]; push_cast; ring
  rw [x1, hB'] at c1
  rw [x2, hB'] at c2
  rw [hd.1, hd.2]
  constructor
  · linear_combination c1
  · linear_combination c2

end Terminal

/-! ### E4. `QSat` of the terminal equations -/

section TermQ
variable {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

theorem kvec_pair (q : QRow (Quad (algebraMap F K δ))) (r : ℕ) (hr : r % 2 = 0) :
    Quad.mk (algebraMap F K δ) (kvec δ q r) (kvec δ q (r + 1)) = q.role r := by
  have h1 : r - r % 2 = r := by omega
  have h2 : (r + 1) - (r + 1) % 2 = r := by omega
  have h3 : (r + 1) % 2 ≠ 0 := by omega
  simp only [kvec, h1, h2, hr, h3, if_true, if_false]
  exact Quad.mk_re_im (algebraMap F K δ) (q.role r)

/-- The two terminal `𝕂′` equations of `identQ`: `(1 − sL′)·S1 = 0`, `(1 − sL′)·S2 = 0`. -/
def termQ (δF : F) : List (QE F) :=
  [ QE.scale (notE (nv AluSZChipJ9.sL)) (QE.var AluSZChipJ9.S1),
    QE.scale (notE (nv AluSZChipJ9.sL)) (QE.var AluSZChipJ9.S2) ]

/-- They are the last two equations of `identQ`. -/
theorem termQ_eq_drop : (AluSZChipJ9.identQ δ : List (QE F)).drop 23 = termQ δ := rfl

theorem termQ_sub : ∀ e ∈ (termQ δ : List (QE F)), e ∈ (AluSZChipJ9.identQ δ : List (QE F)) := fun e he => by
  rw [← termQ_eq_drop δ] at he
  exact List.mem_of_mem_drop he

theorem rowsOf_sL (p : ℕ) (cl : CallL) (r : BRow F) (hr : r ∈ rowsOf (slotRow (F := F) p cl) (slotsOf p cl)) :
    r.sL = 1 := by
  simp only [rowsOf, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨s, _, i, _, rfl⟩ := hr
  rfl

/-- **`QSat` of the terminal `S1 = S2 = 0` equations for `div` / `mod`.** -/
theorem termS_sat (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hcl : CallOK p cl)
    (hop : cl.op = .div ∨ cl.op = .mod) :
    QSat (K := K) δ p cl (termQ δ : List (QE F)) := by
  intro y chal hy hp j hj nxt hn nq hq e he
  obtain ⟨sA, sX, sB, sY, sS, qM, q1, heq, kA, kX, kB, kY, kS, kM, kQ, hne, cA, cB, cX, cY, cS, cM, cQ, hmode⟩ :=
    dm_shapes p cl hpG hcl hop
  have hsl : ∀ s ∈ slotsOf p cl, 0 < s.words.length := by
    intro s hs
    have := hne s (by rw [heq] at hs; exact hs)
    exact List.length_pos_iff.mpr this
  have hN : 0 < ((slotsOf p cl).map (·.words.length)).sum := by
    rw [heq]
    have := hsl sA (by rw [heq]; simp)
    simp; omega
  have hlen : (blockB (F := F) p cl).length = ((slotsOf p cl).map (·.words.length)).sum + 1 := by
    show (hdrRow cl :: rowsOf (slotRow (F := F) p cl) (slotsOf p cl)).length = _
    simp [rowsOf_length]
  simp only [termQ, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  by_cases hl : j + 1 < (blockB (F := F) p cl).length
  · have hsL : nxt.sL = 1 := by
      rw [hn.1 hl]
      show ((hdrRow cl :: rowsOf (slotRow (F := F) p cl) (slotsOf p cl)).getD (j + 1) BRow.zero).sL = 1
      rw [List.getD_cons_succ]
      have hlt : j < (rowsOf (slotRow (F := F) p cl) (slotsOf p cl)).length := by
        have : (rowsOf (slotRow (F := F) p cl) (slotsOf p cl)).length = ((slotsOf p cl).map (·.words.length)).sum :=
          rowsOf_length _ _
        omega
      rw [List.getD_eq_getElem _ _ hlt]
      exact rowsOf_sL p cl _ (List.getElem_mem hlt)
    rcases he with rfl | rfl <;>
    · rw [ev_scale]; simp [CoeffExpr.eval, envB, hsL]
  · have hjN : j = ((slotsOf p cl).map (·.words.length)).sum := by omega
    obtain ⟨b1, b2⟩ := blockQ_getD_last p y cl hsl hN
    have t := dm_terminal (Q := Quad (algebraMap F K δ)) p cl hpG hcl hop y
    subst hjN
    rcases he with rfl | rfl
    · have hk := kvec_pair δ ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero)
        AluSZChipJ9.S1 (by decide)
      have hrole : ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).role AluSZChipJ9.S1 =
          ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).S1 := by
        simp [QRow.role, AluSZChipJ9.S1]
      rw [ev_scale, ev_var]
      dsimp only
      rw [hk, hrole, b1, t.1, mul_zero]
    · have hk := kvec_pair δ ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero)
        AluSZChipJ9.S2 (by decide)
      have hrole : ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).role AluSZChipJ9.S2 =
          ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).S2 := by
        simp [QRow.role, AluSZChipJ9.S2]
      rw [ev_scale, ev_var]
      dsimp only
      rw [hk, hrole, b2, t.2, mul_zero]

end TermQ

end Nock.NockVMROM.Thm54.VclL.Handle.AluSatD

