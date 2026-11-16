/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSatM.lean

  **Honest gate satisfaction of `mul`.**

  For `op = .mul` this proves, over the honest block of `AluHonestRows` (the `mul` call's `slotsOf`: factors `ra rb`
  as 16-bit-half views / splits, the result `rc`, and the 25-bit `mQM` carry block):
  * `GroupSat gSeq`, `GroupSat gCoef`;
  * the 25-bit `mQM` part of `gBits` (`mQM·b_{25+t} = 0`, `t < 7`);
  * the terminal `S1 = S2 = 0` (`QSat` of the last two `identQ` equations), via `CarrySZ.carry_id`.

  The Q bound: the combined coefficient of `W − C` at `X^k` is
  `Σ_i (a_i b_{k−i} − B·h_i h'_{k−i}) + Σ_i h_i h'_{k−1−i} − c_k` with `a = e + 2^16 h`,
  so `a b − B h h' = e e' + 2^16 (e h' + h e') ∈ [0, 2^50]`, at most `62` nonzero terms:
  `d ∈ (−B, 2^56 + 2^38]`, inside `carr_bound0`'s window at `M = 2^25 − 1` (`B·(M+1) = 2^57`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluHonestRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSatM

open Nock Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 1. Coefficient-list arithmetic -/

theorem getD_map0 {α β : Type} [Zero α] [Zero β] (f : α → β) (hf : f 0 = 0) (l : List α) (k : ℕ) :
    (l.map f).getD k 0 = f (l.getD k 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> simp [hf]

theorem getD_addL : ∀ (as bs : List ℤ) (k : ℕ), (addL as bs).getD k 0 = as.getD k 0 + bs.getD k 0
  | [], bs, k => by simp [addL]
  | a :: as, [], k => by simp [addL]
  | a :: as, b :: bs, 0 => by simp [addL]
  | a :: as, b :: bs, k + 1 => by
    simp only [addL, List.getD_cons_succ]; exact getD_addL as bs k

theorem getD_negL (as : List ℤ) (k : ℕ) : (negL as).getD k 0 = -(as.getD k 0) :=
  getD_map0 (fun a : ℤ => -a) (by simp) as k

theorem getD_zl (l : List ℕ) (k : ℕ) : (zl l).getD k 0 = ((l.getD k 0 : ℕ) : ℤ) :=
  getD_map0 (fun a : ℕ => (a : ℤ)) (by simp) l k

theorem getD_hiL (l : List ℕ) (k : ℕ) : (hiL l).getD k 0 = l.getD k 0 / 2 ^ 16 :=
  getD_map0 (fun a : ℕ => a / 2 ^ 16) (by simp) l k

theorem getD_mulL : ∀ (as bs : List ℤ) (k : ℕ),
    (mulL as bs).getD k 0 = ∑ i ∈ Finset.range (k + 1), as.getD i 0 * bs.getD (k - i) 0
  | [], bs, k => by simp [mulL]
  | a :: as, bs, k => by
    rw [mulL, getD_addL, getD_map0 (fun x : ℤ => a * x) (by simp)]
    cases k with
    | zero => simp
    | succ k =>
      rw [List.getD_cons_succ, getD_mulL as bs k, Finset.sum_range_succ' _ (k + 1)]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_sub_add_right, Nat.sub_zero]
      ring

theorem getD_mulL_one (P : List ℤ) (k : ℕ) : (mulL [1] P).getD k 0 = P.getD k 0 := by
  have : mulL [1] P = addL (P.map (1 * ·)) [0] := by simp [mulL]
  rw [this, getD_addL, getD_map0 (fun x : ℤ => 1 * x) (by simp)]
  cases k <;> simp

theorem getD_mulL_lin (B : ℤ) (P : List ℤ) (k : ℕ) :
    (mulL [-B, 1] P).getD k 0 = -B * P.getD k 0 + (if k = 0 then 0 else P.getD (k - 1) 0) := by
  have : mulL [-B, 1] P = addL (P.map (-B * ·)) (0 :: mulL [1] P) := rfl
  rw [this, getD_addL, getD_map0 (fun x : ℤ => -B * x) (by simp)]
  cases k with
  | zero => simp
  | succ k => rw [List.getD_cons_succ, getD_mulL_one]; simp

theorem evB_map_mul (B a : ℤ) : ∀ l : List ℤ, evB B (l.map (a * ·)) = a * evB B l
  | [] => by simp [evB]
  | x :: l => by simp only [List.map_cons, evB, evB_map_mul B a l]; ring

theorem evB_mulL (B : ℤ) : ∀ as bs : List ℤ, evB B (mulL as bs) = evB B as * evB B bs
  | [], bs => by simp [mulL, evB]
  | a :: as, bs => by
    simp only [mulL, evB_addL, evB_map_mul, evB, evB_mulL B as bs]; ring

theorem evR_map_mul {R : Type} [CommRing R] (y : R) (a : ℤ) :
    ∀ l : List ℤ, evR y (l.map (a * ·)) = (a : R) * evR y l
  | [] => by simp [evR]
  | x :: l => by simp only [List.map_cons, evR, evR_map_mul y a l]; push_cast; ring

theorem evR_mulL {R : Type} [CommRing R] (y : R) :
    ∀ as bs : List ℤ, evR y (mulL as bs) = evR y as * evR y bs
  | [], bs => by simp [mulL, evR]
  | a :: as, bs => by
    simp only [mulL, evR_addL, evR_map_mul, evR, evR_mulL y as bs]; ring

/-- `Σ l_i B^i = val l`. -/
theorem evB_zl (l : List ℕ) : evB (Bn : ℤ) (zl l) = (Nock.Atoms.val l : ℤ) := by
  induction l with
  | nil => simp [zl, evB]
  | cons a l ih =>
    have h1 : zl (a :: l) = (a : ℤ) :: zl l := rfl
    rw [h1, evB, ih, Nock.Atoms.val_cons]
    push_cast
    simp [Bn, Nock.Atoms.B]

theorem evR_zl_lin {R : Type} [CommRing R] (y : R) (B : ℤ) : evR y [-B, 1] = y - (B : R) := by
  simp [evR]; ring

/-- `evR` of `wL`: `A·B + (y − B)·hiA·hiB`. -/
theorem evR_wL {R : Type} [CommRing R] (y : R) (A B : List ℕ) :
    evR y (wL A B) = evR y (zl A) * evR y (zl B) + (y - (Bn : R)) * (evR y (zl (hiL A)) * evR y (zl (hiL B))) := by
  unfold wL
  rw [evR_addL, evR_mulL, evR_mulL, evR_mulL, evR_zl_lin]
  simp only [Int.cast_natCast]

theorem evB_wL (A B : List ℕ) :
    evB (Bn : ℤ) (wL A B) = evB (Bn : ℤ) (zl A) * evB (Bn : ℤ) (zl B) := by
  unfold wL
  rw [evB_addL, evB_mulL, evB_mulL, evB_mulL]
  have : evB (Bn : ℤ) [-(Bn : ℤ), 1] = 0 := by simp [evB]
  rw [this]; ring

/-! ### The coefficient bound -/

theorem sum_ite_le (c : ℤ) (hc : 0 ≤ c) : ∀ n : ℕ,
    ∑ i ∈ Finset.range n, (if i < 62 then c else 0) ≤ (min n 62 : ℕ) * c
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_ite_le c hc n
    by_cases h : n < 62
    · rw [if_pos h]
      have : min (n + 1) 62 = min n 62 + 1 := by omega
      rw [this, Nat.cast_add, Nat.cast_one]; nlinarith
    · rw [if_neg h]
      have : min (n + 1) 62 = min n 62 := by omega
      rw [this]; linarith

theorem getD_zero_of_len (l : List ℕ) (n : ℕ) (hl : l.length ≤ n) (i : ℕ) (hi : n ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show l.length ≤ i by omega)]

theorem getD_lt (l : List ℕ) (b : ℕ) (hl : ∀ w ∈ l, w < b) (hb : 0 < b) (i : ℕ) : l.getD i 0 < b := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simpa using hb
  | some w => simpa using hl w (List.mem_of_getElem? h)

/-- One term: `a b − 2^32 h h' ∈ [0, 2^50]` for `a, b < 2^32`, `h = a / 2^16`. -/
theorem term_bound (a b : ℕ) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    0 ≤ (a : ℤ) * b - (Bn : ℤ) * (((a / 2 ^ 16 : ℕ) : ℤ) * ((b / 2 ^ 16 : ℕ) : ℤ)) ∧
    (a : ℤ) * b - (Bn : ℤ) * (((a / 2 ^ 16 : ℕ) : ℤ) * ((b / 2 ^ 16 : ℕ) : ℤ)) ≤ 2 ^ 50 := by
  have ea : a % 2 ^ 16 + 2 ^ 16 * (a / 2 ^ 16) = a := Nat.mod_add_div a _
  have eb : b % 2 ^ 16 + 2 ^ 16 * (b / 2 ^ 16) = b := Nat.mod_add_div b _
  have ha1 : a % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
  have hb1 : b % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
  have ha2 : a / 2 ^ 16 < 2 ^ 16 := by omega
  have hb2 : b / 2 ^ 16 < 2 ^ 16 := by omega
  generalize a % 2 ^ 16 = e at *
  generalize b % 2 ^ 16 = e' at *
  generalize a / 2 ^ 16 = h at *
  generalize b / 2 ^ 16 = h' at *
  subst ea eb
  have key : ((e + 2 ^ 16 * h : ℕ) : ℤ) * ((e' + 2 ^ 16 * h' : ℕ) : ℤ) - (Bn : ℤ) * ((h : ℤ) * (h' : ℤ))
      = (e : ℤ) * e' + 2 ^ 16 * ((e : ℤ) * h' + (h : ℤ) * e') := by
    push_cast [Bn]; ring
  rw [key]
  have e1 : (e : ℤ) ≤ 2 ^ 16 := by exact_mod_cast ha1.le
  have e2 : (e' : ℤ) ≤ 2 ^ 16 := by exact_mod_cast hb1.le
  have e3 : (h : ℤ) ≤ 2 ^ 16 := by exact_mod_cast ha2.le
  have e4 : (h' : ℤ) ≤ 2 ^ 16 := by exact_mod_cast hb2.le
  have n1 : (0 : ℤ) ≤ e := by positivity
  have n2 : (0 : ℤ) ≤ e' := by positivity
  have n3 : (0 : ℤ) ≤ h := by positivity
  have n4 : (0 : ℤ) ≤ h' := by positivity
  have p1 : (e : ℤ) * e' ≤ 2 ^ 16 * 2 ^ 16 := mul_le_mul e1 e2 n2 (by positivity)
  have p2 : (e : ℤ) * h' ≤ 2 ^ 16 * 2 ^ 16 := mul_le_mul e1 e4 n4 (by positivity)
  have p3 : (h : ℤ) * e' ≤ 2 ^ 16 * 2 ^ 16 := mul_le_mul e3 e2 n2 (by positivity)
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg n1 n2, mul_nonneg n1 n4, mul_nonneg n3 n2]

/-- **The carry window of the `mul` identity** at `M = 2^25 − 1`:
every coefficient `d` of `W − C` has `−B < d` and `d + M < B·(M + 1)`. -/
theorem ds_bound (A B C : List ℕ) (hA : ∀ w ∈ A, w < 2 ^ 32) (hB : ∀ w ∈ B, w < 2 ^ 32)
    (hC : ∀ w ∈ C, w < 2 ^ 32) (hlA : A.length ≤ 62) (hlB : B.length ≤ 62) :
    ∀ d ∈ addL (wL A B) (negL (zl C)),
      -(Bn : ℤ) < d ∧ d + (2 ^ 25 - 1) < (Bn : ℤ) * ((2 ^ 25 - 1) + 1) := by
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hd
  have hk' : (addL (wL A B) (negL (zl C))).getD k 0 = (addL (wL A B) (negL (zl C)))[k] := by
    simp [List.getD_eq_getElem?_getD, hk]
  rw [← hk', getD_addL, getD_negL, getD_zl]
  have hc : ((C.getD k 0 : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast getD_lt C _ hC (by norm_num) k
  have hc0 : (0 : ℤ) ≤ ((C.getD k 0 : ℕ) : ℤ) := by positivity
  unfold wL
  rw [getD_addL, getD_mulL (zl A) (zl B) k, getD_mulL_lin]
  simp only [getD_mulL (zl (hiL A)) (zl (hiL B))]
  -- bounds on the pieces
  set TT : ℕ → ℤ := fun i => ((A.getD i 0 : ℕ) : ℤ) * ((B.getD (k - i) 0 : ℕ) : ℤ) -
    (Bn : ℤ) * (((A.getD i 0 / 2 ^ 16 : ℕ) : ℤ) * ((B.getD (k - i) 0 / 2 ^ 16 : ℕ) : ℤ)) with hTT
  have hsplit : (∑ i ∈ Finset.range (k + 1), (zl A).getD i 0 * (zl B).getD (k - i) 0) +
      -(Bn : ℤ) * (∑ i ∈ Finset.range (k + 1), (zl (hiL A)).getD i 0 * (zl (hiL B)).getD (k - i) 0) =
      ∑ i ∈ Finset.range (k + 1), TT i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hTT, getD_zl, getD_hiL]; ring
  have hT0 : ∀ i, 0 ≤ TT i := fun i =>
    (term_bound _ _ (getD_lt A _ hA (by norm_num) i) (getD_lt B _ hB (by norm_num) (k - i))).1
  have hT1 : ∀ i, TT i ≤ if i < 62 then 2 ^ 50 else 0 := fun i => by
    by_cases h : i < 62
    · rw [if_pos h]
      exact (term_bound _ _ (getD_lt A _ hA (by norm_num) i) (getD_lt B _ hB (by norm_num) (k - i))).2
    · rw [if_neg h]
      have : A.getD i 0 = 0 := getD_zero_of_len A 62 hlA i (by omega)
      rw [hTT]
      simp only [this, Nat.zero_div, Nat.cast_zero, zero_mul, mul_zero, sub_zero, le_refl]
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), TT i := Finset.sum_nonneg fun i _ => hT0 i
  have hS1 : ∑ i ∈ Finset.range (k + 1), TT i ≤ 62 * 2 ^ 50 := by
    calc ∑ i ∈ Finset.range (k + 1), TT i
        ≤ ∑ i ∈ Finset.range (k + 1), (if i < 62 then (2 : ℤ) ^ 50 else 0) := Finset.sum_le_sum fun i _ => hT1 i
      _ ≤ (min (k + 1) 62 : ℕ) * 2 ^ 50 := sum_ite_le _ (by positivity) _
      _ ≤ 62 * 2 ^ 50 := by
        have : ((min (k + 1) 62 : ℕ) : ℤ) ≤ 62 := by exact_mod_cast Nat.min_le_right _ _
        nlinarith
  -- the second piece
  have hH : 0 ≤ (if k = 0 then (0 : ℤ) else ∑ i ∈ Finset.range (k - 1 + 1),
      (zl (hiL A)).getD i 0 * (zl (hiL B)).getD (k - 1 - i) 0) ∧
      (if k = 0 then (0 : ℤ) else ∑ i ∈ Finset.range (k - 1 + 1),
      (zl (hiL A)).getD i 0 * (zl (hiL B)).getD (k - 1 - i) 0) ≤ 62 * 2 ^ 32 := by
    split_ifs with hk0
    · norm_num
    · have hh : ∀ i, 0 ≤ (zl (hiL A)).getD i 0 * (zl (hiL B)).getD (k - 1 - i) 0 ∧
          (zl (hiL A)).getD i 0 * (zl (hiL B)).getD (k - 1 - i) 0 ≤ if i < 62 then 2 ^ 32 else 0 := fun i => by
        simp only [getD_zl, getD_hiL]
        have a1 : A.getD i 0 / 2 ^ 16 < 2 ^ 16 := by
          have := getD_lt A _ hA (by norm_num) i; omega
        have b1 : B.getD (k - 1 - i) 0 / 2 ^ 16 < 2 ^ 16 := by
          have := getD_lt B _ hB (by norm_num) (k - 1 - i); omega
        refine ⟨by positivity, ?_⟩
        by_cases h : i < 62
        · rw [if_pos h]
          have a2 : ((A.getD i 0 / 2 ^ 16 : ℕ) : ℤ) ≤ 2 ^ 16 := by exact_mod_cast a1.le
          have b2 : ((B.getD (k - 1 - i) 0 / 2 ^ 16 : ℕ) : ℤ) ≤ 2 ^ 16 := by exact_mod_cast b1.le
          calc _ ≤ (2 ^ 16 : ℤ) * 2 ^ 16 := mul_le_mul a2 b2 (by positivity) (by positivity)
            _ = 2 ^ 32 := by norm_num
        · rw [if_neg h]
          have : A.getD i 0 = 0 := getD_zero_of_len A 62 hlA i (by omega)
          rw [this]
          simp only [Nat.zero_div, Nat.cast_zero, zero_mul, le_refl]
      refine ⟨Finset.sum_nonneg fun i _ => (hh i).1, ?_⟩
      calc _ ≤ ∑ i ∈ Finset.range (k - 1 + 1), (if i < 62 then (2 : ℤ) ^ 32 else 0) :=
            Finset.sum_le_sum fun i _ => (hh i).2
        _ ≤ (min (k - 1 + 1) 62 : ℕ) * 2 ^ 32 := sum_ite_le _ (by positivity) _
        _ ≤ 62 * 2 ^ 32 := by
          have : ((min (k - 1 + 1) 62 : ℕ) : ℤ) ≤ 62 := by exact_mod_cast Nat.min_le_right _ _
          nlinarith
  have hB32 : (Bn : ℤ) = 2 ^ 32 := by norm_num [Bn]
  constructor <;> nlinarith [hH.1, hH.2, hsplit, hS0, hS1]

/-! ## 2. The block layout `hdr · A · B · C · Q` -/

section Layout
variable {α : Type}

/-- A list laid out as a head, then four runs. -/
def lay (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC nQ : ℕ) : List α :=
  hd :: ((List.range nA).map fA ++ ((List.range nB).map fB ++ ((List.range nC).map fC ++ (List.range nQ).map fQ)))

theorem lay_length (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC nQ : ℕ) :
    (lay hd fA fB fC fQ nA nB nC nQ).length = 1 + nA + nB + nC + nQ := by
  simp [lay]; omega

theorem getD_range_map (f : ℕ → α) (n j : ℕ) (d : α) (h : j < n) :
    ((List.range n).map f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The `j`-th element, by position. -/
def layAt (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC : ℕ) (j : ℕ) : α :=
  if j = 0 then hd else if j ≤ nA then fA (j - 1) else if j ≤ nA + nB then fB (j - 1 - nA)
  else if j ≤ nA + nB + nC then fC (j - 1 - nA - nB) else fQ (j - 1 - nA - nB - nC)

theorem lay_getD (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC nQ : ℕ) (d : α) (j : ℕ)
    (hj : j < 1 + nA + nB + nC + nQ) :
    (lay hd fA fB fC fQ nA nB nC nQ).getD j d = layAt hd fA fB fC fQ nA nB nC j := by
  unfold lay layAt
  rcases j with _ | j
  · simp
  · rw [List.getD_cons_succ, if_neg (Nat.succ_ne_zero j)]
    by_cases h1 : j < nA
    · rw [List.getD_append _ _ _ _ (by simpa using h1), getD_range_map _ _ _ _ h1, if_pos (by omega)]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
      simp only [List.length_map, List.length_range]
      by_cases h2 : j - nA < nB
      · rw [List.getD_append _ _ _ _ (by simpa using h2), getD_range_map _ _ _ _ h2, if_neg (by omega),
          if_pos (by omega)]
        congr 1
      · rw [List.getD_append_right _ _ _ _ (by simpa using h2)]
        simp only [List.length_map, List.length_range]
        by_cases h3 : j - nA - nB < nC
        · rw [List.getD_append _ _ _ _ (by simpa using h3), getD_range_map _ _ _ _ h3, if_neg (by omega),
            if_neg (by omega), if_pos (by omega)]
          congr 1
        · rw [List.getD_append_right _ _ _ _ (by simpa using h3)]
          simp only [List.length_map, List.length_range]
          rw [getD_range_map _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          congr 1

theorem layAt_zero (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC : ℕ) :
    layAt hd fA fB fC fQ nA nB nC 0 = hd := by simp [layAt]
theorem layAt_A (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ nA) :
    layAt hd fA fB fC fQ nA nB nC j = fA (j - 1) := by
  unfold layAt; rw [if_neg (by omega), if_pos h2]
theorem layAt_B (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC j : ℕ) (h1 : nA < j) (h2 : j ≤ nA + nB) :
    layAt hd fA fB fC fQ nA nB nC j = fB (j - 1 - nA) := by
  unfold layAt; rw [if_neg (by omega), if_neg (by omega), if_pos h2]
theorem layAt_C (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC j : ℕ) (h1 : nA + nB < j) (h2 : j ≤ nA + nB + nC) :
    layAt hd fA fB fC fQ nA nB nC j = fC (j - 1 - nA - nB) := by
  unfold layAt; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]
theorem layAt_Q (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC j : ℕ) (h1 : nA + nB + nC < j) :
    layAt hd fA fB fC fQ nA nB nC j = fQ (j - 1 - nA - nB - nC) := by
  unfold layAt; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The pair lemma**: a relation holding on every consecutive pair of the layout (and between the last row and any
admissible successor) holds at every row against every `NextOK`-style successor. -/
theorem lay_sat (R : α → α → Prop) (OK : α → Prop) (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC nQ : ℕ) (d : α)
    (hA : 1 ≤ nA) (hB : 1 ≤ nB) (hC : 1 ≤ nC) (hQ : 1 ≤ nQ)
    (h0 : R hd (fA 0))
    (hAA : ∀ i, i + 1 < nA → R (fA i) (fA (i + 1))) (hBB : ∀ i, i + 1 < nB → R (fB i) (fB (i + 1)))
    (hCC : ∀ i, i + 1 < nC → R (fC i) (fC (i + 1))) (hQQ : ∀ i, i + 1 < nQ → R (fQ i) (fQ (i + 1)))
    (hAB : R (fA (nA - 1)) (fB 0)) (hBC : R (fB (nB - 1)) (fC 0)) (hCQ : R (fC (nC - 1)) (fQ 0))
    (hQend : ∀ nxt, OK nxt → R (fQ (nQ - 1)) nxt) :
    ∀ j < 1 + nA + nB + nC + nQ, ∀ nxt,
      ((j + 1 < 1 + nA + nB + nC + nQ → nxt = (lay hd fA fB fC fQ nA nB nC nQ).getD (j + 1) d) ∧
        (1 + nA + nB + nC + nQ ≤ j + 1 → OK nxt)) →
      R ((lay hd fA fB fC fQ nA nB nC nQ).getD j d) nxt := by
  intro j hj nxt ⟨h1, h2⟩
  rw [lay_getD _ _ _ _ _ _ _ _ _ _ _ hj]
  by_cases hl : j + 1 < 1 + nA + nB + nC + nQ
  · rw [h1 hl, lay_getD _ _ _ _ _ _ _ _ _ _ _ hl]
    by_cases e0 : j = 0
    · subst e0
      rw [layAt_zero, layAt_A _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
      exact h0
    by_cases eA : j ≤ nA
    · rw [layAt_A _ _ _ _ _ _ _ _ _ (by omega) eA]
      by_cases eA' : j + 1 ≤ nA
      · rw [layAt_A _ _ _ _ _ _ _ _ _ (by omega) eA', show j + 1 - 1 = j - 1 + 1 by omega]
        exact hAA (j - 1) (by omega)
      · rw [layAt_B _ _ _ _ _ _ _ _ _ (by omega) (by omega), show j + 1 - 1 - nA = 0 by omega,
          show j - 1 = nA - 1 by omega]
        exact hAB
    by_cases eB : j ≤ nA + nB
    · rw [layAt_B _ _ _ _ _ _ _ _ _ (by omega) eB]
      by_cases eB' : j + 1 ≤ nA + nB
      · rw [layAt_B _ _ _ _ _ _ _ _ _ (by omega) eB', show j + 1 - 1 - nA = j - 1 - nA + 1 by omega]
        exact hBB (j - 1 - nA) (by omega)
      · rw [layAt_C _ _ _ _ _ _ _ _ _ (by omega) (by omega), show j + 1 - 1 - nA - nB = 0 by omega,
          show j - 1 - nA = nB - 1 by omega]
        exact hBC
    by_cases eC : j ≤ nA + nB + nC
    · rw [layAt_C _ _ _ _ _ _ _ _ _ (by omega) eC]
      by_cases eC' : j + 1 ≤ nA + nB + nC
      · rw [layAt_C _ _ _ _ _ _ _ _ _ (by omega) eC', show j + 1 - 1 - nA - nB = j - 1 - nA - nB + 1 by omega]
        exact hCC (j - 1 - nA - nB) (by omega)
      · rw [layAt_Q _ _ _ _ _ _ _ _ _ (by omega), show j + 1 - 1 - nA - nB - nC = 0 by omega,
          show j - 1 - nA - nB = nC - 1 by omega]
        exact hCQ
    · rw [layAt_Q _ _ _ _ _ _ _ _ _ (by omega), layAt_Q _ _ _ _ _ _ _ _ _ (by omega),
        show j + 1 - 1 - nA - nB - nC = j - 1 - nA - nB - nC + 1 by omega]
      exact hQQ (j - 1 - nA - nB - nC) (by omega)
  · have hlast : j + 1 = 1 + nA + nB + nC + nQ := by omega
    rw [layAt_Q _ _ _ _ _ _ _ _ _ (by omega), show j - 1 - nA - nB - nC = nQ - 1 by omega]
    exact hQend nxt (h2 (by omega))

theorem layAt_prop (P : α → Prop) (hd : α) (fA fB fC fQ : ℕ → α) (nA nB nC j : ℕ)
    (hA : ∀ i, P (fA i)) (hB : ∀ i, P (fB i)) (hC : ∀ i, P (fC i)) (hQ : ∀ i, P (fQ i)) (hj : j ≠ 0) :
    P (layAt hd fA fB fC fQ nA nB nC j) := by
  unfold layAt
  rw [if_neg hj]
  split_ifs
  · exact hA _
  · exact hB _
  · exact hC _
  · exact hQ _

end Layout

/-! ## 3. The slots of a `mul` call -/

section MulSlots

/-- The factor slot `ra`. -/
def sA (p : ℕ) (cl : CallL) : SlotL := handleSlot p .mul cl.lbv 0 cl.a cl.kA cl.vA
/-- The factor slot `rb`. -/
def sB (p : ℕ) (cl : CallL) : SlotL := handleSlot p .mul cl.lbv 1 cl.b cl.kB cl.vB
/-- The result slot `rc`. -/
def sC (p : ℕ) (cl : CallL) : SlotL := handleSlot p .mul cl.lbv 2 cl.c cl.kE cl.vE
/-- The `mQM` carry slot. -/
def sQ (p : ℕ) (cl : CallL) : SlotL :=
  qSlot .mul false (carr (Bn : ℤ) 0 (addL (wL (sA p cl).vw (sB p cl).vw) (negL (zl (sC p cl).vw))))

theorem slotsOf_mul (p : ℕ) (cl : CallL) (hop : cl.op = .mul) :
    slotsOf p cl = [sA p cl, sB p cl, sC p cl, sQ p cl] := by
  simp only [slotsOf, hop]; rfl

theorem sA_shape (p : ℕ) (cl : CallL) :
    (sA p cl).role = some 0 ∧ ((sA p cl).mode = 1 ∨ (sA p cl).mode = 2) ∧ (sA p cl).cf1 = 0 ∧ (sA p cl).cf2 = 0 := by
  unfold sA handleSlot; split_ifs <;> simp_all [coefOf, isFactor]

theorem sB_shape (p : ℕ) (cl : CallL) :
    (sB p cl).role = some 1 ∧ ((sB p cl).mode = 1 ∨ (sB p cl).mode = 2) ∧ (sB p cl).cf1 = 0 ∧ (sB p cl).cf2 = 0 := by
  unfold sB handleSlot; split_ifs <;> simp_all [coefOf, isFactor]

theorem sC_shape (p : ℕ) (cl : CallL) :
    (sC p cl).role = some 2 ∧ ((sC p cl).mode = 0 ∨ (sC p cl).mode = 1) ∧ (sC p cl).cf1 = -1 ∧ (sC p cl).cf2 = 0 := by
  unfold sC handleSlot; split_ifs <;> simp_all [coefOf, isFactor]

theorem sQ_shape (p : ℕ) (cl : CallL) :
    (sQ p cl).role = none ∧ (sQ p cl).mode = 5 ∧ (sQ p cl).cf1 = 1 ∧ (sQ p cl).cf2 = 0 := by
  unfold sQ qSlot; simp

theorem handleSlot_words_pos (p : ℕ) (hpG : p = Nock.Atoms.p) (o : PrimOp) (lb r v k s : ℕ) :
    1 ≤ (handleSlot p o lb r v k s).words.length := by
  unfold handleSlot
  split_ifs with h1 h2
  · simp [splitOf]
  · have : Nock.Atoms.IsBig v := by unfold Nock.Atoms.IsBig; omega
    have := Nock.Atoms.two_le_length_of_big this
    simpa using (by omega : 1 ≤ (Nock.Atoms.limbs v).length)
  · simp

theorem sQ_words_pos (p : ℕ) (cl : CallL) : 1 ≤ (sQ p cl).words.length := by
  unfold sQ qSlot; simp only [Bool.false_eq_true, if_false]
  split_ifs with h
  · simp
  · exact List.length_pos_iff.mpr h

theorem handleSlot_vw_lt (p : ℕ) (hpG : p = Nock.Atoms.p) (o : PrimOp) (lb r v k s : ℕ) :
    ∀ w ∈ (handleSlot p o lb r v k s).vw, w < 2 ^ 32 := by
  have hp : p < 2 ^ 32 * 2 ^ 32 := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  unfold handleSlot
  split_ifs with h1 h2
  · intro w hw
    simp only [splitOf, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Nat.mod_lt _ (by norm_num)
    · show v / 2 ^ 32 < 2 ^ 32
      exact Nat.div_lt_of_lt_mul (by omega)
  · intro w hw
    have := (Nock.Atoms.limbs_canonical v).1 w hw
    simpa [Nock.Atoms.B] using this
  · intro w hw
    have := (Nock.Atoms.limbs_canonical v).1 w hw
    simpa [Nock.Atoms.B] using this

theorem handleSlot_val (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) :
    Nock.Atoms.val (handleSlot p o lb r v k s).vw = v := by
  unfold handleSlot
  split_ifs with h1 h2
  · simp only [splitOf, Nock.Atoms.val_cons, Nock.Atoms.val_nil]
    have : Nock.Atoms.B = 2 ^ 32 := rfl
    rw [this]; have := Nat.mod_add_div v (2 ^ 32); omega
  · exact Nock.Atoms.val_limbs v
  · exact Nock.Atoms.val_limbs v

theorem sA_vw_words (p : ℕ) (cl : CallL) : (sA p cl).vw = (sA p cl).words := by
  unfold sA handleSlot; split_ifs with h1 h2
  · rfl
  · rfl
  · simp_all [isFactor]

theorem sB_vw_words (p : ℕ) (cl : CallL) : (sB p cl).vw = (sB p cl).words := by
  unfold sB handleSlot; split_ifs with h1 h2
  · rfl
  · rfl
  · simp_all [isFactor]

/-- **The honest `mul` identity vanishes at `X = B`.** -/
theorem ds_eval_zero (p : ℕ) (cl : CallL) (hop : cl.op = .mul) (hcl : CallOK p cl) :
    evB (Bn : ℤ) (addL (wL (sA p cl).vw (sB p cl).vw) (negL (zl (sC p cl).vw))) = 0 := by
  have hsem := hcl.sem
  rw [hop] at hsem
  simp only [Nock.Jet.Prim.primSem, Option.some.injEq] at hsem
  rw [evB_addL, evB_negL, evB_wL, evB_zl, evB_zl, evB_zl]
  simp only [sA, sB, sC, handleSlot_val]
  rw [← hsem]; push_cast; ring

/-- **The `mQM` words fit in 25 bits.** -/
theorem sQ_words_lt (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hop : cl.op = .mul) (hcl : CallOK p cl) :
    ∀ w ∈ (sQ p cl).words, w < 2 ^ 25 := by
  have hA62 : (sA p cl).vw.length ≤ 62 := by
    have := hcl.limbs62 (sA p cl) (by rw [slotsOf_mul p cl hop]; simp)
      (by rcases (sA_shape p cl).2.1 with h | h <;> simp [h])
    rwa [sA_vw_words]
  have hB62 : (sB p cl).vw.length ≤ 62 := by
    have := hcl.limbs62 (sB p cl) (by rw [slotsOf_mul p cl hop]; simp)
      (by rcases (sB_shape p cl).2.1 with h | h <;> simp [h])
    rwa [sB_vw_words]
  have hd := ds_bound (sA p cl).vw (sB p cl).vw (sC p cl).vw (handleSlot_vw_lt p hpG _ _ _ _ _ _)
    (handleSlot_vw_lt p hpG _ _ _ _ _ _) (handleSlot_vw_lt p hpG _ _ _ _ _ _) hA62 hB62
  have hq := carr_bound0 (B := (Bn : ℤ)) (M := 2 ^ 25 - 1) (by norm_num [Bn]) (by norm_num) _
    (ds_eval_zero p cl hop hcl) hd
  intro w hw
  unfold sQ qSlot at hw
  simp only [Bool.false_eq_true, if_false] at hw
  split_ifs at hw with hws
  · simp at hw; omega
  · obtain ⟨q, hqm, rfl⟩ := List.mem_map.mp hw
    have := hq q hqm
    omega

end MulSlots

/-! ## 4. Row-level gate lemmas -/

section Rows
variable {F : Type} [Field F]

open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG)

@[simp] theorem slotRow_role (p : ℕ) (cl : CallL) (s : SlotL) (i j : ℕ) :
    (slotRow (F := F) p cl s i).role j = ind (s.role = some j) := rfl
@[simp] theorem slotRow_mode (p : ℕ) (cl : CallL) (s : SlotL) (i j : ℕ) :
    (slotRow (F := F) p cl s i).mode j = ind (j = s.mode) := rfl
@[simp] theorem slotRow_op (p : ℕ) (cl : CallL) (s : SlotL) (i j : ℕ) :
    (slotRow (F := F) p cl s i).op j = ind (j = opIx cl.op) := rfl
@[simp] theorem slotRow_eos (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) :
    (slotRow (F := F) p cl s i).eos = ind (i + 1 = s.words.length) := rfl
@[simp] theorem slotRow_fst (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) :
    (slotRow (F := F) p cl s i).fst = ind (i = 0) := rfl
@[simp] theorem slotRow_sL (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) :
    (slotRow (F := F) p cl s i).sL = 1 := rfl
@[simp] theorem slotRow_cf1 (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) :
    (slotRow (F := F) p cl s i).cf1 = if i = 0 then (s.cf1 : F) else 0 := rfl
@[simp] theorem slotRow_cf2 (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) :
    (slotRow (F := F) p cl s i).cf2 = if i = 0 then (s.cf2 : F) else 0 := rfl
@[simp] theorem slotRow_bit (p : ℕ) (cl : CallL) (s : SlotL) (i t : ℕ) :
    (slotRow (F := F) p cl s i).bit t = (bitOf (s.words.getD i 0) t : F) := rfl

@[simp] theorem hdrRow_role (cl : CallL) (j : ℕ) : (hdrRow (F := F) cl).role j = 0 := rfl
@[simp] theorem hdrRow_mode (cl : CallL) (j : ℕ) : (hdrRow (F := F) cl).mode j = 0 := rfl
@[simp] theorem hdrRow_eos (cl : CallL) : (hdrRow (F := F) cl).eos = 0 := rfl
@[simp] theorem hdrRow_fst (cl : CallL) : (hdrRow (F := F) cl).fst = 0 := rfl
@[simp] theorem hdrRow_sL (cl : CallL) : (hdrRow (F := F) cl).sL = 0 := rfl
@[simp] theorem hdrRow_op (cl : CallL) (j : ℕ) : (hdrRow (F := F) cl).op j = ind (j = opIx cl.op) := rfl
@[simp] theorem hdrRow_bit (cl : CallL) (t : ℕ) : (hdrRow (F := F) cl).bit t = 0 := rfl

theorem opIx_mul (cl : CallL) (hop : cl.op = .mul) (j : ℕ) :
    (ind (j = opIx cl.op) : F) = if j = 3 then 1 else 0 := by
  simp [ind, hop, opIx]

/-- Every `gSeq` gate carries the factor `eos`. -/
theorem gSeq_eos0 (cur nxt : BRow F) (h : cur.eos = 0) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AG F)), (AG.gate a).eval (envB cur.col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.ar, AG.gate, CoeffExpr.eval, envB, h]

theorem gSeq_eval (cur nxt : BRow F)
    (o0 : cur.op 0 = 0) (o1 : cur.op 1 = 0) (o2 : cur.op 2 = 0) (o3 : cur.op 3 = 1) (o4 : cur.op 4 = 0)
    (o5 : cur.op 5 = 0) (r3 : cur.role 3 = 0) (r4 : cur.role 4 = 0) (r5 : cur.role 5 = 0)
    (r6 : cur.role 6 = 0) (m4 : cur.mode 4 = 0)
    (d0 : cur.eos * cur.role 0 = 0 ∨ nxt.role 1 = 1) (d1 : cur.eos * cur.role 1 = 0 ∨ nxt.role 2 = 1)
    (d2 : cur.eos * cur.role 2 = 0 ∨ nxt.mode 5 = 1) (d3 : cur.eos * cur.mode 5 = 0 ∨ nxt.sL = 0) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AG F)), (AG.gate a).eval (envB cur.col nxt.col) = 0 := by
  have e0 : cur.eos * cur.role 0 * (1 - nxt.role 1) = 0 := by
    rcases d0 with h | h
    · rw [h, zero_mul]
    · rw [h]; ring
  have e1 : cur.eos * cur.role 1 * (1 - nxt.role 2) = 0 := by
    rcases d1 with h | h
    · rw [h, zero_mul]
    · rw [h]; ring
  have e2 : cur.eos * cur.role 2 * (1 - nxt.mode 5) = 0 := by
    rcases d2 with h | h
    · rw [h, zero_mul]
    · rw [h]; ring
  have e3 : cur.eos * cur.mode 5 * nxt.sL = 0 := by
    rcases d3 with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [AluSZChipJ9.succ, AluSZChipJ9.prod3, AluSZChipJ9.ar, AluSZChipJ9.sumC, CoeffExpr.sumList, List.foldr_cons, List.foldr_nil, AG.gate,
    CoeffExpr.eval, envB, BRow.col_oAdd, BRow.col_oSub, BRow.col_oLt, BRow.col_oMul, BRow.col_oDiv,
    BRow.col_oMod, BRow.col_ra, BRow.col_rb, BRow.col_rc, BRow.col_rd, BRow.col_rx, BRow.col_ry, BRow.col_rs,
    BRow.col_mQ1, BRow.col_mQM, BRow.col_eos, BRow.col_sL, o0, o1, o2, o3, o4, o5, r3, r4, r5, r6, m4] <;>
  first | ring1 | linear_combination e0 | linear_combination e1 | linear_combination e2 |
    linear_combination e3

theorem gCoef_eval (cur nxt : BRow F)
    (o0 : cur.op 0 = 0) (o1 : cur.op 1 = 0) (o2 : cur.op 2 = 0) (o3 : cur.op 3 = 1) (o4 : cur.op 4 = 0)
    (o5 : cur.op 5 = 0) (r3 : cur.role 3 = 0) (r4 : cur.role 4 = 0) (r5 : cur.role 5 = 0)
    (r6 : cur.role 6 = 0) (m4 : cur.mode 4 = 0)
    (a0 : cur.fst * cur.role 0 * cur.cf1 = 0) (a0' : cur.fst * cur.role 0 * cur.cf2 = 0)
    (a1 : cur.fst * cur.role 1 * cur.cf1 = 0) (a1' : cur.fst * cur.role 1 * cur.cf2 = 0)
    (a2 : cur.fst * cur.role 2 * (cur.cf1 + 1) = 0) (a2' : cur.fst * cur.role 2 * cur.cf2 = 0)
    (aq : cur.fst * cur.mode 5 * (cur.cf1 - 1) = 0) (aq' : cur.fst * cur.mode 5 * cur.cf2 = 0) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AG F)), (AG.gate a).eval (envB cur.col nxt.col) = 0 := by
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
  simp only [AluSZChipJ9.coef, AluSZChipJ9.sgnLt, AluSZChipJ9.prod3, AluSZChipJ9.ar, AluSZChipJ9.sumC,
    CoeffExpr.sumList, List.foldr_cons, List.foldr_nil, AG.gate,
    CoeffExpr.eval, envB, BRow.col_oAdd, BRow.col_oSub, BRow.col_oLt, BRow.col_oMul, BRow.col_oDiv,
    BRow.col_oMod, BRow.col_ra, BRow.col_rb, BRow.col_rc, BRow.col_rd, BRow.col_rx, BRow.col_ry, BRow.col_rs,
    BRow.col_mQ1, BRow.col_mQM, BRow.col_fst, BRow.col_cf1, BRow.col_cf2, BRow.col_lb, o0, o1, o2, o3, o4, o5,
    r3, r4, r5, r6, m4] <;>
  first | ring1 | linear_combination a0 | linear_combination a0' | linear_combination a1 |
    linear_combination a1' | linear_combination a2 | linear_combination a2' | linear_combination aq |
    linear_combination aq'

/-- The mQM part of `gBits`. -/
def gBitsM : List (AG F) :=
  (List.range 7).map (fun t => AluSZChipJ9.ar (.mul (cv AluSZChipJ9.mQM) (cv (AluSZChipJ9.bt0 + 25 + t))))

theorem gBits_split : (AluSZChipJ9.gBits : List (AG F)) =
    (List.range 32).map (fun t => AluSZChipJ9.ar (boolE (cv (AluSZChipJ9.bt0 + t)))) ++ gBitsM := rfl

theorem gBitsM_eval (cur nxt : BRow F) (h : ∀ t < 7, cur.mode 5 * cur.bit (25 + t) = 0) :
    ∀ a ∈ (gBitsM : List (AG F)), (AG.gate a).eval (envB cur.col nxt.col) = 0 := by
  intro a ha
  simp only [gBitsM, List.mem_map, List.mem_range] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  have hc := BRow.col_bit cur (25 + t) (by omega)
  simp only [AluSZChipJ9.ar, AG.gate, CoeffExpr.eval, envB, BRow.col_mQM]
  rw [Nat.add_assoc, hc]
  exact h t ht

end Rows

/-! ## 5. The groups -/

section Groups
variable {F : Type} [Field F]

open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG)

/-- A gate list vanishes at a (current, next) pair. -/
def PairOK (gs : List (AG F)) (cur nxt : BRow F) : Prop :=
  ∀ a ∈ gs, (AG.gate a).eval (envB cur.col nxt.col) = 0

theorem blockB_mul (p : ℕ) (cl : CallL) (hop : cl.op = .mul) :
    blockB (F := F) p cl = lay (hdrRow cl) (slotRow p cl (sA p cl)) (slotRow p cl (sB p cl))
      (slotRow p cl (sC p cl)) (slotRow p cl (sQ p cl)) (sA p cl).words.length (sB p cl).words.length
      (sC p cl).words.length (sQ p cl).words.length := by
  unfold blockB
  rw [slotsOf_mul p cl hop]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, lay, slotRows]

/-- **The pair reduction**: a gate list holds on the whole `mul` block once it holds on the ten pair shapes. -/
theorem groupSat_mul (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hop : cl.op = .mul)
    (gs : List (AG F))
    (h0 : PairOK gs (hdrRow cl) (slotRow p cl (sA p cl) 0))
    (hAA : ∀ i, i + 1 < (sA p cl).words.length →
      PairOK gs (slotRow p cl (sA p cl) i) (slotRow p cl (sA p cl) (i + 1)))
    (hBB : ∀ i, i + 1 < (sB p cl).words.length →
      PairOK gs (slotRow p cl (sB p cl) i) (slotRow p cl (sB p cl) (i + 1)))
    (hCC : ∀ i, i + 1 < (sC p cl).words.length →
      PairOK gs (slotRow p cl (sC p cl) i) (slotRow p cl (sC p cl) (i + 1)))
    (hQQ : ∀ i, i + 1 < (sQ p cl).words.length →
      PairOK gs (slotRow p cl (sQ p cl) i) (slotRow p cl (sQ p cl) (i + 1)))
    (hAB : PairOK gs (slotRow p cl (sA p cl) ((sA p cl).words.length - 1)) (slotRow p cl (sB p cl) 0))
    (hBC : PairOK gs (slotRow p cl (sB p cl) ((sB p cl).words.length - 1)) (slotRow p cl (sC p cl) 0))
    (hCQ : PairOK gs (slotRow p cl (sC p cl) ((sC p cl).words.length - 1)) (slotRow p cl (sQ p cl) 0))
    (hQend : ∀ nxt : BRow F, nxt.sL = 0 → nxt.fst = 0 →
      PairOK gs (slotRow p cl (sQ p cl) ((sQ p cl).words.length - 1)) nxt) :
    GroupSat (F := F) p cl gs := by
  intro j hj nxt hn a ha
  rw [blockB_mul p cl hop] at hj hn ⊢
  simp only [NextOK, lay_length] at hn hj
  exact lay_sat (PairOK gs) (fun n : BRow F => n.sL = 0 ∧ n.fst = 0) _ _ _ _ _ _ _ _ _ BRow.zero
    (handleSlot_words_pos p hpG _ _ _ _ _ _) (handleSlot_words_pos p hpG _ _ _ _ _ _)
    (handleSlot_words_pos p hpG _ _ _ _ _ _) (sQ_words_pos p cl)
    h0 hAA hBB hCC hQQ hAB hBC hCQ (fun n h => hQend n h.1 h.2) j hj nxt hn a ha

/-! ### gSeq -/

theorem gSeq_slotRow (p : ℕ) (cl : CallL) (hop : cl.op = .mul) (s : SlotL) (i : ℕ) (nxt : BRow F)
    (hr : s.role = none ∨ s.role = some 0 ∨ s.role = some 1 ∨ s.role = some 2) (hm : s.mode ≠ 4)
    (h0 : i + 1 = s.words.length → s.role = some 0 → nxt.role 1 = 1)
    (h1 : i + 1 = s.words.length → s.role = some 1 → nxt.role 2 = 1)
    (h2 : i + 1 = s.words.length → s.role = some 2 → nxt.mode 5 = 1)
    (h3 : i + 1 = s.words.length → s.mode = 5 → nxt.sL = 0) :
    PairOK (AluSZChipJ9.gSeq : List (AG F)) (slotRow p cl s i) nxt := by
  by_cases hE : i + 1 = s.words.length
  · have hR : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → (ind (s.role = some j) : F) = 0 := by
      intro j a b c
      rcases hr with h | h | h | h <;> simp [ind, h] <;> omega
    refine gSeq_eval (slotRow p cl s i) nxt ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [opIx_mul cl hop]
    · simp [opIx_mul cl hop]
    · simp [opIx_mul cl hop]
    · simp [opIx_mul cl hop]
    · simp [opIx_mul cl hop]
    · simp [opIx_mul cl hop]
    · exact hR 3 (by omega) (by omega) (by omega)
    · exact hR 4 (by omega) (by omega) (by omega)
    · exact hR 5 (by omega) (by omega) (by omega)
    · exact hR 6 (by omega) (by omega) (by omega)
    · simp [ind]; exact fun h => hm h.symm
    · by_cases hs : s.role = some 0
      · right; exact h0 hE hs
      · left; simp [ind, hE, hs]
    · by_cases hs : s.role = some 1
      · right; exact h1 hE hs
      · left; simp [ind, hE, hs]
    · by_cases hs : s.role = some 2
      · right; exact h2 hE hs
      · left; simp [ind, hE, hs]
    · by_cases hs : s.mode = 5
      · right; exact h3 hE hs
      · left; simp [ind, hE, hs]; intro h; exact hs h.symm
  · exact gSeq_eos0 _ _ (by simp [ind, hE])

/-- **`GroupSat gSeq` for `mul`.** -/
theorem gSeq_sat_mul (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hop : cl.op = .mul) :
    GroupSat (F := F) p cl AluSZChipJ9.gSeq := by
  have mA : (sA p cl).mode ≠ 4 := by rcases (sA_shape p cl).2.1 with h | h <;> omega
  have mB : (sB p cl).mode ≠ 4 := by rcases (sB_shape p cl).2.1 with h | h <;> omega
  have mC : (sC p cl).mode ≠ 4 := by rcases (sC_shape p cl).2.1 with h | h <;> omega
  have mQ : (sQ p cl).mode ≠ 4 := by rw [(sQ_shape p cl).2.1]; omega
  have rA := (sA_shape p cl).1
  have rB := (sB_shape p cl).1
  have rC := (sC_shape p cl).1
  have rQ := (sQ_shape p cl).1
  refine groupSat_mul p cl hpG hop _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact gSeq_eos0 _ _ (by simp)
  · intro i hi
    exact gSeq_slotRow p cl hop _ i _ (Or.inr (Or.inl rA)) mA (fun hE => absurd hE (by omega))
      (fun hE => absurd hE (by omega)) (fun hE => absurd hE (by omega)) (fun hE => absurd hE (by omega))
  · intro i hi
    exact gSeq_slotRow p cl hop _ i _ (Or.inr (Or.inr (Or.inl rB))) mB (fun hE => absurd hE (by omega))
      (fun hE => absurd hE (by omega)) (fun hE => absurd hE (by omega)) (fun hE => absurd hE (by omega))
  · intro i hi
    exact gSeq_slotRow p cl hop _ i _ (Or.inr (Or.inr (Or.inr rC))) mC (fun hE => absurd hE (by omega))
      (fun hE => absurd hE (by omega)) (fun hE => absurd hE (by omega)) (fun hE => absurd hE (by omega))
  · intro i hi
    exact gSeq_slotRow p cl hop _ i _ (Or.inl rQ) mQ (fun hE => absurd hE (by omega))
      (fun hE => absurd hE (by omega)) (fun hE => absurd hE (by omega)) (fun hE => absurd hE (by omega))
  · refine gSeq_slotRow p cl hop _ _ _ (Or.inr (Or.inl rA)) mA ?_ ?_ ?_ ?_
    · intro _ _; simp [rB, ind]
    · intro _ hs; rw [rA] at hs; simp at hs
    · intro _ hs; rw [rA] at hs; simp at hs
    · intro _ hs; exfalso; rcases (sA_shape p cl).2.1 with h | h <;> omega
  · refine gSeq_slotRow p cl hop _ _ _ (Or.inr (Or.inr (Or.inl rB))) mB ?_ ?_ ?_ ?_
    · intro _ hs; rw [rB] at hs; simp at hs
    · intro _ _; simp [rC, ind]
    · intro _ hs; rw [rB] at hs; simp at hs
    · intro _ hs; exfalso; rcases (sB_shape p cl).2.1 with h | h <;> omega
  · refine gSeq_slotRow p cl hop _ _ _ (Or.inr (Or.inr (Or.inr rC))) mC ?_ ?_ ?_ ?_
    · intro _ hs; rw [rC] at hs; simp at hs
    · intro _ hs; rw [rC] at hs; simp at hs
    · intro _ _; simp [(sQ_shape p cl).2.1, ind]
    · intro _ hs; exfalso; rcases (sC_shape p cl).2.1 with h | h <;> omega
  · intro nxt hsl hfst
    refine gSeq_slotRow p cl hop _ _ _ (Or.inl rQ) mQ ?_ ?_ ?_ ?_
    · intro _ hs; rw [rQ] at hs; simp at hs
    · intro _ hs; rw [rQ] at hs; simp at hs
    · intro _ hs; rw [rQ] at hs; simp at hs
    · intro _ _; exact hsl

/-! ### gCoef -/

theorem gCoef_slotRow (p : ℕ) (cl : CallL) (hop : cl.op = .mul) (s : SlotL) (i : ℕ) (nxt : BRow F)
    (hr : s.role = none ∨ s.role = some 0 ∨ s.role = some 1 ∨ s.role = some 2) (hm : s.mode ≠ 4)
    (c0 : s.role = some 0 → s.cf1 = 0 ∧ s.cf2 = 0) (c1 : s.role = some 1 → s.cf1 = 0 ∧ s.cf2 = 0)
    (c2 : s.role = some 2 → s.cf1 = -1 ∧ s.cf2 = 0) (cq : s.mode = 5 → s.cf1 = 1 ∧ s.cf2 = 0) :
    PairOK (AluSZChipJ9.gCoef : List (AG F)) (slotRow p cl s i) nxt := by
  have hR : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → (ind (s.role = some j) : F) = 0 := by
    intro j a b c
    rcases hr with h | h | h | h <;> simp [ind, h] <;> omega
  refine gCoef_eval (slotRow p cl s i) nxt ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [opIx_mul cl hop]
  · simp [opIx_mul cl hop]
  · simp [opIx_mul cl hop]
  · simp [opIx_mul cl hop]
  · simp [opIx_mul cl hop]
  · simp [opIx_mul cl hop]
  · exact hR 3 (by omega) (by omega) (by omega)
  · exact hR 4 (by omega) (by omega) (by omega)
  · exact hR 5 (by omega) (by omega) (by omega)
  · exact hR 6 (by omega) (by omega) (by omega)
  · simp [ind]; exact fun h => hm h.symm
  · by_cases hi : i = 0
    · by_cases hs : s.role = some 0
      · obtain ⟨h1, h2⟩ := c0 hs; simp [ind, hi, hs, h1]
      · simp [ind, hi, hs]
    · simp [ind, hi]
  · by_cases hi : i = 0
    · by_cases hs : s.role = some 0
      · obtain ⟨h1, h2⟩ := c0 hs; simp [ind, hi, hs, h2]
      · simp [ind, hi, hs]
    · simp [ind, hi]
  · by_cases hi : i = 0
    · by_cases hs : s.role = some 1
      · obtain ⟨h1, h2⟩ := c1 hs; simp [ind, hi, hs, h1]
      · simp [ind, hi, hs]
    · simp [ind, hi]
  · by_cases hi : i = 0
    · by_cases hs : s.role = some 1
      · obtain ⟨h1, h2⟩ := c1 hs; simp [ind, hi, hs, h2]
      · simp [ind, hi, hs]
    · simp [ind, hi]
  · by_cases hi : i = 0
    · by_cases hs : s.role = some 2
      · obtain ⟨h1, h2⟩ := c2 hs; simp [ind, hi, hs, h1]
      · simp [ind, hi, hs]
    · simp [ind, hi]
  · by_cases hi : i = 0
    · by_cases hs : s.role = some 2
      · obtain ⟨h1, h2⟩ := c2 hs; simp [ind, hi, hs, h2]
      · simp [ind, hi, hs]
    · simp [ind, hi]
  · by_cases hi : i = 0
    · by_cases hs : s.mode = 5
      · obtain ⟨h1, h2⟩ := cq hs; simp [ind, hi, hs, h1]
      · simp [ind, hi, hs, Ne.symm hs]
    · simp [ind, hi]
  · by_cases hi : i = 0
    · by_cases hs : s.mode = 5
      · obtain ⟨h1, h2⟩ := cq hs; simp [ind, hi, hs, h2]
      · simp [ind, hi, hs, Ne.symm hs]
    · simp [ind, hi]

/-- **`GroupSat gCoef` for `mul`.** -/
theorem gCoef_sat_mul (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hop : cl.op = .mul) :
    GroupSat (F := F) p cl AluSZChipJ9.gCoef := by
  have mA : (sA p cl).mode ≠ 4 := by rcases (sA_shape p cl).2.1 with h | h <;> omega
  have mB : (sB p cl).mode ≠ 4 := by rcases (sB_shape p cl).2.1 with h | h <;> omega
  have mC : (sC p cl).mode ≠ 4 := by rcases (sC_shape p cl).2.1 with h | h <;> omega
  have mQ : (sQ p cl).mode ≠ 4 := by rw [(sQ_shape p cl).2.1]; omega
  have rA := (sA_shape p cl).1
  have rB := (sB_shape p cl).1
  have rC := (sC_shape p cl).1
  have rQ := (sQ_shape p cl).1
  have cA : ∀ (nxt : BRow F) i, PairOK (AluSZChipJ9.gCoef : List (AG F)) (slotRow p cl (sA p cl) i) nxt := by
    intro nxt i
    refine gCoef_slotRow p cl hop _ i nxt (Or.inr (Or.inl rA)) mA (fun _ => ⟨(sA_shape p cl).2.2.1,
      (sA_shape p cl).2.2.2⟩) (fun h => by rw [rA] at h; simp at h) (fun h => by rw [rA] at h; simp at h)
      (fun h => by exfalso; rcases (sA_shape p cl).2.1 with h' | h' <;> omega)
  have cB : ∀ (nxt : BRow F) i, PairOK (AluSZChipJ9.gCoef : List (AG F)) (slotRow p cl (sB p cl) i) nxt := by
    intro nxt i
    refine gCoef_slotRow p cl hop _ i nxt (Or.inr (Or.inr (Or.inl rB))) mB (fun h => by rw [rB] at h; simp at h)
      (fun _ => ⟨(sB_shape p cl).2.2.1, (sB_shape p cl).2.2.2⟩) (fun h => by rw [rB] at h; simp at h)
      (fun h => by exfalso; rcases (sB_shape p cl).2.1 with h' | h' <;> omega)
  have cC : ∀ (nxt : BRow F) i, PairOK (AluSZChipJ9.gCoef : List (AG F)) (slotRow p cl (sC p cl) i) nxt := by
    intro nxt i
    refine gCoef_slotRow p cl hop _ i nxt (Or.inr (Or.inr (Or.inr rC))) mC (fun h => by rw [rC] at h; simp at h)
      (fun h => by rw [rC] at h; simp at h) (fun _ => ⟨(sC_shape p cl).2.2.1, (sC_shape p cl).2.2.2⟩)
      (fun h => by exfalso; rcases (sC_shape p cl).2.1 with h' | h' <;> omega)
  have cQ : ∀ (nxt : BRow F) i, PairOK (AluSZChipJ9.gCoef : List (AG F)) (slotRow p cl (sQ p cl) i) nxt := by
    intro nxt i
    refine gCoef_slotRow p cl hop _ i nxt (Or.inl rQ) mQ (fun h => by rw [rQ] at h; simp at h)
      (fun h => by rw [rQ] at h; simp at h) (fun h => by rw [rQ] at h; simp at h)
      (fun _ => ⟨(sQ_shape p cl).2.2.1, (sQ_shape p cl).2.2.2⟩)
  refine groupSat_mul p cl hpG hop _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [AluSZChipJ9.gCoef, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    simp [AluSZChipJ9.coef, AluSZChipJ9.prod3, AluSZChipJ9.ar, AG.gate, CoeffExpr.eval, envB]
  · exact fun i _ => cA _ i
  · exact fun i _ => cB _ i
  · exact fun i _ => cC _ i
  · exact fun i _ => cQ _ i
  · exact cA _ _
  · exact cB _ _
  · exact cC _ _
  · exact fun nxt _ _ => cQ _ _

/-! ### gBits (the 25-bit `mQM` part) -/

theorem bitOf_ge (w t : ℕ) (hw : w < 2 ^ 25) (ht : 25 ≤ t) : bitOf w t = 0 := by
  unfold bitOf
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) ht))]

theorem gBitsM_slotRow (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) (nxt : BRow F)
    (hq : s.mode = 5 → s.words.getD i 0 < 2 ^ 25) :
    PairOK (gBitsM : List (AG F)) (slotRow p cl s i) nxt := by
  refine gBitsM_eval _ _ fun t ht => ?_
  by_cases hs : s.mode = 5
  · have := bitOf_ge _ (25 + t) (hq hs) (by omega)
    rw [slotRow_bit, this]; simp
  · simp [ind, Ne.symm hs]

/-- **The `mQM` part of `gBits` for `mul`**: `mQM·b_{25+t} = 0`. -/
theorem gBitsM_sat_mul (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hop : cl.op = .mul) (hcl : CallOK p cl) :
    GroupSat (F := F) p cl gBitsM := by
  have hQ := sQ_words_lt p cl hpG hop hcl
  have h5 : ∀ (s : SlotL), s.mode ≠ 5 → ∀ (nxt : BRow F) i, PairOK (gBitsM : List (AG F)) (slotRow p cl s i) nxt :=
    fun s hs nxt i => gBitsM_slotRow p cl s i nxt (fun h => absurd h hs)
  have cQ : ∀ (nxt : BRow F) i, PairOK (gBitsM : List (AG F)) (slotRow p cl (sQ p cl) i) nxt :=
    fun nxt i => gBitsM_slotRow p cl _ i nxt (fun _ => getD_lt _ _ hQ (by norm_num) i)
  have cA := h5 (sA p cl) (by rcases (sA_shape p cl).2.1 with h | h <;> omega)
  have cB := h5 (sB p cl) (by rcases (sB_shape p cl).2.1 with h | h <;> omega)
  have cC := h5 (sC p cl) (by rcases (sC_shape p cl).2.1 with h | h <;> omega)
  refine groupSat_mul p cl hpG hop _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact gBitsM_eval _ _ fun t ht => by simp
  · exact fun i _ => cA _ i
  · exact fun i _ => cB _ i
  · exact fun i _ => cC _ i
  · exact fun i _ => cQ _ i
  · exact cA _ _
  · exact cB _ _
  · exact cC _ _
  · exact fun nxt _ _ => cQ _ _

end Groups

/-! ## 6. The terminal `S1 = S2 = 0` -/

section Term

theorem runSums_length {Q : Type} [CommRing Q] : ∀ (acc : Q × Q) (ds : List (Q × Q)),
    (runSums acc ds).length = ds.length
  | _, [] => rfl
  | acc, d :: ds => by simp [runSums, runSums_length (acc.1 + d.1, acc.2 + d.2) ds]

theorem runSums_last {Q : Type} [CommRing Q] : ∀ (n : ℕ) (acc : Q × Q) (ds : List (Q × Q)),
    ds.length = n + 1 →
    (runSums acc ds).getD n (0, 0) = (acc.1 + (ds.map Prod.fst).sum, acc.2 + (ds.map Prod.snd).sum)
  | 0, acc, [d], _ => by simp [runSums]
  | 0, acc, d :: d' :: ds, h => by simp at h
  | n + 1, acc, [], h => by simp at h
  | n + 1, acc, d :: ds, h => by
    have ih := runSums_last n (acc.1 + d.1, acc.2 + d.2) ds (by simpa using h)
    simp only [runSums, List.getD_cons_succ, ih, List.map_cons, List.sum_cons]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring
  | 0, acc, [], h => by simp at h

theorem blockD_sum {Q : Type} [CommRing Q] (n : ℕ) (hn : 1 ≤ n) (d : Q × Q) :
    ((((List.range n).map fun i => if i = 0 then d else (0, 0)).map Prod.fst).sum = d.1) ∧
    ((((List.range n).map fun i => if i = 0 then d else (0, 0)).map Prod.snd).sum = d.2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [List.range_succ_eq_map, Function.comp_def]

variable {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

theorem kvec_pair (q : QRow (Quad (algebraMap F K δ))) (r : ℕ) (hr : r % 2 = 0) :
    Quad.mk (algebraMap F K δ) (kvec δ q r) (kvec δ q (r + 1)) = q.role r := by
  have h1 : r - r % 2 = r := by omega
  have h2 : (r + 1) - (r + 1) % 2 = r := by omega
  have h3 : (r + 1) % 2 ≠ 0 := by omega
  simp only [kvec, h1, h2, hr, h3, if_true, if_false]
  exact Quad.mk_re_im (algebraMap F K δ) (q.role r)

/-! ### The lane contributions of a `mul` block -/

section MulD
variable {Q : Type} [CommRing Q] (y : Q)

/-- The `D` list of one slot's lane rows. -/
def blkD (p : ℕ) (cl : CallL) (s : SlotL) : List (Q × Q) :=
  (List.range s.words.length).map fun i => if i = 0 then AluHonestRows.slotD p y cl s else (0, 0)

theorem laneD_mul (p : ℕ) (cl : CallL) (hop : cl.op = .mul) :
    AluHonestRows.laneD p y cl = blkD y p cl (sA p cl) ++ (blkD y p cl (sB p cl) ++ (blkD y p cl (sC p cl) ++
      blkD y p cl (sQ p cl))) := by
  unfold AluHonestRows.laneD
  rw [slotsOf_mul p cl hop]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, blkD]

theorem laneD_sums (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hop : cl.op = .mul) :
    (((AluHonestRows.laneD p y cl).map Prod.fst).sum = (AluHonestRows.slotD p y cl (sA p cl)).1 + ((AluHonestRows.slotD p y cl (sB p cl)).1 +
        ((AluHonestRows.slotD p y cl (sC p cl)).1 + (AluHonestRows.slotD p y cl (sQ p cl)).1))) ∧
    (((AluHonestRows.laneD p y cl).map Prod.snd).sum = (AluHonestRows.slotD p y cl (sA p cl)).2 + ((AluHonestRows.slotD p y cl (sB p cl)).2 +
        ((AluHonestRows.slotD p y cl (sC p cl)).2 + (AluHonestRows.slotD p y cl (sQ p cl)).2))) := by
  rw [laneD_mul y p cl hop]
  simp only [List.map_append, List.sum_append, blkD]
  have wA : 1 ≤ (sA p cl).words.length := handleSlot_words_pos p hpG _ _ _ _ _ _
  have wB : 1 ≤ (sB p cl).words.length := handleSlot_words_pos p hpG _ _ _ _ _ _
  have wC : 1 ≤ (sC p cl).words.length := handleSlot_words_pos p hpG _ _ _ _ _ _
  have a := blockD_sum (Q := Q) (sA p cl).words.length wA (AluHonestRows.slotD p y cl (sA p cl))
  have b := blockD_sum (Q := Q) (sB p cl).words.length wB (AluHonestRows.slotD p y cl (sB p cl))
  have c := blockD_sum (Q := Q) (sC p cl).words.length wC (AluHonestRows.slotD p y cl (sC p cl))
  have d := blockD_sum (Q := Q) (sQ p cl).words.length (sQ_words_pos p cl) (AluHonestRows.slotD p y cl (sQ p cl))
  exact ⟨by rw [a.1, b.1, c.1, d.1], by rw [a.2, b.2, c.2, d.2]⟩

theorem latch_mul (p : ℕ) (cl : CallL) (hop : cl.op = .mul) :
    AluHonestRows.latchOf p y cl = (AluHonestRows.slotL y (sA p cl), AluHonestRows.slotHO y (sA p cl) 0) := by
  unfold AluHonestRows.latchOf
  rw [slotsOf_mul p cl hop]
  simp [List.find?_cons, isF1, (sA_shape p cl).1, hop]

theorem slotD_A (p : ℕ) (cl : CallL) : AluHonestRows.slotD p y cl (sA p cl) = (0, 0) := by
  unfold AluHonestRows.slotD
  have : isF2 cl.op (sA p cl) = false := by simp [isF2, (sA_shape p cl).1]
  rw [if_neg (by simp [this])]
  simp [(sA_shape p cl).2.2.1, (sA_shape p cl).2.2.2]

theorem slotD_B (p : ℕ) (cl : CallL) (hop : cl.op = .mul) :
    AluHonestRows.slotD p y cl (sB p cl) = ((AluHonestRows.slotL y (sA p cl)) * AluHonestRows.slotL y (sB p cl) +
      (y - (Bn : Q)) * (AluHonestRows.slotHO y (sA p cl) 0 * AluHonestRows.slotHO y (sB p cl) 0), 0) := by
  unfold AluHonestRows.slotD
  have : isF2 cl.op (sB p cl) = true := by simp [isF2, (sB_shape p cl).1, hop]
  rw [if_pos this, latch_mul y p cl hop]
  simp [(sB_shape p cl).2.2.2]

theorem slotD_C (p : ℕ) (cl : CallL) :
    AluHonestRows.slotD p y cl (sC p cl) = (-(AluHonestRows.slotL y (sC p cl)), 0) := by
  unfold AluHonestRows.slotD
  have : isF2 cl.op (sC p cl) = false := by simp [isF2, (sC_shape p cl).1]
  rw [if_neg (by simp [this])]
  simp [(sC_shape p cl).2.2.1, (sC_shape p cl).2.2.2]

theorem slotD_Q (p : ℕ) (cl : CallL) :
    AluHonestRows.slotD p y cl (sQ p cl) = (AluHonestRows.slotL y (sQ p cl), 0) := by
  unfold AluHonestRows.slotD
  have : isF2 cl.op (sQ p cl) = false := by simp [isF2, (sQ_shape p cl).1]
  rw [if_neg (by simp [this])]
  simp [(sQ_shape p cl).2.2.1, (sQ_shape p cl).2.2.2]

theorem slotL_vw (s : SlotL) (hm : s.mode ≠ 4 ∧ s.mode ≠ 5) : AluHonestRows.slotL y s = evR y (zl s.vw) := by
  unfold AluHonestRows.slotL; rw [if_neg (by omega)]; rfl

theorem slotHO_vw (s : SlotL) (hm : s.mode ≠ 0 ∧ s.mode ≠ 4) (hv : s.vw = s.words) :
    AluHonestRows.slotHO y s 0 = evR y (zl (hiL s.vw)) := by
  unfold AluHonestRows.slotHO hornerFrom horner; rw [if_neg (by omega), List.drop_zero, hv]

theorem slotL_Q (p : ℕ) (cl : CallL) :
    AluHonestRows.slotL y (sQ p cl) = (y - (Bn : Q)) * evR y (zl (sQ p cl).words) := by
  unfold AluHonestRows.slotL AluHonestRows.slotH hornerFrom horner
  rw [if_pos (by rw [(sQ_shape p cl).2.1]; simp), if_neg (by rw [(sQ_shape p cl).2.1]; omega),
    if_neg (by rw [(sQ_shape p cl).2.1]; omega), List.drop_zero]

end MulD

theorem carr_ok (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hop : cl.op = .mul) (hcl : CallOK p cl) :
    ∀ q ∈ carr (Bn : ℤ) 0 (addL (wL (sA p cl).vw (sB p cl).vw) (negL (zl (sC p cl).vw))),
      0 ≤ q ∧ q ≤ 2 ^ 25 - 1 := by
  have hA62 : (sA p cl).vw.length ≤ 62 := by
    have := hcl.limbs62 (sA p cl) (by rw [slotsOf_mul p cl hop]; simp)
      (by rcases (sA_shape p cl).2.1 with h | h <;> simp [h])
    rwa [sA_vw_words]
  have hB62 : (sB p cl).vw.length ≤ 62 := by
    have := hcl.limbs62 (sB p cl) (by rw [slotsOf_mul p cl hop]; simp)
      (by rcases (sB_shape p cl).2.1 with h | h <;> simp [h])
    rwa [sB_vw_words]
  have hd := ds_bound (sA p cl).vw (sB p cl).vw (sC p cl).vw (handleSlot_vw_lt p hpG _ _ _ _ _ _)
    (handleSlot_vw_lt p hpG _ _ _ _ _ _) (handleSlot_vw_lt p hpG _ _ _ _ _ _) hA62 hB62
  exact carr_bound0 (B := (Bn : ℤ)) (M := 2 ^ 25 - 1) (by norm_num [Bn]) (by norm_num) _
    (ds_eval_zero p cl hop hcl) hd

theorem zl_toNat (qs : List ℤ) (h : ∀ q ∈ qs, 0 ≤ q) : zl (qs.map Int.toNat) = qs := by
  unfold zl
  rw [List.map_map]
  conv_rhs => rw [← List.map_id qs]
  apply List.map_congr_left
  intro q hq
  simp [Int.toNat_of_nonneg (h q hq)]

theorem evR_wordsQ {Q : Type} [CommRing Q] (y : Q) (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p)
    (hop : cl.op = .mul) (hcl : CallOK p cl) :
    evR y (zl (sQ p cl).words) =
      evR y (carr (Bn : ℤ) 0 (addL (wL (sA p cl).vw (sB p cl).vw) (negL (zl (sC p cl).vw)))) := by
  have hok := carr_ok p cl hpG hop hcl
  unfold sQ qSlot
  simp only [Bool.false_eq_true, if_false]
  split_ifs with h
  · have := List.map_eq_nil_iff.mp h
    rw [this]; simp [zl, evR]
  · rw [zl_toNat _ (fun q hq => (hok q hq).1)]

/-- **The `S1` total of a `mul` block vanishes** (`carry_id`). -/
theorem S1_total_mul {Q : Type} [CommRing Q] (y : Q) (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p)
    (hop : cl.op = .mul) (hcl : CallOK p cl) :
    (hdrD (Q := Q) cl).1 + ((AluHonestRows.laneD p y cl).map Prod.fst).sum = 0 := by
  have hd0 : (hdrD (Q := Q) cl).1 = 0 := by simp [hdrD, hop]
  rw [hd0, (laneD_sums y p cl hpG hop).1, slotD_A, slotD_B y p cl hop, slotD_C, slotD_Q]
  have mA : (sA p cl).mode ≠ 4 ∧ (sA p cl).mode ≠ 5 := by rcases (sA_shape p cl).2.1 with h | h <;> omega
  have mB : (sB p cl).mode ≠ 4 ∧ (sB p cl).mode ≠ 5 := by rcases (sB_shape p cl).2.1 with h | h <;> omega
  have mC : (sC p cl).mode ≠ 4 ∧ (sC p cl).mode ≠ 5 := by rcases (sC_shape p cl).2.1 with h | h <;> omega
  have oA : (sA p cl).mode ≠ 0 ∧ (sA p cl).mode ≠ 4 := by rcases (sA_shape p cl).2.1 with h | h <;> omega
  have oB : (sB p cl).mode ≠ 0 ∧ (sB p cl).mode ≠ 4 := by rcases (sB_shape p cl).2.1 with h | h <;> omega
  rw [slotL_vw y _ mA, slotL_vw y _ mB, slotL_vw y _ mC, slotHO_vw y _ oA (sA_vw_words p cl),
    slotHO_vw y _ oB (sB_vw_words p cl), slotL_Q y p cl, evR_wordsQ y p cl hpG hop hcl]
  have E1 := carry_id (B := (Bn : ℤ)) (by norm_num [Bn]) y
    (addL (wL (sA p cl).vw (sB p cl).vw) (negL (zl (sC p cl).vw))) (ds_eval_zero p cl hop hcl)
  have E2 : evR y (addL (wL (sA p cl).vw (sB p cl).vw) (negL (zl (sC p cl).vw))) =
      evR y (zl (sA p cl).vw) * evR y (zl (sB p cl).vw) +
        (y - (Bn : Q)) * (evR y (zl (hiL (sA p cl).vw)) * evR y (zl (hiL (sB p cl).vw))) -
        evR y (zl (sC p cl).vw) := by
    rw [evR_addL, evR_negL, evR_wL]; ring
  simp only [Int.cast_natCast] at E1
  simp only [zero_add]
  linear_combination (-1 : Q) * E2 + E1

/-- **The `S2` total of a `mul` block vanishes** (`cf2 = 0` throughout, hdr `D2 = 0`). -/
theorem S2_total_mul {Q : Type} [CommRing Q] (y : Q) (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p)
    (hop : cl.op = .mul) :
    (hdrD (Q := Q) cl).2 + ((AluHonestRows.laneD p y cl).map Prod.snd).sum = 0 := by
  have hd0 : (hdrD (Q := Q) cl).2 = 0 := by simp [hdrD, hop]
  rw [hd0, (laneD_sums y p cl hpG hop).2, slotD_A, slotD_B y p cl hop, slotD_C, slotD_Q]
  simp

/-- The last block row of `blockQ`: `S1`, `S2` are the totals. -/
theorem blockQ_last {Q : Type} [CommRing Q] (y : Q) (p : ℕ) (cl : CallL) (n : ℕ)
    (hD : (AluHonestRows.laneD p y cl).length = n + 1) (hHL : (laneHL y cl p).length = n + 1) :
    ((blockQ p y cl).getD (n + 1) QRow.zero).S1 =
        (hdrD (Q := Q) cl).1 + ((AluHonestRows.laneD p y cl).map Prod.fst).sum ∧
    ((blockQ p y cl).getD (n + 1) QRow.zero).S2 =
        (hdrD (Q := Q) cl).2 + ((AluHonestRows.laneD p y cl).map Prod.snd).sum := by
  have key := runSums_last n (hdrD (Q := Q) cl) (AluHonestRows.laneD p y cl) hD
  have hs : (runSums (hdrD (Q := Q) cl) (AluHonestRows.laneD p y cl)).length = n + 1 := by
    rw [runSums_length, hD]
  rw [List.getD_eq_getElem _ _ (by omega : n < (runSums (hdrD (Q := Q) cl) (AluHonestRows.laneD p y cl)).length)]
    at key
  simp only [blockQ, List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simp [hD, hHL, hs])]
  simp only [List.getElem_map, List.getElem_zip]
  exact ⟨congrArg Prod.fst key, congrArg Prod.snd key⟩

/-- The two terminal `𝕂′` equations of `identQ`: `(1 − sL′)·S1 = 0`, `(1 − sL′)·S2 = 0`. -/
def termQ (δF : F) : List (QE F) :=
  [ QE.scale (notE (nv AluSZChipJ9.sL)) (QE.var AluSZChipJ9.S1),
    QE.scale (notE (nv AluSZChipJ9.sL)) (QE.var AluSZChipJ9.S2) ]

/-- They are the last two equations of `identQ`. -/
theorem termQ_eq_drop : (AluSZChipJ9.identQ δ : List (QE F)).drop 23 = termQ δ := rfl

theorem laneD_length_mul {Q : Type} [CommRing Q] (y : Q) (p : ℕ) (cl : CallL) (hop : cl.op = .mul) :
    (AluHonestRows.laneD p y cl).length =
      (sA p cl).words.length + (sB p cl).words.length + (sC p cl).words.length + (sQ p cl).words.length := by
  rw [laneD_mul y p cl hop]; simp [blkD]; omega

theorem laneHL_length_mul {Q : Type} [CommRing Q] (y : Q) (p : ℕ) (cl : CallL) (hop : cl.op = .mul) :
    (laneHL y cl p).length =
      (sA p cl).words.length + (sB p cl).words.length + (sC p cl).words.length + (sQ p cl).words.length := by
  unfold laneHL
  rw [slotsOf_mul p cl hop]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, List.length_map,
    List.length_range]
  omega

/-- **The terminal `S1 = S2 = 0` for `mul`** (`QSat` of the last two `identQ` equations). -/
theorem termS_sat_mul (p : ℕ) (cl : CallL) (hpG : p = Nock.Atoms.p) (hop : cl.op = .mul)
    (hcl : CallOK p cl) : QSat (K := K) δ p cl (termQ δ : List (QE F)) := by
  intro y chal hy hp j hj nxt hn nq hq e he
  have wA : 1 ≤ (sA p cl).words.length := handleSlot_words_pos p hpG _ _ _ _ _ _
  have wB : 1 ≤ (sB p cl).words.length := handleSlot_words_pos p hpG _ _ _ _ _ _
  have wC : 1 ≤ (sC p cl).words.length := handleSlot_words_pos p hpG _ _ _ _ _ _
  have wQ : 1 ≤ (sQ p cl).words.length := sQ_words_pos p cl
  have hlen : (blockB (F := F) p cl).length =
      1 + (sA p cl).words.length + (sB p cl).words.length + (sC p cl).words.length +
        (sQ p cl).words.length := by
    rw [blockB_mul p cl hop, lay_length]
  simp only [termQ, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  by_cases hl : j + 1 < (blockB (F := F) p cl).length
  · have hsL : nxt.sL = 1 := by
      rw [hn.1 hl, blockB_mul p cl hop, lay_getD _ _ _ _ _ _ _ _ _ _ _ (by omega)]
      exact layAt_prop (fun r : BRow F => r.sL = 1) _ _ _ _ _ _ _ _ _
        (fun i => slotRow_sL _ _ _ _) (fun i => slotRow_sL _ _ _ _) (fun i => slotRow_sL _ _ _ _)
        (fun i => slotRow_sL _ _ _ _) (by omega)
    rcases he with rfl | rfl <;>
    · rw [ev_scale]; simp [CoeffExpr.eval, envB, hsL]
  · have hjl : j + 1 = (blockB (F := F) p cl).length := by omega
    obtain ⟨n, hn1⟩ : ∃ n, (sA p cl).words.length + (sB p cl).words.length + (sC p cl).words.length +
        (sQ p cl).words.length = n + 1 := ⟨(sA p cl).words.length + (sB p cl).words.length + (sC p cl).words.length +
        (sQ p cl).words.length - 1, by omega⟩
    have hjn : j = n + 1 := by omega
    have hD : (AluHonestRows.laneD p y cl).length = n + 1 := by rw [laneD_length_mul y p cl hop, hn1]
    have hHL : (laneHL y cl p).length = n + 1 := by rw [laneHL_length_mul y p cl hop, hn1]
    obtain ⟨b1, b2⟩ := blockQ_last y p cl n hD hHL
    have t1 := S1_total_mul y p cl hpG hop hcl
    have t2 := S2_total_mul y p cl hpG hop
    subst hjn
    rcases he with rfl | rfl
    · have hk := kvec_pair δ ((blockQ p y cl).getD (n + 1) QRow.zero) AluSZChipJ9.S1 (by decide)
      have hrole : ((blockQ p y cl).getD (n + 1) QRow.zero).role AluSZChipJ9.S1 =
          ((blockQ p y cl).getD (n + 1) QRow.zero).S1 := by simp [QRow.role, AluSZChipJ9.S1]
      rw [ev_scale, ev_var]
      dsimp only
      rw [hk, hrole, b1, t1, mul_zero]
    · have hk := kvec_pair δ ((blockQ p y cl).getD (n + 1) QRow.zero) AluSZChipJ9.S2 (by decide)
      have hrole : ((blockQ p y cl).getD (n + 1) QRow.zero).role AluSZChipJ9.S2 =
          ((blockQ p y cl).getD (n + 1) QRow.zero).S2 := by simp [QRow.role, AluSZChipJ9.S2]
      rw [ev_scale, ev_var]
      dsimp only
      rw [hk, hrole, b2, t2, mul_zero]

end Term

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSatM
