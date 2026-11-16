import Nock.AxisBatching
import Nock.Reference

/-!
The `(counts, pw)` functional of weighted trees and the address-polynomial certificate.  It defines
the weighted tree `WT`, the address `addr` of a path at `λ`, and proves the functional identity for
arbitrary wrapper weights at arbitrary positions, the per-exponent coefficient with no multiplicity
assumption, honest exactness for a single record, and injectivity of the address polynomial `addrP`.
It then analyses the per-record `bracket` certificate: the bracket is zero exactly when the padding
bits vanish and the verify path extends the read path; the honest placement has bracket zero; and a
verify above its read, a read and verify on the same node with padding, a read wrapper with no verify
below it, and a zero axis are all rejected.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch554

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Polynomial

variable {K : Type*} [Field K]

/-! ## A. The weighted tree and the `(counts, pw)` functional -/

/-- A tree with `decompose` forks, `halt` leaves, and wrappers injecting an arbitrary
`(δc, δw)` at timestamp exponent `e` (a `read_root` or `verify_child` with any weights). -/
inductive WT (K : Type*) where
  | leaf : WT K
  | fork : WT K → WT K → WT K
  | wrap : ℕ → K → K → WT K → WT K

/-- `bit true = 1`, `bit false = 0`. -/
def bit (b : Bool) : K := if b then 1 else 0

theorem bit_inj [Nontrivial K] {a b : Bool} (h : bit (K := K) a = bit b) : a = b := by
  cases a <;> cases b <;> simp [bit] at h ⊢

/-- `pw_P = λ·(pw_L + pw_R)`; a wrapper adds `δw·X^e`; a leaf is `0`. -/
noncomputable def pw (l : K) : WT K → K[X]
  | .leaf => 0
  | .fork L R => C l * (pw l L + pw l R)
  | .wrap e _ dw c => pw l c + C dw * X ^ e

/-- `counts_P = counts_L + counts_R + (λ − 1)(pw_L + pw_R) + pw_R`; a wrapper adds `δc·X^e`. -/
noncomputable def cnt (l : K) : WT K → K[X]
  | .leaf => 0
  | .fork L R => cnt l L + cnt l R + C (l - 1) * (pw l L + pw l R) + pw l R
  | .wrap e dc _ c => cnt l c + C dc * X ^ e

/-- The address accumulated from `a` down a top-down path. -/
def addrFrom (l a : K) (p : List Bool) : K := p.foldl (fun x e => l * x + bit e) a

/-- The address of a top-down path from a root of address `1`. -/
def addr (l : K) (p : List Bool) : K := addrFrom l 1 p

theorem addrFrom_cons (l a : K) (e : Bool) (p : List Bool) :
    addrFrom l a (e :: p) = addrFrom l (l * a + bit e) p := rfl

theorem addrFrom_append (l a : K) (p q : List Bool) :
    addrFrom l a (p ++ q) = addrFrom l (addrFrom l a p) q := List.foldl_append ..

/-- The accumulator enters linearly with weight `λ^{|p|}`. -/
theorem addrFrom_linear (l : K) (p : List Bool) :
    ∀ a : K, addrFrom l a p = l ^ p.length * a + addrFrom l 0 p := by
  induction p with
  | nil => intro a; simp [addrFrom]
  | cons e p ih =>
      intro a
      rw [addrFrom_cons, ih, addrFrom_cons l 0, ih (l * 0 + bit e), List.length_cons, pow_succ]
      ring

/-- **Going up one edge `e`**: `P ↦ P + λ^{|p|}·(λ − 1 + e)` — the standard address needs the
depth power of the leaf, which is what `pw` carries. -/
theorem addr_cons (l : K) (e : Bool) (p : List Bool) :
    addr l (e :: p) = addr l p + l ^ p.length * (l - 1 + bit e) := by
  unfold addr
  rw [addrFrom_cons, addrFrom_linear, addrFrom_linear l p 1]
  ring

/-- `P_{q ++ b} = λ^{|b|}·(P_q − 1) + P_b`: the address of `b` under `q`. -/
theorem addr_append (l : K) (p q : List Bool) :
    addr l (p ++ q) = l ^ q.length * (addr l p - 1) + addr l q := by
  unfold addr
  rw [addrFrom_append, addrFrom_linear l q, addrFrom_linear l q 1]
  ring

@[simp] theorem addr_nil (l : K) : addr l [] = 1 := rfl

/-- The wrappers of a tree with their top-down paths. -/
def wraps : WT K → List (List Bool × ℕ × K × K)
  | .leaf => []
  | .fork L R =>
      (wraps L).map (fun x => (false :: x.1, x.2)) ++ (wraps R).map (fun x => (true :: x.1, x.2))
  | .wrap e dc dw c => ([], e, dc, dw) :: wraps c

/-- A wrapper's `counts` contribution at the top: `(δc + (P_p − 1)·δw)·X^e`. -/
noncomputable def cntTerm (l : K) (x : List Bool × ℕ × K × K) : K[X] :=
  C (x.2.2.1 + (addr l x.1 - 1) * x.2.2.2) * X ^ x.2.1

/-- A wrapper's `pw` contribution at the top: `λ^{|p|}·δw·X^e`. -/
noncomputable def pwTerm (l : K) (x : List Bool × ℕ × K × K) : K[X] :=
  C (l ^ x.1.length * x.2.2.2) * X ^ x.2.1

theorem shift_pw (l : K) (b : Bool) (L : List (List Bool × ℕ × K × K)) :
    ((L.map (fun x => (b :: x.1, x.2))).map (pwTerm l)).sum = C l * (L.map (pwTerm l)).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, ih, pwTerm, List.length_cons, pow_succ, C_mul]
      ring

theorem shift_cnt (l : K) (b : Bool) (L : List (List Bool × ℕ × K × K)) :
    ((L.map (fun x => (b :: x.1, x.2))).map (cntTerm l)).sum
      = (L.map (cntTerm l)).sum + C (l - 1 + bit b) * (L.map (pwTerm l)).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, ih, cntTerm, pwTerm, addr_cons, C_add, C_sub, C_mul,
        C_pow, C_1]
      ring

/-- **The functional, exactly, for arbitrary wrapper weights at arbitrary positions.**
`counts_top = Σ_wrappers (δc + (P_p − 1)·δw)·X^e`, `pw_top = Σ_wrappers λ^{|p|}·δw·X^e`. -/
theorem functional (l : K) (t : WT K) :
    cnt l t = ((wraps t).map (cntTerm l)).sum ∧ pw l t = ((wraps t).map (pwTerm l)).sum := by
  induction t with
  | leaf => simp [cnt, pw, wraps]
  | fork L R ihl ihr =>
      obtain ⟨hcl, hpl⟩ := ihl
      obtain ⟨hcr, hpr⟩ := ihr
      simp only [cnt, pw, wraps, List.map_append, List.sum_append, shift_cnt, shift_pw, hcl, hpl,
        hcr, hpr]
      constructor
      · simp only [bit, if_true, Bool.false_eq_true, if_false, add_zero, C_add, C_sub, C_1]
        ring
      · ring
  | wrap e dc dw c ih =>
      obtain ⟨hc, hp⟩ := ih
      simp only [cnt, pw, wraps, List.map_cons, List.sum_cons, hc, hp, cntTerm, pwTerm, addr_nil,
        List.length_nil, pow_zero, one_mul, sub_self, zero_mul, add_zero]
      constructor <;> ring

/-! ## B. The `MTree` instance and the per-exponent coefficient -/

noncomputable def ofM (s : K) (A W : ℕ → K) : MTree K → WT K
  | .halt => .leaf
  | .decompose L R => .fork (ofM s A W L) (ofM s A W R)
  | .read e c => .wrap e (-(A e)) (-(W e)) (ofM s A W c)
  | .verify e _ c => .wrap e s s (ofM s A W c)

noncomputable def cntM (l s : K) (A W : ℕ → K) (t : MTree K) : K[X] := cnt l (ofM s A W t)
noncomputable def pwM (l s : K) (A W : ℕ → K) (t : MTree K) : K[X] := pw l (ofM s A W t)

/-- The design's gates, as the recursion of `cntM`/`pwM`. -/
theorem cntM_decompose (l s : K) (A W : ℕ → K) (L R : MTree K) :
    cntM l s A W (.decompose L R)
      = cntM l s A W L + cntM l s A W R + C (l - 1) * (pwM l s A W L + pwM l s A W R)
        + pwM l s A W R := rfl
theorem pwM_decompose (l s : K) (A W : ℕ → K) (L R : MTree K) :
    pwM l s A W (.decompose L R) = C l * (pwM l s A W L + pwM l s A W R) := rfl
theorem cntM_verify (l s : K) (A W : ℕ → K) (e : ℕ) (a : K) (c : MTree K) :
    cntM l s A W (.verify e a c) = cntM l s A W c + C s * X ^ e := rfl
theorem pwM_verify (l s : K) (A W : ℕ → K) (e : ℕ) (a : K) (c : MTree K) :
    pwM l s A W (.verify e a c) = pwM l s A W c + C s * X ^ e := rfl
theorem cntM_read (l s : K) (A W : ℕ → K) (e : ℕ) (c : MTree K) :
    cntM l s A W (.read e c) = cntM l s A W c + C (-(A e)) * X ^ e := rfl
theorem pwM_read (l s : K) (A W : ℕ → K) (e : ℕ) (c : MTree K) :
    pwM l s A W (.read e c) = pwM l s A W c + C (-(W e)) * X ^ e := rfl
theorem cntM_halt (l s : K) (A W : ℕ → K) : cntM l s A W .halt = 0 := rfl
theorem pwM_halt (l s : K) (A W : ℕ → K) : pwM l s A W .halt = 0 := rfl

/-- Top-down paths of the `verify_child` nodes with exponent `e`. -/
def vpaths (e : ℕ) : MTree K → List (List Bool)
  | .halt => []
  | .decompose L R => (vpaths e L).map (false :: ·) ++ (vpaths e R).map (true :: ·)
  | .read _ c => vpaths e c
  | .verify e' _ c => (if e' = e then [([] : List Bool)] else []) ++ vpaths e c

/-- Top-down paths of the `read_root` wrappers with exponent `e`. -/
def rpaths (e : ℕ) : MTree K → List (List Bool)
  | .halt => []
  | .decompose L R => (rpaths e L).map (false :: ·) ++ (rpaths e R).map (true :: ·)
  | .read e' c => (if e' = e then [([] : List Bool)] else []) ++ rpaths e c
  | .verify _ _ c => rpaths e c

/-- `Σ_p P_p` and `Σ_p λ^{|p|}` over a path list. -/
noncomputable def sumAddr (l : K) (L : List (List Bool)) : K := (L.map (addr l)).sum
noncomputable def sumPow (l : K) (L : List (List Bool)) : K := (L.map fun p => l ^ p.length).sum

theorem sumAddr_shift (l : K) (b : Bool) (L : List (List Bool)) :
    sumAddr l (L.map (b :: ·)) = sumAddr l L + (l - 1 + bit b) * sumPow l L := by
  induction L with
  | nil => simp [sumAddr, sumPow]
  | cons p L ih =>
      simp only [List.map_cons, sumAddr, sumPow, List.sum_cons] at ih ⊢
      rw [addr_cons, ih]; ring

theorem sumPow_shift (l : K) (b : Bool) (L : List (List Bool)) :
    sumPow l (L.map (b :: ·)) = l * sumPow l L := by
  induction L with
  | nil => simp [sumPow]
  | cons p L ih =>
      simp only [List.map_cons, sumPow, List.sum_cons, List.length_cons, pow_succ] at ih ⊢
      rw [ih]; ring

theorem sumAddr_append (l : K) (L L' : List (List Bool)) :
    sumAddr l (L ++ L') = sumAddr l L + sumAddr l L' := by simp [sumAddr]
theorem sumPow_append (l : K) (L L' : List (List Bool)) :
    sumPow l (L ++ L') = sumPow l L + sumPow l L' := by simp [sumPow]

/-- **The per-exponent coefficient, with no multiplicity assumption.**
`(pw).coeff e = s·Σ_V λ^{|V|} − W_e·Σ_R λ^{|R|}` and
`(counts).coeff e = s·Σ_V P_V − (A_e·#R + W_e·(Σ_R P_R − #R))`, i.e.
`s·Σ_V P_V − Σ_R (A_e + W_e·(P_R − 1))`, over ALL verifies and reads of exponent `e`. -/
theorem coeff_cntM (l s : K) (A W : ℕ → K) (e : ℕ) (t : MTree K) :
    (pwM l s A W t).coeff e = s * sumPow l (vpaths e t) - W e * sumPow l (rpaths e t)
    ∧ (cntM l s A W t).coeff e
        = s * sumAddr l (vpaths e t)
          - (A e * (rpaths e t).length + W e * (sumAddr l (rpaths e t) - (rpaths e t).length)) := by
  induction t with
  | halt => simp [cntM, pwM, cnt, pw, ofM, vpaths, rpaths, sumAddr, sumPow]
  | decompose L R ihl ihr =>
      obtain ⟨hpl, hcl⟩ := ihl
      obtain ⟨hpr, hcr⟩ := ihr
      have hc : (cntM l s A W (.decompose L R)).coeff e
          = (cntM l s A W L).coeff e + (cntM l s A W R).coeff e
            + (l - 1) * ((pwM l s A W L).coeff e + (pwM l s A W R).coeff e)
            + (pwM l s A W R).coeff e := by
        rw [cntM_decompose]; simp only [coeff_add, coeff_C_mul]
      have hp : (pwM l s A W (.decompose L R)).coeff e
          = l * ((pwM l s A W L).coeff e + (pwM l s A W R).coeff e) := by
        rw [pwM_decompose]; simp only [coeff_add, coeff_C_mul]
      rw [hc, hp, hpl, hcl, hpr, hcr]
      simp only [vpaths, rpaths, sumAddr_append, sumPow_append, sumAddr_shift, sumPow_shift,
        List.length_append, List.length_map, bit, if_true, Bool.false_eq_true, if_false]
      push_cast
      constructor <;> ring
  | read e' c ih =>
      obtain ⟨hp, hc⟩ := ih
      have hc' : (cntM l s A W (.read e' c)).coeff e
          = (cntM l s A W c).coeff e + (if e = e' then -(A e') else 0) := by
        rw [cntM_read]; simp only [coeff_add, coeff_C_mul, coeff_X_pow]; split_ifs <;> simp
      have hp' : (pwM l s A W (.read e' c)).coeff e
          = (pwM l s A W c).coeff e + (if e = e' then -(W e') else 0) := by
        rw [pwM_read]; simp only [coeff_add, coeff_C_mul, coeff_X_pow]; split_ifs <;> simp
      rw [hc', hp', hp, hc]
      by_cases h : e' = e
      · subst h
        simp only [rpaths, vpaths, if_true, List.singleton_append, sumAddr, sumPow, List.map_cons,
          List.sum_cons, addr_nil, List.length_nil, pow_zero, List.length_cons]
        simp only [sumAddr, sumPow] at *
        push_cast
        constructor <;> ring
      · simp [rpaths, vpaths, h, Ne.symm h]
  | verify e' a c ih =>
      obtain ⟨hp, hc⟩ := ih
      have hc' : (cntM l s A W (.verify e' a c)).coeff e
          = (cntM l s A W c).coeff e + (if e = e' then s else 0) := by
        rw [cntM_verify]; simp only [coeff_add, coeff_C_mul, coeff_X_pow]; split_ifs <;> simp
      have hp' : (pwM l s A W (.verify e' a c)).coeff e
          = (pwM l s A W c).coeff e + (if e = e' then s else 0) := by
        rw [pwM_verify]; simp only [coeff_add, coeff_C_mul, coeff_X_pow]; split_ifs <;> simp
      rw [hc', hp', hp, hc]
      by_cases h : e' = e
      · subst h
        simp only [rpaths, vpaths, if_true, List.singleton_append, sumAddr, sumPow, List.map_cons,
          List.sum_cons, addr_nil, List.length_nil, pow_zero]
        simp only [sumAddr, sumPow] at *
        constructor <;> ring
      · simp [rpaths, vpaths, h, Ne.symm h]

/-- **One record**: exactly one verify at `v` and one read at `r` with exponent `e` gives the
brief's bracket `s·P_V − A_e − W_e·(P_R − 1)`. -/
theorem single_record (l s : K) (A W : ℕ → K) (e : ℕ) (t : MTree K) (v r : List Bool)
    (hv : vpaths e t = [v]) (hr : rpaths e t = [r]) :
    (cntM l s A W t).coeff e = s * addr l v - A e - W e * (addr l r - 1) := by
  rw [(coeff_cntM l s A W e t).2, hv, hr]
  simp [sumAddr]; ring

/-- Place a subtree at the end of a top-down path, `halt` siblings. -/
def place : List Bool → MTree K → MTree K
  | [], t => t
  | false :: p, t => .decompose (place p t) .halt
  | true :: p, t => .decompose .halt (place p t)

omit [Field K] in
theorem vpaths_place (e : ℕ) (p : List Bool) (t : MTree K) :
    vpaths e (place p t) = (vpaths e t).map (p ++ ·) := by
  induction p with
  | nil => simp [place]
  | cons b p ih => cases b <;> simp [place, vpaths, ih, List.map_map, Function.comp_def]

omit [Field K] in
theorem rpaths_place (e : ℕ) (p : List Bool) (t : MTree K) :
    rpaths e (place p t) = (rpaths e t).map (p ++ ·) := by
  induction p with
  | nil => simp [place]
  | cons b p ih => cases b <;> simp [place, rpaths, ih, List.map_map, Function.comp_def]

/-- The honest single-record tree: read wrapper at `q`, verify at `q ++ b` below it. -/
def honestTree (e : ℕ) (a : K) (q b : List Bool) : MTree K :=
  place q (.read e (place b (.verify e a .halt)))

omit [Field K] in
theorem honestTree_paths (e : ℕ) (a : K) (q b : List Bool) :
    vpaths e (honestTree e a q b) = [q ++ b] ∧ rpaths e (honestTree e a q b) = [q] := by
  simp [honestTree, vpaths_place, rpaths_place, vpaths, rpaths]

omit [Field K] in
theorem honestTree_paths_other (e e' : ℕ) (a : K) (q b : List Bool) (h : e' ≠ e) :
    vpaths e' (honestTree e a q b) = [] ∧ rpaths e' (honestTree e a q b) = [] := by
  simp [honestTree, vpaths_place, rpaths_place, vpaths, rpaths, h, Ne.symm h]

/-- **Honest exactness for every `λ`, every `s`, every placement**: with
`A_e = s·P_b`, `W_e = s·λ^{|b|}` (the certificate of the relative path `b`), the top `counts`
and `pw` are the zero polynomial. -/
theorem honest_single_record (l s : K) (e : ℕ) (a : K) (q b : List Bool) :
    cntM l s (fun _ => s * addr l b) (fun _ => s * l ^ b.length) (honestTree e a q b) = 0
    ∧ pwM l s (fun _ => s * addr l b) (fun _ => s * l ^ b.length) (honestTree e a q b) = 0 := by
  obtain ⟨hv, hr⟩ := honestTree_paths e a q b
  constructor
  · ext e'
    rw [coeff_zero]
    by_cases h : e' = e
    · subst h
      rw [single_record _ _ _ _ _ _ _ _ hv hr, addr_append]; ring
    · obtain ⟨hv', hr'⟩ := honestTree_paths_other e e' a q b h
      rw [(coeff_cntM _ _ _ _ _ _).2, hv', hr']; simp [sumAddr]
  · ext e'
    rw [coeff_zero]
    by_cases h : e' = e
    · subst h
      rw [(coeff_cntM _ _ _ _ _ _).1, hv, hr]
      simp [sumPow, List.length_append, pow_add]; ring
    · obtain ⟨hv', hr'⟩ := honestTree_paths_other e e' a q b h
      rw [(coeff_cntM _ _ _ _ _ _).1, hv', hr']; simp [sumPow]

/-! ## C. The certificate in polynomial form and the per-record identity -/

/-- The address polynomial of a top-down path, `X = λ` (`addrP p` evaluates to `addr λ p`). -/
noncomputable def addrPFrom (a : K[X]) (p : List Bool) : K[X] :=
  p.foldl (fun x e => X * x + C (bit e)) a

noncomputable def addrP (p : List Bool) : K[X] := addrPFrom 1 p

theorem addrPFrom_eval (l : K) (a : K[X]) (p : List Bool) :
    (addrPFrom a p).eval l = addrFrom l (a.eval l) p := by
  induction p generalizing a with
  | nil => rfl
  | cons e p ih =>
      show (addrPFrom ((X : K[X]) * a + C (bit e)) p).eval l = addrFrom l (l * a.eval l + bit e) p
      rw [ih]; simp

theorem addrP_eval (l : K) (p : List Bool) : (addrP p).eval l = addr l p := by
  unfold addrP addr; rw [addrPFrom_eval]; simp

theorem addrPFrom_linear (p : List Bool) :
    ∀ a : K[X], addrPFrom a p = X ^ p.length * a + addrPFrom 0 p := by
  induction p with
  | nil => intro a; simp [addrPFrom]
  | cons e p ih =>
      intro a
      show addrPFrom ((X : K[X]) * a + C (bit e)) p
        = X ^ (p.length + 1) * a + addrPFrom (X * 0 + C (bit e)) p
      rw [ih, ih (X * 0 + C (bit e)), pow_succ]
      ring

theorem addrP_append (p q : List Bool) :
    addrP (K := K) (p ++ q) = X ^ q.length * (addrP p - 1) + addrP q := by
  unfold addrP
  rw [addrPFrom, List.foldl_append, ← addrPFrom, ← addrPFrom, addrPFrom_linear q,
    addrPFrom_linear q 1]
  ring

theorem addrP_snoc (p : List Bool) (e : Bool) :
    addrP (K := K) (p ++ [e]) = X * addrP p + C (bit e) := by
  unfold addrP addrPFrom
  rw [List.foldl_append]; rfl

@[simp] theorem addrP_nil : addrP (K := K) [] = 1 := rfl

/-- The coefficients of `addrP p`: `1` at `X^{|p|}`, the bit at distance `i` from the leaf at
`X^i`, `0` above. -/
theorem addrP_coeff (p : List Bool) (i : ℕ) :
    (addrP (K := K) p).coeff i = if i = p.length then 1 else bit (p.reverse.getD i false) := by
  induction p using List.reverseRecOn generalizing i with
  | nil =>
      cases i with
      | zero => simp
      | succ i => simp [coeff_one, bit]
  | append_singleton p e ih =>
      rw [addrP_snoc]
      cases i with
      | zero =>
          simp [coeff_add, coeff_X_mul, coeff_C]
      | succ i =>
          rw [coeff_add, coeff_X_mul, coeff_C, if_neg (Nat.succ_ne_zero i), add_zero, ih,
            List.reverse_append, List.reverse_singleton, List.singleton_append, List.getD_cons_succ,
            List.length_append, List.length_singleton]
          simp

theorem addrP_coeff_length (p : List Bool) : (addrP (K := K) p).coeff p.length = 1 := by
  rw [addrP_coeff, if_pos rfl]

theorem addrP_coeff_gt (p : List Bool) (i : ℕ) (h : p.length < i) :
    (addrP (K := K) p).coeff i = 0 := by
  rw [addrP_coeff, if_neg (by omega), List.getD_eq_default _ _ (by simp; omega)]
  simp [bit]

theorem addrP_ne_zero (p : List Bool) : addrP (K := K) p ≠ 0 := by
  intro h
  have := addrP_coeff_length (K := K) p
  rw [h, coeff_zero] at this
  exact zero_ne_one this

/-- **`addrP` is injective**: the address polynomial determines the path. -/
theorem addrP_injective : Function.Injective (addrP (K := K)) := by
  intro p p' h
  have hlen : p.length = p'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := congrArg (fun q : K[X] => q.coeff p'.length) h
      rw [addrP_coeff_gt p _ hlt, addrP_coeff_length] at h1
      exact zero_ne_one h1
    · have h1 := congrArg (fun q : K[X] => q.coeff p.length) h
      rw [addrP_coeff_length, addrP_coeff_gt p' _ hgt] at h1
      exact one_ne_zero h1
  have hrev : p.reverse = p'.reverse := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    have hc := congrArg (fun q : K[X] => q.coeff i) h
    rw [addrP_coeff, addrP_coeff, if_neg (by simp at h1; omega), if_neg (by simp at h2; omega)]
      at hc
    have := bit_inj hc
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  exact List.reverse_injective hrev

/-- The relative path certified by `(m, c)`: `[c_1, …, c_m]` (top-down, `c_1` the first edge
below the read, `c_m` the edge into the verify). -/
def bitsOf (m : ℕ) (c : ℕ → Bool) : List Bool := List.ofFn fun i : Fin m => c (i.val + 1)

omit [Field K] in
theorem bitsOf_length (m : ℕ) (c : ℕ → Bool) : (bitsOf m c).length = m := by
  simp [bitsOf]

omit [Field K] in
theorem bitsOf_succ (m : ℕ) (c : ℕ → Bool) :
    bitsOf (m + 1) c = bitsOf m c ++ [c (m + 1)] := by
  unfold bitsOf
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

/-- `a_λ = P_{[c_1..c_m]} = X^m + Σ_{j=1}^m c_j X^{m−j}`. -/
theorem addrP_bitsOf (m : ℕ) (c : ℕ → Bool) :
    addrP (K := K) (bitsOf m c)
      = X ^ m + ∑ j ∈ Finset.range m, C (bit (c (j + 1))) * X ^ (m - (j + 1)) := by
  induction m with
  | zero => simp [bitsOf]
  | succ m ih =>
      rw [bitsOf_succ, addrP_snoc, ih, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one,
        mul_add, Finset.mul_sum, pow_succ]
      have : ∀ j ∈ Finset.range m,
          (X : K[X]) * (C (bit (c (j + 1))) * X ^ (m - (j + 1)))
            = C (bit (c (j + 1))) * X ^ (m + 1 - (j + 1)) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [show m + 1 - (j + 1) = (m - (j + 1)) + 1 by omega, pow_succ]; ring
      rw [Finset.sum_congr rfl this]
      ring

/-- The brief's `C = Σ_{j≤n} c_j λ^{−j}` (with `c_0 = 1`) times `λ^n`:
`Cpoly n c = X^n + Σ_{j=1}^n c_j X^{n−j}` — a polynomial, no inverse. -/
noncomputable def Cpoly (n : ℕ) (c : ℕ → Bool) : K[X] :=
  X ^ n + ∑ j ∈ Finset.range n, C (bit (c (j + 1))) * X ^ (n - (j + 1))

/-- With the padding bits `c_{j>m}` zero, `Cpoly = X^{n−m}·a_λ`. -/
theorem Cpoly_split (n m : ℕ) (c : ℕ → Bool) (hm : m ≤ n)
    (hpad : ∀ j, m < j → j ≤ n → c j = false) :
    Cpoly (K := K) n c = X ^ (n - m) * addrP (bitsOf m c) := by
  rw [Cpoly, addrP_bitsOf, ← Finset.sum_range_add_sum_Ico _ hm]
  have hzero : ∑ j ∈ Finset.Ico m n, C (bit (c (j + 1))) * X ^ (n - (j + 1)) = (0 : K[X]) := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [hpad (j + 1) (by omega) (by omega)]; simp [bit]
  rw [hzero, add_zero, mul_add, Finset.mul_sum, ← pow_add, Nat.sub_add_cancel hm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show n - (j + 1) = (n - m) + (m - (j + 1)) by omega, pow_add]; ring

/-- `X^m·Cpoly` expanded: the padding bit `c_j` (`j > m`) sits alone at `X^{m+n−j}`. -/
theorem X_pow_mul_Cpoly (n m : ℕ) (c : ℕ → Bool) :
    X ^ m * Cpoly (K := K) n c
      = X ^ (m + n) + ∑ j ∈ Finset.range n, C (bit (c (j + 1))) * X ^ (m + n - (j + 1)) := by
  rw [Cpoly, mul_add, ← pow_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show m + n - (j + 1) = m + (n - (j + 1)) by omega, pow_add]; ring

noncomputable def bracket (n m : ℕ) (c : ℕ → Bool) (v r : List Bool) : K[X] :=
  X ^ n * addrP v - X ^ m * Cpoly n c - X ^ (m + n) * (addrP r - 1)

theorem bracket_eval (l : K) (n m : ℕ) (c : ℕ → Bool) (v r : List Bool) :
    (bracket n m c v r).eval l
      = l ^ n * addr l v - l ^ m * (Cpoly n c).eval l - l ^ (m + n) * (addr l r - 1) := by
  simp [bracket, addrP_eval]

/-- A padding bit is read off the bracket's low coefficient. -/
theorem bracket_coeff_padding (n m : ℕ) (c : ℕ → Bool) (v r : List Bool) (j₀ : ℕ)
    (hj₀ : m ≤ j₀) (hj₀n : j₀ < n) :
    (bracket (K := K) n m c v r).coeff (m + n - (j₀ + 1)) = -(bit (c (j₀ + 1))) := by
  unfold bracket
  rw [coeff_sub, coeff_sub, X_pow_mul_Cpoly, coeff_add, finsetSum_coeff, coeff_X_pow_mul',
    coeff_X_pow_mul', coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [Finset.sum_eq_single j₀]
  · simp [coeff_C_mul, coeff_X_pow]
  · intro j hj hne
    rw [Finset.mem_range] at hj
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hj₀n) h

/-- **The per-record identity, both directions, at the exact certificate.**
The bracket is the zero polynomial **iff** every padding bit `c_{j>m}` is `0` and the verify
sits at relative path `[c_1, …, c_m]` under the read.  The Laurent step (padding forced) and
the ancestry step (`addrP` injective) are one statement. -/
theorem bracket_zero_iff (n m : ℕ) (c : ℕ → Bool) (v r : List Bool) (hm : m ≤ n) :
    bracket (K := K) n m c v r = 0
      ↔ (∀ j, m < j → j ≤ n → c j = false) ∧ v = r ++ bitsOf m c := by
  constructor
  · intro h
    have hpad : ∀ j, m < j → j ≤ n → c j = false := by
      intro j hmj hjn
      obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨j - 1, by omega⟩
      have hc := bracket_coeff_padding (K := K) n m c v r j₀ (by omega) (by omega)
      rw [h, coeff_zero] at hc
      cases hcj : c (j₀ + 1)
      · rfl
      · exfalso; rw [hcj] at hc; simp [bit] at hc
    refine ⟨hpad, ?_⟩
    have hsplit := Cpoly_split (K := K) n m c hm hpad
    have h' : X ^ n * (addrP v - addrP (r ++ bitsOf m c)) = (0 : K[X]) := by
      rw [addrP_append, bitsOf_length, ← h, bracket, hsplit, ← mul_assoc, ← pow_add,
        Nat.add_sub_cancel' hm]
      ring
    rcases mul_eq_zero.mp h' with hX | hd
    · exact absurd hX (pow_ne_zero _ X_ne_zero)
    · exact addrP_injective (sub_eq_zero.mp hd)
  · rintro ⟨hpad, rfl⟩
    rw [bracket, Cpoly_split n m c hm hpad, addrP_append, bitsOf_length, ← mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hm]
    ring

/-- **Completeness of the certificate**: the honest placement has bracket `0` for every `λ`. -/
theorem bracket_honest (n m : ℕ) (c : ℕ → Bool) (r : List Bool) (hm : m ≤ n)
    (hpad : ∀ j, m < j → j ≤ n → c j = false) :
    bracket (K := K) n m c (r ++ bitsOf m c) r = 0 :=
  (bracket_zero_iff n m c _ r hm).mpr ⟨hpad, rfl⟩

/-- Zero bracket puts the verify at or strictly below the read (`R` is a prefix of `V`). -/
theorem bracket_zero_prefix (n m : ℕ) (c : ℕ → Bool) (v r : List Bool) (hm : m ≤ n)
    (h : bracket (K := K) n m c v r = 0) : r <+: v := by
  obtain ⟨_, rfl⟩ := (bracket_zero_iff n m c v r hm).mp h
  exact List.prefix_append r _

/-- **Attack: a verify ABOVE its read** (`|V| < |R|`) — never accepted, for any certificate. -/
theorem verify_above_read_rejected (n m : ℕ) (c : ℕ → Bool) (v r : List Bool) (hm : m ≤ n)
    (hlt : v.length < r.length) : bracket (K := K) n m c v r ≠ 0 := by
  intro h
  have := (bracket_zero_prefix n m c v r hm h).length_le
  omega

/-- **Attack: read and verify on the SAME node** — accepted only with `m = 0` and no padding,
i.e. the certified axis is `1` (`/[1 R] = R`, honest). -/
theorem same_node_forces_axis_one (n m : ℕ) (c : ℕ → Bool) (v : List Bool) (hm : m ≤ n) :
    bracket (K := K) n m c v v = 0 ↔ m = 0 ∧ ∀ j, 0 < j → j ≤ n → c j = false := by
  rw [bracket_zero_iff n m c v v hm]
  constructor
  · rintro ⟨hpad, hv⟩
    have hb : bitsOf m c = [] := by
      have := congrArg List.length hv
      simp [bitsOf_length] at this
      exact List.eq_nil_of_length_eq_zero (by simp [bitsOf_length]; omega)
    have hm0 : m = 0 := by have := bitsOf_length m c; rw [hb] at this; simpa using this.symm
    exact ⟨hm0, fun j hj hjn => hpad j (by omega) hjn⟩
  · rintro ⟨rfl, hpad⟩
    exact ⟨fun j hj hjn => hpad j hj hjn, by simp [bitsOf]⟩

/-- **Attack: a read wrapper whose subtree has no verify** — the verify is then not below the
read, so the only zero bracket is `V = R` (`a = 1`); any `a ≠ 1` is rejected. -/
theorem read_over_leaf_rejected (n m : ℕ) (c : ℕ → Bool) (v r : List Bool) (hm : m ≤ n)
    (hnot : ¬ r <+: v) : bracket (K := K) n m c v r ≠ 0 :=
  fun h => hnot (bracket_zero_prefix n m c v r hm h)

/-- **`a = 0` is unrepresentable**: `a_λ = X^m·Cpoly` is monic, never the zero polynomial; a
read wrapper alone (no verify of its exponent anywhere) leaves `−a_λ·ts ≠ 0`. -/
theorem certified_axis_ne_zero (n m : ℕ) (c : ℕ → Bool) :
    X ^ m * Cpoly (K := K) n c ≠ 0 := by
  intro h
  have hc := congrArg (fun q : K[X] => q.coeff (m + n)) h
  simp only [X_pow_mul_Cpoly, coeff_add, finsetSum_coeff, coeff_X_pow, coeff_C_mul,
    coeff_zero, if_true] at hc
  rw [Finset.sum_eq_zero] at hc
  · simp at hc
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega), mul_zero]

/-- **Cross-root, both roots.**  Root 1 holds the read wrapper at `q` (subtree free of
the record), root 2 the verify at `p`.  Root 1's `X^e`-coefficient polynomial is
`−X^m·(Cpoly + X^n(P_q − 1))` and root 2's is `X^n·P_p`; BOTH are nonzero for every certificate
`(m, c)` and every `q`, `p` — the per-root check rejects on either root, with no `a = 0` escape. -/
theorem cross_root_both_nonzero (n m : ℕ) (c : ℕ → Bool) (q p : List Bool) :
    -(X ^ m * (Cpoly (K := K) n c + X ^ n * (addrP q - 1))) ≠ 0
    ∧ X ^ n * addrP (K := K) p ≠ 0 := by
  constructor
  · rw [neg_ne_zero]
    refine mul_ne_zero (pow_ne_zero _ X_ne_zero) ?_
    intro h
    have hc := congrArg (fun z : K[X] => z.coeff (n + q.length)) h
    simp only [coeff_add, coeff_X_pow_mul', coeff_sub, coeff_zero] at hc
    rw [if_pos (Nat.le_add_right n _), Nat.add_sub_cancel_left, addrP_coeff_length] at hc
    have hC : (Cpoly (K := K) n c).coeff (n + q.length) = if q.length = 0 then 1 else 0 := by
      simp only [Cpoly, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul]
      rw [Finset.sum_eq_zero, add_zero]
      · by_cases hq : q.length = 0 <;> simp [hq]
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [if_neg (by omega), mul_zero]
    rw [hC] at hc
    by_cases hq : q.length = 0
    · rw [if_pos hq, coeff_one, if_pos hq] at hc; simp at hc
    · rw [if_neg hq, coeff_one, if_neg hq] at hc; simp at hc
  · exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (addrP_ne_zero p)

end Nock.RedTeam.Batch554
