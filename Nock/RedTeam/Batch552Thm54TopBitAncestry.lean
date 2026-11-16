/-
  Nock/RedTeam/Batch552Thm54TopBitAncestry.lean

  **Item D (the per-record identity forces ancestry) and the SURVIVING memory
  functional: the standard address needs a `λ^depth` accumulator `pw`, not the paper's `ind`.**

  Item D.  Write a node's address as a bit list `q` (LSB first, `q[0]` = the edge into the node)
  and `bitsPoly q = X^{|q|} + Σ qᵢXⁱ` (`X = λ`).  No case split — `d_V < m`,
  `d_V = m`, dominated bits, `V = R`, a verify above its read — is needed: injectivity covers
  every list.  The reversed orientation (top-down lists, `A_V − A_R = λ^{d_R}(ã − 1)`) is the same
  lemma with the concatenation swapped (`identity_forces_ancestry_reversed`).

  The functional.  Design (i)'s ascending rule reverses bits.  The standard address
  goes up one edge as `P ↦ P + λ^d·(λ − 1 + e)` — it needs the leaf's depth power, which the
  paper's `ind = Σ w` does not carry but `pw = Σ w·λ^d` (`pw_P = λ·(pw_L + pw_R)`) does:
    `counts_P = counts_L + counts_R + (λ − 1)·(pw_L + pw_R) + pw_R`.
  With the verify adding `(ts, ts)` and the read wrapper adding `(−a_λ·ts, −T·ts)` to
  `(counts, pw)`, a leaf `(c, u)` at path `p` contributes `c + (P_p − 1)·u` to the root
  (`countsS_eq_sum`, every sign, every position, wrappers included), so the root's `X^e`
  coefficient of a record with verify at `v` and read at `r` is `P_v − a_λ − T·(P_r − 1)`
  (`record_coefficient`) — zero as a polynomial in `λ` iff `V` is under `R` at address `a`
  (item D).
-/
import Nock.RedTeam.Batch550Thm54TopBitModel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch552

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch546 (axisL)
open Nock.RedTeam.Batch550 (embed revAddr stdAddr axisL_five)
open Polynomial

variable {K : Type*} [Field K]

/-! ## Item D — polynomials of bit lists -/

/-- `bitsPoly q = X^{|q|} + Σ_i qᵢ·Xⁱ`, `q[0]` the LSB. -/
noncomputable def bitsPoly : List Bool → K[X]
  | [] => 1
  | e :: q => X * bitsPoly q + C (if e then (1 : K) else 0)

theorem bitsPoly_append (a r : List Bool) :
    bitsPoly (K := K) (a ++ r) = X ^ a.length * bitsPoly r + (bitsPoly a - X ^ a.length) := by
  induction a with
  | nil => simp [bitsPoly]
  | cons e a ih =>
      simp only [List.cons_append, bitsPoly, ih, List.length_cons, pow_succ]
      ring

theorem bitsPoly_coeff_zero (e : Bool) (q : List Bool) :
    (bitsPoly (K := K) (e :: q)).coeff 0 = if e then 1 else 0 := by
  cases e <;> simp [bitsPoly]

theorem bitsPoly_coeff_succ (e : Bool) (q : List Bool) (i : ℕ) :
    (bitsPoly (K := K) (e :: q)).coeff (i + 1) = (bitsPoly q).coeff i := by
  cases e <;> simp [bitsPoly, coeff_X_mul, coeff_one]

theorem bitsPoly_coeff_length (q : List Bool) :
    (bitsPoly (K := K) q).coeff q.length = 1 := by
  induction q with
  | nil => simp [bitsPoly]
  | cons e q ih => rw [List.length_cons, bitsPoly_coeff_succ, ih]

theorem bitsPoly_coeff_gt (q : List Bool) (i : ℕ) (h : q.length < i) :
    (bitsPoly (K := K) q).coeff i = 0 := by
  induction q generalizing i with
  | nil =>
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp [bitsPoly, coeff_one]
  | cons e q ih =>
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [bitsPoly_coeff_succ]
      exact ih j (by simp at h; omega)

/-- **`bitsPoly` is injective**: a monic polynomial with `0/1` lower coefficients determines its
bit list. -/
theorem bitsPoly_inj : ∀ q q' : List Bool, bitsPoly (K := K) q = bitsPoly q' → q = q' := by
  intro q
  induction q with
  | nil =>
      intro q' h
      cases q' with
      | nil => rfl
      | cons e' q' =>
          exfalso
          have h1 : (bitsPoly (K := K) []).coeff (q'.length + 1)
              = (bitsPoly (e' :: q')).coeff (q'.length + 1) := by rw [h]
          have h2 := bitsPoly_coeff_length (K := K) (e' :: q')
          rw [List.length_cons] at h2
          rw [bitsPoly_coeff_gt [] _ (by simp), h2] at h1
          exact zero_ne_one h1
  | cons e q ih =>
      intro q' h
      cases q' with
      | nil =>
          exfalso
          have h1 : (bitsPoly (K := K) (e :: q)).coeff (q.length + 1)
              = (bitsPoly []).coeff (q.length + 1) := by rw [h]
          have h2 := bitsPoly_coeff_length (K := K) (e :: q)
          rw [List.length_cons] at h2
          rw [bitsPoly_coeff_gt [] _ (by simp), h2] at h1
          exact one_ne_zero h1
      | cons e' q' =>
          have h0 : (bitsPoly (K := K) (e :: q)).coeff 0 = (bitsPoly (e' :: q')).coeff 0 := by
            rw [h]
          rw [bitsPoly_coeff_zero, bitsPoly_coeff_zero] at h0
          have hq : bitsPoly (K := K) q = bitsPoly q' := by
            ext i
            have h2 : (bitsPoly (K := K) (e :: q)).coeff (i + 1)
                = (bitsPoly (e' :: q')).coeff (i + 1) := by rw [h]
            rwa [bitsPoly_coeff_succ, bitsPoly_coeff_succ] at h2
          rw [ih q' hq]
          congr 1
          cases e <;> cases e' <;> simp at h0 ⊢

theorem bitsPoly_injective : Function.Injective (bitsPoly (K := K)) :=
  fun q q' h => bitsPoly_inj q q' h

/-- **Item D, standard orientation (the author's identity).**  `P_V − a_λ = λ^m·(P_R − 1)` with
`a_λ = bitsPoly b` and `m = |b|` forces `V = b ++ R`: `V` is at relative address `b` under `R`. -/
theorem identity_forces_ancestry (v r b : List Bool)
    (h : bitsPoly (K := K) v - bitsPoly b = X ^ b.length * (bitsPoly r - 1)) :
    v = b ++ r :=
  bitsPoly_inj (K := K) v (b ++ r) (by rw [bitsPoly_append]; linear_combination h)

/-- Completeness: the honest placement satisfies the identity (for every `λ`, as polynomials). -/
theorem ancestry_satisfies_identity (r b : List Bool) :
    bitsPoly (K := K) (b ++ r) - bitsPoly b = X ^ b.length * (bitsPoly r - 1) := by
  rw [bitsPoly_append]; ring

/-- **Item D, reversed orientation** (top-down lists, the ascending functional):
`A_V − A_R = λ^{d_R}·(ã − 1)` with `ã = bitsPoly b'` forces `V = R ++ b'`. -/
theorem identity_forces_ancestry_reversed (v r b' : List Bool)
    (h : bitsPoly (K := K) v - bitsPoly r = X ^ r.length * (bitsPoly b' - 1)) :
    v = r ++ b' :=
  bitsPoly_inj (K := K) v (r ++ b') (by rw [bitsPoly_append]; linear_combination h)

/-- `revAddr` and `stdAddr`  are evaluations of `bitsPoly`. -/
theorem revAddr_eq_eval (l : K) (p : List Bool) : revAddr l p = (bitsPoly p).eval l := by
  induction p with
  | nil => simp [revAddr, bitsPoly]
  | cons e p ih => cases e <;> simp [revAddr, bitsPoly, ih]

theorem stdAddr_eq_eval (l : K) (p : List Bool) :
    stdAddr l p = (bitsPoly p.reverse).eval l := by
  simp [stdAddr, revAddr_eq_eval]

theorem revAddr_append_singleton (l : K) (q : List Bool) (e : Bool) :
    revAddr l (q ++ [e]) = revAddr l q + l ^ q.length * (l - 1 + if e then 1 else 0) := by
  induction q with
  | nil => simp [revAddr]; ring
  | cons e' q ih => simp only [List.cons_append, revAddr, ih, List.length_cons, pow_succ]; ring

/-- The standard address goes up one edge as `P ↦ P + λ^d·(λ − 1 + e)`: it needs `λ^d`. -/
theorem stdAddr_cons (l : K) (e : Bool) (p : List Bool) :
    stdAddr l (e :: p) = stdAddr l p + l ^ p.length * (l - 1 + if e then 1 else 0) := by
  simp only [stdAddr, List.reverse_cons, revAddr_append_singleton, List.length_reverse]

/-! ## The surviving functional: `(counts, pw)` -/

/-- `pw = Σ w·λ^{depth}`: `decompose` scales by `λ`; the verify adds `ts`, the read wrapper
subtracts `T·ts`. -/
noncomputable def pwS (l : K) (T : ℕ → K) : MTree K → K[X]
  | .halt => 0
  | .decompose L R => C l * (pwS l T L + pwS l T R)
  | .read e c => pwS l T c - C (T e) * X ^ e
  | .verify e _ c => pwS l T c + X ^ e

/-- `counts_P = counts_L + counts_R + (λ − 1)·(pw_L + pw_R) + pw_R`; the verify adds `ts`, the
read wrapper subtracts `a_λ·ts` (record fields keyed by the timestamp exponent). -/
noncomputable def countsS (l : K) (T A : ℕ → K) : MTree K → K[X]
  | .halt => 0
  | .decompose L R =>
      countsS l T A L + countsS l T A R + C (l - 1) * (pwS l T L + pwS l T R) + pwS l T R
  | .read e c => countsS l T A c - C (A e) * X ^ e
  | .verify e _ c => countsS l T A c + X ^ e

/-- The leaves of a tree with their top-down paths and timestamp exponents; `true` marks a read
wrapper. -/
def leaves : MTree K → List (List Bool × ℕ × Bool)
  | .halt => []
  | .decompose L R =>
      (leaves L).map (fun x => (false :: x.1, x.2)) ++ (leaves R).map (fun x => (true :: x.1, x.2))
  | .read e c => ([], e, true) :: leaves c
  | .verify e _ c => ([], e, false) :: leaves c

/-- A leaf's `(counts, pw)` weights, from its `(exponent, isRead)`. -/
noncomputable def leafC (A : ℕ → K) (x : ℕ × Bool) : K[X] :=
  if x.2 then -(C (A x.1) * X ^ x.1) else X ^ x.1

noncomputable def leafU (T : ℕ → K) (x : ℕ × Bool) : K[X] :=
  if x.2 then -(C (T x.1) * X ^ x.1) else X ^ x.1

/-- The `counts` contribution of a leaf list at the top: `c + (P_p − 1)·u` per leaf. -/
noncomputable def sumC (l : K) (T A : ℕ → K) (L : List (List Bool × ℕ × Bool)) : K[X] :=
  (L.map fun x => leafC A x.2 + C (stdAddr l x.1 - 1) * leafU T x.2).sum

/-- The `pw` contribution: `λ^{|p|}·u` per leaf. -/
noncomputable def sumU (l : K) (T : ℕ → K) (L : List (List Bool × ℕ × Bool)) : K[X] :=
  (L.map fun x => C (l ^ x.1.length) * leafU T x.2).sum

theorem sumC_nil (l : K) (T A : ℕ → K) : sumC l T A [] = 0 := rfl
theorem sumU_nil (l : K) (T : ℕ → K) : sumU l T [] = 0 := rfl

theorem sumC_cons (l : K) (T A : ℕ → K) (x : List Bool × ℕ × Bool)
    (L : List (List Bool × ℕ × Bool)) :
    sumC l T A (x :: L) = (leafC A x.2 + C (stdAddr l x.1 - 1) * leafU T x.2) + sumC l T A L := by
  simp [sumC]

theorem sumU_cons (l : K) (T : ℕ → K) (x : List Bool × ℕ × Bool)
    (L : List (List Bool × ℕ × Bool)) :
    sumU l T (x :: L) = C (l ^ x.1.length) * leafU T x.2 + sumU l T L := by
  simp [sumU]

theorem sumC_append (l : K) (T A : ℕ → K) (L L' : List (List Bool × ℕ × Bool)) :
    sumC l T A (L ++ L') = sumC l T A L + sumC l T A L' := by
  simp [sumC]

theorem sumU_append (l : K) (T : ℕ → K) (L L' : List (List Bool × ℕ × Bool)) :
    sumU l T (L ++ L') = sumU l T L + sumU l T L' := by
  simp [sumU]

/-- Going up one edge `b`: every leaf's `counts` term gains `(λ − 1 + b)·λ^{|p|}·u`. -/
theorem sumC_shift (l : K) (T A : ℕ → K) (b : Bool) (L : List (List Bool × ℕ × Bool)) :
    sumC l T A (L.map fun x => (b :: x.1, x.2))
      = sumC l T A L + C (l - 1 + if b then 1 else 0) * sumU l T L := by
  induction L with
  | nil => simp [sumC, sumU]
  | cons x L ih =>
      simp only [List.map_cons, sumC_cons, sumU_cons, ih, stdAddr_cons]
      cases b <;> simp only [if_true, Bool.false_eq_true, if_false, add_zero, C_add, C_sub, C_mul,
        C_pow, C_1] <;> ring

theorem sumU_shift (l : K) (T : ℕ → K) (b : Bool) (L : List (List Bool × ℕ × Bool)) :
    sumU l T (L.map fun x => (b :: x.1, x.2)) = C l * sumU l T L := by
  induction L with
  | nil => simp [sumU]
  | cons x L ih =>
      simp only [List.map_cons, sumU_cons, ih, List.length_cons, pow_succ, C_mul]
      ring

/-- **Item C for the surviving form — the functional, exactly, for every sign and position.**
Each leaf `(c, u)` at path `p` contributes `c + (P_p − 1)·u` to `counts` and `λ^{|p|}·u` to
`pw`. -/
theorem countsS_eq_sum (l : K) (T A : ℕ → K) (t : MTree K) :
    countsS l T A t = sumC l T A (leaves t) ∧ pwS l T t = sumU l T (leaves t) := by
  induction t with
  | halt => simp [countsS, pwS, leaves, sumC, sumU]
  | decompose L R ihl ihr =>
      obtain ⟨hcl, hpl⟩ := ihl
      obtain ⟨hcr, hpr⟩ := ihr
      simp only [countsS, pwS, leaves, sumC_append, sumU_append, sumC_shift, sumU_shift,
        hcl, hpl, hcr, hpr]
      constructor
      · simp only [if_true, Bool.false_eq_true, if_false, add_zero, C_add, C_sub, C_1]; ring
      · ring
  | read e c ih =>
      obtain ⟨hc, hp⟩ := ih
      simp only [countsS, pwS, leaves, sumC_cons, sumU_cons, hc, hp, leafC, leafU, if_true,
        stdAddr, List.reverse_nil, revAddr, List.length_nil, pow_zero, C_1, sub_self, C_0]
      constructor <;> ring
  | verify e a c ih =>
      obtain ⟨hc, hp⟩ := ih
      simp only [countsS, pwS, leaves, sumC_cons, sumU_cons, hc, hp, leafC, leafU,
        Bool.false_eq_true, if_false, stdAddr, List.reverse_nil, revAddr, List.length_nil,
        pow_zero, C_1, sub_self, C_0]
      constructor <;> ring

/-- Coefficient extraction through a list sum. -/
theorem coeff_list_sum (L : List K[X]) (k : ℕ) :
    L.sum.coeff k = (L.map fun p => p.coeff k).sum := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

theorem leaf_coeff (l : K) (T A : ℕ → K) (x : List Bool × ℕ × Bool) (e : ℕ) :
    (leafC A x.2 + C (stdAddr l x.1 - 1) * leafU T x.2).coeff e
      = if x.2.1 = e then
          (if x.2.2 then -(A x.2.1) - T x.2.1 * (stdAddr l x.1 - 1) else stdAddr l x.1)
        else 0 := by
  rcases x with ⟨p, e', b⟩
  by_cases h : e' = e
  · subst h
    cases b <;> simp [leafC, leafU, coeff_X_pow, coeff_sub, coeff_C_mul, sub_mul] <;> ring
  · cases b <;> simp [leafC, leafU, coeff_X_pow, coeff_sub, coeff_C_mul, sub_mul, h, Ne.symm h]

/-- Only the leaves of exponent `e` reach the `X^e` coefficient. -/
theorem sum_filter_exponent (L : List (List Bool × ℕ × Bool)) (e : ℕ) (g : List Bool × ℕ × Bool → K) :
    (L.map fun x => if x.2.1 = e then g x else 0).sum
      = ((L.filter fun x => x.2.1 = e).map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
      by_cases h : x.2.1 = e
      · simp [h, ih]
      · simp [h, ih]

/-- **The per-record coefficient.**  If the leaves of exponent `e` are exactly one verify at
path `v` and one read wrapper at path `r`, the root's `X^e` coefficient of `counts` is
`P_v − a_λ − T·(P_r − 1)` evaluated at `λ`. -/
theorem record_coefficient (l : K) (T A : ℕ → K) (t : MTree K) (e : ℕ) (v r : List Bool)
    (h : (leaves t).filter (fun x => x.2.1 = e) = [(v, e, false), (r, e, true)]) :
    (countsS l T A t).coeff e = stdAddr l v - A e - T e * (stdAddr l r - 1) := by
  rw [(countsS_eq_sum l T A t).1, sumC, coeff_list_sum, List.map_map]
  have : ((leaves t).map ((fun p : K[X] => p.coeff e) ∘
      fun x => leafC A x.2 + C (stdAddr l x.1 - 1) * leafU T x.2)).sum
      = ((leaves t).map fun x => if x.2.1 = e then
          (if x.2.2 then -(A x.2.1) - T x.2.1 * (stdAddr l x.1 - 1) else stdAddr l x.1)
          else 0).sum := by
    congr 1
    apply List.map_congr_left
    intro x _
    exact leaf_coeff l T A x e
  rw [this, sum_filter_exponent, h]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_true,
    Bool.false_eq_true, if_false, add_zero]
  ring

/-- The coefficient is the evaluation at `λ` of the item-D polynomial
`bitsPoly v.rev − bitsPoly b − X^{|b|}·(bitsPoly r.rev − 1)` when the record is certified as
`a_λ = bitsPoly b`, `T = λ^{|b|}`: it vanishes for EVERY `λ` iff `v.rev = b ++ r.rev`
(`identity_forces_ancestry`), i.e. iff `V` is at address `b` under `R`. -/
theorem record_coefficient_eval (l : K) (T A : ℕ → K) (t : MTree K) (e : ℕ) (v r b : List Bool)
    (h : (leaves t).filter (fun x => x.2.1 = e) = [(v, e, false), (r, e, true)])
    (hA : A e = (bitsPoly b).eval l) (hT : T e = l ^ b.length) :
    (countsS l T A t).coeff e
      = (bitsPoly v.reverse - bitsPoly b - X ^ b.length * (bitsPoly r.reverse - 1)).eval l := by
  rw [record_coefficient l T A t e v r h, hA, hT, stdAddr_eq_eval, stdAddr_eq_eval]
  simp

/-! ## Concrete traces -/

theorem leaves_embed (p : List Bool) (t : MTree K) :
    leaves (embed p t) = (leaves t).map (fun x => (p ++ x.1, x.2)) := by
  induction p with
  | nil => simp [embed]
  | cons e p ih => cases e <;> simp [embed, leaves, ih, List.map_map, Function.comp_def]

theorem pwS_embed (l : K) (T : ℕ → K) (p : List Bool) (t : MTree K) :
    pwS l T (embed p t) = C (l ^ p.length) * pwS l T t := by
  induction p with
  | nil => simp [embed]
  | cons e p ih => cases e <;> simp [embed, pwS, ih, pow_succ, C_mul] <;> ring

theorem countsS_embed (l : K) (T A : ℕ → K) (p : List Bool) (t : MTree K) :
    countsS l T A (embed p t) = countsS l T A t + C (stdAddr l p - 1) * pwS l T t := by
  induction p with
  | nil => simp [embed, stdAddr, revAddr]
  | cons e p ih =>
      cases e
      · simp only [embed, countsS, pwS, ih, pwS_embed, stdAddr_cons]
        simp only [Bool.false_eq_true, if_false, add_zero, C_sub, C_add, C_mul, C_pow, C_1]
        ring
      · simp only [embed, countsS, pwS, ih, pwS_embed, stdAddr_cons]
        simp only [if_true, C_sub, C_add, C_mul, C_pow, C_1]
        ring

/-- **Honest exactness for every `λ`, per root.**  A read wrapper at the end of path `q` with the
verify at path `p` below it, `a_λ = P_p`, `T = λ^{|p|}`: `counts = pw = 0` at the top. -/
theorem honest_exact (l : K) (e : ℕ) (a : K) (q p : List Bool) :
    countsS l (fun _ => l ^ p.length) (fun _ => stdAddr l p)
        (embed q (.read e (embed p (.verify e a .halt)))) = 0
    ∧ pwS l (fun _ => l ^ p.length) (embed q (.read e (embed p (.verify e a .halt)))) = 0 := by
  have h1 : countsS l (fun _ => l ^ p.length) (fun _ => stdAddr l p)
      (.read e (embed p (.verify e a .halt))) = 0 := by
    simp only [countsS, countsS_embed, pwS, pwS_embed, C_sub, C_pow, C_1]; ring
  have h2 : pwS l (fun _ => l ^ p.length) (.read e (embed p (.verify e a .halt))) = 0 := by
    simp only [pwS, pwS_embed, C_pow]; ring
  rw [countsS_embed, pwS_embed, h1, h2]; simp

theorem reversal_rejected (l : K) (e : ℕ) :
    countsS l (fun _ => l ^ 2) (fun _ => axisL l 63 5)
        (.read e (embed [true, false] (.verify e 0 .halt))) = C (l - 1) * X ^ e
    ∧ countsS l (fun _ => l ^ 2) (fun _ => axisL l 63 5)
        (.read e (embed [false, true] (.verify e 0 .halt))) = 0 := by
  rw [axisL_five l 63 (by norm_num)]
  constructor
  · simp only [countsS, countsS_embed, pwS, pwS_embed, C_sub, C_pow, C_1, C_add]
    have : stdAddr l [true, false] = l ^ 2 + l := by simp [stdAddr, revAddr]; ring
    rw [this]; simp only [C_add, C_pow, C_sub]; ring
  · simp only [countsS, countsS_embed, pwS, pwS_embed, C_sub, C_pow, C_1, C_add]
    have : stdAddr l [false, true] = l ^ 2 + 1 := by simp [stdAddr, revAddr]; ring
    rw [this]; simp only [C_add, C_pow, C_1]; ring

/-- `t1` (`a = 1`, `T = 1`) gives
`λ(λ − 1)·ts`, `t2` (`a = 2`, `T = λ`) gives `λ²(λ − 1)·ts`, `tfull` gives `λ(λ − 1)·ts₂` —
all nonzero polynomials in `λ`. -/
theorem t1_rejected (l : K) (e : ℕ) :
    countsS l (fun _ => 1) (fun _ => 1) (Batch546.t1 e 0) = C (l * (l - 1)) * X ^ e := by
  simp only [Batch546.t1, countsS, pwS, C_sub, C_mul, C_1]; ring

theorem t2_rejected (l : K) (e : ℕ) :
    countsS l (fun _ => l) (fun _ => l) (Batch546.t2 e 0) = C (l ^ 2 * (l - 1)) * X ^ e := by
  simp only [Batch546.t2, countsS, pwS, C_sub, C_mul, C_pow, C_1]; ring

theorem tfull_rejected (l : K) (e₁ e₂ : ℕ) (hne : e₁ ≠ e₂) :
    countsS l (fun e => if e = e₁ then l else 1) (fun e => if e = e₁ then l + 1 else 1)
      (Batch546.tfull e₁ e₂ 0 0) = C (l * (l - 1)) * X ^ e₂ := by
  simp only [Batch546.tfull, countsS, pwS, if_true, if_neg (Ne.symm hne), C_sub, C_add, C_1,
    C_mul]
  ring

/-- Root 1 (the bare
read wrapper) has `counts = −a_λ·ts` and root 2 has `counts = P_p·ts`; `P_p` is monic in `λ`,
so the two cannot both vanish identically. -/
theorem cross_root_rejected (l : K) (T : ℕ → K) (e : ℕ) (a : K) (p : List Bool) :
    countsS l T (fun _ => a) (.read e .halt) = -(C a * X ^ e)
    ∧ countsS l T (fun _ => a) (embed p (.verify e 0 .halt)) = C (stdAddr l p) * X ^ e
    ∧ (bitsPoly (K := K) p.reverse).coeff p.length = 1 := by
  refine ⟨by simp [countsS], ?_, ?_⟩
  · simp only [countsS_embed, countsS, pwS, C_sub, C_1]; ring
  · rw [← List.length_reverse]; exact bitsPoly_coeff_length _

end Nock.RedTeam.Batch552

#print axioms Nock.RedTeam.Batch552.bitsPoly_injective
#print axioms Nock.RedTeam.Batch552.identity_forces_ancestry
#print axioms Nock.RedTeam.Batch552.identity_forces_ancestry_reversed
#print axioms Nock.RedTeam.Batch552.countsS_eq_sum
#print axioms Nock.RedTeam.Batch552.record_coefficient_eval
#print axioms Nock.RedTeam.Batch552.honest_exact
#print axioms Nock.RedTeam.Batch552.reversal_rejected
#print axioms Nock.RedTeam.Batch552.tfull_rejected
#print axioms Nock.RedTeam.Batch552.cross_root_rejected
