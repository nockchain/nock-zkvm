/-
: the error-free DEEP binding
lemma, word side. Words `f : ι → K` on an injective evaluation map `x : ι → K` (the LDE domain `D`), an
out-of-domain point `z` (`ζ ω^k`), a claimed value `v`, the DEEP quotient word `(f − v)/(X − z)`.

If a polynomial `q` (`natDegree q < M`) agrees with the DEEP quotient word on `S`, then the "unquotient"
`q·(X − z) + v` (`natDegree < M + 1`, value `v` at `z`) agrees with `f` on the same `S`. If some polynomial `P`
(`natDegree P < M + 1`) agrees with `f` on `S'` and `|S ∩ S'| ≥ M + 1` (guaranteed by `|S| + |S'| ≥ |ι| + M + 1`,
i.e. unique decoding), then `P = q·(X − z) + v`, hence `P(z) = v`. No probability; nothing is assumed about `f`.
Pure Mathlib.
-/
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace NockvmE2E.Deep

section
variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → K)

/-- `p` agrees with the word `f` on `S` (read through the evaluation map `x`). -/
def Agree (f : ι → K) (p : K[X]) (S : Finset ι) : Prop := ∀ i ∈ S, f i = p.eval (x i)

/-- The DEEP quotient word `(f − v)/(X − z)` on the domain. -/
noncomputable def deepWord (f : ι → K) (z v : K) : ι → K := fun i => (f i - v) / (x i - z)

/-- The unquotient `q·(X − z) + v`. -/
noncomputable def unquot (q : K[X]) (z v : K) : K[X] := q * (Polynomial.X - Polynomial.C z) + Polynomial.C v

theorem unquot_natDegree_lt {q : K[X]} {M : ℕ} (hq : q.natDegree < M) (z v : K) :
    (unquot q z v).natDegree < M + 1 := by
  unfold unquot
  refine (natDegree_add_le _ _).trans_lt (max_lt ?_ (by rw [natDegree_C]; omega))
  refine natDegree_mul_le.trans_lt ?_
  rw [natDegree_X_sub_C]; omega

@[simp] theorem eval_unquot (q : K[X]) (z v : K) : (unquot q z v).eval z = v := by
  simp [unquot]

/-- **Word-quotient algebra.** Off the domain (`z ∉ x(ι)`), agreement of `q` with the DEEP quotient word
on `S` is agreement of `q·(X − z) + v` with `f` on `S`. -/
theorem agree_unquot {f : ι → K} {z v : K} (hz : ∀ i, x i ≠ z) {q : K[X]} {S : Finset ι}
    (h : Agree x (deepWord x f z v) q S) : Agree x f (unquot q z v) S := by
  intro i hi
  have hne : x i - z ≠ 0 := sub_ne_zero.mpr (hz i)
  have hq := h i hi
  simp only [deepWord] at hq
  simp only [unquot, eval_add, eval_mul, eval_sub, eval_X, eval_C]
  rw [← hq, div_mul_cancel₀ _ hne]; ring

theorem degree_lt_of_natDegree_lt {p : K[X]} {N : ℕ} (h : p.natDegree < N) : p.degree < N :=
  lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast h)

/-- Two polynomials of `natDegree < N` that agree on `N` distinct domain points are equal. -/
theorem eq_of_eval_eq (hx : Function.Injective x) {p q : K[X]} {N : ℕ} (hp : p.natDegree < N)
    (hq : q.natDegree < N) {S : Finset ι} (hS : N ≤ S.card) (h : ∀ i ∈ S, p.eval (x i) = q.eval (x i)) :
    p = q := by
  classical
  have hc : (S.image x).card = S.card := Finset.card_image_of_injective _ hx
  refine eq_of_degrees_lt_of_eval_finset_eq (S.image x) ?_ ?_ ?_
  · rw [hc]; exact (degree_lt_of_natDegree_lt hp).trans_le (by exact_mod_cast hS)
  · rw [hc]; exact (degree_lt_of_natDegree_lt hq).trans_le (by exact_mod_cast hS)
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact h i hi

/-- Two polynomials of `natDegree < N` agreeing with the same word on `S`, `S'` with `|S ∩ S'| ≥ N`
are equal. -/
theorem eq_of_agree (hx : Function.Injective x) {f : ι → K} {p q : K[X]} {N : ℕ} (hp : p.natDegree < N)
    (hq : q.natDegree < N) {S S' : Finset ι} (hpS : Agree x f p S) (hqS : Agree x f q S')
    (hS : N ≤ (S ∩ S').card) : p = q :=
  eq_of_eval_eq x hx hp hq hS fun i hi => by
    rw [Finset.mem_inter] at hi
    rw [← hpS i hi.1, ← hqS i hi.2]

/-- Counting: `|S| + |S'| ≥ |ι| + N` gives `|S ∩ S'| ≥ N`. -/
theorem card_inter_ge {S S' : Finset ι} {N : ℕ} (h : Fintype.card ι + N ≤ S.card + S'.card) :
    N ≤ (S ∩ S').card := by
  have h1 := Finset.card_union_add_card_inter S S'
  have h2 : (S ∪ S').card ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **The DEEP binding lemma (single opening, error-free).** `P` (`natDegree < M+1`) agrees with `f` on `S'`;
`q` (`natDegree < M`) agrees with the DEEP quotient word of `(f, z, v)` on `S`; `z` is off the domain; and
`|S| + |S'| ≥ |ι| + M + 1` (unique decoding). Then `P = q·(X − z) + v`, so `P(z) = v`. -/
theorem deep_binding (hx : Function.Injective x) {f : ι → K} {z v : K} (hz : ∀ i, x i ≠ z)
    {P q : K[X]} {M : ℕ} (hP : P.natDegree < M + 1) (hq : q.natDegree < M) {S S' : Finset ι}
    (hqS : Agree x (deepWord x f z v) q S) (hPS : Agree x f P S')
    (hcard : Fintype.card ι + (M + 1) ≤ S.card + S'.card) :
    P = unquot q z v ∧ P.eval z = v := by
  have hE : unquot q z v = P :=
    eq_of_agree x hx (unquot_natDegree_lt hq z v) hP (agree_unquot x hz hqS) hPS (card_inter_ge hcard)
  exact ⟨hE.symm, by rw [← hE, eval_unquot]⟩

end

end NockvmE2E.Deep
