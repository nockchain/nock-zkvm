import Nock.Framework
import Nock.AIR
import Nock.Counts
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Shows that `RAP.d` is the multivariate total degree of the constraints and does not bound the composed univariate degree. It also states the selector-variable degree cost, the row-constraint counts, and that `RAP.Satisfies` does not read `RAP.e`. -/

namespace AtkDeg

open Nock Nock.Framework Nock.Framework.Reify Nock.Reified
open scoped Polynomial

variable {F : Type*} [Field F]

/-! ## 1.  `RAP.d` does NOT bound the composed univariate degree.

  `single_point_gate_degree_lb` bounds `g.natDegree` for a *univariate*
  `g : F[X]`.  `RAP.d` is `Finset.univ.sup (fun i => (C i).totalDegree)` — the *multivariate*
  total degree of the symbolic constraint in the `Y_{i,j}`.  The two are unrelated: here is a
  RAP with `d = 1` whose composed constraint polynomial has degree 100. -/

noncomputable def tinyRAP : RAP ℚ where
  e := 1
  k := 1
  wRAP := fun _ => 1
  w := 1
  w_eq := by simp
  h := 1
  d := 1
  s := 1
  ω := 1
  β := 1
  I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
  C := fun _ => MvPolynomial.X (⟨0, by norm_num⟩, 0)
  C_vars := by
    intro i
    rw [MvPolynomial.vars_X, Finset.singleton_subset_iff, Finset.mem_product]
    exact ⟨Finset.mem_univ _, by simp⟩
  C_deg := by intro i; simp [MvPolynomial.totalDegree_X]
  H := ∅
  β_ne_zero := one_ne_zero
  I_bound := by
    intro q hq
    have h2 := (Finset.mem_product.mp hq).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h | h <;> omega

/-- `d = 1` … -/
theorem tinyRAP_d : tinyRAP.d = 1 := rfl

/-- … while the composed polynomial has degree `100`.  So no bound on the composed univariate
    degree (e.g. `single_point_gate_degree_lb`'s `H.card - 1 ≤ g.natDegree`) says ANYTHING about
    `RAP.d`, hence nothing about `CanonicalRAP.common_d`. -/
theorem d_does_not_bound_composed_degree (R : RAP ℚ) (i : Fin R.s) (j : Fin R.w)
    (hC : R.C i = MvPolynomial.X (j, 0)) (P : Fin R.w → ℚ[X]) :
    R.compose P i = (P j).comp (Polynomial.C (R.ω ^ (0 : ℕ)) * Polynomial.X) := by
  rw [RAP.compose, hC, MvPolynomial.aeval_X]

/-- Concretely: such a `C i` has `totalDegree = 1`, so `d = 1` suffices, while the composed
    polynomial is `P j` itself — of unbounded degree.  With Lagrange trace encodings
    (`encodeComputeTrace`) `P j` already has degree `~2^h`, so "the composed polynomial needs
    degree `≥ |H| − 1`" is a statement about a quantity the `RAP` never records. -/
theorem gate_C_has_totalDegree_one (R : RAP ℚ) (j : Fin R.w) :
    (MvPolynomial.X (R := ℚ) (j, (0:ℕ))).totalDegree = 1 :=
  MvPolynomial.totalDegree_X _

theorem composed_degree_can_be_100 (c : ℚ) (hc : c ≠ 0) :
    (((Polynomial.X : ℚ[X]) ^ 100).comp (Polynomial.C c * Polynomial.X)).natDegree = 100 := by
  rw [Polynomial.natDegree_comp]
  rw [Polynomial.natDegree_X_pow]
  rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X]

/-! ## 2.  Consequence: a *selector variable* costs exactly `+1` of multivariate total degree.

  So a kind-activation gate implemented as a (preprocessed) column raises `airToRAP`'s `d` from
  4 to 5 — it does not raise it to `~2^h`.  `common_d` is then still discharge-able (both chips
  gated ⇒ both at 5). -/

theorem gate_costs_exactly_one_totalDegree {σ : Type*} [DecidableEq σ] (v : σ)
    (q : MvPolynomial σ ℚ) (hq : q ≠ 0) :
    (MvPolynomial.X v * q).totalDegree = q.totalDegree + 1 := by
  rw [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero v) hq,
    MvPolynomial.totalDegree_X]
  omega

/-! ## 3.  The `.row` constraints are 526 of 527 (compute) and 75 of 80 (memory), and their max
    degree is already 4.  (The counts below are `rfl`/`decide` facts about the shipped AIRs.) -/

set_option maxRecDepth 100000 in
theorem compute_row_kind_count :
    (Reified.Trans.computeAIRchained.constraints.countP
      (fun c => c.kind == Reified.ConstraintKind.row)) = 526 := by rfl

set_option maxRecDepth 100000 in
theorem compute_transition_kind_count :
    (Reified.Trans.computeAIRchained.constraints.countP
      (fun c => c.kind == Reified.ConstraintKind.transition)) = 1 := by rfl

set_option maxRecDepth 100000 in
theorem compute_boundary_and_terminal_are_absent :
    (Reified.Trans.computeAIRchained.constraints.countP
      (fun c => c.kind == Reified.ConstraintKind.boundary)) = 0 ∧
    (Reified.Trans.computeAIRchained.constraints.countP
      (fun c => c.kind == Reified.ConstraintKind.terminal)) = 0 := by
  constructor <;> rfl

set_option maxRecDepth 100000 in
theorem row_kind_constraints_reach_degree_four :
    ((Reified.Trans.computeAIRchained.constraints.filter
        (fun c => c.kind == Reified.ConstraintKind.row)).foldr
      (fun c a => max c.expr.degree a) 0) = 4 := by rfl

/-! ## 4.  `RAP.e` is consumed by nothing: `RAP.Satisfies` is `e`-blind. -/

theorem satisfies_is_e_blind (R : RAP F) (e' : ℕ) (P : Fin R.w → F[X]) :
    R.Satisfies P ↔ ({R with e := e'} : RAP F).Satisfies (P) := Iff.rfl

theorem tinyRAP_order_omega_is_one : orderOf tinyRAP.ω = 1 := by
  simp [tinyRAP]

end AtkDeg

section Audit
#print axioms AtkDeg.tinyRAP_d
#print axioms AtkDeg.d_does_not_bound_composed_degree
#print axioms AtkDeg.gate_C_has_totalDegree_one
#print axioms AtkDeg.composed_degree_can_be_100
#print axioms AtkDeg.gate_costs_exactly_one_totalDegree
#print axioms AtkDeg.compute_row_kind_count
#print axioms AtkDeg.compute_transition_kind_count
#print axioms AtkDeg.compute_boundary_and_terminal_are_absent
#print axioms AtkDeg.row_kind_constraints_reach_degree_four
#print axioms AtkDeg.satisfies_is_e_blind
end Audit
