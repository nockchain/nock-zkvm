/-
  FOURTH-PASS ADVERSARIAL REVIEW of plan §D1b.  Part 4:
    * independent re-verification of v3's two headline corrections;
    * the ω-orbit precondition that option E (and A2′, and D) all need.
-/
import Nock.Framework
import Nock.AIR
import Nock.Counts

namespace Rev4

open Nock Nock.Framework Nock.Framework.Reify Nock.Reified
open scoped Polynomial

variable {F : Type*} [Field F]

/-! ## 5a.  v3 headline #1, re-verified INDEPENDENTLY of `atk_degree.lean`.

  `RAP.d` bounds `MvPolynomial.totalDegree` of the SYMBOLIC `C i` (field `C_deg`).  `RAP.Satisfies`
  says only that the COMPOSED univariate vanishes on `H`.  These are different quantities, and
  nothing links them: here a RAP whose `d = 1` is satisfied by a trace whose composed constraint
  polynomial has `natDegree = 100`. -/

theorem d_bounds_only_the_symbolic_degree (R : RAP F) (i : Fin R.s) : (R.C i).totalDegree ≤ R.d :=
  R.C_deg i

/-- A degree-1 symbolic constraint `Y_{j,0}` composes to `P_j` itself, of arbitrary degree. -/
theorem composed_degree_unbounded_by_d (R : RAP ℚ) (i : Fin R.s) (j : Fin R.w)
    (hC : R.C i = MvPolynomial.X (j, 0)) (hd : R.d = 1) (P : Fin R.w → ℚ[X])
    (hP : P j = Polynomial.X ^ 100 * Polynomial.C (R.ω ^ (0:ℕ))⁻¹ ^ 100)
    (hω : R.ω ≠ 0) :
    R.d = 1 ∧ (R.compose P i).natDegree = 100 := by
  refine ⟨hd, ?_⟩
  rw [RAP.compose, hC, MvPolynomial.aeval_X, hP]
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul (by simpa using pow_ne_zero _ hω),
    Polynomial.natDegree_X]
  simp [Polynomial.natDegree_mul, pow_ne_zero, inv_ne_zero hω]

/-! ## 5b.  v3 headline #2, re-verified: a `.point` variable is a PINNED COLUMN or nothing.

  Every symbolic variable of a `RAP` lives in `Fin w × ℕ`, and `RAP.compose` sends `(i,j)` to
  `P_i(ω^j·X)`.  So any reification of a hypothetical `.point` is some `X (i,j)`, and it evaluates
  to `x` only when `(P i).eval (ω^j·x) = x`.  Stated over the shipped `compose`, hypothesis-free
  in the trace: -/

theorem point_variable_must_be_a_pinned_column (R : RAP F) (q : Fin R.w × ℕ)
    (P : Fin R.w → F[X]) (i : Fin R.s) (hC : R.C i = MvPolynomial.X q) (x : F) :
    (R.compose P i).eval x = (P q.1).eval (R.ω ^ (q.2 : ℕ) * x) := by
  rw [compose_eval, hC, MvPolynomial.eval_X]

/-- …and the prover, who picks `P`, defeats it: the all-zero trace makes every such "point"
    variable read `0`, not `x`.  (This is `eval_exprToMv`'s failure, restated on the real
    `RAP.compose`.) -/
theorem prover_defeats_the_point_variable (R : RAP ℚ) (q : Fin R.w × ℕ) (i : Fin R.s)
    (hC : R.C i = MvPolynomial.X q) (x : ℚ) (hx : x ≠ 0) :
    (R.compose (fun _ => 0) i).eval x ≠ x := by
  rw [point_variable_must_be_a_pinned_column R q _ i hC x]
  simpa using (Ne.symm hx)

/-! ## 5c.

  `envOfTrace P ω x` reads the "next row" as `P_i(ω·x)`.  The shipped `ComputeProblem`/`MemProblem`
  constrain `nodes` only by injectivity and leave `ω` free, so today the reified `.transition`
  gate relates row `k` to the point `ω·nodes k`, which need not be a row at all. -/

/-- With `ω = 1` the "transition" gate degenerates to a ROW gate: `traceNext = traceCur`. -/
theorem omega_one_degenerates_transition {w : ℕ} (P : Fin w → F[X]) (x : F)
    (chalVal pubVal : ℕ → F) (i : ℕ) :
    (envOfTrace P 1 x chalVal pubVal).traceNext i = (envOfTrace P 1 x chalVal pubVal).trace i := by
  simp [envOfTrace]

/-- The orbit condition is what makes the next-row read land on the next row. -/
theorem orbit_gives_adjacency {n : ℕ} {w : ℕ} (P : Fin w → F[X]) (ω β : F) (k : ℕ)
    (chalVal pubVal : ℕ → F) (nodes : ℕ → F) (horb : ∀ j, nodes j = β * ω ^ j) (i : ℕ) (hi : i < w) :
    (envOfTrace P ω (nodes k) chalVal pubVal).traceNext i = (P ⟨i, hi⟩).eval (nodes (k + 1)) := by
  simp only [envOfTrace, dif_pos hi, horb]
  ring_nf

/-- With an orbit-PREFIX domain `H = {β·ω^k : k < n}` (a subset of the paper's coset, not the whole
    of it), the transition domain is `H.erase (β·ω^(n-1))` and the last row is genuinely excluded —
    so `B_padding.lean`'s cyclic-`ln` contradiction (`seed·(α^n − 1) = 0`) never arises.  The
    exclusion is a `Finset.erase`: zero columns, zero degree, zero `RAP` changes. -/
theorem prefix_domain_excludes_wrap [DecidableEq F] (n : ℕ) (ω β : F)
    (hinj : Function.Injective (fun k : Fin n => β * ω ^ (k : ℕ))) :
    (Finset.image (fun k : Fin n => β * ω ^ (k : ℕ)) Finset.univ).card = n ∧
    β * ω ^ (n - 1) ∉ (Finset.image (fun k : Fin n => β * ω ^ (k : ℕ))
        Finset.univ).erase (β * ω ^ (n - 1)) := by
  refine ⟨?_, Finset.notMem_erase _ _⟩
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

end Rev4

section Audit
#print axioms Rev4.d_bounds_only_the_symbolic_degree
#print axioms Rev4.composed_degree_unbounded_by_d
#print axioms Rev4.point_variable_must_be_a_pinned_column
#print axioms Rev4.prover_defeats_the_point_variable
#print axioms Rev4.omega_one_degenerates_transition
#print axioms Rev4.orbit_gives_adjacency
#print axioms Rev4.prefix_domain_excludes_wrap
end Audit
