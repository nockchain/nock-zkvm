/-
  ADVERSARIAL SCRATCH A — can a point-dependent selector exist at all?
-/
import Nock.Framework
import Nock.AIR

namespace Attack

open Nock Nock.Framework Nock.Framework.Reify
open scoped Polynomial

variable {F : Type*} [Field F]

/-! ## A1.  `airToRAP` RAPs are **point-blind**: the composed constraint at `x` is a function of
     the row values only.  For a constant trace it is literally independent of `x`. -/

theorem composed_const_trace_indep_of_point
    (air : Reified.AIR) (chalVal pubVal : ℕ → F) (v : Fin air.numTraceCols → F)
    (eDeg hExp : ℕ) (ω β : F) (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp)
    (i : Fin (airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).s) (x y : F) :
    ((airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).compose
        (fun j => Polynomial.C (v j)) i).eval x
      = ((airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).compose
        (fun j => Polynomial.C (v j)) i).eval y := by
  rw [compose_eval, compose_eval]
  simp

/-- **No wrap-exclusion is expressible.**  For *any* reified AIR and *any* constant trace, if some
    constraint is violated at one point of `H` it is violated at *every* point of `H`.  So the
    "gate the `.transition` off at the last row" behaviour that A2 needs cannot be obtained by
    changing the constraint list alone: the composed polynomial has no access to the evaluation
    point.  (Contrapositive form: satisfied at one point ⇒ satisfied everywhere.) -/
theorem no_point_selector_on_constant_traces
    (air : Reified.AIR) (chalVal pubVal : ℕ → F) (v : Fin air.numTraceCols → F)
    (eDeg hExp : ℕ) (ω β : F) (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp)
    (x₀ : F) (hx₀ : x₀ ∈ H)
    (h : ∀ i : Fin (airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).s,
        ((airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).compose
          (fun j => Polynomial.C (v j)) i).eval x₀ = 0) :
    (airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).Satisfies
      (fun j => Polynomial.C (v j)) := by
  intro i x _
  rw [composed_const_trace_indep_of_point air chalVal pubVal v eDeg hExp ω β H hβ hh1 i x x₀]
  exact h i

/-! ## A2.  The only field constants an `Expr` can name are integer casts. -/

/-- `Reified.Expr.Const` carries an `ℤ`.  Every constant an AIR can name is therefore in the image
    of `Int.cast`, i.e. in the prime subfield.  A selector constant `traceStep^(2^h−1)` (a
    primitive `2^h`-th root of unity) is *not* nameable this way in general. -/
example (c : ℤ) (env : Reified.Env F) : (Reified.Expr.Const c).eval env = (c : F) := rfl

/-! ## A3.  Out-of-range column indices reify to `0` — a "clock column" cannot be smuggled in
     without changing `numTraceCols`. -/

theorem exprToMv_out_of_range {w : ℕ} (chalVal pubVal : ℕ → F) (i : ℕ) (hi : ¬ i < w) :
    exprToMv (w := w) chalVal pubVal (Reified.tc i) = 0 := by
  simp [exprToMv, Reified.tc, hi]

/-- Concretely: writing the clock as column 94 of `computeAIR` (which has `numTraceCols = 94`)
    reifies to the *zero* polynomial, so the "selector" `clk − s` becomes the nonzero constant
    `−s` and the gated constraint is unsatisfiable rather than gated. -/
theorem clock_col_94_reifies_to_zero (chalVal pubVal : ℕ → F) :
    exprToMv (w := Reified.computeAIR.numTraceCols) chalVal pubVal (Reified.tc 94) = 0 := by
  simp only [exprToMv, Reified.tc, Reified.computeAIR, dif_neg (by decide : ¬ (94 < 94))]
  rfl

/-- …and on the deep-embedding side too: `computeEnvFull` reads column 94 as `0`. -/
theorem computeEnvFull_col94 (inp : Nock.ComputeTable.Inputs F)
    (op : Nock.ComputeTable.State → F) (pub : Nock.ComputeTable.Pub F)
    (dec : Nock.ComputeTable.Dec F) (ex : Nock.ComputeTable.Extra F) :
    (Reified.computeEnvFull inp op pub dec ex).trace 94 = 0 := rfl

end Attack
