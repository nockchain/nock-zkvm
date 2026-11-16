/-
  ADVERSARIAL REVIEW — option C (`VarKind.point` + RAP preprocessing).

  The plan proposes, verbatim:
     add `VarKind.point` with `exprToMv (.Var.point _) := MvPolynomial.X (pointVar)`
     and `envOfTrace.point := x`, `Expr.degree (.Var.point _) := 0`
  at "~40 lines, additive to the deep embedding, no column-layout change".

  This file implements exactly that and shows what breaks.
-/
import Nock.Framework
import Nock.AIR
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

namespace AtkPoint

open Nock Nock.Framework Nock.Framework.Reify
open scoped Polynomial

/-! ## 0.  A faithful mini-copy of the deep embedding, WITH the proposed `.point` kind. -/

inductive VK | traceCur | traceNext | challenge | publicVal | point
deriving DecidableEq

inductive E
  | Var (kind : VK) (idx : ℕ)
  | Const (c : ℤ)
  | Add (a b : E) | Sub (a b : E) | Mul (a b : E) | Neg (a : E) | Pow (e : E) (n : ℕ)

structure Env' (K : Type*) where
  trace     : ℕ → K
  traceNext : ℕ → K
  chal      : ℕ → K
  pub       : ℕ → K
  point     : K                       -- the proposed new field

variable {F : Type*} [Field F]

def E.eval : E → Env' F → F
  | .Var .traceCur i,  env => env.trace i
  | .Var .traceNext i, env => env.traceNext i
  | .Var .challenge i, env => env.chal i
  | .Var .publicVal i, env => env.pub i
  | .Var .point _,     env => env.point          -- proposed
  | .Const c,          _   => (c : F)
  | .Add a b,          env => a.eval env + b.eval env
  | .Sub a b,          env => a.eval env - b.eval env
  | .Mul a b,          env => a.eval env * b.eval env
  | .Neg a,            env => - a.eval env
  | .Pow e n,          env => (e.eval env) ^ n

/-- The proposed degree assignment: `Expr.degree (.Var.point _) := 0`. -/
def E.degree : E → ℕ
  | .Var .traceCur _  => 1
  | .Var .traceNext _ => 1
  | .Var .challenge _ => 0
  | .Var .publicVal _ => 0
  | .Var .point _     => 0                        -- proposed
  | .Const _          => 0
  | .Add a b          => max a.degree b.degree
  | .Sub a b          => max a.degree b.degree
  | .Mul a b          => a.degree + b.degree
  | .Neg a            => a.degree
  | .Pow e n          => n * e.degree

/-- The proposed reification.  `pointVar : Fin w × ℕ` is forced: `RAP.C i` lives in
    `MvPolynomial (Fin w × ℕ) F`, so the ONLY variables available are column/row pairs. -/
noncomputable def exprToMv' {w : ℕ} (chalVal pubVal : ℕ → F) (pointVar : Fin w × ℕ) :
    E → MvPolynomial (Fin w × ℕ) F
  | .Var .traceCur i  => if h : i < w then MvPolynomial.X (⟨i, h⟩, 0) else 0
  | .Var .traceNext i => if h : i < w then MvPolynomial.X (⟨i, h⟩, 1) else 0
  | .Var .challenge i => MvPolynomial.C (chalVal i)
  | .Var .publicVal i => MvPolynomial.C (pubVal i)
  | .Var .point _     => MvPolynomial.X pointVar          -- proposed
  | .Const c          => MvPolynomial.C (c : F)
  | .Add a b          => exprToMv' chalVal pubVal pointVar a + exprToMv' chalVal pubVal pointVar b
  | .Sub a b          => exprToMv' chalVal pubVal pointVar a - exprToMv' chalVal pubVal pointVar b
  | .Mul a b          => exprToMv' chalVal pubVal pointVar a * exprToMv' chalVal pubVal pointVar b
  | .Neg a            => - exprToMv' chalVal pubVal pointVar a
  | .Pow e n          => (exprToMv' chalVal pubVal pointVar e) ^ n

/-- The proposed environment: `envOfTrace.point := x`. -/
noncomputable def envOfTrace' {w : ℕ} (P : Fin w → F[X]) (ω x : F) (chalVal pubVal : ℕ → F) :
    Env' F where
  trace     := fun i => if h : i < w then (P ⟨i, h⟩).eval x else 0
  traceNext := fun i => if h : i < w then (P ⟨i, h⟩).eval (ω * x) else 0
  chal      := chalVal
  pub       := pubVal
  point     := x                                            -- proposed

/-! ## 1.  BLOCKING: the faithfulness lemma `eval_exprToMv` becomes FALSE.

  `eval_exprToMv` (`NockInstances.lean:209`) is the crux of the whole AIR→RAP bridge and is
  currently UNCONDITIONAL.  With `.point` it fails for the free trace: the substitution rule
  `Y_{i,j} ↦ P_i(ω^j·X)` sends `pointVar` to `(P pointVar.1).eval (ω^pointVar.2 · x)`, which has
  nothing to do with `x`. -/

theorem eval_exprToMv'_FAILS :
    ∃ (w : ℕ) (P : Fin w → ℚ[X]) (ω x : ℚ) (chalVal pubVal : ℕ → ℚ) (pointVar : Fin w × ℕ)
      (e : E),
      MvPolynomial.eval (fun q : Fin w × ℕ => (P q.1).eval (ω ^ (q.2 : ℕ) * x))
          (exprToMv' chalVal pubVal pointVar e)
        ≠ e.eval (envOfTrace' P ω x chalVal pubVal) := by
  refine ⟨1, (fun _ => 0), 1, 1, (fun _ => 0), (fun _ => 0), (⟨0, by norm_num⟩, 0),
    E.Var .point 0, ?_⟩
  simp [exprToMv', E.eval, envOfTrace']

/-- The prover, who chooses `P`, can always defeat it.
    So the "point variable" is a *point* only if a column is preprocessed — i.e. exactly the
    column-layout change option C claims not to need. -/
theorem point_forces_a_pinned_column
    {w : ℕ} (P : Fin w → F[X]) (ω x : F) (chalVal pubVal : ℕ → F) (pointVar : Fin w × ℕ)
    (h : MvPolynomial.eval (fun q : Fin w × ℕ => (P q.1).eval (ω ^ (q.2 : ℕ) * x))
            (exprToMv' chalVal pubVal pointVar (E.Var .point 0))
          = (E.Var .point 0).eval (envOfTrace' P ω x chalVal pubVal)) :
    (P pointVar.1).eval (ω ^ (pointVar.2 : ℕ) * x) = x := by
  simpa [exprToMv', E.eval, envOfTrace'] using h

/-! ## 2. -/

theorem exprToMv'_totalDegree_le_FAILS :
    ∃ (w : ℕ) (chalVal pubVal : ℕ → ℚ) (pointVar : Fin w × ℕ) (e : E),
      ¬ ((exprToMv' (w := w) chalVal pubVal pointVar e).totalDegree ≤ e.degree) := by
  refine ⟨1, (fun _ => 0), (fun _ => 0), (⟨0, by norm_num⟩, 0), E.Var .point 0, ?_⟩
  simp [exprToMv', E.degree, MvPolynomial.totalDegree_X]

/-- The only repair is `E.degree (.Var.point _) := 1`. -/
def gated (c : E) : E := E.Mul (E.Sub (E.Var .point 0) (E.Const 1)) c

theorem gating_costs_one_degree_if_point_is_degree_one
    (deg1 : E → ℕ) (hpt : deg1 (E.Var .point 0) = 1)
    (hconst : deg1 (E.Const 1) = 0)
    (hsub : ∀ a b, deg1 (E.Sub a b) = max (deg1 a) (deg1 b))
    (hmul : ∀ a b, deg1 (E.Mul a b) = deg1 a + deg1 b) (c : E) :
    deg1 (gated c) = deg1 c + 1 := by
  simp [gated, hmul, hsub, hpt, hconst, Nat.add_comm]

/-! ## 3.  The plan's A2-reason-1 ("its constant is unnameable") is refuted: `.challenge` is an
    arbitrary field-element slot and `chalVal` is a free `ℕ → F` parameter of `airToRAP`. -/

theorem challenge_names_an_arbitrary_field_element (c : F) (j : ℕ)
    (chalVal : ℕ → F) (hc : chalVal j = c) (pubVal : ℕ → F) {w : ℕ} :
    exprToMv (w := w) chalVal pubVal (Reified.Expr.Var .challenge j) = MvPolynomial.C c := by
  simp [exprToMv, hc]

/-! ## 4.  A preprocessed selector column raises the RAP's `d` (`sup totalDegree`) by one. -/

theorem selector_raises_totalDegree (v : Fin 2 × ℕ) (q : MvPolynomial (Fin 2 × ℕ) ℚ)
    (hq : q ≠ 0) : (MvPolynomial.X v * q).totalDegree = q.totalDegree + 1 := by
  rw [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero v) hq,
    MvPolynomial.totalDegree_X]
  omega

end AtkPoint

section Audit
#print axioms AtkPoint.eval_exprToMv'_FAILS
#print axioms AtkPoint.point_forces_a_pinned_column
#print axioms AtkPoint.exprToMv'_totalDegree_le_FAILS
#print axioms AtkPoint.gating_costs_one_degree_if_point_is_degree_one
#print axioms AtkPoint.challenge_names_an_arbitrary_field_element
#print axioms AtkPoint.selector_raises_totalDegree
end Audit
