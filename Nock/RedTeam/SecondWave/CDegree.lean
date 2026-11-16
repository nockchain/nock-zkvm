import Nock.Framework
import Nock.Counts

namespace Attack

open Nock Nock.Framework Nock.Framework.Reify Nock.Reified
open scoped Polynomial

open Classical

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## C1.  Gating a `.boundary` constraint ON at a single point of `H` costs degree `|H| − 1`
     in the evaluation variable, not `1`.

  `RAP.Satisfies` is "vanishes on ALL of `H`".  So a boundary gate that is genuinely enforced only
  at `x₀` must have a composed polynomial that vanishes on `H ∖ {x₀}` and is nonzero at `x₀`
  (otherwise it is enforced nowhere).  Any such polynomial has degree `≥ |H| − 1`. -/

theorem single_point_gate_degree_lb (H : Finset F) (x₀ : F) (hx₀ : x₀ ∈ H) (g : F[X])
    (hvanish : ∀ x ∈ H.erase x₀, g.eval x = 0) (hactive : g.eval x₀ ≠ 0) :
    H.card - 1 ≤ g.natDegree := by
  by_contra hlt
  push_neg at hlt
  have hcard : g.natDegree < (H.erase x₀).card := by
    rwa [Finset.card_erase_of_mem hx₀]
  have : g = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g (H.erase x₀) hvanish hcard
  exact hactive (by rw [this]; simp)

/-! ## C2.  `airToRAP`'s `d` is `sup totalDegree` over `F`, which is NOT `AIR.maxDegree`.

  `Counts.lean` proves facts about `AIR.maxDegree` (the syntactic `Expr.degree`).  The `RAP.d`
  field is `Finset.univ.sup (fun i => (airC air chalVal pubVal i).totalDegree)` — a different,
  field-dependent, noncomputable quantity.  Here is a witness expression where the two differ by 2,
  so no `Counts.lean` theorem constrains `d`. -/

def cancelExpr : Reified.Expr :=
  .Sub (.Mul (Reified.tc 0) (Reified.tc 0)) (.Mul (Reified.tc 0) (Reified.tc 0))

example : cancelExpr.degree = 2 := rfl

theorem cancelExpr_totalDegree_zero (chalVal pubVal : ℕ → F) :
    (exprToMv (w := 1) chalVal pubVal cancelExpr).totalDegree = 0 := by
  have h0 : exprToMv (w := 1) chalVal pubVal cancelExpr = 0 := by
    simp [exprToMv, cancelExpr, Reified.tc]
  simp [h0]

/-! ## C3.  The enabling lemma for the smallest fix (make `d` a *parameter* with a `≤` proof):
     `totalDegree (exprToMv e) ≤ e.degree` holds generically, by structural induction. -/

theorem exprToMv_totalDegree_le {w : ℕ} (chalVal pubVal : ℕ → F) (e : Reified.Expr) :
    (exprToMv (w := w) chalVal pubVal e).totalDegree ≤ e.degree := by
  induction e with
  | Var kind i =>
    cases kind
    · simp only [exprToMv, Reified.Expr.degree]
      split
      · rw [MvPolynomial.totalDegree_X]
      · simp
    · simp only [exprToMv, Reified.Expr.degree]
      split
      · rw [MvPolynomial.totalDegree_X]
      · simp
    · simp [exprToMv, Reified.Expr.degree]
    · simp [exprToMv, Reified.Expr.degree]
  | Const c =>
    simp only [exprToMv, Reified.Expr.degree, Nat.le_zero]
    exact MvPolynomial.totalDegree_C _
  | Add a b iha ihb =>
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le_max iha ihb)
  | Sub a b iha ihb =>
    refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le_max iha ihb)
  | Mul a b iha ihb =>
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add iha ihb)
  | Neg a iha => rw [exprToMv, MvPolynomial.totalDegree_neg]; exact iha
  | Pow a n iha =>
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    cases hd : a.degree with
    | zero =>
      have hz : (exprToMv chalVal pubVal a).totalDegree = 0 :=
        Nat.eq_zero_of_le_zero (by simpa [hd] using iha)
      simp [Reified.Expr.degree, Reified.Expr.powDegree, hd, hz]
    | succ d =>
      simp only [Reified.Expr.degree, Reified.Expr.powDegree.eq_def, hd]
      rw [Nat.mul_comm (d + 1) n]
      exact Nat.mul_le_mul_left n (by simpa [hd] using iha)

/-- Consequence: every `computeAIR` constraint reifies to total degree ≤ 4, for any field and any
    challenge/public valuation — the honest, provable form of the "degree 4" claim at the RAP level.
    (This is an inequality; `airToRAP` currently demands the exact `sup`.) -/
theorem computeAIR_reified_deg_le_four (chalVal pubVal : ℕ → F)
    (i : Fin Reified.computeAIR.constraints.length) :
    (airC (F := F) Reified.computeAIR chalVal pubVal i).totalDegree ≤ 4 := by
  refine le_trans (exprToMv_totalDegree_le chalVal pubVal _) ?_
  have hmem : (Reified.computeAIR.constraints.get i) ∈ Reified.computeAIR.constraints :=
    List.get_mem _ _
  -- `AIR.maxDegree` is a fold-max over the list, so every member's degree is bounded by it
  have hb : ∀ (l : List Reified.Constraint) (c : Reified.Constraint), c ∈ l →
      c.expr.degree ≤ l.foldr (fun c acc => max c.expr.degree acc) 0 := by
    intro l
    induction l with
    | nil => intro c hc; cases hc
    | cons a t ih =>
      intro c hc
      rcases List.mem_cons.mp hc with h | h
      · subst h; exact le_max_left _ _
      · exact le_trans (ih c h) (le_max_right _ _)
  have := hb Reified.computeAIR.constraints _ hmem
  rw [show Reified.computeAIR.constraints.foldr (fun c acc => max c.expr.degree acc) 0 = 4 from
    Reified.computeAIR_maxDegree] at this
  exact this

end Attack
