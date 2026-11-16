import Nock.NockVMROM.Thm54.ExprSubstitution

/-! The predicate `traceOnly` for expressions reading only current-row trace columns, and the lemma that such an expression evaluates identically in any two environments with the same trace. -/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.FamilyChipTwins

open Nock Nock.Reified

/-- An expression that reads only current-row trace columns. -/
def traceOnly : Expr → Bool
  | .Var .traceCur _ => true
  | .Var _ _ => false
  | .Const _ => true
  | .Add a b => traceOnly a && traceOnly b
  | .Sub a b => traceOnly a && traceOnly b
  | .Mul a b => traceOnly a && traceOnly b
  | .Neg a => traceOnly a
  | .Pow a _ => traceOnly a

theorem eval_congr_of_traceOnly {K : Type} [Field K] (e : Expr) {E E' : Env K}
    (ht : E.trace = E'.trace) (he : traceOnly e = true) : e.eval E = e.eval E' := by
  induction e with
  | Var kind i =>
      cases kind
      · simp only [Expr.eval, ht]
      all_goals simp [traceOnly] at he
  | Const c => rfl
  | Add a b iha ihb =>
      simp only [traceOnly, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1, ihb he.2]
  | Sub a b iha ihb =>
      simp only [traceOnly, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1, ihb he.2]
  | Mul a b iha ihb =>
      simp only [traceOnly, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1, ihb he.2]
  | Neg a ih =>
      simp only [traceOnly] at he
      simp only [Expr.eval, ih he]
  | Pow a n ih =>
      simp only [traceOnly] at he
      simp only [Expr.eval, ih he]

end Nock.NockVMROM.Thm54.FamilyChipTwins
