import Nock.AIR

/-!
# Expr reindexer with evaluation commutation (Track C infrastructure)

Composing the segmented table / walk / IO AIRs into the paper's two monolithic RAPs requires
re-indexing constraint columns onto a shared column space. No generic `Expr` renaming existed. This
module supplies one: `Expr.mapVars` renames every variable index by a per-`VarKind` function, and
`Expr.eval_mapVars` proves evaluation commutes with the corresponding environment remap. The
special case `Expr.shiftTrace off` shifts trace-column indices by a constant offset — exactly the
operation a disjoint-column composition needs — with its own commutation corollary.

This is the reindexing half of the Track C infrastructure. It does not build the monolithic RAP
(the IO-field mismatch and row-domain reconciliation remain; see the census), but it removes the
"no `Expr` reindexer exists" blocker and is proved kernel-clean.
-/

namespace Nock.Reified

/-- Remap an environment's variable indices per `VarKind`. -/
def Env.remap {K : Type*} (g : VarKind → ℕ → ℕ) (env : Env K) : Env K where
  trace := fun i => env.trace (g .traceCur i)
  traceNext := fun i => env.traceNext (g .traceNext i)
  chal := fun i => env.chal (g .challenge i)
  pub := fun i => env.pub (g .publicVal i)

/-- Rename every variable index in an expression by a per-`VarKind` function. -/
def Expr.mapVars (g : VarKind → ℕ → ℕ) : Expr → Expr
  | .Var k i => .Var k (g k i)
  | .Const c => .Const c
  | .Add a b => .Add (a.mapVars g) (b.mapVars g)
  | .Sub a b => .Sub (a.mapVars g) (b.mapVars g)
  | .Mul a b => .Mul (a.mapVars g) (b.mapVars g)
  | .Neg a => .Neg (a.mapVars g)
  | .Pow a n => .Pow (a.mapVars g) n

/-- **Evaluation commutes with reindexing.** Evaluating a reindexed expression equals evaluating the
original expression under the remapped environment. -/
theorem Expr.eval_mapVars {K : Type*} [Field K] (g : VarKind → ℕ → ℕ) :
    ∀ (e : Expr) (env : Env K), (e.mapVars g).eval env = e.eval (env.remap g)
  | .Var k i, env => by cases k <;> rfl
  | .Const c, _ => rfl
  | .Add a b, env => by
      simp only [Expr.mapVars, Expr.eval, Expr.eval_mapVars g a, Expr.eval_mapVars g b]
  | .Sub a b, env => by
      simp only [Expr.mapVars, Expr.eval, Expr.eval_mapVars g a, Expr.eval_mapVars g b]
  | .Mul a b, env => by
      simp only [Expr.mapVars, Expr.eval, Expr.eval_mapVars g a, Expr.eval_mapVars g b]
  | .Neg a, env => by
      simp only [Expr.mapVars, Expr.eval, Expr.eval_mapVars g a]
  | .Pow a n, env => by
      simp only [Expr.mapVars, Expr.eval, Expr.eval_mapVars g a]

/-- Reindexing preserves trace-degree: variable indices change but the `VarKind` (hence degree
contribution) does not. -/
theorem Expr.degree_mapVars (g : VarKind → ℕ → ℕ) :
    ∀ e : Expr, (e.mapVars g).degree = e.degree
  | .Var k _ => by cases k <;> rfl
  | .Const _ => rfl
  | .Add a b => by simp only [Expr.mapVars, Expr.degree, Expr.degree_mapVars g a,
      Expr.degree_mapVars g b]
  | .Sub a b => by simp only [Expr.mapVars, Expr.degree, Expr.degree_mapVars g a,
      Expr.degree_mapVars g b]
  | .Mul a b => by simp only [Expr.mapVars, Expr.degree, Expr.degree_mapVars g a,
      Expr.degree_mapVars g b]
  | .Neg a => by simp only [Expr.mapVars, Expr.degree, Expr.degree_mapVars g a]
  | .Pow a n => by simp only [Expr.mapVars, Expr.degree, Expr.degree_mapVars g a]

/-- Shift only the trace-column indices (current and next) by a constant offset; challenges and
public values are untouched. This is the disjoint-composition reindexing operation. -/
def Expr.shiftTrace (off : ℕ) : Expr → Expr :=
  Expr.mapVars fun k i =>
    match k with
    | .traceCur => i + off
    | .traceNext => i + off
    | _ => i

/-- Evaluating a trace-shifted expression equals evaluating the original under an environment whose
trace columns are read at the shifted index. -/
theorem Expr.eval_shiftTrace {K : Type*} [Field K] (off : ℕ) (e : Expr) (env : Env K) :
    (e.shiftTrace off).eval env =
      e.eval { env with
        trace := fun i => env.trace (i + off)
        traceNext := fun i => env.traceNext (i + off) } := by
  rw [Expr.shiftTrace, Expr.eval_mapVars]
  rfl

/-- Trace shifting preserves degree. -/
theorem Expr.degree_shiftTrace (off : ℕ) (e : Expr) :
    (e.shiftTrace off).degree = e.degree :=
  Expr.degree_mapVars _ e

end Nock.Reified

#print axioms Nock.Reified.Expr.eval_mapVars
#print axioms Nock.Reified.Expr.degree_mapVars
#print axioms Nock.Reified.Expr.eval_shiftTrace
#print axioms Nock.Reified.Expr.degree_shiftTrace
