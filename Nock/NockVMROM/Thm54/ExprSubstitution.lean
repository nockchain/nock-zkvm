import Nock.NockVMROM.Thm54.ExprReindex

/-!
# Symbolic expression substitution

Unlike `Expr.mapVars`, substitution maps each source variable to an arbitrary target expression.
This is required by the record-free optimized compute codec: erased memory-record columns are
replaced by their decoder equations rather than by target-column projections.
-/

namespace Nock.Reified

open Classical

/-- Simultaneous, capture-free substitution of every AIR variable by a symbolic expression. -/
def Expr.subst (σ : VarKind → ℕ → Expr) : Expr → Expr
  | .Var k i => σ k i
  | .Const c => .Const c
  | .Add a b => .Add (a.subst σ) (b.subst σ)
  | .Sub a b => .Sub (a.subst σ) (b.subst σ)
  | .Mul a b => .Mul (a.subst σ) (b.subst σ)
  | .Neg a => .Neg (a.subst σ)
  | .Pow a n => .Pow (a.subst σ) n

/-- Variables occurring in an expression. -/
def Expr.vars : Expr → Finset (VarKind × ℕ)
  | .Var k i => {(k, i)}
  | .Const _ => ∅
  | .Add a b | .Sub a b | .Mul a b => a.vars ∪ b.vars
  | .Neg a | .Pow a _ => a.vars

/-- The target-variable support reachable through one substitution. -/
def Expr.substSupport (σ : VarKind → ℕ → Expr) (e : Expr) :
    Finset (VarKind × ℕ) :=
  e.vars.biUnion fun x => (σ x.1 x.2).vars

/-- Evaluate source variables through the target environment. -/
def Env.ofSubst {K : Type*} [Field K]
    (σ : VarKind → ℕ → Expr) (env : Env K) : Env K where
  trace i := (σ .traceCur i).eval env
  traceNext i := (σ .traceNext i).eval env
  chal i := (σ .challenge i).eval env
  pub i := (σ .publicVal i).eval env

/-- Evaluation commutes with arbitrary symbolic substitution. -/
theorem Expr.eval_subst {K : Type*} [Field K]
    (σ : VarKind → ℕ → Expr) :
    ∀ (e : Expr) (env : Env K), (Expr.subst σ e).eval env = e.eval (Env.ofSubst σ env)
  | .Var k i, env => by cases k <;> rfl
  | .Const _, _ => rfl
  | .Add a b, env => by simp [Expr.subst, Expr.eval, eval_subst σ a, eval_subst σ b]
  | .Sub a b, env => by simp [Expr.subst, Expr.eval, eval_subst σ a, eval_subst σ b]
  | .Mul a b, env => by simp [Expr.subst, Expr.eval, eval_subst σ a, eval_subst σ b]
  | .Neg a, env => by simp [Expr.subst, Expr.eval, eval_subst σ a]
  | .Pow a n, env => by simp [Expr.subst, Expr.eval, eval_subst σ a]

/-- Substitution introduces no variables outside the union of the replacement supports. -/
theorem Expr.vars_subst_subset (σ : VarKind → ℕ → Expr) :
    ∀ e : Expr, (Expr.subst σ e).vars ⊆ e.substSupport σ
  | .Var k i => by simp [Expr.subst, Expr.vars, Expr.substSupport]
  | .Const _ => by simp [Expr.subst, Expr.vars, Expr.substSupport]
  | .Add a b => by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨y, hya, hyx⟩ := Finset.mem_biUnion.mp (vars_subst_subset σ a hx)
        exact Finset.mem_biUnion.mpr ⟨y, by simp [Expr.vars, hya], hyx⟩
      · obtain ⟨y, hyb, hyx⟩ := Finset.mem_biUnion.mp (vars_subst_subset σ b hx)
        exact Finset.mem_biUnion.mpr ⟨y, by simp [Expr.vars, hyb], hyx⟩
  | .Sub a b => by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨y, hya, hyx⟩ := Finset.mem_biUnion.mp (vars_subst_subset σ a hx)
        exact Finset.mem_biUnion.mpr ⟨y, by simp [Expr.vars, hya], hyx⟩
      · obtain ⟨y, hyb, hyx⟩ := Finset.mem_biUnion.mp (vars_subst_subset σ b hx)
        exact Finset.mem_biUnion.mpr ⟨y, by simp [Expr.vars, hyb], hyx⟩
  | .Mul a b => by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨y, hya, hyx⟩ := Finset.mem_biUnion.mp (vars_subst_subset σ a hx)
        exact Finset.mem_biUnion.mpr ⟨y, by simp [Expr.vars, hya], hyx⟩
      · obtain ⟨y, hyb, hyx⟩ := Finset.mem_biUnion.mp (vars_subst_subset σ b hx)
        exact Finset.mem_biUnion.mpr ⟨y, by simp [Expr.vars, hyb], hyx⟩
  | .Neg a => vars_subst_subset σ a
  | .Pow a _ => vars_subst_subset σ a

/-- Degree discipline for a substitution: source trace variables may become degree-`d`
expressions, while challenges and public values remain trace-degree zero. -/
def Expr.SubstDegreeLE (σ : VarKind → ℕ → Expr) (d : ℕ) : Prop :=
  (∀ i, (σ .traceCur i).degree ≤ d) ∧
  (∀ i, (σ .traceNext i).degree ≤ d) ∧
  (∀ i, (σ .challenge i).degree = 0) ∧
  (∀ i, (σ .publicVal i).degree = 0)

/-- A degree-respecting substitution multiplies the source trace degree by at most `d`. -/
theorem Expr.degree_subst_le (σ : VarKind → ℕ → Expr) (d : ℕ)
    (hσ : SubstDegreeLE σ d) :
    ∀ e : Expr, (Expr.subst σ e).degree ≤ e.degree * d
  | .Var .traceCur i => by simpa [Expr.subst, Expr.degree] using hσ.1 i
  | .Var .traceNext i => by simpa [Expr.subst, Expr.degree] using hσ.2.1 i
  | .Var .challenge i => by simp [Expr.subst, Expr.degree, hσ.2.2.1 i]
  | .Var .publicVal i => by simp [Expr.subst, Expr.degree, hσ.2.2.2 i]
  | .Const _ => by simp [Expr.subst, Expr.degree]
  | .Add a b => by
      simp only [Expr.subst, Expr.degree]
      exact max_le
        ((degree_subst_le σ d hσ a).trans (Nat.mul_le_mul_right d (Nat.le_max_left _ _)))
        ((degree_subst_le σ d hσ b).trans (Nat.mul_le_mul_right d (Nat.le_max_right _ _)))
  | .Sub a b => by
      simp only [Expr.subst, Expr.degree]
      exact max_le
        ((degree_subst_le σ d hσ a).trans (Nat.mul_le_mul_right d (Nat.le_max_left _ _)))
        ((degree_subst_le σ d hσ b).trans (Nat.mul_le_mul_right d (Nat.le_max_right _ _)))
  | .Mul a b => by
      simp only [Expr.subst, Expr.degree, Nat.add_mul]
      exact Nat.add_le_add (degree_subst_le σ d hσ a) (degree_subst_le σ d hσ b)
  | .Neg a => by simpa [Expr.subst, Expr.degree] using degree_subst_le σ d hσ a
  | .Pow a n => by
      simp only [Expr.subst, Expr.degree]
      have h := degree_subst_le σ d hσ a
      cases hsub : (Expr.subst σ a).degree with
      | zero =>
        simp only [Expr.powDegree, hsub]
        exact Nat.zero_le _
      | succ k =>
        cases hbase : a.degree with
        | zero =>
          have : k + 1 ≤ 0 := by simpa [hsub, hbase] using h
          omega
        | succ m =>
          simp only [Expr.powDegree, hsub, hbase]
          have h' : k + 1 ≤ (m + 1) * d := by simpa [hsub, hbase] using h
          calc
            (k + 1) * n = n * (k + 1) := Nat.mul_comm _ _
            _ ≤ n * ((m + 1) * d) := Nat.mul_le_mul_left _ h'
            _ = (m + 1) * n * d := by ac_rfl

/-- Ordinary renaming is the projection-only special case of substitution. -/
theorem Expr.subst_vars_eq_mapVars (g : VarKind → ℕ → ℕ) :
    ∀ e : Expr, Expr.subst (fun k i => .Var k (g k i)) e = e.mapVars g
  | .Var _ _ | .Const _ => rfl
  | .Add a b => by simp [Expr.subst, Expr.mapVars, subst_vars_eq_mapVars g a,
      subst_vars_eq_mapVars g b]
  | .Sub a b => by simp [Expr.subst, Expr.mapVars, subst_vars_eq_mapVars g a,
      subst_vars_eq_mapVars g b]
  | .Mul a b => by simp [Expr.subst, Expr.mapVars, subst_vars_eq_mapVars g a,
      subst_vars_eq_mapVars g b]
  | .Neg a => by simp [Expr.subst, Expr.mapVars, subst_vars_eq_mapVars g a]
  | .Pow a n => by simp [Expr.subst, Expr.mapVars, subst_vars_eq_mapVars g a]

end Nock.Reified

#print axioms Nock.Reified.Expr.eval_subst
#print axioms Nock.Reified.Expr.vars_subst_subset
#print axioms Nock.Reified.Expr.degree_subst_le
#print axioms Nock.Reified.Expr.subst_vars_eq_mapVars
