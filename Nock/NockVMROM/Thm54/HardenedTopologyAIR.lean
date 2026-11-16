import Nock.AIR

/-!
# Hardened topology selectors — the paper's sum-to-one constraint (Track E)

The quarantined generic topology AIRs (`RawTopologyAIR.computeAIR` / `memoryAIR`) accept an
all-zero trace: `allZero_generic_satisfies` compiles that forgery. The structural reason is that
they carry no *non-triviality* constraint. Every gated payload constraint is of the form
`active · (…)`, so setting every selector to `0` discharges them, and the bare fanout difference
`vcur 0 − vcur 1` is `0 − 0 = 0` on the all-zero trace.

The paper closes exactly this hole with a **sum-to-one** state-selector constraint
(`op₁₁ + Σⱼ opⱼ = 1` at `the paper`, `Σⱼ st(i,j) = 1` at `the paper`), together
with per-selector booleanity. This module compiles that mechanism as an additive, kernel-clean AIR
and proves the two facts that matter:

1. **The all-zero trace is rejected** by any AIR carrying a sum-to-one constraint over `n ≥ 1`
   selectors (`hardenedSelector_rejects_allZero`). This is precisely the forgery the generic
   topology AIR admits — the sum-to-one gate turns `0 = 1` into a contradiction.
2. **A genuine one-hot trace is accepted** (`hardenedSelector_oneHot_sat`), so the hardening is not
   vacuous; it rejects only the degenerate assignment.

Scope, stated honestly: sum-to-one kills the specific *all-zero* attack. It does **not** by itself
make an arbitrary prover-supplied topology trace fully sound, because it forces *some* state to be
selected, not the *correct* one for the committed BFS node. Binding the selected state to the real
node is the cross-table obligation handled by the walk multiset accumulator (`walkAIR`, Track E's
second half); until that binding is in place the production path keeps the verifier-generated trace.
The `maxDegree` of the added constraints is `2`, matching the existing topology AIR, so the
hardening does not raise the degree.
-/

namespace Nock.NockVMROM.Thm54.HardenedTopologyAIR

open Nock Nock.Reified

/-- The `j`-th state-selector column, read from the current row. -/
def stVar (j : ℕ) : Expr := .Var .traceCur j

/-- Per-selector booleanity gate `stⱼ · (1 − stⱼ) = 0` (paper booleanity of the state selectors). -/
def selectorBoolExpr (j : ℕ) : Expr := .Mul (stVar j) (.Sub (.Const 1) (stVar j))

/-- The symbolic sum `Σ_{j < n} stⱼ`. -/
def sumSelectorsExpr (n : ℕ) : Expr :=
  (List.range n).foldr (fun j acc => .Add (stVar j) acc) (.Const 0)

/-- The paper's sum-to-one gate `(Σ_{j<n} stⱼ) − 1 = 0`. -/
def sumToOneExpr (n : ℕ) : Expr := .Sub (sumSelectorsExpr n) (.Const 1)

/-- Booleanity of every selector plus one sum-to-one gate. -/
def hardenedSelectorConstraints (n : ℕ) : List Constraint :=
  ((List.range n).map fun j => (⟨.row, selectorBoolExpr j⟩ : Constraint)) ++
    [⟨.row, sumToOneExpr n⟩]

/-- The additive hardening AIR: `n` selector columns, booleanity, and sum-to-one. -/
def hardenedSelectorAIR (n : ℕ) : AIR where
  numTraceCols := n
  numChallenges := 0
  numPublic := 0
  constraints := hardenedSelectorConstraints n

/-- A row assignment satisfies the AIR iff every constraint's expression vanishes on it. -/
def RowSat {K : Type*} [Field K] (air : AIR) (env : Env K) : Prop :=
  ∀ c ∈ air.constraints, c.expr.eval env = 0

section Eval

variable {K : Type*} [Field K]

@[simp] theorem stVar_eval (j : ℕ) (env : Env K) : (stVar j).eval env = env.trace j := rfl

theorem stVar_degree (j : ℕ) : (stVar j).degree = 1 := rfl

/-- The symbolic selector sum evaluates to the list-sum of the selector column values. -/
theorem sumSelectorsExpr_eval (n : ℕ) (env : Env K) :
    (sumSelectorsExpr n).eval env = ((List.range n).map fun j => env.trace j).sum := by
  unfold sumSelectorsExpr
  induction (List.range n) with
  | nil => simp [Expr.eval]
  | cons a t ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, Expr.eval, stVar_eval, ih]

/-- **The all-zero trace makes the sum-to-one gate evaluate to `-1`.** -/
theorem sumToOneExpr_eval_allZero (n : ℕ)
    (env : Env K) (hzero : ∀ j, env.trace j = 0) :
    (sumToOneExpr n).eval env = -1 := by
  unfold sumToOneExpr
  simp only [Expr.eval, sumSelectorsExpr_eval]
  have : ((List.range n).map fun j => env.trace j).sum = 0 := by
    rw [List.sum_eq_zero]
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact hzero j
  rw [this]
  simp

/-- **Forgery killed.** For `n ≥ 1`, the all-zero trace does not satisfy the hardened AIR: the
sum-to-one gate forces `-1 = 0`, impossible in a field. This is exactly the assignment that
`RawTopologyAIR.allZero_generic_satisfies` shows the *un*hardened generic topology AIR accepts. -/
theorem hardenedSelector_rejects_allZero (n : ℕ)
    (env : Env K) (hzero : ∀ j, env.trace j = 0) :
    ¬ RowSat (hardenedSelectorAIR n) env := by
  intro hsat
  have hmem : (⟨.row, sumToOneExpr n⟩ : Constraint) ∈ (hardenedSelectorAIR n).constraints := by
    simp [hardenedSelectorAIR, hardenedSelectorConstraints]
  have h0 : (sumToOneExpr n).eval env = 0 := hsat _ hmem
  rw [sumToOneExpr_eval_allZero n env hzero] at h0
  exact (neg_ne_zero.mpr (one_ne_zero (α := K))) h0

end Eval

/-! ## Non-vacuity: a genuine one-hot trace is accepted -/

/-- A concrete two-state one-hot environment: selector `0` active, selector `1` inactive. -/
def oneHotEnv (K : Type*) [Field K] : Env K where
  trace := fun j => if j = 0 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- **The hardening is not vacuous.** A genuine one-hot assignment over two selectors satisfies
both booleanity and sum-to-one. -/
theorem hardenedSelector_oneHot_sat (K : Type*) [Field K] :
    RowSat (hardenedSelectorAIR 2) (oneHotEnv K) := by
  have hr : List.range 2 = [0, 1] := by decide
  intro c hc
  simp only [hardenedSelectorAIR, hardenedSelectorConstraints, hr, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with h | h | h <;> subst h <;>
    simp [selectorBoolExpr, sumToOneExpr, sumSelectorsExpr_eval, stVar, oneHotEnv, Expr.eval, hr,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

/-- The added constraints have trace-degree at most `2` (booleanity is degree 2, sum-to-one is
degree 1), so the hardening does not raise the topology AIR's maximum degree. -/
theorem hardenedSelectorAIR_maxDegree_le (n : ℕ) :
    ∀ c ∈ (hardenedSelectorAIR n).constraints, c.degree ≤ 2 := by
  intro c hc
  simp only [hardenedSelectorAIR, hardenedSelectorConstraints, List.mem_append,
    List.mem_map, List.mem_singleton] at hc
  rcases hc with ⟨j, _, rfl⟩ | rfl
  · -- booleanity: st · (1 - st), trace-degree 1 + max 0 1 = 2
    simp only [Constraint.degree, selectorBoolExpr, stVar_degree, Expr.degree]
    omega
  · -- sum-to-one: degree 1 ≤ 2
    have hsum : (sumSelectorsExpr n).degree ≤ 1 := by
      unfold sumSelectorsExpr
      induction (List.range n) with
      | nil => simp [Expr.degree]
      | cons a t ih => simp only [List.foldr_cons, Expr.degree, stVar_degree]; omega
    simp only [Constraint.degree, sumToOneExpr, Expr.degree]
    omega

/-! ## Track E (second half): the paper's topology commitment already exists as `walkAIR`

The plan's second Track-E step proposed replacing the verifier-generated linear-work topology with
"authenticated succinct cross-table commitments". That primitive does not need inventing: the paper
specifies a **line-indexed multiset accumulator** for the topology walk, and
it is already formalized as `Nock.Reified.walkAIR` — an accumulator AIR carrying the RLC challenge
and the `walkAccStep` accumulation transition. -/

/-- `walkAIR` is the paper's line-indexed multiset accumulator: it draws one RLC challenge and its
transition constraints contain the accumulation step `walkAccStep`. -/
theorem walkAIR_is_multiset_accumulator :
    (⟨.transition, Nock.Reified.Trans.walkAccStep⟩ : Constraint) ∈
        Nock.Reified.Trans.walkAIR.constraints ∧
      Nock.Reified.Trans.walkAIR.numChallenges = 1 ∧
      Nock.Reified.Trans.walkAIR.constraints.length = 7 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [Nock.Reified.Trans.walkAIR]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

end Nock.NockVMROM.Thm54.HardenedTopologyAIR

#print axioms Nock.NockVMROM.Thm54.HardenedTopologyAIR.sumToOneExpr_eval_allZero
#print axioms Nock.NockVMROM.Thm54.HardenedTopologyAIR.walkAIR_is_multiset_accumulator
#print axioms Nock.NockVMROM.Thm54.HardenedTopologyAIR.hardenedSelector_rejects_allZero
#print axioms Nock.NockVMROM.Thm54.HardenedTopologyAIR.hardenedSelector_oneHot_sat
#print axioms Nock.NockVMROM.Thm54.HardenedTopologyAIR.hardenedSelectorAIR_maxDegree_le
