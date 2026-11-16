import Nock.AIR
import Nock.Counts
import Nock.Framework
import Mathlib.LinearAlgebra.Lagrange

/-!
# S2 TraceEncoding — foundation: row-local constraints ignore the next row

The row-local AIRs `computeAIR` / `(memoryAIR (K := K))` contain no `traceNext` reads (the single cross-row
transition gate lives in `computeAIRchained`/`memoryAIRchained`).  So evaluating a row constraint
depends only on `trace`/`chal`/`pub`, never `traceNext`.  This is the lever that lets an
interpolated trace's `envOfTrace` (whose `traceNext` reads the *next* row) agree with the per-row
`computeEnvFull` (whose `traceNext` is `0`): the row constraints can't tell the difference.

`Expr.noTraceNext` + `Expr.eval_eq_of_noTraceNext` provide the generic independence lemma;
`computeAIR_noTraceNext` / `memoryAIR_noTraceNext` discharge it for the two reified AIRs by kernel
reduction.
-/

namespace Nock.Reified

set_option maxRecDepth 40000

/-- `true` iff the expression contains no `traceNext` (next-row) variable. -/
def Expr.noTraceNext : Expr → Bool
  | .Var .traceNext _ => false
  | .Var _ _ => true
  | .Const _ => true
  | .Add a b => a.noTraceNext && b.noTraceNext
  | .Sub a b => a.noTraceNext && b.noTraceNext
  | .Mul a b => a.noTraceNext && b.noTraceNext
  | .Neg a => a.noTraceNext
  | .Pow e _ => e.noTraceNext

/-- **A `traceNext`-free expression's evaluation is independent of `env.traceNext`.**  If two
    environments agree on `trace`, `chal`, and `pub`, a `noTraceNext` expression evaluates equally. -/
theorem Expr.eval_eq_of_noTraceNext {K : Type*} [Field K] :
    ∀ {e : Expr}, e.noTraceNext = true → ∀ {env1 env2 : Env K},
      (∀ i, env1.trace i = env2.trace i) → (∀ i, env1.chal i = env2.chal i) →
      (∀ i, env1.pub i = env2.pub i) → e.eval env1 = e.eval env2 := by
  intro e
  induction e with
  | Var kind idx =>
      intro he env1 env2 ht hc hp
      cases kind with
      | traceCur => simpa only [Expr.eval] using ht idx
      | traceNext => simp [Expr.noTraceNext] at he
      | challenge => simpa only [Expr.eval] using hc idx
      | publicVal => simpa only [Expr.eval] using hp idx
  | Const c => intro _ _ _ _ _ _; rfl
  | Add a b iha ihb =>
      intro he env1 env2 ht hc hp
      simp only [Expr.noTraceNext, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc hp, ihb he.2 ht hc hp]
  | Sub a b iha ihb =>
      intro he env1 env2 ht hc hp
      simp only [Expr.noTraceNext, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc hp, ihb he.2 ht hc hp]
  | Mul a b iha ihb =>
      intro he env1 env2 ht hc hp
      simp only [Expr.noTraceNext, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc hp, ihb he.2 ht hc hp]
  | Neg a iha =>
      intro he env1 env2 ht hc hp
      simp only [Expr.eval, iha he ht hc hp]
  | Pow a n iha =>
      intro he env1 env2 ht hc hp
      simp only [Expr.eval, iha he ht hc hp]

/-- **`computeAIR` is row-local: no constraint reads the next row.** (Kernel reduction over the 526
    reified constraints.) -/
theorem computeAIR_noTraceNext :
    computeAIR.constraints.all (fun c => c.expr.noTraceNext) = true := by rfl

section MemTraceLocal
variable {K : Type*} [Field K]

/-- **`(memoryAIR (K := K))` is row-local: no constraint reads the next row.** -/
theorem memoryAIR_noTraceNext :
    (memoryAIR (K := K)).constraints.all (fun c => c.expr.noTraceNext) = true := by rfl

/-- `true` iff the expression is `traceNext`-free AND every current-row (`traceCur`) index is `< n`
    (so its evaluation depends only on `trace` below `n`, plus `chal`/`pub`). -/
def Expr.wellScoped (n : ℕ) : Expr → Bool
  | .Var .traceCur i => decide (i < n)
  | .Var .traceNext _ => false
  | .Var _ _ => true
  | .Const _ => true
  | .Add a b => a.wellScoped n && b.wellScoped n
  | .Sub a b => a.wellScoped n && b.wellScoped n
  | .Mul a b => a.wellScoped n && b.wellScoped n
  | .Neg a => a.wellScoped n
  | .Pow e _ => e.wellScoped n

/-- **A `wellScoped n` expression's eval depends only on `trace` below `n` (plus `chal`/`pub`).** -/
theorem Expr.eval_eq_of_wellScoped {K : Type*} [Field K] {n : ℕ} :
    ∀ {e : Expr}, e.wellScoped n = true → ∀ {env1 env2 : Env K},
      (∀ i, i < n → env1.trace i = env2.trace i) → (∀ i, env1.chal i = env2.chal i) →
      (∀ i, env1.pub i = env2.pub i) → e.eval env1 = e.eval env2 := by
  intro e
  induction e with
  | Var kind idx =>
      intro he env1 env2 ht hc hp
      cases kind with
      | traceCur =>
          simp only [Expr.wellScoped, decide_eq_true_eq] at he
          simpa only [Expr.eval] using ht idx he
      | traceNext => simp [Expr.wellScoped] at he
      | challenge => simpa only [Expr.eval] using hc idx
      | publicVal => simpa only [Expr.eval] using hp idx
  | Const c => intro _ _ _ _ _ _; rfl
  | Add a b iha ihb =>
      intro he env1 env2 ht hc hp
      simp only [Expr.wellScoped, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc hp, ihb he.2 ht hc hp]
  | Sub a b iha ihb =>
      intro he env1 env2 ht hc hp
      simp only [Expr.wellScoped, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc hp, ihb he.2 ht hc hp]
  | Mul a b iha ihb =>
      intro he env1 env2 ht hc hp
      simp only [Expr.wellScoped, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc hp, ihb he.2 ht hc hp]
  | Neg a iha =>
      intro he env1 env2 ht hc hp
      simp only [Expr.eval, iha he ht hc hp]
  | Pow a k iha =>
      intro he env1 env2 ht hc hp
      simp only [Expr.eval, iha he ht hc hp]

/-- **Every `computeAIR` constraint is `wellScoped 94`** (row-local, all 94 columns in range). -/
theorem computeAIR_wellScoped :
    computeAIR.constraints.all (fun c => c.expr.wellScoped 94) = true := by rfl

/-- **Every `(memoryAIR (K := K))` constraint is `wellScoped 35`.** -/
theorem memoryAIR_wellScoped :
    (memoryAIR (K := K)).constraints.all (fun c => c.expr.wellScoped 36) = true := by rfl

end MemTraceLocal

/-! ### Encoding-correctness spike (single row / single evaluation point)

  The **constant encoding** of a compute row `(inp, pub, dec, ex)` — column `i ↦ C (env.trace i)` —
  makes `envOfTrace` agree with the per-row `computeEnvFull` on every `computeAIR` constraint's
  evaluation, at any point `x₀` and shift `ω`.  The next-row reads of `envOfTrace` are invisible
  (row constraints are `wellScoped 94`), so no `traceNext`/boundary reasoning is needed.  This is
  the encoding-correctness lemma that the multi-row Lagrange construction generalizes. -/

open Nock.ComputeTable in
/-- **Single-row encoding correctness.**  For the constant encoding of a compute row, each
    `computeAIR` constraint evaluates identically under `envOfTrace` and under `computeEnvFull`. -/
theorem computeRow_env_match {K : Type*} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) (x₀ ω : K)
    (c : Constraint) (hc : c ∈ computeAIR.constraints) :
    c.expr.eval (Nock.Framework.Reify.envOfTrace
        (fun i : Fin computeAIR.numTraceCols =>
          Polynomial.C ((computeEnvFull inp (opSel pub.state) pub dec ex).trace i.val))
        ω x₀ (computeEnvFull inp (opSel pub.state) pub dec ex).chal
        (computeEnvFull inp (opSel pub.state) pub dec ex).pub)
      = c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec ex) := by
  set env := computeEnvFull inp (opSel pub.state) pub dec ex with henv
  refine Expr.eval_eq_of_wellScoped ((List.all_eq_true.mp computeAIR_wellScoped) c hc) ?_ ?_ ?_
  · intro i hi
    simp only [Nock.Framework.Reify.envOfTrace,
      dif_pos (lt_of_lt_of_eq hi computeAIR_numTraceCols.symm), Polynomial.eval_C]
  · intro i; rfl
  · intro i; rfl

/-! ### Multi-row encoding correctness (Lagrange interpolation)

  The multi-row generalization of `computeRow_env_match`.  Given a finite family of `n` compute
  rows (each described by an `Env K`, in practice a `computeEnvFull`) and an injective set of
  evaluation nodes `nodes : Fin n → K`, the **Lagrange trace encoder** interpolates, column by
  column, the per-row trace values through the nodes.  Because every `computeAIR` constraint is
  `wellScoped 94` (row-local, `traceNext`-free), evaluating the interpolated trace's `envOfTrace`
  at the node `nodes k` reproduces exactly `computeAIR`'s evaluation on row `k`'s environment. -/

/-- **Lagrange trace encoder for a finite family of rows.**  Column `j` is the unique polynomial of
    degree `< n` interpolating the per-row values `k ↦ (env k).trace j` through the nodes `nodes`. -/
noncomputable def encodeComputeTrace {K : Type*} [Field K] {n : ℕ}
    (env : Fin n → Env K) (nodes : Fin n → K) :
    Fin computeAIR.numTraceCols → Polynomial K :=
  fun j => Lagrange.interpolate Finset.univ nodes (fun k => (env k).trace j.val)

/-- **Eval-at-node for the Lagrange trace encoder.**  At each node `nodes k`, column `j` of the
    interpolated trace returns exactly row `k`'s trace value `(env k).trace j` (via Mathlib's
    `Lagrange.eval_interpolate_at_node`, using injectivity of `nodes`). -/
theorem encodeComputeTrace_eval_at_node {K : Type*} [Field K] {n : ℕ}
    (env : Fin n → Env K) (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (k : Fin n) (j : Fin computeAIR.numTraceCols) :
    (encodeComputeTrace env nodes j).eval (nodes k) = (env k).trace j.val :=
  Lagrange.eval_interpolate_at_node (fun k => (env k).trace j.val) hnodes.injOn (Finset.mem_univ k)

/-- **Multi-row encoding correctness.**  For the Lagrange encoding of a finite family of compute
    rows through injective nodes, each `computeAIR` constraint evaluates identically under
    `envOfTrace … (nodes k)` and under row `k`'s environment `env k`.  Mirrors
    `computeRow_env_match`, with the constant-encoding `Polynomial.eval_C` step replaced by the
    Lagrange eval-at-node lemma `encodeComputeTrace_eval_at_node`. -/
theorem computeMultiRow_env_match {K : Type*} [Field K] {n : ℕ}
    (env : Fin n → Env K) (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (ω : K) (k : Fin n) (c : Constraint) (hc : c ∈ computeAIR.constraints) :
    c.expr.eval (Nock.Framework.Reify.envOfTrace
        (encodeComputeTrace env nodes) ω (nodes k) (env k).chal (env k).pub)
      = c.expr.eval (env k) := by
  refine Expr.eval_eq_of_wellScoped ((List.all_eq_true.mp computeAIR_wellScoped) c hc) ?_ ?_ ?_
  · intro i hi
    simp only [Nock.Framework.Reify.envOfTrace,
      dif_pos (lt_of_lt_of_eq hi computeAIR_numTraceCols.symm)]
    exact encodeComputeTrace_eval_at_node env nodes hnodes k ⟨i, lt_of_lt_of_eq hi computeAIR_numTraceCols.symm⟩
  · intro i; rfl
  · intro i; rfl

#print axioms computeMultiRow_env_match

/-! ### Whole-trace compute bridge (THM54 assembly)

  Assembling the row-local encoding-correctness lemma `computeMultiRow_env_match` with the per-row
  soundness biconditional `computeAIR_iff_RAP` (AIR.lean), the algorithmic-verifier equivalence
  `ComputeTable.equiv_compute` (ComputeTable.lean), and the reification correspondence
  `Nock.Framework.Reify.airToRAP_satisfies_iff` (NockInstances.lean) yields the **whole-trace**
  bridge: the per-row verifier `Vcomp` accepts every one of the `n` compute rows **iff** the
  Lagrange-encoded trace satisfies the reified `computeAIR` RAP over the node domain
  `Finset.image nodes univ`.  This is pure assembly of already-proven pieces — no new math. -/

section Thm54WholeTraceBridge
open Nock.ComputeTable
open Classical

/-- **Reified satisfaction ⟺ per-row constraint vanishing (generic environment family).**
    For any family `env : Fin n → Env K` whose challenge columns are all `chalVal` and whose public
    columns are all zero (matching the `pubVal := fun _ => 0` fed to `airToRAP`), the Lagrange trace
    encoder satisfies the reified `computeAIR` RAP over the node domain iff every `computeAIR`
    constraint vanishes on every row `env k`.  This is `airToRAP_satisfies_iff` specialized to the
    node domain: `x ∈ Finset.image nodes univ` is reduced to `x = nodes k` via `Finset.mem_image`,
    and the two environments are matched by `computeMultiRow_env_match` after bridging
    `(env k).chal ↦ chalVal` / `(env k).pub ↦ 0`. -/
theorem satisfies_iff_perRow_env {K : Type*} [Field K] {n : ℕ}
    (env : Fin n → Env K) (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (chalVal : ℕ → K) (eDeg hExp : ℕ) (ω β : K) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp)
    (hchal : ∀ k, (env k).chal = chalVal) (hpub : ∀ k, (env k).pub = fun _ => 0) :
    (Nock.Framework.Reify.airToRAP computeAIR chalVal (fun _ => 0) eDeg hExp ω β
        (Finset.image nodes Finset.univ) hβ hh1).Satisfies (encodeComputeTrace env nodes)
      ↔ ∀ k, ∀ c ∈ computeAIR.constraints, c.expr.eval (env k) = 0 := by
  rw [Nock.Framework.Reify.airToRAP_satisfies_iff]
  constructor
  · intro h k c hc
    have hk := h (nodes k) (Finset.mem_image_of_mem nodes (Finset.mem_univ k)) c hc
    rw [← hchal k, ← hpub k, computeMultiRow_env_match env nodes hnodes ω k c hc] at hk
    exact hk
  · intro h x hx c hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    rw [← hchal k, ← hpub k, computeMultiRow_env_match env nodes hnodes ω k c hc]
    exact h k c hc

/-- **Whole-trace compute bridge (THM54).**  Over a family of `n` compute rows with injective
    evaluation nodes `nodes`, shared challenge vector `chalVal` (the `hchal` well-formedness
    condition — every row decodes the same `(α, z, a, b, c)`, stated through the `ex`-independent
    `.chal` projection of `computeEnvFull`), per-row well-formedness `WF` (`hwf`) and non-degenerate
    `z ≠ 0` (`hz`): the algorithmic compute verifier accepts *every* row iff there is an auxiliary
    witness family `ex` for which the Lagrange-encoded trace satisfies the reified `computeAIR` RAP
    over the node domain.

    Proof skeleton (assembly): `equiv_compute` (per row) ↔ ∃ ex-family (via `choose`/reassembly),
    `computeAIR_iff_RAP` (per row, using `hz`) rewrites `RAPcomp` ⟺ per-row constraint vanishing,
    and `satisfies_iff_perRow_env` bridges that to reified `Satisfies`. -/
theorem computeTable_reified_iff {K : Type*} [Field K] {n : ℕ}
    (inp : Fin n → Inputs K) (pub : Fin n → Pub K) (dec : Fin n → Dec K)
    (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (chalVal : ℕ → K) (eDeg hExp : ℕ) (ω β : K) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp)
    (hchal : ∀ k, (computeEnvFull (inp k) (opSel (pub k).state) (pub k) (dec k) ⟨0, 0⟩).chal = chalVal)
    (hwf : ∀ k, WF (inp k) (pub k)) (hz : ∀ k, (inp k).z ≠ 0) :
    (∀ k, Vcomp (inp k) (pub k) (dec k))
      ↔ ∃ ex : Fin n → Extra K,
          (Nock.Framework.Reify.airToRAP computeAIR chalVal (fun _ => 0) eDeg hExp ω β
              (Finset.image nodes Finset.univ) hβ hh1).Satisfies
            (encodeComputeTrace
              (fun k => computeEnvFull (inp k) (opSel (pub k).state) (pub k) (dec k) (ex k)) nodes) := by
  constructor
  · intro hV
    have hex_exists : ∀ k, ∃ e : Extra K, RAPcomp (inp k) (pub k) (dec k) e :=
      fun k => (equiv_compute (inp k) (pub k) (dec k) (hwf k)).mpr (hV k)
    choose ex hex using hex_exists
    refine ⟨ex, ?_⟩
    rw [satisfies_iff_perRow_env
          (fun k => computeEnvFull (inp k) (opSel (pub k).state) (pub k) (dec k) (ex k))
          nodes hnodes chalVal eDeg hExp ω β hβ hh1 (fun k => hchal k) (fun k => rfl)]
    intro k c hc
    exact (computeAIR_iff_RAP (inp k) (pub k) (dec k) (ex k) (hz k)).mpr (hex k) c hc
  · rintro ⟨ex, hSat⟩
    rw [satisfies_iff_perRow_env
          (fun k => computeEnvFull (inp k) (opSel (pub k).state) (pub k) (dec k) (ex k))
          nodes hnodes chalVal eDeg hExp ω β hβ hh1 (fun k => hchal k) (fun k => rfl)] at hSat
    intro k
    exact (equiv_compute (inp k) (pub k) (dec k) (hwf k)).mp
      ⟨ex k, (computeAIR_iff_RAP (inp k) (pub k) (dec k) (ex k) (hz k)).mp
        (fun c hc => hSat k c hc)⟩

end Thm54WholeTraceBridge

#print axioms computeTable_reified_iff

/-! ### Whole-trace MEMORY bridge (THM54 assembly — mirror of the compute bridge)

  The near-mechanical mirror of the compute bridge above, transported to the memory table.  Every
  step is the memory analog: `computeAIR`→`(memoryAIR (K := K))`, `encodeComputeTrace`→`encodeMemoryTrace`,
  `computeMultiRow_env_match`→`memoryMultiRow_env_match`, and the per-row soundness biconditional
  `computeAIR_iff_RAP` (which has no `memoryAIR_*` counterpart in `AIR.lean`) is inlined from
  `memoryAIR_sound`/`memoryAIR_toRAP` together with `MemoryTable.equiv_mem`.  The memory row is
  described by just `(Inputs, Pub)` (no `dec`), and the auxiliary witness family is a single field
  element per row — the free LogUp inverse `g` threaded through `memoryEnvFull`'s `mg`.  Because
  `memoryEnvFull`'s `.pub` is `fun _ => 0` (identical to `computeEnvFull`), the public-bridge is the
  same trivial `rfl`. -/

section Thm54WholeTraceBridgeMem
open MemoryTable
open Classical

/-- **Lagrange trace encoder for a finite family of memory rows.**  Column `j` is the unique
    polynomial of degree `< n` interpolating the per-row values `k ↦ (env k).trace j` through the
    nodes `nodes`.  Mirror of `encodeComputeTrace` (width `(memoryAIR (K := K)).numTraceCols = 36`). -/
noncomputable def encodeMemoryTrace {K : Type*} [Field K] {n : ℕ}
    (env : Fin n → Env K) (nodes : Fin n → K) :
    Fin (memoryAIR (K := K)).numTraceCols → Polynomial K :=
  fun j => Lagrange.interpolate Finset.univ nodes (fun k => (env k).trace j.val)

/-- **Eval-at-node for the Lagrange memory-trace encoder.**  At each node `nodes k`, column `j`
    returns exactly row `k`'s trace value.  Mirror of `encodeComputeTrace_eval_at_node`. -/
theorem encodeMemoryTrace_eval_at_node {K : Type*} [Field K] {n : ℕ}
    (env : Fin n → Env K) (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (k : Fin n) (j : Fin (memoryAIR (K := K)).numTraceCols) :
    (encodeMemoryTrace env nodes j).eval (nodes k) = (env k).trace j.val :=
  Lagrange.eval_interpolate_at_node (fun k => (env k).trace j.val) hnodes.injOn (Finset.mem_univ k)

/-- **Multi-row memory encoding correctness.**  For the Lagrange encoding of a finite family of
    memory rows through injective nodes, each `(memoryAIR (K := K))` constraint evaluates identically under
    `envOfTrace … (nodes k)` and under row `k`'s environment `env k`.  Mirror of
    `computeMultiRow_env_match` (`memoryAIR_wellScoped` / `memoryAIR_numTraceCols`). -/
theorem memoryMultiRow_env_match {K : Type*} [Field K] {n : ℕ}
    (env : Fin n → Env K) (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (ω : K) (k : Fin n) (c : Constraint) (hc : c ∈ (memoryAIR (K := K)).constraints) :
    c.expr.eval (Nock.Framework.Reify.envOfTrace
        (encodeMemoryTrace env nodes) ω (nodes k) (env k).chal (env k).pub)
      = c.expr.eval (env k) := by
  refine Expr.eval_eq_of_wellScoped ((List.all_eq_true.mp memoryAIR_wellScoped) c hc) ?_ ?_ ?_
  · intro i hi
    simp only [Nock.Framework.Reify.envOfTrace,
      dif_pos (lt_of_lt_of_eq hi memoryAIR_numTraceCols.symm)]
    exact encodeMemoryTrace_eval_at_node env nodes hnodes k ⟨i, lt_of_lt_of_eq hi memoryAIR_numTraceCols.symm⟩
  · intro i; rfl
  · intro i; rfl

#print axioms memoryMultiRow_env_match

/-- **Reified satisfaction ⟺ per-row constraint vanishing (memory, generic environment family).**
    Mirror of `satisfies_iff_perRow_env` for `(memoryAIR (K := K))`: for any family `env : Fin n → Env K` whose
    challenge columns are all `chalVal` and whose public columns are all zero, the Lagrange trace
    encoder satisfies the reified `(memoryAIR (K := K))` RAP over the node domain iff every `(memoryAIR (K := K))`
    constraint vanishes on every row `env k`. -/
theorem satisfies_iff_perRow_env_mem {K : Type*} [Field K] {n : ℕ}
    (env : Fin n → Env K) (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (chalVal : ℕ → K) (eDeg hExp : ℕ) (ω β : K) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp)
    (hchal : ∀ k, (env k).chal = chalVal) (hpub : ∀ k, (env k).pub = fun _ => 0) :
    (Nock.Framework.Reify.airToRAP (memoryAIR (K := K)) chalVal (fun _ => 0) eDeg hExp ω β
        (Finset.image nodes Finset.univ) hβ hh1).Satisfies (encodeMemoryTrace env nodes)
      ↔ ∀ k, ∀ c ∈ (memoryAIR (K := K)).constraints, c.expr.eval (env k) = 0 := by
  rw [Nock.Framework.Reify.airToRAP_satisfies_iff]
  constructor
  · intro h k c hc
    have hk := h (nodes k) (Finset.mem_image_of_mem nodes (Finset.mem_univ k)) c hc
    rw [← hchal k, ← hpub k, memoryMultiRow_env_match env nodes hnodes ω k c hc] at hk
    exact hk
  · intro h x hx c hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    rw [← hchal k, ← hpub k, memoryMultiRow_env_match env nodes hnodes ω k c hc]
    exact h k c hc

/-- **Whole-trace memory bridge (THM54).**  Over a family of `n` memory rows with injective
    evaluation nodes `nodes`, shared challenge vector `chalVal` (`hchal`, stated through the
    `mg`-independent `.chal` projection of `memoryEnvFull` at the placeholder witness `0`), per-row
    well-formedness `WF` (`hwf`) and non-degenerate `z ≠ 0` (`hz`): the algorithmic memory verifier
    `V_mem` accepts *every* row iff there is an auxiliary LogUp-inverse witness family `g` for which
    the Lagrange-encoded trace satisfies the reified `(memoryAIR (K := K))` RAP over the node domain.

    Proof skeleton (assembly), mirroring `computeTable_reified_iff`: `MemoryTable.equiv_mem` (per
    row) ↔ ∃ `g`-family (via `choose`/reassembly); the missing `memoryAIR_iff_RAP` is inlined from
    `memoryAIR_sound` (completeness, using `hz`) and `memoryAIR_toRAP` (soundness); and
    `satisfies_iff_perRow_env_mem` bridges per-row vanishing to reified `Satisfies`. -/
theorem memoryTable_reified_iff {K : Type*} [Field K] {n : ℕ}
    (minp : Fin n → MemoryTable.Inputs K) (mrow : Fin n → MemoryTable.Pub K)
    (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (chalVal : ℕ → K) (eDeg hExp : ℕ) (ω β : K) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp)
    (hchal : ∀ k, (memoryEnvFull (minp k) (MemoryTable.opSel (mrow k).st) (mrow k) 0).chal = chalVal)
    (hwf : ∀ k, MemoryTable.WF (minp k) (mrow k)) (hz : ∀ k, (minp k).z ≠ 0) :
    (∀ k, MemoryTable.Vmem (minp k) (mrow k))
      ↔ ∃ g : Fin n → K,
          (Nock.Framework.Reify.airToRAP (memoryAIR (K := K)) chalVal (fun _ => 0) eDeg hExp ω β
              (Finset.image nodes Finset.univ) hβ hh1).Satisfies
            (encodeMemoryTrace
              (fun k => memoryEnvFull (minp k) (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) nodes) := by
  refine ⟨?_, ?_⟩
  · intro hV
    have hg_exists : ∀ k, ∃ g : K, MemoryTable.RAPmem (minp k) (mrow k) g :=
      fun k => (MemoryTable.equiv_mem (minp k) (mrow k) (hwf k)).mpr (hV k)
    choose g hg using hg_exists
    refine ⟨g, ?_⟩
    rw [satisfies_iff_perRow_env_mem
          (fun k => memoryEnvFull (minp k) (MemoryTable.opSel (mrow k).st) (mrow k) (g k))
          nodes hnodes chalVal eDeg hExp ω β hβ hh1 (fun k => hchal k) (fun k => rfl)]
    intro k c hc
    exact ((memoryAIR_sound (minp k) (mrow k) (g k)).mpr ⟨hg k, hz k⟩) c hc
  · rintro ⟨g, hSat⟩
    rw [satisfies_iff_perRow_env_mem
          (fun k => memoryEnvFull (minp k) (MemoryTable.opSel (mrow k).st) (mrow k) (g k))
          nodes hnodes chalVal eDeg hExp ω β hβ hh1 (fun k => hchal k) (fun k => rfl)] at hSat
    intro k
    exact (MemoryTable.equiv_mem (minp k) (mrow k) (hwf k)).mp
      ⟨g k, memoryAIR_toRAP (minp k) (mrow k) (g k) (fun c hc => hSat k c hc)⟩

end Thm54WholeTraceBridgeMem

#print axioms memoryTable_reified_iff

end Nock.Reified
