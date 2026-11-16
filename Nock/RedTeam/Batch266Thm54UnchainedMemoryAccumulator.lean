/-
  Nock/RedTeam/Batch266Thm54UnchainedMemoryAccumulator.lean

**The earlier version of this
  file proved**:

  * `deployed_memory_chip_accepts_shifted_accumulator` — for any trace `P.memoryChip` accepted,
    any interior row `i₀` and any `δ ∈ 𝔽³`, the trace with `δ_k · L_{i₀}` added to the six
    accumulator columns was still accepted;
  * `shifted_trace_is_unchained` — that trace violated `acc_before(i₀) = acc_after(i₀ − 1)`;
  * `accumulator_value_is_free` — the prover could set the running sum to any target, so the
    terminal check `last · (acc_after − terminal) = 0` said nothing about the records;
  * `canonical_memory_trace_bumped_is_accepted` — non-vacuity at the package's own honest trace.

  The paper's `acc_mem` is **one** column whose transition reads `acc_mem(i−1)` and `acc_mem(i)`
, seeded at `:549` and read out at `:586`; the tree had materialised "`acc`
  at the next row" as a second committed column and never bound it to the next row's first one.

  The theorems above are thereby **false** of the deployed chip and
  are unstatable here in their old form. What this file records now:

  * the read-set facts that remain true (§A–C): every gate *other than* the new chain gate is
    blind to the shift, so the chain gate is the **only** thing that rejects it — the repair is
    exactly one gate wide;
  * **`repaired_chip_rejects_shifted_accumulator`** (§D): at the consumed `P.memoryChip`, for any
    accepted trace, any row `i₀ ≥ 1` and any `δ` whose gathered value `Σ δ_k b_k` is nonzero, the
    bumped trace is **rejected** — the new gate at row `i₀ − 1` evaluates to `−Σ δ_k b_k`;
  * the honest trace still passes (`canonicalMemoryTrace_satisfies`, unchanged), so the gate is
    a strict tightening of the accepted set with no completeness cost.

  Not claimed: anything about the compute chip (its accumulator, role `32`, was already read at
  this row and the next by the `aux[2]` residual pins); that the two-role layout is the paper's —
  it is not, and W2 replaces it by the single column at the paper.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Mathlib.LinearAlgebra.Lagrange

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch266

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Module
open scoped Polynomial

noncomputable section


/-- The two rows' worth of accumulator variables, as `𝕂`-role variables. -/
def accRoleVars : Finset (VarKind × ℕ) :=
  {(VarKind.traceCur, 43), (VarKind.traceCur, 44), (VarKind.traceNext, 43), (VarKind.traceNext, 44)}

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. The deployed layout, and what reads the six accumulator columns -/

/-- The deployed memory layout: extension role `r` occupies columns `6 + 3r .. 6 + 3r + 2`. -/
theorem memCol0_eq (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).col0 3 = memoryCol0 := rfl

/-- The six accumulator columns: role `43` is `135..137`, role `44` is `138..140`. -/
def IsAccCol (i : ℕ) : Prop := 135 ≤ i ∧ i < 141

instance (i : ℕ) : Decidable (IsAccCol i) := by unfold IsAccCol; infer_instance

theorem accCol_of_role43 (k : Fin 3) : IsAccCol (6 + 3 * 43 + (k : ℕ)) := by
  unfold IsAccCol; omega

theorem accCol_of_role44 (k : Fin 3) : IsAccCol (6 + 3 * 44 + (k : ℕ)) := by
  unfold IsAccCol; omega

theorem not_accCol_of_role (idx : ℕ) (h43 : idx ≠ 43) (h44 : idx ≠ 44) (k : Fin 3) :
    ¬ IsAccCol (6 + 3 * idx + (k : ℕ)) := by
  unfold IsAccCol; omega

/-- Read a variable off an environment. -/
def envAt (env : Env K) : VarKind → ℕ → K
  | .traceCur, i => env.trace i
  | .traceNext, i => env.traceNext i
  | .challenge, i => env.chal i
  | .publicVal, i => env.pub i

/-- Evaluation depends only on the syntactic support: two environments that agree off a set `S`
disjoint from the support evaluate alike. -/
theorem eval_congr_of_disjoint (S : Finset (VarKind × ℕ)) (env env' : Env K)
    (hagree : ∀ v : VarKind × ℕ, v ∉ S → envAt env' v.1 v.2 = envAt env v.1 v.2) :
    ∀ e : Expr, (∀ v ∈ S, v ∉ exprVariableSupport e) → e.eval env' = e.eval env
  | .Const _, _ => rfl
  | .Var k i, h => by
      have hv : (k, i) ∉ S := fun hmem => h _ hmem (by simp [exprVariableSupport])
      have := hagree (k, i) hv
      cases k <;> simpa [envAt, Expr.eval] using this
  | .Add x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_congr_of_disjoint S env env' hagree x (fun v hv => (h v hv).1),
        eval_congr_of_disjoint S env env' hagree y (fun v hv => (h v hv).2)]
  | .Sub x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_congr_of_disjoint S env env' hagree x (fun v hv => (h v hv).1),
        eval_congr_of_disjoint S env env' hagree y (fun v hv => (h v hv).2)]
  | .Mul x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_congr_of_disjoint S env env' hagree x (fun v hv => (h v hv).1),
        eval_congr_of_disjoint S env env' hagree y (fun v hv => (h v hv).2)]
  | .Neg x, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_congr_of_disjoint S env env' hagree x h]
  | .Pow x n, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_congr_of_disjoint S env env' hagree x h]

/-! ## B. The base-field row mutation and its gathered `𝕂` image -/

/-- `envF'` is `envF` with the same `δ k` added to columns `135 + k` (role `43`) and `138 + k`
(role `44`) at the current row, the six accumulator columns arbitrary at the next row, and
everything else equal. -/
structure AccShift (envF envF' : Env F) (δ : Fin 3 → F) : Prop where
  trace_off : ∀ i, ¬ IsAccCol i → envF'.trace i = envF.trace i
  trace_before : ∀ k : Fin 3, envF'.trace (135 + k) = envF.trace (135 + k) + δ k
  trace_after : ∀ k : Fin 3, envF'.trace (138 + k) = envF.trace (138 + k) + δ k
  next_off : ∀ i, ¬ IsAccCol i → envF'.traceNext i = envF.traceNext i
  chal : ∀ i, envF'.chal i = envF.chal i
  pub : ∀ i, envF'.pub i = envF.pub i

/-- The `𝕂`-valued shift the base-field `δ` gathers to. -/
def gatherShift (b : Basis (Fin 3) F K) (δ : Fin 3 → F) : K := ∑ k, δ k • b k

section Gather

variable (b : Basis (Fin 3) F K) {envF envF' : Env F} {δ : Fin 3 → F} (h : AccShift envF envF' δ)
include h

theorem gather_trace_off (idx : ℕ) (h43 : idx ≠ 43) (h44 : idx ≠ 44) :
    (gatherEnv b memoryCol0 envF').trace idx = (gatherEnv b memoryCol0 envF).trace idx := by
  simp only [gatherEnv, memoryCol0]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h.trace_off _ (not_accCol_of_role idx h43 h44 k)]

theorem gather_trace_43 :
    (gatherEnv b memoryCol0 envF').trace 43 =
      (gatherEnv b memoryCol0 envF).trace 43 + gatherShift b δ := by
  simp only [gatherEnv, memoryCol0, gatherShift]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := h.trace_before k
  rw [show 6 + 3 * 43 + (k : ℕ) = 135 + (k : ℕ) by norm_num, hk, add_smul]

theorem gather_trace_44 :
    (gatherEnv b memoryCol0 envF').trace 44 =
      (gatherEnv b memoryCol0 envF).trace 44 + gatherShift b δ := by
  simp only [gatherEnv, memoryCol0, gatherShift]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := h.trace_after k
  rw [show 6 + 3 * 44 + (k : ℕ) = 138 + (k : ℕ) by norm_num, hk, add_smul]

theorem gather_next_off (idx : ℕ) (h43 : idx ≠ 43) (h44 : idx ≠ 44) :
    (gatherEnv b memoryCol0 envF').traceNext idx =
      (gatherEnv b memoryCol0 envF).traceNext idx := by
  simp only [gatherEnv, memoryCol0]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h.next_off _ (not_accCol_of_role idx h43 h44 k)]

theorem gather_chal (idx : ℕ) :
    (gatherEnv b memoryCol0 envF').chal idx = (gatherEnv b memoryCol0 envF).chal idx := by
  simp only [gatherEnv, memoryCol0]
  exact Finset.sum_congr rfl fun k _ => by rw [h.chal]

theorem gather_pub (idx : ℕ) :
    (gatherEnv b memoryCol0 envF').pub idx = (gatherEnv b memoryCol0 envF).pub idx := by
  simp only [gatherEnv, memoryCol0]
  exact Finset.sum_congr rfl fun k _ => by rw [h.pub]

/-- Off the four accumulator role-variables the two gathered environments agree. -/
theorem gather_agree_off_acc :
    ∀ v : VarKind × ℕ, v ∉ accRoleVars →
      envAt (gatherEnv b memoryCol0 envF') v.1 v.2 = envAt (gatherEnv b memoryCol0 envF) v.1 v.2 := by
  rintro ⟨kind, idx⟩ hv
  simp only [accRoleVars, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or] at hv
  cases kind with
  | traceCur =>
      have h43 : idx ≠ 43 := fun e => hv.1 ⟨rfl, e⟩
      have h44 : idx ≠ 44 := fun e => hv.2.1 ⟨rfl, e⟩
      exact gather_trace_off b h idx h43 h44
  | traceNext =>
      have h43 : idx ≠ 43 := fun e => hv.2.2.1 ⟨rfl, e⟩
      have h44 : idx ≠ 44 := fun e => hv.2.2.2 ⟨rfl, e⟩
      exact gather_next_off b h idx h43 h44
  | challenge => exact gather_chal b h idx
  | publicVal => exact gather_pub b h idx

/-- Any `𝕂`-gate whose support avoids the four accumulator role-variables is blind to the shift. -/
theorem ext_gate_blind (e : Expr) (hsupp : ∀ v ∈ accRoleVars, v ∉ exprVariableSupport e) :
    e.eval (gatherEnv b memoryCol0 envF') = e.eval (gatherEnv b memoryCol0 envF) :=
  eval_congr_of_disjoint accRoleVars _ _ (gather_agree_off_acc b h) e hsupp

end Gather

/-! ## C. Every gate but the chain gate is blind to the shift (read-set facts, still true) -/

/-! ### Syntactic read-set facts (no environment involved) -/

/-- The twenty-one folds, other than folds `17` and `18`, do not read the
accumulator roles at either row: their supports avoid `accRoleVars`. -/
theorem fold_support_avoids_acc (j : Fin 21) (h17 : j ≠ 17) (h18 : j ≠ 18) :
    ∀ v ∈ accRoleVars, v ∉ exprVariableSupport (foldAt (K := K) j) :=
  foldAt_support_avoids_acc (K := K) j (Fin.val_ne_of_ne h17) (Fin.val_ne_of_ne h18)

theorem deg1_support_avoids_acc :
    ∀ g ∈ degreeOneEndpoints, ∀ v ∈ accRoleVars, v ∉ exprVariableSupport g := by
  intro g hg; cases hg

theorem deg3_support_avoids_acc :
    ∀ g ∈ degreeThreeEndpoints, ∀ v ∈ accRoleVars, v ∉ exprVariableSupport g := by
  intro g hg; cases hg

/-- The two fold sources that do read the accumulator: `firstMask · acc` and
`lastMask · (acc′ − terminal)` (`sampledSources[7]`, `[8]`, at fold indices `38`, `39`). -/
theorem source38_eq :
    (extensionFoldSources (K := K)).get ⟨38, extensionFoldSources_get_lt (K := K) 38⟩ =
      .Mul (.Var .traceCur 47) (.Var .traceCur 43) := rfl

theorem source39_eq :
    (extensionFoldSources (K := K)).get ⟨39, extensionFoldSources_get_lt (K := K) 39⟩ =
      .Mul (.Var .traceCur 48) (.Sub (.Var .traceCur 44) (.Var .traceCur 40)) := rfl

theorem source17_support_avoids_acc :
    ∀ v ∈ accRoleVars,
      v ∉ exprVariableSupport
        ((extensionFoldSources (K := K)).get ⟨17, extensionFoldSources_get_lt (K := K) 17⟩) := by
  intro v hv
  rw [List.get_eq_getElem, extensionFoldSource_support_carrier (K₁ := K) (K₂ := ZMod 31)]
  exact extensionFoldSource17_avoid_acc v hv

theorem source18_support_avoids_acc :
    ∀ v ∈ accRoleVars,
      v ∉ exprVariableSupport
        ((extensionFoldSources (K := K)).get ⟨18, extensionFoldSources_get_lt (K := K) 18⟩) := by
  intro v hv
  rw [List.get_eq_getElem, extensionFoldSource_support_carrier (K₁ := K) (K₂ := ZMod 31)]
  exact extensionFoldSource18_avoid_acc v hv

/-- Bucket `18` carries fold sources `18` and `39` (the analogue of `foldAt17_eval`). -/
theorem foldAt18_eval (env : Env K) :
    (foldAt (K := K) (18 : Fin 21)).eval env =
      ((extensionFoldSources (K := K)).get ⟨18, extensionFoldSources_get_lt (K := K) 18⟩).eval env +
      foldChallenge.eval env *
        ((extensionFoldSources (K := K)).get ⟨39, extensionFoldSources_get_lt (K := K) 39⟩).eval env := by
  simpa using foldAt_eval_two (K := K) (18 : Fin 21) (by decide) env

section Row

variable (b : Basis (Fin 3) F K) {envF envF' : Env F} {δ : Fin 3 → F} (h : AccShift envF envF' δ)
include h

/-- Fold `17` is blind to the shift when the first mask vanishes at the row. -/
theorem fold17_blind (h47 : (gatherEnv b memoryCol0 envF).trace 47 * gatherShift b δ = 0) :
    (foldAt (K := K) 17).eval (gatherEnv b memoryCol0 envF') = (foldAt (K := K) 17).eval (gatherEnv b memoryCol0 envF) := by
  rw [foldAt17_eval, foldAt17_eval]
  rw [ext_gate_blind b h _ source17_support_avoids_acc, source38_eq]
  simp only [Expr.eval, foldChallenge]
  rw [gather_chal b h, gather_trace_off b h 47 (by norm_num) (by norm_num), gather_trace_43 b h]
  rw [mul_add, h47, add_zero]

/-- Fold `18` is blind to the shift when the last mask vanishes at the row. -/
theorem fold18_blind (h48 : (gatherEnv b memoryCol0 envF).trace 48 * gatherShift b δ = 0) :
    (foldAt (K := K) 18).eval (gatherEnv b memoryCol0 envF') = (foldAt (K := K) 18).eval (gatherEnv b memoryCol0 envF) := by
  rw [foldAt18_eval, foldAt18_eval]
  rw [ext_gate_blind b h _ source18_support_avoids_acc, source39_eq]
  simp only [Expr.eval, foldChallenge]
  rw [gather_chal b h, gather_trace_off b h 48 (by norm_num) (by norm_num),
    gather_trace_off b h 40 (by norm_num) (by norm_num), gather_trace_44 b h]
  rw [show (gatherEnv b memoryCol0 envF).trace 44 + gatherShift b δ -
      (gatherEnv b memoryCol0 envF).trace 40 =
      ((gatherEnv b memoryCol0 envF).trace 44 - (gatherEnv b memoryCol0 envF).trace 40) +
        gatherShift b δ by ring]
  rw [mul_add, h48, add_zero]

/-- Every `𝕂`-valued gate of the chip is blind to the shift at a row where both masks vanish
against it. -/
theorem ext_gates_blind
    (h47 : (gatherEnv b memoryCol0 envF).trace 47 * gatherShift b δ = 0)
    (h48 : (gatherEnv b memoryCol0 envF).trace 48 * gatherShift b δ = 0) :
    ∀ g ∈ extensionTransitionGates (K := K) ++ degreeOneEndpoints ++ degreeThreeEndpoints,
      g.eval (gatherEnv b memoryCol0 envF') = g.eval (gatherEnv b memoryCol0 envF) := by
  intro g hg
  simp only [List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · change g ∈ List.ofFn (foldAt (K := K)) at hg
    simp only [List.mem_ofFn] at hg
    obtain ⟨j, rfl⟩ := hg
    by_cases h17 : j = 17
    · subst h17; exact fold17_blind b h h47
    by_cases h18 : j = 18
    · subst h18; exact fold18_blind b h h48
    exact ext_gate_blind b h _ (fold_support_avoids_acc j h17 h18)
  · exact ext_gate_blind b h _ (deg1_support_avoids_acc g hg)
  · exact ext_gate_blind b h _ (deg3_support_avoids_acc g hg)

/-- The eleven base gates: the eight that do not read the six columns are unchanged, and the
three accumulator steps `acc′ − acc − contribution` cancel the common shift. -/
theorem base_gates_blind :
    ∀ g ∈ foldedBaseTransitionGates b, g.eval envF' = g.eval envF := by
  intro g hg
  have hoff : ∀ i, ¬ IsAccCol i → envF'.trace i = envF.trace i := h.trace_off
  simp only [foldedBaseTransitionGates, semanticBaseTail, List.mem_append, List.mem_cons,
    List.mem_ofFn, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl) | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simp [bbool, bcur, CoeffExpr.eval, hoff 0 (by unfold IsAccCol; omega)]
  · simp [bbool, bcur, CoeffExpr.eval, hoff 1 (by unfold IsAccCol; omega)]
  · simp [bbool, bcur, CoeffExpr.eval, hoff 2 (by unfold IsAccCol; omega)]
  · simp [bbool, bcur, CoeffExpr.eval, hoff 3 (by unfold IsAccCol; omega)]
  · simp [bsum4, CoeffExpr.eval, hoff 0 (by unfold IsAccCol; omega),
      hoff 1 (by unfold IsAccCol; omega), hoff 2 (by unfold IsAccCol; omega),
      hoff 3 (by unfold IsAccCol; omega)]
  · -- `sampledTerminalCoord k` reads column `126 + k` (role `40`) and public `12 + k`
    -- — neither is an accumulator column.
    simp only [sampledTerminalCoord, extCoord, CoeffExpr.eval]
    rw [hoff (6 + 3 * 40 + (k : ℕ)) (by unfold IsAccCol; omega), h.pub]
  · -- `sampledAccumulatorCoord k`: `(138+k) − ((135+k) + (132+k))`.
    simp only [sampledAccumulatorCoord, extCoord, CoeffExpr.eval]
    have h44 := h.trace_after k
    have h43 := h.trace_before k
    rw [show 6 + 3 * 44 + (k : ℕ) = 138 + (k : ℕ) by norm_num,
      show 6 + 3 * 43 + (k : ℕ) = 135 + (k : ℕ) by norm_num, h44, h43,
      hoff (6 + 3 * 42 + (k : ℕ)) (by unfold IsAccCol; omega)]
    ring

/-- The twelve equality checks (selector mirrors `51 + s ↔` base column `s`) are unchanged. -/
theorem equality_checks_blind :
    ∀ g ∈ foldedEqualityChecks b, g.eval envF' = g.eval envF := by
  intro g hg
  obtain ⟨m, hm, k, rfl⟩ := (mem_mixedExpandList b memoryCol0 _ g).mp hg
  rw [← mixedCompile_eval b memoryCol0 (isCoordEnv_gather b memoryCol0 envF') m k,
    ← mixedCompile_eval b memoryCol0 (isCoordEnv_gather b memoryCol0 envF) m k]
  congr 1
  simp only [mixedEqualityChecks, List.mem_ofFn] at hm
  obtain ⟨s, rfl⟩ := hm
  simp only [selectorMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
  rw [gather_trace_off b h (51 + (s : ℕ)) (by omega) (by omega),
    h.trace_off (s : ℕ) (by unfold IsAccCol; omega)]

/-- The five mixed gates other than the accumulator chain are unchanged (A-mem-2's
denominator pin reads roles `37`, `19..26` and the two coin slots; the dequeue-mask pin
reads role `56` and preprocessing column `154`; none of them are accumulator columns). -/
theorem other_mixed_gates_blind :
    ∀ g ∈ foldedMixedTransitionGates (F := F), g ≠ accChainMixed →
      g.eval (gatherEnv b memoryCol0 envF') envF' = g.eval (gatherEnv b memoryCol0 envF) envF := by
  intro g hg hne
  simp only [foldedMixedTransitionGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [firstMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [gather_trace_off b h 47 (by norm_num) (by norm_num),
      h.trace_off 4 (by unfold IsAccCol; omega)]
  · simp only [lastMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [gather_trace_off b h 48 (by norm_num) (by norm_num),
      h.trace_off 5 (by unfold IsAccCol; omega)]
  · simp only [chainMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [gather_trace_off b h 28 (by norm_num) (by norm_num),
      gather_next_off b h 27 (by norm_num) (by norm_num),
      h.trace_off 5 (by unfold IsAccCol; omega)]
  · exact absurd rfl hne
  · simp only [denominatorPinMixed, recordRLC, recordRLCExpr, reqIdxRLCTerm, reqIdxCol, bcur,
      CoeffExpr.eval, MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval]
    rw [gather_chal b h, gather_chal b h, gather_trace_off b h 37 (by norm_num) (by norm_num),
      gather_trace_off b h 19 (by norm_num) (by norm_num),
      gather_trace_off b h 20 (by norm_num) (by norm_num),
      gather_trace_off b h 21 (by norm_num) (by norm_num),
      gather_trace_off b h 22 (by norm_num) (by norm_num),
      gather_trace_off b h 23 (by norm_num) (by norm_num),
      gather_trace_off b h 24 (by norm_num) (by norm_num),
      gather_trace_off b h 25 (by norm_num) (by norm_num),
      gather_trace_off b h 26 (by norm_num) (by norm_num),
      gather_trace_off b h 57 (by norm_num) (by norm_num),
      h.trace_off 181 (by unfold IsAccCol; omega)]
  · simp only [dequeueMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [gather_trace_off b h 56 (by norm_num) (by norm_num),
      h.trace_off 154 (by unfold IsAccCol; omega)]

omit h in
/-- **The accumulator chain gate sees the shift at the row before it.**  If this row's next-row
read of role `43` moved by `Δ` while its current-row role `44` and the base mask did not, the
gate moves by exactly `−(1 − last) · Δ`. -/
theorem accStep_sees_next_row_shift (envF envF' : Env F) (Δ : K)
    (hcur43 : (gatherEnv b memoryCol0 envF').trace 43 = (gatherEnv b memoryCol0 envF).trace 43)
    (hcur42 : (gatherEnv b memoryCol0 envF').trace 42 = (gatherEnv b memoryCol0 envF).trace 42)
    (hnext43 : (gatherEnv b memoryCol0 envF').traceNext 43 =
      (gatherEnv b memoryCol0 envF).traceNext 43 + Δ)
    (h5 : envF'.trace 5 = envF.trace 5) :
    (accStep (F := F)).eval (gatherEnv b memoryCol0 envF') envF' =
      (accStep (F := F)).eval (gatherEnv b memoryCol0 envF) envF
        + algebraMap F K (1 - envF.trace 5) * Δ := by
  simp only [accStep, MixedExpr.eval, bcur, CoeffExpr.eval]
  rw [hcur43, hcur42, hnext43, h5]
  ring

omit h in

theorem accChain_sees_next_row_shift (envF envF' : Env F) (Δ : K)
    (hcur44 : (gatherEnv b memoryCol0 envF').trace 44 = (gatherEnv b memoryCol0 envF).trace 44)
    (hnext43 : (gatherEnv b memoryCol0 envF').traceNext 43 =
      (gatherEnv b memoryCol0 envF).traceNext 43 + Δ)
    (h5 : envF'.trace 5 = envF.trace 5) :
    (accChainMixed (F := F)).eval (gatherEnv b memoryCol0 envF') envF' =
      (accChainMixed (F := F)).eval (gatherEnv b memoryCol0 envF) envF
        - algebraMap F K (1 - envF.trace 5) * Δ := by
  simp only [accChainMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
  rw [hcur44, hnext43, h5]
  ring

end Row

/-! ## D. The shifted trace, and its rejection at the consumed chip -/

section Trace

variable {n : ℕ} (nodes : Fin n → F) (i₀ : Fin n) (δ : Fin 3 → F)

/-- The coordinate a column in `135..140` carries: `(c − 135) % 3`. -/
def accCoord (c : ℕ) : Fin 3 := ⟨(c - 135) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem accCoord_before (k : Fin 3) : accCoord (135 + (k : ℕ)) = k := by
  apply Fin.ext; simp only [accCoord]; omega

/-- `Q` with `δ_k · L_{i₀}` added to the six accumulator columns, where `L_{i₀}` is the Lagrange
basis polynomial of row `i₀` over the row nodes: it is `1` at `nodes i₀` and `0` at every other
row node, so the shift touches exactly one row. -/
def shiftTrace {w : ℕ} (Q : Fin w → F[X]) : Fin w → F[X] :=
  fun c => if IsAccCol (c : ℕ) then
    Q c + Polynomial.C (δ (accCoord (c : ℕ))) * Lagrange.basis Finset.univ nodes i₀
  else Q c

theorem shiftTrace_off {w : ℕ} (Q : Fin w → F[X]) (c : Fin w) (hc : ¬ IsAccCol (c : ℕ)) :
    shiftTrace nodes i₀ δ Q c = Q c := by
  simp [shiftTrace, hc]

theorem shiftTrace_eval (hinj : Function.Injective nodes) {w : ℕ} (Q : Fin w → F[X])
    (c : Fin w) (hc : IsAccCol (c : ℕ)) (j : Fin n) :
    (shiftTrace nodes i₀ δ Q c).eval (nodes j) =
      (Q c).eval (nodes j) + (if j = i₀ then δ (accCoord (c : ℕ)) else 0) := by
  simp only [shiftTrace, if_pos hc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hj : j = i₀
  · subst hj
    rw [Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ _), if_pos rfl, mul_one]
  · rw [Lagrange.eval_basis_of_ne (Ne.symm hj) (Finset.mem_univ _), if_neg hj, mul_zero]

/-- The shifted trace at row `i₀` really moves: `acc_before(i₀)` by `δ`, coordinatewise. -/
theorem shiftTrace_moves_before (hinj : Function.Injective nodes) {w : ℕ} (hw : 141 ≤ w)
    (Q : Fin w → F[X]) (k : Fin 3) :
    (shiftTrace nodes i₀ δ Q ⟨135 + (k : ℕ), by omega⟩).eval (nodes i₀) =
      (Q ⟨135 + (k : ℕ), by omega⟩).eval (nodes i₀) + δ k := by
  rw [shiftTrace_eval nodes i₀ δ hinj Q _ (by unfold IsAccCol; simp; omega) i₀, if_pos rfl,
    accCoord_before]

end Trace

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The source chip the consumed memory chip pads. -/
abbrev sourceOf : FixedPreprocessingRAP F :=
  namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
    P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
    P.optimized.family.problem.cfg.kMem

/-- The residual-column padding of the consumed chip. -/
abbrev extraOf : Fin (sourceOf P).rap.k → ℕ :=
  RAPPadding.firstRoundExtra (sourceOf P).rap (sourceOf P).rounds_pos
    (RAPPadding.memoryResidualColumns 3)

/-- Projecting the padded trace commutes with the shift (the column inclusion is `Fin.castAdd`,
which preserves the column index). -/
theorem projectTrace_shiftTrace {n : ℕ} (nodes : Fin n → F) (i₀ : Fin n) (δ : Fin 3 → F)
    (R : RAP F) (extra : Fin R.k → ℕ) (Q : Fin (R.w + RAPPadding.extraWidth extra) → F[X]) :
    RAPPadding.projectTrace R extra (shiftTrace nodes i₀ δ Q) =
      shiftTrace nodes i₀ δ (RAPPadding.projectTrace R extra Q) := by
  funext c
  simp [RAPPadding.projectTrace, shiftTrace, RAPPadding.columnInclusion] <;> rfl

/-- The row-`i` environment of the source trace shifted at row `i + 1`, against the original's:
the current row is untouched, the next-row read of role `43` moved by `Σ δ_k b_k`. -/
theorem shifted_env_at_predecessor
    (Q : Fin (sourceOf P).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.memRows) (δ : Fin 3 → F) :
    (∀ c : ℕ,
      (envOfTrace (shiftTrace P.optimized.memoryNodes ⟨(i : ℕ) + 1, hi⟩ δ Q) P.optimized.orbit.ω
        (P.optimized.memoryNodes i) P.optimized.memoryChallenge P.optimized.memoryPublic).trace c =
      (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
        P.optimized.memoryChallenge P.optimized.memoryPublic).trace c) ∧
      (gatherEnv P.optimized.basis memoryCol0
        (envOfTrace (shiftTrace P.optimized.memoryNodes ⟨(i : ℕ) + 1, hi⟩ δ Q) P.optimized.orbit.ω
          (P.optimized.memoryNodes i) P.optimized.memoryChallenge P.optimized.memoryPublic)).traceNext 43 =
      (gatherEnv P.optimized.basis memoryCol0
        (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
          P.optimized.memoryChallenge P.optimized.memoryPublic)).traceNext 43 +
        gatherShift P.optimized.basis δ := by
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
  have hinj := P.optimized.memoryNodes_injective
  have hsucc : P.optimized.memoryNodes ⟨(i : ℕ) + 1, hi⟩ =
      P.optimized.memoryNodes i * P.optimized.orbit.ω :=
    P.optimized.memoryOrbitAligned i hi
  have hne : i ≠ ⟨(i : ℕ) + 1, hi⟩ := fun e => by
    have := congrArg Fin.val e; simp at this
  refine ⟨?_, ?_⟩
  · intro c
    simp only [envOfTrace]
    split_ifs with hc
    · by_cases hacc : IsAccCol c
      · rw [shiftTrace_eval _ _ _ hinj Q ⟨c, hc⟩ hacc i, if_neg hne, add_zero]
      · rw [shiftTrace_off _ _ _ Q ⟨c, hc⟩ hacc]
    · rfl
  · simp only [gatherEnv, memoryCol0, gatherShift]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlt : 6 + 3 * 43 + (k : ℕ) < (sourceOf P).rap.w := by rw [hw]; omega
    simp only [envOfTrace, dif_pos hlt]
    rw [mul_comm, ← hsucc]
    rw [shiftTrace_eval _ _ _ hinj Q ⟨6 + 3 * 43 + (k : ℕ), hlt⟩
      (by show IsAccCol (6 + 3 * 43 + (k : ℕ)); unfold IsAccCol; omega)
      ⟨(i : ℕ) + 1, hi⟩, if_pos rfl]
    rw [show accCoord (6 + 3 * 43 + (k : ℕ)) = k by
      apply Fin.ext; simp only [accCoord]; omega]
    rw [add_smul]

/-- **The repaired chip rejects the unchained accumulator.**  At the consumed `P.memoryChip`: for
any accepted trace, any row `i₀ ≥ 1`, and any `δ ∈ 𝔽³` whose gathered value `Σ δ_k b_k` is
nonzero, the trace with the six accumulator columns bumped by `δ` at row `i₀` — the very trace
the former `deployed_memory_chip_accepts_shifted_accumulator` accepted — is **not** accepted:
the accumulator chain gate `accChainMixed` at row `i₀ − 1` evaluates to `−Σ δ_k b_k`. -/
theorem repaired_chip_rejects_shifted_accumulator
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (i₀ : Fin P.optimized.family.problem.cfg.memRows) (hi₀ : (i₀ : ℕ) ≠ 0)
    (δ : Fin 3 → F) (hδ : gatherShift P.optimized.basis δ ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.memoryChip
      (shiftTrace P.optimized.memoryNodes i₀ δ Qm) := by
  intro hsat'
  have hsrc := (final_satisfies_iff_source P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic
    P.optimized.orbit P.optimized.family.problem.cfg.kMem Qm).mp hsat
  have hsrc' := (final_satisfies_iff_source P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic
    P.optimized.orbit P.optimized.family.problem.cfg.kMem _).mp hsat'
  have hproj : RAPPadding.projectTrace (sourceOf P).rap (extraOf P)
      (shiftTrace P.optimized.memoryNodes i₀ δ Qm) =
        shiftTrace P.optimized.memoryNodes i₀ δ
          (RAPPadding.projectTrace (sourceOf P).rap (extraOf P) Qm) :=
    projectTrace_shiftTrace P.optimized.memoryNodes i₀ δ (sourceOf P).rap (extraOf P) Qm
  change RAP.SatisfiesWithPreprocessing (sourceOf P)
    (RAPPadding.projectTrace (sourceOf P).rap (extraOf P)
      (shiftTrace P.optimized.memoryNodes i₀ δ Qm)) at hsrc'
  rw [hproj] at hsrc'
  set Q := RAPPadding.projectTrace (sourceOf P).rap (extraOf P) Qm with hQ
  -- the predecessor row `i` with `i₀ = i + 1`
  obtain ⟨i, hi, rfl⟩ : ∃ (i : Fin P.optimized.family.problem.cfg.memRows)
      (hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.memRows), i₀ = ⟨(i : ℕ) + 1, hi⟩ := by
    refine ⟨⟨(i₀ : ℕ) - 1, by omega⟩, by simp; omega, ?_⟩
    apply Fin.ext; simp; omega
  -- the chain gate at row `i`, in both traces
  have hlang := expandChipTail_satisfies_iff_language (memorySourceTemplate P.optimized.basis)
    P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
    (rowNodeSet P.optimized.memoryNodes) 2
  rw [memCol0_eq] at hlang
  have hx : P.optimized.memoryNodes i ∈ rowNodeSet P.optimized.memoryNodes := by
    simp [rowNodeSet]
  have hmem : accStep (F := F) ∈
      (memorySourceTemplate (F := F) (K := K) P.optimized.basis).mixedTransition := by
    simp [memorySourceTemplate, mixedTransitionGates, paperKGates, paperKGatesCore, ioCoreGates]
  have hraw : (expandChipTail (memorySourceTemplate P.optimized.basis) P.optimized.basis
      P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes) 2).Satisfies Q := hsrc.1
  have hraw' : (expandChipTail (memorySourceTemplate P.optimized.basis) P.optimized.basis
      P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes) 2).Satisfies
        (shiftTrace P.optimized.memoryNodes ⟨(i : ℕ) + 1, hi⟩ δ Q) := hsrc'.1
  erw [hlang] at hraw hraw'
  have hgate : (accStep (F := F)).eval
      (gatherEnv P.optimized.basis memoryCol0
        (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
          P.optimized.memoryChallenge P.optimized.memoryPublic))
      (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
        P.optimized.memoryChallenge P.optimized.memoryPublic) = 0 :=
    (hraw _ hx).2.2.2 _ hmem
  have hgate' : (accStep (F := F)).eval
      (gatherEnv P.optimized.basis memoryCol0
        (envOfTrace (shiftTrace P.optimized.memoryNodes ⟨(i : ℕ) + 1, hi⟩ δ Q) P.optimized.orbit.ω
          (P.optimized.memoryNodes i) P.optimized.memoryChallenge P.optimized.memoryPublic))
      (envOfTrace (shiftTrace P.optimized.memoryNodes ⟨(i : ℕ) + 1, hi⟩ δ Q) P.optimized.orbit.ω
        (P.optimized.memoryNodes i) P.optimized.memoryChallenge P.optimized.memoryPublic) = 0 :=
    (hraw' _ hx).2.2.2 _ hmem
  -- the environments at row `i`
  obtain ⟨hcur, hnext⟩ := shifted_env_at_predecessor P Q i hi δ
  have h43 : (gatherEnv P.optimized.basis memoryCol0
      (envOfTrace (shiftTrace P.optimized.memoryNodes ⟨(i : ℕ) + 1, hi⟩ δ Q) P.optimized.orbit.ω
        (P.optimized.memoryNodes i) P.optimized.memoryChallenge P.optimized.memoryPublic)).trace 43 =
      (gatherEnv P.optimized.basis memoryCol0
        (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
          P.optimized.memoryChallenge P.optimized.memoryPublic)).trace 43 := by
    simp only [gatherEnv, memoryCol0]
    exact Finset.sum_congr rfl fun k _ => by rw [hcur]
  have h42 : (gatherEnv P.optimized.basis memoryCol0
      (envOfTrace (shiftTrace P.optimized.memoryNodes ⟨(i : ℕ) + 1, hi⟩ δ Q) P.optimized.orbit.ω
        (P.optimized.memoryNodes i) P.optimized.memoryChallenge P.optimized.memoryPublic)).trace 42 =
      (gatherEnv P.optimized.basis memoryCol0
        (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
          P.optimized.memoryChallenge P.optimized.memoryPublic)).trace 42 := by
    simp only [gatherEnv, memoryCol0]
    exact Finset.sum_congr rfl fun k _ => by rw [hcur]
  have hmoved := accStep_sees_next_row_shift P.optimized.basis _ _
    (gatherShift P.optimized.basis δ) h43 h42 hnext (hcur 5)
  rw [hgate, hgate', zero_add] at hmoved
  -- the mask at row `i` is zero: `i` is not the last row
  have hmask : (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
      P.optimized.memoryChallenge P.optimized.memoryPublic).trace 5 = 0 := by
    have hw : (sourceOf P).rap.w = 182 :=
      (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
        P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
    have h5 : (5 : ℕ) < (sourceOf P).rap.w := by rw [hw]; norm_num
    have hcol5 : Q ⟨5, h5⟩ = OptimizedMemoryCanonicalTrace.lastRowMask P.optimized.memoryNodes :=
      hsrc.2 ⟨1, by
        have hfc : (sourceOf P).fixedCount = 4 := rfl
        rw [hfc]; norm_num⟩
    simp only [envOfTrace, dif_pos h5]
    rw [hcol5, OptimizedMemoryCanonicalTrace.lastRowMask_eval _ P.optimized.memoryNodes_injective,
      if_neg (by omega)]
  rw [hmask, sub_zero, map_one, one_mul] at hmoved
  exact hδ hmoved.symm

/-- The honest trace is unaffected by the repair: the package's own canonical memory trace is
still accepted (no completeness cost), while its bumped versions are now rejected. -/
theorem canonical_trace_accepted_and_bumped_rejected [Fintype F] [DecidableEq F] 
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent)
    (i₀ : Fin P.optimized.family.problem.cfg.memRows) (hi₀ : (i₀ : ℕ) ≠ 0)
    (δ : Fin 3 → F) (hδ : gatherShift P.optimized.basis δ ≠ 0) :
    RAP.SatisfiesWithPreprocessing P.memoryChip (canonicalMemoryTrace P) ∧
      ¬ RAP.SatisfiesWithPreprocessing P.memoryChip
        (shiftTrace P.optimized.memoryNodes i₀ δ (canonicalMemoryTrace P)) :=
  ⟨canonicalMemoryTrace_satisfies P hmore hC,
    repaired_chip_rejects_shifted_accumulator P (canonicalMemoryTrace P)
      (canonicalMemoryTrace_satisfies P hmore hC) i₀ hi₀ δ hδ⟩

/-- A nonzero `δ` gathers to a nonzero `𝕂` value (the basis is a basis), so the rejection
theorem is not vacuous in `hδ`. -/
theorem gatherShift_ne_zero (b : Basis (Fin 3) F K) (δ : Fin 3 → F) (hδ : δ ≠ 0) :
    gatherShift b δ ≠ 0 := by
  intro h0
  apply hδ
  funext k
  have := congrArg (fun x => coord b x k) h0
  simpa [gatherShift, coord_sum_smul, coord_zero] using this

end Deployed

end

end Nock.RedTeam.Batch266

#print axioms Nock.RedTeam.Batch266.ext_gates_blind
#print axioms Nock.RedTeam.Batch266.base_gates_blind
#print axioms Nock.RedTeam.Batch266.equality_checks_blind
#print axioms Nock.RedTeam.Batch266.other_mixed_gates_blind
#print axioms Nock.RedTeam.Batch266.accChain_sees_next_row_shift
#print axioms Nock.RedTeam.Batch266.repaired_chip_rejects_shifted_accumulator
#print axioms Nock.RedTeam.Batch266.canonical_trace_accepted_and_bumped_rejected
#print axioms Nock.RedTeam.Batch266.gatherShift_ne_zero
