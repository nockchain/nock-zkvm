/-
  Nock/RedTeam/Batch270Thm54UnboundMemoryDenominator.lean

  **The memory chip's response denominator is a free column: nothing binds role `37` to the row's
  record, and the memory chip reads no sampled coin.**  The paper's denominator is
  `RLC^α(x_mem(i,·)) − β`: a function of the row's memory record and the two
  sampled coins.  The compute chip has exactly that binding (the three denominator pins
  `correctedFinalExtGate 17..19`, `OptimizedComputeHostileAccumulator.denomPin_eval_iff`, which
  decode `pole + RLC^γ(recordⱼ)` from the row's own record columns through `computeTraceSubst`);
  the memory chip does not.

  Compiled here:

  * `role37_read_only_by_safe_normalisation` — of the fifty `transitionSources`, exactly one
    mentions `(traceCur, 37)`, and it is `sampledSources[4]`; `mixed_gates_off_role37`,
    `base_gates_off_role37` — no mixed gate and no committed base gate reads it either.
  * `memory_sources_read_no_sampled_coin` — every challenge index any transition source reads is
    one of `0, 1, 2` (the memory table's), `3` (the forest walk's) or `6` (the fold coin): the
    sampled `γ`/`pole` are not readable by the memory chip at all, so no gate *could* bind the
    denominator today.
  * `row_language_accepts_any_denominator` — at any row where all fifty sources vanish with
    `ver = 1` and `last = 0`, replacing the denominator by **any** nonzero `d'` (with the inverse,
    safe, contribution and `acc_after` columns adjusted accordingly) leaves all fifty sources
    vanishing.

  Consequence: `OptimizedMemoryHostileAccumulator.hostile_logUp_sums_agree` equates the compute
  side's `Σ 1/(pole + RLC^γ(record))` with a memory-side sum over prover-chosen denominators; the
  response **records** are not yet what is being counted.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch270

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Module

noncomputable section

local instance : FiniteDimensional (ZMod 31) (ZMod 31) := inferInstance

/-! ## A. Read sets -/

/-- Does an expression read `(traceCur, 37)`? -/
def readsRole37 (e : Expr) : Bool := decide ((VarKind.traceCur, 37) ∈ exprVariableSupport e)

/-- **Exactly one of the fifty transition sources mentions the response denominator**, and it is
the inactive-safe normalisation `safe = ver · denom + (1 − ver)`. -/
theorem role37_read_only_by_safe_normalisation :
    List.filter readsRole37 (transitionSources (K := ZMod 31)) =
      [.Sub (extVar .traceCur 50)
        (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37))
          (.Sub (.Const 1) (extVar .traceCur 39)))] := by
  set_option maxRecDepth 100000 in decide

/-- The challenge indices any transition source reads. -/
def challengeReads (e : Expr) : Finset ℕ :=
  (exprVariableSupport e).filter (fun v => v.1 = VarKind.challenge) |>.image Prod.snd

/-- **The memory chip reads no sampled coin**: every challenge index read by a transition source
is a memory-table coin (`0..2`), the forest coin (`3`) or the fold coin (`6`).  The sampled
`γ`/`pole` (compute challenges `7`/`8`) are not readable by the memory chip, so no committed
gate could bind role `37` to the row's record today. -/
theorem memory_sources_read_no_sampled_coin :
    ∀ e ∈ transitionSources (K := ZMod 31),
      challengeReads e ⊆ {0, 1, 2, 3, 4, 5, 6, 7, 8} := by
  set_option maxRecDepth 100000 in decide

/-- Does a mixed gate read extension role `r` at the current row? -/
def mixedReadsCur {F : Type} [Field F] : MixedExpr F → ℕ → Bool
  | .Var .traceCur i, r => decide (i = r)
  | .Var _ _, _ => false
  | .Lift _, _ => false
  | .Scale _ u, r => mixedReadsCur u r
  | .Const _, _ => false
  | .Add x y, r | .Sub x y, r | .Mul x y, r => mixedReadsCur x r || mixedReadsCur y r
  | .Neg x, r | .Pow x _, r => mixedReadsCur x r

/-- Since A-mem-2 the fifth mixed
gate, `denominatorPinMixed`, does — so this is now stated of the four gates other than the pin,
with `denominatorPin_reads_role37` as the positive control. -/
theorem mixed_gates_off_role37 {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) :
    ∀ g ∈ foldedMixedTransitionGates (F := F), g ≠ denominatorPinMixed → mixedReadsCur g 37 = false := by
  intro g hg hne
  simp only [foldedMixedTransitionGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hne
  · rfl

/-- **The repair, as a read-set fact**: the committed denominator pin reads role `37` — the
memory chip now has a second reader of the denominator beyond the safe normalisation. -/
theorem denominatorPin_reads_role37 {F : Type} [Field F] :
    mixedReadsCur (denominatorPinMixed (F := F)) 37 = true := rfl

/-- The challenge indices a mixed gate reads. -/
def mixedChallengeReads {F : Type} [Field F] : MixedExpr F → List ℕ
  | .Var .challenge i => [i]
  | .Var _ _ => []
  | .Lift _ => []
  | .Scale _ u => mixedChallengeReads u
  | .Const _ => []
  | .Add x y | .Sub x y | .Mul x y => mixedChallengeReads x ++ mixedChallengeReads y
  | .Neg x | .Pow x _ => mixedChallengeReads x

theorem denominatorPin_reads_sampled_coins {F : Type} [Field F] :
    mixedChallengeReads (denominatorPinMixed (F := F)) = [5, 4, 4, 4, 4, 4, 4, 4, 4, 4] := rfl

/-- Does a base gate read raw column `c`? -/
def coeffReadsCur {F : Type} [Field F] : CoeffExpr F → ℕ → Bool
  | .var .traceCur i, c => decide (i = c)
  | .var _ _, _ => false
  | .const _, _ => false
  | .add x y, c | .sub x y, c | .mul x y, c => coeffReadsCur x c || coeffReadsCur y c
  | .neg x, c => coeffReadsCur x c
  | .pow x _, c => coeffReadsCur x c

theorem terminalCoord_off_role37 {F : Type} [Field F] (j k : Fin 3) :
    coeffReadsCur (sampledTerminalCoord (F := F) j) (117 + (k : ℕ)) = false := by
  fin_cases j <;> fin_cases k <;> rfl

theorem accumulatorCoord_off_role37 {F : Type} [Field F] (j k : Fin 3) :
    coeffReadsCur (sampledAccumulatorCoord (F := F) j) (117 + (k : ℕ)) = false := by
  fin_cases j <;> fin_cases k <;> rfl

/-- No committed base gate reads the denominator's three columns `117..119`. -/
theorem base_gates_off_role37 {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) :
    ∀ g ∈ foldedBaseTransitionGates b, ∀ k : Fin 3, coeffReadsCur g (117 + (k : ℕ)) = false := by
  intro g hg k
  simp only [foldedBaseTransitionGates, semanticBaseTail, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_ofFn] at hg
  rcases hg with h | h | h
  · rcases h with rfl | rfl | rfl | rfl | rfl <;> fin_cases k <;>
      simp [coeffReadsCur, bbool, bcur, bsum4]
  · obtain ⟨j, hj⟩ := h
    rw [← hj]
    exact terminalCoord_off_role37 j k
  · obtain ⟨j, hj⟩ := h
    rw [← hj]
    exact accumulatorCoord_off_role37 j k

/-! ## B. The row language accepts any nonzero denominator -/

variable {K : Type} [Field K]

/-- Read a variable off an environment. -/
def envAt (env : Env K) : VarKind → ℕ → K
  | .traceCur, i => env.trace i
  | .traceNext, i => env.traceNext i
  | .challenge, i => env.chal i
  | .publicVal, i => env.pub i

theorem eval_eq_of_support_agree (env env' : Env K) :
    ∀ e : Expr, (∀ v ∈ exprVariableSupport e, envAt env' v.1 v.2 = envAt env v.1 v.2) →
      e.eval env' = e.eval env
  | .Const _, _ => rfl
  | .Var k i, h => by
      have := h (k, i) (by simp [exprVariableSupport])
      cases k <;> simpa [envAt, Expr.eval] using this
  | .Add x y, h => by
      simp only [exprVariableSupport, Finset.mem_union] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x (fun v hv => h v (Or.inl hv)),
        eval_eq_of_support_agree env env' y (fun v hv => h v (Or.inr hv))]
  | .Sub x y, h => by
      simp only [exprVariableSupport, Finset.mem_union] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x (fun v hv => h v (Or.inl hv)),
        eval_eq_of_support_agree env env' y (fun v hv => h v (Or.inr hv))]
  | .Mul x y, h => by
      simp only [exprVariableSupport, Finset.mem_union] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x (fun v hv => h v (Or.inl hv)),
        eval_eq_of_support_agree env env' y (fun v hv => h v (Or.inr hv))]
  | .Neg x, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x h]
  | .Pow x n, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x h]

/-- The five current-row roles the substitution touches. -/
def touched : Finset (VarKind × ℕ) :=
  {(VarKind.traceCur, 37), (VarKind.traceCur, 38), (VarKind.traceCur, 42),
    (VarKind.traceCur, 44), (VarKind.traceCur, 50)}

/-- The forty non-sampled sources read none of the five touched roles. -/
theorem nonSampled_sources_off_touched :
    ∀ e ∈ memoryRowSources (K := ZMod 31) ++ [memoryChainSource] ++
        walkBoundarySources ++ walkTransitionSources,
      ∀ v ∈ touched, v ∉ exprVariableSupport e := by
  set_option maxRecDepth 100000 in decide

/-- The row with denominator `d'`: `denom := d'`, `safe := d'`, `inv := d'⁻¹`,
`contribution := d'⁻¹`, `acc_after := acc_before + d'⁻¹`; every other variable unchanged. -/
def swapDenominator (env : Env K) (d' : K) : Env K where
  trace i :=
    if i = 37 then d' else if i = 50 then d' else if i = 38 then d'⁻¹
    else if i = 42 then d'⁻¹ else if i = 44 then env.trace 43 + d'⁻¹ else env.trace i
  traceNext := env.traceNext
  chal := env.chal
  pub := env.pub

theorem eval_swap_of_off (env : Env K) (d' : K) (e : Expr)
    (hoff : ∀ v ∈ touched, v ∉ exprVariableSupport e) :
    e.eval (swapDenominator env d') = e.eval env := by
  apply eval_eq_of_support_agree
  intro v hv
  rcases v with ⟨k, i⟩
  cases k
  · simp only [envAt, swapDenominator]
    have h37 : i ≠ 37 := fun h => hoff _ (by subst h; simp [touched]) hv
    have h38 : i ≠ 38 := fun h => hoff _ (by subst h; simp [touched]) hv
    have h42 : i ≠ 42 := fun h => hoff _ (by subst h; simp [touched]) hv
    have h44 : i ≠ 44 := fun h => hoff _ (by subst h; simp [touched]) hv
    have h50 : i ≠ 50 := fun h => hoff _ (by subst h; simp [touched]) hv
    simp [h37, h38, h42, h44, h50]
  all_goals rfl

/-- **Any nonzero denominator is accepted by the SOURCE row language** at a verifying, non-last
row. -/
theorem row_language_accepts_any_denominator (env : Env (ZMod 31))
    (hall : ∀ e ∈ transitionSources (K := ZMod 31), e.eval env = 0)
    (hver : env.trace 39 = 1) (hnotLast : env.trace 48 = 0)
    (d' : ZMod 31) (hd' : d' ≠ 0) :
    ∀ e ∈ transitionSources (K := ZMod 31),
      e.eval (swapDenominator env d') = 0 := by
  intro e he
  have he' := he
  change e ∈ memoryRowSources (K := ZMod 31) ++ [memoryChainSource] ++
      walkBoundarySources ++ walkTransitionSources ++ sampledSources at he
  simp only [List.mem_append] at he
  rcases he with hother | hs
  · rw [eval_swap_of_off env d' e (nonSampled_sources_off_touched e
      (by simpa [List.mem_append, or_assoc] using hother))]
    exact hall e he'
  · have h43 : (swapDenominator env d').trace 43 = env.trace 43 := by
      simp [swapDenominator]
    simp only [sampledSources, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact (eval_swap_of_off env d' _ (by decide)).trans (hall _ he')
      | (simp only [extVar, Expr.eval, swapDenominator, Int.cast_one, hver, hnotLast]
         simp [hd'])
      | (simp only [extVar, Expr.eval, swapDenominator, Int.cast_one, hver, hnotLast]
         ring)

/-- **The mixed bucket rejects the swap** (A-mem-2): at the swapped row the committed denominator
pin evaluates to `d' − denom`, so it vanishes iff `d' = denom` — the repair, at the row level
`row_language_accepts_any_denominator` works at.  The roles the swap touches (`38, 42, 44, 50`)
and the record roles `19..26` and coins are not what the pin reads, apart from role `37` itself. -/
theorem mixed_bucket_rejects_swapped_denominator {F : Type} [Field F] [Algebra F K]
    (env : Env K) (envF : Env F) (d' : K) :
    (denominatorPinMixed (F := F)).eval (swapDenominator env d') envF =
      (denominatorPinMixed (F := F)).eval env envF + (d' - env.trace 37) := by
  simp only [denominatorPinMixed, recordRLC, recordRLCExpr, reqIdxRLCTerm, MixedExpr.eval,
    MixedExpr.ofExpr_eval, Expr.eval, swapDenominator]
  norm_num

theorem swapped_denominator_rejected_iff {F : Type} [Field F] [Algebra F K]
    (env : Env K) (envF : Env F) (d' : K)
    (hpin : (denominatorPinMixed (F := F)).eval env envF = 0) :
    (denominatorPinMixed (F := F)).eval (swapDenominator env d') envF = 0 ↔ d' = env.trace 37 := by
  rw [mixed_bucket_rejects_swapped_denominator, hpin, zero_add, sub_eq_zero]

end

end Nock.RedTeam.Batch270

#print axioms Nock.RedTeam.Batch270.role37_read_only_by_safe_normalisation
#print axioms Nock.RedTeam.Batch270.memory_sources_read_no_sampled_coin
#print axioms Nock.RedTeam.Batch270.mixed_gates_off_role37
#print axioms Nock.RedTeam.Batch270.base_gates_off_role37
#print axioms Nock.RedTeam.Batch270.row_language_accepts_any_denominator
#print axioms Nock.RedTeam.Batch270.denominatorPin_reads_role37
#print axioms Nock.RedTeam.Batch270.denominatorPin_reads_sampled_coins
#print axioms Nock.RedTeam.Batch270.mixed_bucket_rejects_swapped_denominator
#print axioms Nock.RedTeam.Batch270.swapped_denominator_rejected_iff
