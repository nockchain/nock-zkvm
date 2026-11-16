/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/OptimizedComputeHostileAccumulator.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/OptimizedComputeHostileAccumulator.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.MemoryFactorizationScope
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction

namespace Nock.NockVMROM.Thm54

namespace OptimizedComputeHostileAccumulator

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates
open OptimizedComputeSemanticRealization
open StrictExtension
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Typed form of `isFirst · acc`. -/
def accInitTyped : CorrectedFinalTypedExpr := (correctedLowerFinal finalAccInit).getD (.const 0)

/-- Typed form of `isLast · (acc_after − requests)`. -/
def accTerminalTyped : CorrectedFinalTypedExpr :=
  (correctedLowerFinal finalAccTerminal).getD (.const 0)

theorem lower_accInit : correctedLowerFinal finalAccInit = some accInitTyped := by decide

theorem lower_accTerminal : correctedLowerFinal finalAccTerminal = some accTerminalTyped := by
  decide

theorem anchors_mem_endpoint2 :
    accInitTyped ∈ correctedEndpoint2 ∧ accTerminalTyped ∈ correctedEndpoint2 := by
  constructor <;>
  · rw [correctedEndpoint2, List.mem_filterMap]
    first
    | exact ⟨finalAccInit, by simp, lower_accInit⟩
    | exact ⟨finalAccTerminal, by simp, lower_accTerminal⟩

theorem accInit_eval (env : CorrectedFinalTypedEnv F K) :
    accInitTyped.eval env = algebraMap F K (env.baseTrace 11) * env.extTrace 32 := by
  rw [← correctedLowerFinal_eval env _ _ lower_accInit]
  simp [finalAccInit, OptimizedComputeTemplate.fixedIsFirst, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv]

theorem accTerminal_eval (env : CorrectedFinalTypedEnv F K) :
    accTerminalTyped.eval env =
      algebraMap F K (env.baseTrace 12) * (env.extTrace 60 - env.extensionPublic 2) := by
  rw [← correctedLowerFinal_eval env _ _ lower_accTerminal]
  simp [finalAccTerminal, OptimizedComputeTemplate.fixedIsLast, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv, accAfterIndex]

/-- The committed inactive-safe denominator witness of slot `j` (extension roles `33..35`). -/
def safeDenomWitness (env : CorrectedFinalTypedEnv F K) (j : Fin 3) : K :=
  env.extTrace ⟨33 + (j : ℕ), by omega⟩

theorem source_trace_ext (env : CorrectedFinalTypedEnv F K) (i : Fin 63) :
    env.toSourceEnv.trace (13 + (i : ℕ)) = env.extTrace i := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp

/-- **The anchored step, read at the `𝕂` level.**  On any typed environment the committed
`aux[2]` gate is the `FoldedProgStep3` relation between `acc` (role `32`), `acc_after` (role
`60`), the three safe denominator witnesses and the three activity masks. -/
theorem correctedAccAfterStep_eval_iff (env : CorrectedFinalTypedEnv F K) :
    correctedAccAfterStep.eval env = 0 ↔
      FoldedProgStep3 (env.extTrace 32) (env.extTrace 60)
        (safeDenomWitness env 0) (safeDenomWitness env 1) (safeDenomWitness env 2)
        (activeMask env 0) (activeMask env 1) (activeMask env 2) := by
  rw [← correctedLowerFinal_eval env _ _ correctedLowerFinal_accAfterStep, finalAccAfterStep,
    Expr.eval_subst, optimizedAccAfterStep_eval]
  set E := env.toSourceEnv with hE
  have hacc : (sampledIOSubst .traceCur 0).eval (Env.ofSubst finalSampledNamespace E) =
      env.extTrace 32 := by
    change (Expr.Var .traceCur (13 + 32)).eval E = _
    simp only [Expr.eval]
    exact source_trace_ext env 32
  have hafter : (Env.ofSubst finalSampledNamespace E).trace accAfterIndex = env.extTrace 60 := by
    change E.trace (13 + 60) = _
    exact source_trace_ext env 60
  have h1 : (sampledIOSubst .traceCur 1).eval (Env.ofSubst finalSampledNamespace E) =
      safeDenomWitness env 0 := by
    change (Expr.Var .traceCur (13 + 33)).eval E = _
    simp only [Expr.eval]
    exact source_trace_ext env 33
  have h2 : (sampledIOSubst .traceCur 2).eval (Env.ofSubst finalSampledNamespace E) =
      safeDenomWitness env 1 := by
    change (Expr.Var .traceCur (13 + 34)).eval E = _
    simp only [Expr.eval]
    exact source_trace_ext env 34
  have h3 : (sampledIOSubst .traceCur 3).eval (Env.ofSubst finalSampledNamespace E) =
      safeDenomWitness env 2 := by
    change (Expr.Var .traceCur (13 + 35)).eval E = _
    simp only [Expr.eval]
    exact source_trace_ext env 35
  have h4 : (sampledIOSubst .traceCur 4).eval (Env.ofSubst finalSampledNamespace E) =
      activeMask env 0 := rfl
  have h5 : (sampledIOSubst .traceCur 5).eval (Env.ofSubst finalSampledNamespace E) =
      activeMask env 1 := rfl
  have h6 : (sampledIOSubst .traceCur 6).eval (Env.ofSubst finalSampledNamespace E) =
      activeMask env 2 := rfl
  rw [hacc, hafter, h1, h2, h3, h4, h5, h6]

/-- The semantic denominator of slot `j`, `pole + RLC^γ(recordⱼ)`, reconstructed from the row's
own record columns through the source decoder (`sampledDenom`, `computeTraceSubst`), in the
production challenge namespace. -/
def slotDenominator (env : CorrectedFinalTypedEnv F K) (j : Fin 3) : K :=
  ((sampledDenom .traceCur j).subst finalSampledNamespace).eval env.toSourceEnv

theorem finalExtTransitionGates_get_pin (j : Fin 3) :
    finalExtTransitionGates.get ⟨((⟨78 + (j : ℕ), by have := j.isLt; omega⟩ :
        CorrectedCoreExtGateId) : ℕ), by have := j.isLt; simp; omega⟩ =
      (sampledDenomPin .traceCur j).subst finalSampledNamespace := by
  fin_cases j <;> decide

/-- The denominator pin at the source level. -/
theorem denomPin_source_iff (env : CorrectedFinalTypedEnv F K) (j : ℕ) (hj : j < 3) :
    ((sampledDenomPin .traceCur j).subst finalSampledNamespace).eval env.toSourceEnv = 0 ↔
      safeDenomWitness env ⟨j, hj⟩ =
        SafeDenom (activeMask env ⟨j, hj⟩) (slotDenominator env ⟨j, hj⟩) := by
  rw [Expr.eval_subst]
  set E := env.toSourceEnv with hE
  have ha : (sampledActive .traceCur j).eval (Env.ofSubst finalSampledNamespace E) =
      activeMask env ⟨j, hj⟩ := by
    interval_cases j <;> rfl
  have hd : (sampledDenom .traceCur j).eval (Env.ofSubst finalSampledNamespace E) =
      slotDenominator env ⟨j, hj⟩ := by
    rw [slotDenominator, Expr.eval_subst]
  have hw : (sampledDenomWitness .traceCur j).eval (Env.ofSubst finalSampledNamespace E) =
      safeDenomWitness env ⟨j, hj⟩ := by
    interval_cases j
    · change (Expr.Var .traceCur (13 + 33)).eval E = _
      simp only [Expr.eval]
      exact source_trace_ext env 33
    · change (Expr.Var .traceCur (13 + 34)).eval E = _
      simp only [Expr.eval]
      exact source_trace_ext env 34
    · change (Expr.Var .traceCur (13 + 35)).eval E = _
      simp only [Expr.eval]
      exact source_trace_ext env 35
  simp only [sampledDenomPin, sampledSafeDenom, Expr.eval, hw, ha, hd, SafeDenom, sub_eq_zero,
    Int.cast_one]

/-- **The denominator pin, read at the `𝕂` level.**  Committed gate `78 + j` says the safe
denominator witness of slot `j` is `aⱼ · (pole + RLC^γ(recordⱼ)) + (1 − aⱼ)`. -/
theorem denomPin_eval_iff (env : CorrectedFinalTypedEnv F K) (j : Fin 3) :
    (correctedFinalExtGate ⟨78 + (j : ℕ), by have := j.isLt; omega⟩).eval env = 0 ↔
      safeDenomWitness env j = SafeDenom (activeMask env j) (slotDenominator env j) := by
  rw [← correctedFinalExtGate_eval_source, finalExtTransitionGates_get_pin]
  exact denomPin_source_iff env j j.isLt

/-- The sampled coins as the row reads them: `γ` is challenge `7`, the pole challenge `8`
(`finalSampledGamma`/`finalSampledPole`). -/
def rowCoins (env : CorrectedFinalTypedEnv F K) : FiniteIO.IOCoins K :=
  ⟨env.toSourceEnv.chal 7, env.toSourceEnv.chal 8⟩

/-- **The slot denominator is the compression of the row's record with the row's coins**:
`pole + RLC^γ(recordⱼ)`. -/
theorem slotDenominator_eq_compress (env : CorrectedFinalTypedEnv F K) (j : Fin 3) :
    slotDenominator env j = FiniteIO.compress (rowCoins env) (rowRecord env j) := by
  simp only [slotDenominator, FiniteIO.compress, rowCoins, Walk.rlc, rowRecord,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases j <;>
    simp [sampledDenom, sampledRecordRLC, sampledPole, sampledGamma, finalSampledNamespace,
      finalSampledPole, finalSampledGamma, sampledChallenge, sampledChallengeBase,
      List.range_succ, Expr.subst, Expr.eval, Expr.eval_subst, Env.ofSubst] <;>
    ring

/-- One row's log-derivative contribution as the chip commits it: `Σⱼ aⱼ · dⱼ⁻¹`. -/
def rowTerm (env : CorrectedFinalTypedEnv F K) : K :=
  activeMask env 0 * (safeDenomWitness env 0)⁻¹ +
    activeMask env 1 * (safeDenomWitness env 1)⁻¹ +
    activeMask env 2 * (safeDenomWitness env 2)⁻¹

/-- Under nonzero safe denominators the step says exactly `acc_after = acc + rowTerm`. -/
theorem accAfter_eq_of_step (env : CorrectedFinalTypedEnv F K)
    (hstep : correctedAccAfterStep.eval env = 0)
    (hd : ∀ j : Fin 3, safeDenomWitness env j ≠ 0) :
    env.extTrace 60 = env.extTrace 32 + rowTerm env := by
  have h := (correctedAccAfterStep_eval_iff env).1 hstep
  rw [foldedProgStep3_iff _ _ _ _ _ _ _ _ (hd 0) (hd 1) (hd 2)] at h
  simpa [rowTerm, add_assoc] using h

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}

/-- The paper-form row term `Σⱼ aⱼ / (pole + RLC^γ(recordⱼ))`. -/
def logUpRowTerm (env : CorrectedFinalTypedEnv F K) : K :=
  activeMask env 0 * (slotDenominator env 0)⁻¹ +
    activeMask env 1 * (slotDenominator env 1)⁻¹ +
    activeMask env 2 * (slotDenominator env 2)⁻¹

/-- The free opcode selector read off a gathered row, as a `State`-indexed vector in `𝕂`. -/
def rowSelector (env : CorrectedFinalTypedEnv F K) : Nock.ComputeTable.State → K :=
  fun st => algebraMap F K (env.baseTrace ⟨Nock.Reified.opCol st, by cases st <;> decide⟩)

end Deployed

end

end OptimizedComputeHostileAccumulator

end Nock.NockVMROM.Thm54
