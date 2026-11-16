/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/OptimizedMemoryHostileAccumulator.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/OptimizedMemoryHostileAccumulator.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

namespace Nock.NockVMROM.Thm54

namespace OptimizedMemoryHostileAccumulator

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open OptimizedMemoryGateBasis
open StrictExtension
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem ioCore_mem_mixed (b : Basis (Fin 3) F K) {g : MixedExpr F}
    (hg : g ∈ ioCoreGates (F := F)) :
    g ∈ mixedTransitionGates (K := K) b := by
  simp [mixedTransitionGates, paperKGates, paperKGatesCore, hg]

theorem accInit_mem (b : Basis (Fin 3) F K) :
    accInit (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates])

theorem accTerminal_mem (b : Basis (Fin 3) F K) :
    accTerminal (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates])

theorem accStep_mem (b : Basis (Fin 3) F K) :
    accStep (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates])

theorem contribution_mem (b : Basis (Fin 3) F K) :
    contribution (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates])

theorem verBool_mem (b : Basis (Fin 3) F K) :
    verBool (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates])

theorem safeNormalisation_mem (b : Basis (Fin 3) F K) :
    safeNormalisation (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates])

theorem safeInverse_mem (b : Basis (Fin 3) F K) :
    safeInverse (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates])

theorem denominatorPinMixed_mem (b : Basis (Fin 3) F K) :
    denominatorPinMixed (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates, denominatorPin])

/-- The sampled coins as the memory row reads them: `γ` is memory `𝕂` challenge slot `4`, the
pole slot `5` (`OptimizedProductionAcceptanceAt.memory_sampled_coins`).  The memory twin of
`OptimizedComputeHostileAccumulator.rowCoins`. -/
def memRowCoins (envK : Env K) : FiniteIO.IOCoins K := ⟨envK.chal 4, envK.chal 5⟩

/-- The nine-scalar response record of the row, read off extension roles `19..26`
plus `C'` at role `57` (`NockVM.encRec` 9-wide under `memorySubst`).  The memory twin of
`OptimizedComputeHostileAccumulator.rowRecord`. -/
def memRowRecord (envK : Env K) : Fin 9 → K :=
  fun c => if (c : ℕ) < 8 then envK.trace (19 + (c : ℕ)) else envK.trace 57

/-- The ten-scalar record of the row: `memRowRecord` with the base-field exponent
carrier `reqIdx` (physical column `reqIdxCol = 181`) as tenth slot. -/
def memRowRecord10 (envK : Env K) (envF : Env F) : Fin 10 → K :=
  RecordCarrier.withExp (memRowRecord envK) (algebraMap F K (envF.trace 181))

/-- The upstream hostile record (`HostileRecordLists`) is `memRowRecord10`. -/
theorem rowRecord_eq_memRowRecord10 (envK : Env K) (envF : Env F) :
    rowRecord envK envF = memRowRecord10 envK envF := by
  funext c
  refine Fin.lastCases ?_ (fun c => ?_) c
  · simp [rowRecord, memRowRecord10, RecordCarrier.withExp_last]
  · have hc := c.isLt
    by_cases h8 : (c : ℕ) < 8
    · simp [rowRecord, memRowRecord10, memRowRecord, h8]
    · have : (c : ℕ) = 8 := by omega
      simp [rowRecord, memRowRecord10, memRowRecord, h8, this]

omit [FiniteDimensional F K] in
theorem denominatorPin_eval_iff (envK : Env K) (envF : Env F) :
    (denominatorPinMixed (F := F)).eval envK envF = 0 ↔
      envK.trace 37 = FiniteIO.compress (memRowCoins envK) (memRowRecord10 envK envF) := by
  rw [memRowRecord10, FiniteIO.compress, RecordCarrier.rlc_withExp]
  simp only [denominatorPinMixed, recordRLC, reqIdxRLCTerm, reqIdxCol, recordRLCExpr,
    MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval, memRowCoins, memRowRecord, Walk.rlc,
    Fin.sum_univ_succ, Fin.sum_univ_zero, sub_eq_zero, bcur, CoeffExpr.eval]
  constructor <;> intro h <;> rw [h] <;> simp <;> ring

/-- One row's response-side log-derivative contribution as the chip commits it: `ver · denom⁻¹`
(role `39` times the inverse of role `37`). -/
def memRowTerm (envK : Env K) : K := envK.trace 39 * (envK.trace 37)⁻¹

/-- Same identity from the committed paper IO gates. -/
theorem contribution_eq_memRowTerm_of_io (envK : Env K) (envF : Env F)
    (hver : (verBool (F := F)).eval envK envF = 0)
    (hnorm : (safeNormalisation (F := F)).eval envK envF = 0)
    (hinv : (safeInverse (F := F)).eval envK envF = 0)
    (hcontrib : (contribution (F := F)).eval envK envF = 0) :
    envK.trace 42 = memRowTerm envK := by
  simp only [verBool, safeNormalisation, safeInverse, contribution, MixedExpr.eval,
    sub_eq_zero, mul_eq_zero, Int.cast_one] at hver hnorm hinv hcontrib
  rw [memRowTerm, hcontrib]
  rcases hver with hv | hv
  · rw [hv]; simp
  · rw [hv] at hnorm ⊢
    simp only [one_mul, sub_self, add_zero] at hnorm
    rw [hnorm] at hinv
    simpa [one_mul] using eq_inv_of_mul_eq_one_right hinv

end

end OptimizedMemoryHostileAccumulator

end Nock.NockVMROM.Thm54
