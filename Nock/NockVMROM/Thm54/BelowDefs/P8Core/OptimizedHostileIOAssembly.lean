/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/OptimizedHostileIOAssembly.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/OptimizedHostileIOAssembly.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedComputeHostileAccumulator

namespace Nock.NockVMROM.Thm54

namespace OptimizedHostileIOAssembly

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates
open OptimizedComputeSameExecution
open OptimizedComputeSampledTrace
open OptimizedComputeCanonicalSatisfaction
open StrictExtension
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F]
  [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}

omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- The request-side list sum in the `Fin`-indexed form `finiteIO_sound_of_identity` uses. -/
theorem sum_requests_eq_sum_fin {m : ℕ} (records : FiniteIO.PreChallengeRecords K m)
    (coins : FiniteIO.IOCoins K) :
    ((records.requests.map fun r => (FiniteIO.compress coins r)⁻¹).sum) =
      ∑ i, (coins.pole + FiniteIO.reqVals records coins.gamma i)⁻¹ := by
  rw [← Fin.sum_univ_fun_getElem]
  rfl

omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- The response-side list sum, likewise. -/
theorem sum_responses_eq_sum_fin {m : ℕ} (records : FiniteIO.PreChallengeRecords K m)
    (coins : FiniteIO.IOCoins K) :
    ((records.responses.map fun r => (FiniteIO.compress coins r)⁻¹).sum) =
      ∑ j, (coins.pole + FiniteIO.respVals records coins.gamma j)⁻¹ := by
  rw [← Fin.sum_univ_fun_getElem]
  rfl

end

end OptimizedHostileIOAssembly

end Nock.NockVMROM.Thm54
