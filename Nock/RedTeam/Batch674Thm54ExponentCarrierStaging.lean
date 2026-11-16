/-
  Nock/RedTeam/Batch674Thm54ExponentCarrierStaging.lean

  **C6 and the numerals of the THIRTY-FIRST move (lane `exponent-carrier`).**

  * **C6 (B1 staging)**: the memory carrier `reqIdx` (physical memory column `181`, the new last
    source column; old width `204`) and the compute carrier `S` (physical compute column `302`, old
    width `302`) are round-`0` columns, committed before `z`, `α` and `λ`
    (`DeployedStaging.carrier_columns_round_zero`; maps extended to `303` / `205`).
  * **Degrees**: the two carrier gates have degree `≤ 2` (a degree-`1` body under a preprocessing
    mask; the endpoint/step buckets, `computeDegreeOneGates 6e + 1`); the memory record RLC keeps
    trace degree `1` (`denominatorPinMixed` degree `1`, `paperAggregator` degree `2`) — the tenth
    slot is `γ⁹ · algebraMap reqIdx`, a degree-`1` base column times a coin.
-/
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.MixedMemoryGates
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch674

open Nock.NockVMROM.Thm54

/-- **C6.** -/
theorem carrier_columns_round_zero :
    DeployedStaging.memoryColRound OptimizedMemoryGateBasis.reqIdxCol = 0 ∧
      DeployedStaging.computeColRound OptimizedComputeCorrectedFinal.computeExpCol = 0 ∧
      DeployedStaging.memoryRoundFin ⟨OptimizedMemoryGateBasis.reqIdxCol, by decide⟩ = 0 ∧
      DeployedStaging.computeRoundFin ⟨OptimizedComputeCorrectedFinal.computeExpCol, by decide⟩ = 0 ∧
      ((DeployedStaging.deployedChronology.sampledAfter FormRAxisEvent.seedIdx : Fin 3) : ℕ) = 0 :=
  DeployedStaging.carrier_columns_round_zero

theorem carrier_columns : OptimizedMemoryGateBasis.reqIdxCol = 181 ∧
    OptimizedComputeCorrectedFinal.computeExpCol = 302 := ⟨rfl, rfl⟩

/-- The deployed numerals at every package. -/
theorem numerals {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb) :
    (P.computeChip.rap.w = 303 ∧ P.computeChip.rap.s = 418 ∧
        P.computeChip.rap.d = 4 ∧ P.computeChip.rap.k = 2) ∧
      (P.memoryChip.rap.w = 205 ∧ P.memoryChip.rap.s = 156 ∧
        P.memoryChip.rap.d = 4 ∧ P.memoryChip.rap.k = 1) ∧
      (P.computeChip.rap.s - 44 = 374 ∧ P.memoryChip.rap.s - 0 = 156) :=
  OptimizedStrictFullPackage.released_capstone_deployed_numerals P

/-- No coin: the challenge space is still `|𝕂|¹¹`. -/
theorem challenge_space (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) =
      Fintype.card K ^ 11 :=
  OptimizedStrictPackage.card_optimizedProductionChallengeTuple K F

/-- The two carrier gates have degree `≤ 2`. -/
theorem carrier_gate_degrees {F : Type} [Field F] :
    ∀ g ∈ OptimizedComputeCorrectedFinal.computeExpGates (F := F), g.degree ≤ 2 :=
  OptimizedComputeCorrectedFinal.computeExpGates_degree

/-- The memory record RLC keeps its trace degree: the pin is degree `1`, the aggregator `2`. -/
theorem memory_rlc_degrees {F : Type} [Field F] :
    (OptimizedMemoryGateBasis.denominatorPinMixed (F := F)).degree = 1 ∧
      (MemoryPaperFactorization.paperAggregator (F := F)).degree = 2 :=
  ⟨MixedMemoryGates.denominatorPinMixed_degree, MemoryPaperFactorization.paperAggregator_degree⟩

/-- The compute resource counters at `e = 3`. -/
theorem compute_counters :
    Thm54Resources.computeColumns 3 = 303 ∧ Thm54Resources.computeConstraints 3 = 418 ∧
      Thm54Resources.computeDegreeOneGates 3 = 19 ∧
      Thm54Resources.memoryColumns 3 = 205 ∧ Thm54Resources.memoryConstraints 3 = 156 := by
  decide

end Nock.RedTeam.Batch674

#print axioms Nock.RedTeam.Batch674.carrier_columns_round_zero
#print axioms Nock.RedTeam.Batch674.numerals
#print axioms Nock.RedTeam.Batch674.memory_rlc_degrees
