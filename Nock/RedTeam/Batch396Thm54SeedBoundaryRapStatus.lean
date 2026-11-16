/-
  Nock/RedTeam/Batch396Thm54SeedBoundaryRapStatus.lean

  **RAP-status of the seed-boundary finding**.

  This module records that a full
  `RAP.SatisfiesWithPreprocessing` attack is not compiled, and why the
  StrengtheningScope five-row witness is not itself that attack.
-/
import Nock.RedTeam.Batch395Thm54SeedBoundaryDeployed
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

set_option autoImplicit false

namespace Nock.RedTeam.Batch396

open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.RedTeam.Batch395

/-- `paperAggregator` is among the forty-five committed `𝕂`
gates.  The StrengtheningScope witness sets `ipre = icur = 0` on every row, so
on a `read_root` row the aggregator evaluates as `−1 ≠ 0`. -/
theorem paperAggregator_mem_paperKGates :
    paperAggregator (F := ℚ) ∈ paperKGates (F := ℚ) (K := ℚ) := by
  have hrap : paperAggregator (F := ℚ) ∈ rapMemGates (F := ℚ) (K := ℚ) := by
    simp [rapMemGates]
  have hcore : paperAggregator (F := ℚ) ∈ paperKGatesCore (F := ℚ) (K := ℚ) := by
    simp [paperKGatesCore, hrap]
  simpa [paperKGates] using
    List.mem_append_left _ (List.mem_append_left (paperEndpointGates (F := ℚ)) hcore)

/-- The only first-row `Scale` of roles `3`/`4`
is the in-gate walk boundary, which compares against the seed public — no committed ZERO pin
(`Batch395.no_committed_zero_pin`). -/
theorem gate_set_finding :
    (paperKGates (F := ℚ) (K := ℚ)).all (fun g => !isFirstRowAxisSeedPin g || readsSeedPublic g) = true ∧
      (tabVMemGates (F := ℚ) (K := ℚ)).any readsAxisAccumM = true :=
  ⟨no_committed_zero_pin, tabVMem_reads_axis_accumulators⟩

/-- A full `SatisfiesWithPreprocessing` counterexample at `P.memoryChip` is
**not compiled** in Batches 395–396. -/
def fullRapAttackCompiled : Bool := false

theorem fullRapAttackCompiled_is_false : fullRapAttackCompiled = false := rfl

#print axioms gate_set_finding
#print axioms paperAggregator_mem_paperKGates

end Nock.RedTeam.Batch396
