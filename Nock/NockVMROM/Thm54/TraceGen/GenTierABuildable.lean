/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierABuildable.lean

  Fourteen-field `BuildableNockExecution` on AIR-ordered `DotConfig769`.
  Semantic CORE from `semanticData` / `memoryTrace`; the remaining twelve
  fields are the threaded-carrier side-obligations (`q = 769`, `Λ = 22`,
  request/response length 13, orbit `2^8 = 256`).

  HonestCommitment.Data / Inputs are not claimed here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemoryTrace
import Nock.NockVMROM.Thm54.BuildableExecution

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

noncomputable def dotBuildable
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    BuildableNockExecution F K where
  q := 769
  q_gt_one := q_gt_one
  Λ := Λ
  cfg := cfg seedZ alphaA
  execA := execThreadedA seedZ alphaA
  exec := execThreaded seedZ alphaA
  exec_encode := rfl
  semanticData := semanticData hfirst
  memoryTrace := memoryTrace hfirst
  requestNodup := requestNodup_threaded
  recordCountBalance := recordCountBalance_threaded seedZ alphaA
  q_le_ringChar := q_le_ringChar
  two_ne_zero := two_ne_zero
  Ksz_lt_ringChar := Ksz_lt_ringChar seedZ alphaA
  programIOCapacity := programIOCapacity_threaded
  memoryIOCapacity := memoryIOCapacity_threaded

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.dotBuildable
