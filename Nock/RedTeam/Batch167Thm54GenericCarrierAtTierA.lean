/-
  Nock/RedTeam/Batch167Thm54GenericCarrierAtTierA.lean

  **The generic carrier's measurements are the live configuration's literals.**

  `genExactConfig` *defines* `kMem`, `compRows` and `memRows` as the generated
  trace's own counts, where `DotConfig769.cfg` hard-codes `10`, `8` and `184` and its
  `execThreaded` then proves the three length obligations at those literals
  (`GenTierAConfig769.lean:88`, `GenTierAMemAccept.lean:1044`).

  If the two disagreed, the generic carrier would be measuring something other than what the live
  configuration commits, and everything built on it downstream would be about the wrong object.
  This checks they agree, at Tier A's own inputs, with `genExactConfig` actually applied — so the
  side conditions (`hmempos`, `hcomp`, `hmem`) have to be dischargeable there too, which is itself
  part of the claim.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenExactExecution
import Nock.NockVMROM.Thm54.TraceGen.GenTierAHonestData
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.RedTeam.Batch167

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54

/-- Tier A's compute tree, before the row projection. -/
noncomputable def tierACompute : NTree (GenComputeRow K) :=
  renderRows seedZ alphaA (bfsAssign (dotTreeAir))

/-- Tier A's memory forest, before the row projection. -/
noncomputable def tierAMemory : List (NTree (GenMemoryRow K)) :=
  threadedForest seedZ alphaA

/-! ## The three measurements -/

theorem tierA_compRows : (bfsForest [tierACompute]).length = 8 := by
  have h := (execThreaded seedZ alphaA).compute_bfs_length
  rw [show (execThreaded seedZ alphaA).computeTree
      = mapNTree GenComputeRow.row tierACompute from rfl,
    bfsForest_mapNTree_singleton, List.length_map] at h
  exact h

theorem tierA_memRows : (bfsForest tierAMemory).length = 184 := by
  -- a-bearing view (`execThreadedA`): the row count is encode-invariant (`encodeMem`).
  have h := (execThreadedA seedZ alphaA).memory_bfs_length
  rw [show (execThreadedA seedZ alphaA).memoryForest
      = tierAMemory.map (mapNTree GenMemoryRow.row) from rfl,
    bfsForest_mapNTree, List.length_map] at h
  exact h

theorem tierA_kMem : (tierAMemory).length = 10 :=
  threaded_kMem seedZ alphaA

/-! ## The side conditions are dischargeable at Tier A -/

theorem tierA_mempos : 0 < (bfsForest (tierAMemory)).length := by
  rw [tierA_memRows]; norm_num

theorem tierA_comp_le :
    (bfsForest [tierACompute]).length ≤ 2 ^ (executionOrbit).h := by
  rw [tierA_compRows]; norm_num [executionOrbit]

theorem tierA_mem_le :
    (bfsForest (tierAMemory)).length ≤ 2 ^ (executionOrbit).h := by
  rw [tierA_memRows]; norm_num [executionOrbit]

/-! ## The generic config at Tier A's inputs -/

/-- `genExactConfig` really applies at Tier A. -/
noncomputable def tierAGenCfg : ExactConfig DotConfig769.F DotConfig769.K :=
  genExactConfig (cfg seedZ alphaA).challenges 64
    executionOrbit (by norm_num [executionOrbit])
    tierACompute tierAMemory tierA_mempos tierA_comp_le tierA_mem_le

/-- **The measurements are the literals.**  Each is `rfl` against `genExactConfig`'s definition
composed with the theorem above, which is the point: what the configuration had to prove, the
generic carrier has by construction. -/
theorem tierAGenCfg_compRows : tierAGenCfg.compRows = 8 :=
  tierA_compRows

theorem tierAGenCfg_memRows : tierAGenCfg.memRows = 184 :=
  tierA_memRows

theorem tierAGenCfg_kMem : tierAGenCfg.kMem = 10 :=
  tierA_kMem

/-- And they are the live configuration's — **these three fields**, not all seventeen. -/
theorem tierAGenCfg_agrees :
    tierAGenCfg.compRows = (cfg seedZ alphaA).compRows ∧
      tierAGenCfg.memRows = (cfg seedZ alphaA).memRows ∧
      tierAGenCfg.kMem = (cfg seedZ alphaA).kMem :=
  ⟨tierAGenCfg_compRows, tierAGenCfg_memRows, tierAGenCfg_kMem⟩

end Nock.RedTeam.Batch167

#print axioms Nock.RedTeam.Batch167.tierA_compRows
#print axioms Nock.RedTeam.Batch167.tierA_memRows
#print axioms Nock.RedTeam.Batch167.tierAGenCfg_agrees
