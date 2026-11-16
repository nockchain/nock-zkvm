/-
  Nock/NockVMROM/Thm54/P8Core/Batch773Thm54ExpOfRequestList.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch773Thm54ExpOfRequestList`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch773Thm54ExpOfRequestList.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch772Thm54RequestIndex
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch773

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.RedTeam.Batch772
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open scoped Polynomial

noncomputable section

theorem bfs_labels_mapNTree {α β : Type} (f : α → β) (t : NTree α) :
    (bfsForest [mapNTree f t]).map NTree.label = ((bfsForest [t]).map NTree.label).map f := by
  have h := bfsForest_mapNTree f [t]
  rw [List.map_singleton] at h
  rw [h, List.map_map, List.map_map]
  exact List.map_congr_left (fun x _ => mapNTree_label f x)

end

end Nock.RedTeam.Batch773
