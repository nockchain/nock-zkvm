/-
  Nock/RedTeam/Batch1010Thm54AxisViewMemoryTreeBinds.lean

  Additive; generic in the forest.

  But `ProductionStrategy.BindsAtCoin` reads the ROW-LEVEL
  `SemanticStrategy.MemoryTreeBinds` / `BindMemoryRow` / `BindMemRow` on the encoded execution: the
  executed row stores `axis = formRT λ (nockAxisOf s.axis)`, `cprime = formRC λ (nockAxisOf s.axis)`
  with `s.axis` the skeleton's Nock axis.

  **`memoryTreeBinds_of_topologyA`** is `memoryTreeBinds_of_topology'` with
  * the decoder `StrategyOfTracesR0A.decodeMemoryTreeAx q forest ax` (record axis SUPPLIED by `ax`),
  * the axis premise `haxisA`: on every active node the stored `(T, C')` are the Form R encode of
    `ax node.label` at the row's own `λ` — the a-bearing axis, not the stored `T`,
  * the conclusion the row-level `MemoryTreeBinds` that `BindsAt.memoryForest` reads;
  every other premise (`hz`, `htop`, `hseed`, `hleaves`, `hver`, `hservedChild`, `hservedRoot`,
  `hstructF`) unchanged.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0A
import Nock.RedTeam.Batch524Thm54DecodeMemoryRowIn
import Nock.NockVMROM.Thm54.P8Core.Batch1010Thm54AxisViewMemoryTreeBinds

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1010

open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.RedTeam.Batch516 (ServedFingerprint)
open Nock.RedTeam.Batch524 (ForestFPFacts bindFP_of_nounByFP_hit bindFP_halt_parent)
open scoped Classical

variable {K : Type} [Field K] [DecidableEq K]

/-! ## A. The node facts -/

/-! ## B. The active record clause -/

/-! ## C. -/

/-! ## D. Tree and forest form -/

/-! ## E. `hstructF` and `hleaves` from the structure plus the halt leaves -/

end Nock.RedTeam.Batch1010

#print axioms Nock.RedTeam.Batch1010.bindMemRow_readRoot_of_fill
#print axioms Nock.RedTeam.Batch1010.bindMemoryRow_readRoot
#print axioms Nock.RedTeam.Batch1010.bindMemoryRow_verifyChild
#print axioms Nock.RedTeam.Batch1010.memoryTreeBinds_of_fillA
#print axioms Nock.RedTeam.Batch1010.memoryTreeBinds_of_topologyA
#print axioms Nock.RedTeam.Batch1010.memoryForestBinds_of_topologyA
#print axioms Nock.RedTeam.Batch1010.forestFPFacts_of_topology
