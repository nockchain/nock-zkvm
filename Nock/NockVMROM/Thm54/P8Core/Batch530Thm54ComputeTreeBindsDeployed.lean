/-
  Nock/NockVMROM/Thm54/P8Core/Batch530Thm54ComputeTreeBindsDeployed.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch530Thm54ComputeTreeBindsDeployed`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch530Thm54ComputeTreeBindsDeployed.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch525Thm54ComputeTreeBinds
import Nock.NockVMROM.Thm54.P8Core.ExecOfTraces
import Nock.NockVMROM.Thm54.P8Core.Batch516Thm54ComputeJoinSound
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch530

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ExecOfTraces
open scoped Polynomial
open Polynomial
open Nock.RedTeam.Batch525
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.GlobalCarryRecognizer
variable {K : Type} [Field K] [DecidableEq K]

theorem ntree_size_pos {α : Type*} (t : NTree α) : 1 ≤ t.size := by
  cases t
  simp [NTree.size]

theorem child_size_le_of_node {α : Type*} {row : α}
    {ch : List (NTree α)} {c : NTree α} {k : ℕ}
    (hk : (NTree.node row ch).size ≤ k + 1) (hc : c ∈ ch) :
    c.size ≤ k := by
  have hsz : (NTree.node row ch).size = 1 + (ch.map NTree.size).sum := by
    simp [NTree.size]
  have hmem : c.size ∈ ch.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
  have : c.size ≤ (ch.map NTree.size).sum := List.le_sum_of_mem hmem
  omega

end Nock.RedTeam.Batch530
