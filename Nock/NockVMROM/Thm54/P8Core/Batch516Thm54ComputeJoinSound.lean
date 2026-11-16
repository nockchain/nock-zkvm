/-
  Nock/NockVMROM/Thm54/P8Core/Batch516Thm54ComputeJoinSound.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch516Thm54ComputeJoinSound`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch516Thm54ComputeJoinSound.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch515Thm54MemoryTreeBinds

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped Classical

namespace Nock.RedTeam.Batch516

open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch515
variable {K : Type} [Field K] [DecidableEq K]

noncomputable section

/-- A compute fingerprint is some forest node's committed `pt.noun`. -/
def ServedFingerprint (forest : List (NTree (MState × DTmem K)))
    (fp : FP K) : Prop :=
  ∃ t ∈ bfsForest forest, t.label.2.2.pt.noun = fp

end

end Nock.RedTeam.Batch516
