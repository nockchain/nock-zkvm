/-
  Nock/NockVMROM/Thm54/P8Core/Batch1110Thm54C2CombinedInduction.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1110Thm54C2CombinedInduction`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1110Thm54C2CombinedInduction.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1023Thm54S3PairMismatch
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1110

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding
variable {K : Type} [Field K] [DecidableEq K] [Fintype K] [CharP K (ringChar K)]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-- **The census oracle**: every comparison of the node with both sides in the window separates. -/
def CensusOK (z : K) (Λ : ℕ) (v : ComputeRowSkeleton) : Prop :=
  ∀ c ∈ P8Census.skeletonComparisons (K := K) v, c.left.leaves ≤ Λ → c.right.leaves ≤ Λ →
    SepSeed z c.left c.right

/-- **The size-window oracle**: every required size-window noun of the node in the window has it. -/
def WindowOK (z : K) (Λ : ℕ) (v : ComputeRowSkeleton) : Prop :=
  ∀ n ∈ SizeWindowCounting.requiredSizeWindowNouns v, n.leaves ≤ Λ →
    OpcodeSemantics.SizeWindow z n

end Nock.RedTeam.Batch1110
