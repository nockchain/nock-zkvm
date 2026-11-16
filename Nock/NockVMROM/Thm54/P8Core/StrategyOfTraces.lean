/-
  Nock/NockVMROM/Thm54/P8Core/StrategyOfTraces.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.StrategyOfTraces`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/StrategyOfTraces.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.DeployedComputeRows
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding

namespace Nock.NockVMROM.Thm54.StrategyOfTraces

open scoped Classical Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Framework
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- Selector column of a compute state (`ComputeTable.toNat`, `s0…s9` then `cons` at 0).
Reconstruction without `hsat` prefers `s0` when column 0 is `1`. -/
def computeStateOf (env : Env K) : State :=
  if env.trace 1 = 1 then .s1
  else if env.trace 2 = 1 then .s2
  else if env.trace 3 = 1 then .s3
  else if env.trace 4 = 1 then .s4
  else if env.trace 5 = 1 then .s5
  else if env.trace 6 = 1 then .s6
  else if env.trace 7 = 1 then .s7
  else if env.trace 8 = 1 then .s8
  else if env.trace 9 = 1 then .s9
  else if env.trace 10 = 1 then .cons
  else .s0

/-- `pt.noun` is memory `𝕂` columns `0,1,2`. -/
def memoryPtNoun (envK : Env K) : FP K :=
  ⟨envK.trace 0, envK.trace 1, envK.trace 2⟩

/-- Served record halves after `memorySubst` (`AIR` cols `23..28` ↦ roles `19..24`):
root `19–21`, child `22–24`.  Same packing as `memRowRecord` / `recordRLCExpr`. -/
def memoryMemRoot (envK : Env K) : FP K :=
  ⟨envK.trace 19, envK.trace 20, envK.trace 21⟩

def memoryMemChild (envK : Env K) : FP K :=
  ⟨envK.trace 22, envK.trace 23, envK.trace 24⟩

def nounHead : Noun → Noun
  | .cell h _ => h
  | n => n

def nounTail : Noun → Noun
  | .cell _ t => t
  | n => n

end

end Nock.NockVMROM.Thm54.StrategyOfTraces
