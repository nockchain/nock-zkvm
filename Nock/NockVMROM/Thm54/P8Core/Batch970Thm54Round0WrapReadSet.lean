/-
  Nock/NockVMROM/Thm54/P8Core/Batch970Thm54Round0WrapReadSet.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch970Thm54Round0WrapReadSet`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch970Thm54Round0WrapReadSet.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
import Nock.NockVMROM.Thm54.StrategyOfTracesR0
import Nock.NockVMROM.Thm54.P8Core.Batch733Thm54DecodedLambdaSlotMapReadSet
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command

namespace Nock.RedTeam.Batch970

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.RedTeam.Batch733

noncomputable section

section ReadSet

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [DecidableEq F] {N M : ℕ}

theorem certAxisOfEnvs_congr {envsC envsC' : Fin N → Env K} (h : ComputeAgree envsC envsC') :
    certAxisOfEnvs envsC = certAxisOfEnvs envsC' := by
  funext e
  unfold certAxisOfEnvs
  rw [decodedShift_congr h, decodedBits_congr h]

end ReadSet

end

end Nock.RedTeam.Batch970
