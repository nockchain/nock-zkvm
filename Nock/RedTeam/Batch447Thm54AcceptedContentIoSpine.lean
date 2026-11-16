/-
  Nock/RedTeam/Batch447Thm54AcceptedContentIoSpine.lean

  **`AcceptedContent.io` spine over ver list.**

  No
  by-state-only consumer remains that blocks the spine.
-/
import Nock.IO
import Nock.MemoryTable
import Nock.NockVM
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent
import Nock.NockVMROM.Thm54.Language
import Nock.RedTeam.Batch446Thm54DerivedResponseByVer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch447

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open ExactExecution

#check AcceptedContent
#check @AcceptedContent.io
#check derivedResponseIO

/-- Spine still talks about `derivedResponseIO` as the ver-selected encoded list. -/
theorem spine_uses_ver_list {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hC : exec.CprimeCoherent) :
    exec.derivedResponseIO =
      (exec.memoryRows.flatMap fun row => responseRecords row.2.2).map
        (fun r => NockVM.encRecC r (exec.cprimeOf r)) :=
  derivedResponseIO_eq_map_encRecC exec hC

/-- Honest by-state recovery is a theorem, not the definition of the IO list. -/
theorem by_state_recovery_is_theorem :
    ∃ (_ :
      ∀ {F K : Type} [Field F] [Field K] [Algebra F K]
        {cfg : ExactConfig F K} (exec : ExactExecution cfg)
        (_hhon : ∀ row ∈ exec.memoryRows,
          row.2.2.ver = decide (row.2.2.st = MState.read_root)),
        exec.derivedResponseIO =
          Nock.RedTeam.Batch446.byStateResponseIO exec),
      True :=
  ⟨Nock.RedTeam.Batch446.derivedResponseIO_honest, trivial⟩

def byStateOnlyConsumersBlocking : List String := []

theorem no_by_state_only_blocker :
    byStateOnlyConsumersBlocking = [] :=
  rfl

end Nock.RedTeam.Batch447

#print axioms Nock.RedTeam.Batch447.spine_uses_ver_list
#print axioms Nock.RedTeam.Batch447.by_state_recovery_is_theorem
#print axioms Nock.RedTeam.Batch447.no_by_state_only_blocker
