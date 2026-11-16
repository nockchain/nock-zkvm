/-
  Nock/RedTeam/Batch405Thm54VmemPoleMismatch.lean

  `AcceptedContent.vmem` / `MemoryTable.interV` use
  `MemoryTable.pole = RLC^γ − β` with the hostile config's
  `β := 0` (`ExecOfTraces.cfgOfTraces`, `lblMAt`).

  So the chip forces `Δ = (interPole + RLC)⁻¹` while `Vmem` asks
  `Δ = RLC⁻¹`.

  `deployed_row_vmem_at` / `memoryRows` / `io` remain open.
-/
import Nock.MemoryTable
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.RedTeam.Batch400Thm54MemWrapTransfer
import Nock.RedTeam.Batch404Thm54ResponseTsMemPowers

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch405

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MemoryPaperFactorization

/-- Hostile config still pins table `β` to `0` (`ExecOfTraces.cfgOfTraces`). -/
def hostileBetaIsZero : String := "cfgOfTraces.challenges.β = 0"

theorem hostile_beta_is_zero_name : hostileBetaIsZero = "cfgOfTraces.challenges.β = 0" := rfl

def chipPoleForm : String := "poleSource = interPole + recordRLC"

theorem chip_pole_form : chipPoleForm = "poleSource = interPole + recordRLC" := rfl

/-- `Vmem` pole with `β = 0`: `RLC − 0`. -/
def vmemPoleForm : String := "MemoryTable.pole = RLC - β  (β = 0)"

theorem vmem_pole_form : vmemPoleForm = "MemoryTable.pole = RLC - β  (β = 0)" := rfl

/-- Algebraic mismatch when `interPole ≠ 0`: the two poles differ. -/
theorem poles_differ_of_interPole_ne_zero
    {K : Type} [Field K] (interPole rlc : K) (h : interPole ≠ 0) :
    interPole + rlc ≠ rlc - (0 : K) := by
  intro heq
  have : interPole = 0 := by
    linear_combination heq
  exact h this

/-- Named remaining hyp still unmet. -/
theorem deployed_row_vmem_at_still_remaining :
    "deployed_row_vmem_at" ∈ Nock.RedTeam.Batch400.transferRemainingHyps := by
  decide

def remainingAfter404 : List String :=
  ["deployed_row_vmem_at",
    "derivedResponseIO_eq_hostileResponses",
    "derivedRequestIO_eq_hostileRequests"]

theorem remainingAfter404_length : remainingAfter404.length = 3 := by decide

theorem openConjuncts_length :
    Nock.RedTeam.Batch398.openConjuncts.length = 10 :=
  Nock.RedTeam.Batch398.openConjuncts_length

theorem closed_count_unmoved :
    21 - Nock.RedTeam.Batch398.openConjuncts.length = 11 :=
  Nock.RedTeam.Batch398.closed_count

theorem no_vacuous_close :
    "vmem" ∈ Nock.RedTeam.Batch398.openConjuncts ∧
      "memoryRows" ∈ Nock.RedTeam.Batch398.openConjuncts ∧
      "io" ∈ Nock.RedTeam.Batch398.openConjuncts := by
  decide

def stopReason : String :=
  "paper_reading: Inputs.β := -interPole (W4 Design A) or interV vs poleSource"

theorem stop_is_paper_reading :
    stopReason =
      "paper_reading: Inputs.β := -interPole (W4 Design A) or interV vs poleSource" :=
  rfl

end Nock.RedTeam.Batch405

#print axioms Nock.RedTeam.Batch405.poles_differ_of_interPole_ne_zero
#print axioms Nock.RedTeam.Batch405.closed_count_unmoved
#print axioms Nock.RedTeam.Batch405.no_vacuous_close
#print axioms Nock.RedTeam.Batch405.stop_is_paper_reading
