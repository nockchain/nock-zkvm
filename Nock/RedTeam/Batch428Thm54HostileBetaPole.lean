/-
  Nock/RedTeam/Batch428Thm54HostileBetaPole.lean

  **Hostile `β := −interPole`.**

  Algebraic receipt `pole_eq_poleSource`.
-/
import Nock.NockVMROM.Thm54.HostilePoleAlignment
import Nock.RedTeam.Batch405Thm54VmemPoleMismatch
import Nock.RedTeam.Batch400Thm54MemWrapTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch428

open Nock.NockVMROM.Thm54.HostilePoleAlignment

/-- Algebraic identity: `RLC − (−ι) = ι + RLC`. -/
theorem pole_eq_poleSource_algebra
    {K : Type} [Field K] (ι rlc : K) :
    rlc - (-ι) = ι + rlc :=
  Nock.NockVMROM.Thm54.HostilePoleAlignment.pole_eq_poleSource_algebra ι rlc

/-- Β is −interPole. -/
def betaConvention : String := "Inputs.β := -interPole"

theorem beta_convention :
    betaConvention = "Inputs.β := -interPole" :=
  rfl

theorem nx_stop_answered :
    Nock.RedTeam.Batch405.stopReason =
      "paper_reading: Inputs.β := -interPole (W4 Design A) or interV vs poleSource" :=
  Nock.RedTeam.Batch405.stop_is_paper_reading

#check Nock.NockVMROM.Thm54.HostilePoleAlignment.pole_eq_poleSource
#check Nock.NockVMROM.Thm54.HostilePoleAlignment.cfgOfTraces_beta

end Nock.RedTeam.Batch428

#print axioms Nock.RedTeam.Batch428.pole_eq_poleSource_algebra
#print axioms Nock.NockVMROM.Thm54.HostilePoleAlignment.pole_eq_poleSource
