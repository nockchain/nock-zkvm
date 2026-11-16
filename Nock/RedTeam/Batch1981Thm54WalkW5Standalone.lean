/-
  Nock/RedTeam/Batch1981Thm54WalkW5Standalone.lean

  **The end-to-end composition with the walk.**
  Production: `VclL/Chips/StandaloneVCLW.lean`.

  * Same `frameVCL` (11 coins), `seedSpecVCL`,
    `ioSpecVCLQuad`, `tableVCLT hC`, record view.
  * `vcl_epsilonW_le`: `ε ≤ boundVCLW''` with every hypothesis of `epsilon_vclW_le` discharged
    (`hMF_instW`: the memory summands are exactly the seeds over `|𝕂|²` plus the walk event `15W/|𝕂|`;
    `htot_instW`: totals `3D+2 / 3N+W+2D / N+2W`).
  * Checks below: the families are the intended ones (`rfl`), the walk summand is in `MF.summands`.
  * The completeness conjunct is at `memSoundnessVCLW`'s honest fields, `Empty` on this branch until
    W4c (vacuous).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.StandaloneVCLW
import Nock.RedTeam.Batch1980Thm54WalkW5Bound

set_option autoImplicit false

namespace Nock.RedTeam.Batch1981

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.StandaloneW

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC kr : ℕ)

/-- The compute family is the unchanged `compSoundnessVCLT`. -/
theorem CFvW_eq : CFvW (K := K) δF hT hP hC = compSoundnessVCLT F K hC (shapeVW hT hP) δF := rfl

theorem MFvW_eq : MFvW (K := K) δF hT hP hC kr = memSoundnessVCLW δF hT hP kr (C := tableVCLT hC) := rfl

/-- The walk summand is priced inside the composed theorem's `ε` (it is in `MF.summands`). -/
theorem walk_summand_in (V : VerifierData F K hC (shapeVW hT hP)) (x : Unit) :
    vclWalkSummandW δF hT hP kr V (C := tableVCLT hC) ∈ (MFvW (K := K) δF hT hP hC kr).summands V x :=
  memSoundnessVCLW_walk_summand δF hT hP kr V x

end

#check @vcl_standaloneW
#print axioms extraPremises_vclW
#print axioms rowFactsAt_CFvW
#print axioms vcl_standaloneW
#print axioms vcl_standaloneW_soundness
#print axioms epsilon_vclW_le
#print axioms hMF_instW
#print axioms hCF_instW
#print axioms htot_instW
#print axioms vcl_epsilonW_le
#print axioms vcl_standaloneW_soundness_le
#print axioms vcl_standaloneW_155'
#print axioms vcl_standaloneW_154'
#print axioms vcl_standaloneW_164'
#print axioms CFvW_eq
#print axioms MFvW_eq
#print axioms walk_summand_in

end Nock.RedTeam.Batch1981
