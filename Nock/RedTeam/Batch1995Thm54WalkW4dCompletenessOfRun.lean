/-
  Nock/RedTeam/Batch1995Thm54WalkW4dCompletenessOfRun.lean

  **Completeness of the compute family and the WALK memory family
  from a compiler run** (twin of `Batch1955.vcl_completeness_of_run`).

  `vcl_completenessW_of_run`: `TowerD.vcl_completenessW'` with `HJ := honestVCLJW_of_run …` built from
  `hrun`/`hbound`, the walk datum `jointMemW` of the same run (`kr = krW`, the honest walk root count).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointHonestW

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1995

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD

noncomputable section

section Generic
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC : ℕ)

open Classical in
/-- **Completeness at the compiler-built verifier, walk memory family.** -/
theorem vcl_completenessW_of_run {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (αs : Quad (algebraMap F K δF))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hK3 : Module.finrank F K = 3) (hp : 25 ≤ ringChar F)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (hsize : nRows (runTree (K := K) δF hrun hbound) ≤ 2 ^ hC)
    (hrowsC : 3 * nRows (runTree (K := K) δF hrun hbound) < ringChar K)
    (hsizeT : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hT)
    (hsizeP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hP)
    (hleaf : programLeafBound (airReorder (runTree (K := K) δF hrun hbound)) ≤ 2 ^ 110)
    (hmemC : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar F)
    (hmemW : krW (demT (runTree (K := K) δF hrun hbound)).cells (demT (runTree (K := K) δF hrun hbound)).preads +
      (walkRows (demT (runTree (K := K) δF hrun hbound)).cells
        (demT (runTree (K := K) δF hrun hbound)).preads).length < ringChar F)
    (haxis : programAxisBound (airReorder (runTree (K := K) δF hrun hbound)) < 2 ^ 63) :
    let HJ := honestVCLJW_of_run δF hT hP hC hrun hbound Ksz αs hK3 hp hC1 hT1 hP1 hFC hFT hFP
      hsize hrowsC hsizeT hsizeP
    let hmemRows := memRowsW_of_run δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1 hFC hFT hFP hmemC hmemW
    let hkp := kpW_of_run δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1 hFC hFT hFP hmemW
    HJ.V.claim = ⟨subject, formula, result⟩ ∧ HJ.t = runTree (K := K) δF hrun hbound ∧
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFvW4 (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT ++
            (MFvW4 (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
              (jointMemW HJ hF hq hleaf hmemRows haxis hkp),
          s.mem ((CFvW4 (K := K) δF hT hP hC).honestQ HJ.toHonestVCLT χ,
            (MFvW4 (K := K) δF hT hP hC (krT δF HJ.t)).honestQ
              (jointMemW HJ hF hq hleaf hmemRows haxis hkp) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFvW4 (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT ++
        (MFvW4 (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
          (jointMemW HJ hF hq hleaf hmemRows haxis hkp)) := by
  intro HJ hmemRows hkp
  exact ⟨rfl, rfl, vcl_completenessW' δF hT hP hC HJ hF hq hleaf hmemRows haxis hkp⟩

end Generic

end

end Nock.RedTeam.Batch1995

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.vOfRunW
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honestVCLJW_of_run
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.memRowsW_of_run
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.walkLen_pos
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.vcl_completenessW'
#print axioms Nock.RedTeam.Batch1995.vcl_completenessW_of_run
