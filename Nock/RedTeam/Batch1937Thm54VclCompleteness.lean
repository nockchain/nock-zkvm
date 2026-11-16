/-
  Nock/RedTeam/Batch1937Thm54VclCompleteness.lean

  **The joint honest datum and `vcl_completeness`.**  `jointMem HC hf` (TowerJointHonest.lean) is the memory honest datum of the SAME generator run
  as `HC : HonestVCLT` (`V := HC.V`, `d := demT HC.t`); `jointMem_honestV` (rfl), `jointMem_honestReq`
  (`req_zero` at 0, `honestReqCF_eq_req` at 1, 2, `hslot` proved by `demT_slot`).  `vcl_completeness` is the
  frame's `completeness` field at the two VCL families for that pair.
-/
import Nock.RedTeam.Batch1882Thm54VclStandaloneNoHrow
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointHonest

set_option autoImplicit false

namespace Nock.RedTeam.Batch1937

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.RedTeam.Batch1880 Nock.RedTeam.Batch1882

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

open Classical in
/-- **Completeness at the two VCL families**: for the honest compute datum `HC` (one generator run) and the
memory datum `jointMem δF HC hf` of the same run, the probability that some honest bad summand fires at the
honest traces is at most `epsilonOf` of the honest bad list `badT ++ MF.bad`. -/
theorem vcl_completeness (HC : VclL.Compute.TowerD.HonestVCLT F K δF hC (ChipRAP.shapeV hT hP))
    (hf : VclL.Compute.TowerD.JointMemFacts δF hT hP hC HC) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFv (K := K) δF hT hP hC).honestBad HC ++
            (MFv (K := K) δF hT hP hC).honestBad (VclL.Compute.TowerD.jointMem δF HC hf),
          s.mem ((CFv (K := K) δF hT hP hC).honestQ HC χ,
            (MFv (K := K) δF hT hP hC).honestQ (VclL.Compute.TowerD.jointMem δF HC hf) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFv (K := K) δF hT hP hC).honestBad HC ++
        (MFv (K := K) δF hT hP hC).honestBad (VclL.Compute.TowerD.jointMem δF HC hf)) :=
  (SVFrame.standalone_generic (rowFactsAt_CFv δF hT hP hC) (extraPremises_vcl δF hT hP hC)).completeness
    HC (VclL.Compute.TowerD.jointMem δF HC hf)
    (VclL.Compute.TowerD.jointMem_honestV δF HC hf) (VclL.Compute.TowerD.jointMem_honestReq δF HC hf)

end

#print axioms VclL.Compute.TowerD.demT_slot
#print axioms VclL.Compute.TowerD.jointMem_honestV
#print axioms VclL.Compute.TowerD.jointMem_honestReq
#print axioms vcl_completeness

end Nock.RedTeam.Batch1937
