/-
  Nock/RedTeam/Batch1882Thm54VclStandaloneNoHrow.lean

  `hrow : rowFactsAt (CFv..)` is discharged by `rowFactsAt_compSoundnessVCLT`; the
  `ExtraPremises` by `extraPremises_vcl`.  Hypotheses left: `V.Checks`, `msg.Staged`
  (statement-level, consumers' data); the three figures also `Fintype.card K = cK`, the size bounds and
  `leafBoundF <= 2^110`.
-/
import Nock.RedTeam.Batch1880Thm54VclIntegrateStandalone
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowFactsAt

set_option autoImplicit false

namespace Nock.RedTeam.Batch1882

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.RedTeam.Batch1880

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

/-- `rowFactsAt` at the instantiated tower compute family `CFv`. -/
theorem rowFactsAt_CFv : rowFactsAt (CFv (K := K) δF hT hP hC) :=
  VclL.Compute.TowerD.rowFactsAt_compSoundnessVCLT F K hC (shapeV hT hP) δF

open Classical in
/-- **Soundness at the two VCL families, no `hrow`.** -/
theorem vcl_standalone_soundness' 
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf (allSummands (CF := CFv (K := K) δF hT hP hC) (MF := MFv (K := K) δF hT hP hC) V msg.msg0C msg.msg0M
        (jointSummandsStd (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC))) :=
  vcl_standalone_soundness δF hT hP hC (rowFactsAt_CFv δF hT hP hC) (extraPremises_vcl δF hT hP hC) V hV msg hst

open Classical in
/-- **Soundness with its `ε`, no `hrow`.** -/
theorem vcl_standalone_soundness_le'
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      boundVCL'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim) (2 ^ 110) :=
  vcl_standalone_soundness_le δF hT hP hC (rowFactsAt_CFv δF hT hP hC) V hV msg hst

open Classical in
theorem vcl_standalone_155'
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 31) (hD : cellRows V ≤ 2 ^ 31) (hP' : pathRows V ≤ 2 ^ 31)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 155 :=
  vcl_standalone_155 δF hT hP hC (rowFactsAt_CFv δF hT hP hC) V hV msg hst hcK hN hD hP' hΛ

open Classical in
theorem vcl_standalone_154'
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 32) (hD : cellRows V ≤ 2 ^ 32) (hP' : pathRows V ≤ 2 ^ 32)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 154 :=
  vcl_standalone_154 δF hT hP hC (rowFactsAt_CFv δF hT hP hC) V hV msg hst hcK hN hD hP' hΛ

open Classical in
theorem vcl_standalone_164'
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 21) (hD : cellRows V ≤ 2 ^ 20) (hP' : pathRows V ≤ 2 ^ 21)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 164 :=
  vcl_standalone_164 δF hT hP hC (rowFactsAt_CFv δF hT hP hC) V hV msg hst hcK hN hD hP' hΛ

end

#print axioms rowFactsAt_CFv
#print axioms vcl_standalone_soundness'
#print axioms vcl_standalone_soundness_le'
#print axioms vcl_standalone_155'
#print axioms vcl_standalone_154'
#print axioms vcl_standalone_164'

end Nock.RedTeam.Batch1882
