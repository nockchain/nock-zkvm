import Nock.NockVMROM.Thm54.VclL.Compute.TowerGather
import Nock.NockVMROM.Thm54.VclL.Compute.TowerSat
import Nock.NockVMROM.Thm54.VclL.Compute.WalkSatQ7

/-!
# `RowFactsQ7` at the tower gather from acceptance at the tower chip

`RowFactsQ7` (now width-generic)
at the chip datum with the tower gather: `obl` from `towerRowObl` (`computeChipVCLQ7T_obl`), the two
masks from the preprocessing binding of `computeChipVCLQ7T` (columns 11 / 12, as for the Q7S chip).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section RF
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **Acceptance at the tower chip gives the Q7 row facts at the tower gather** (injective nodes). -/
theorem towerRowFactsQ7 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit) P)
    (claim : P8PublicClaim) (pub : ℕ → F) (hinj : Function.Injective nodes) :
    RowFactsQ7 (⟨n, hn, nodes, towerGather δ b, orbit, claim, pub, chalV⟩ :
        ChipDataG F (Quad (algebraMap F K δ)) h) chalV pubVal P := by
  have hs := (computeChipVCLQ7T_sat_iff hn nodes b δ chalV pubVal orbit P).1 hsat
  have h11 : (11 : ℕ) < (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w := by
    change 11 < 410; norm_num
  have h12 : (12 : ℕ) < (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w := by
    change 12 < 410; norm_num
  have m0 : P ⟨11, h11⟩ = firstRowMask nodes := hs.1 ⟨0, by change 0 < 2; norm_num⟩
  have m1 : P ⟨12, h12⟩ = lastRowMask hn nodes := hs.1 ⟨1, by change 1 < 2; norm_num⟩
  refine ⟨towerRowObl δ hn nodes b chalV pubVal orbit P hsat claim pub, fun (i : Fin n) => ⟨?_, ?_⟩⟩
  · simp only [envQ, envOfTrace, dif_pos h11]
    rw [m0, Nock.Framework.firstRowMask_eval _ hinj]
  · simp only [envQ, envOfTrace, dif_pos h12]
    rw [m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]

end RF

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
