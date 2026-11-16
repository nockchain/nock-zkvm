import Nock.NockVMROM.Thm54.P8Core.SVFrameG.Bridge
import Nock.NockVMROM.Thm54.VclL.Chips.StandaloneVCLW

/-! The generic standalone statement `StandaloneG` holds at the walk instance (`CFvW`, `MFvW`), obtained from `vcl_standaloneW` through `standalone_iff`. -/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.P8Core.SVFrameG.Live

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.StandaloneW

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC kr : ℕ)

/-- **`StandaloneG` at the live walk instance** (`vcl_standaloneW` through `standalone_iff`). -/
theorem vcl_standaloneW_G :
    StandaloneG (CFvW (K := K) δF hT hP hC).toCore (MFvW (K := K) δF hT hP hC kr).toCore
      (jointSummandsStd (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr)) :=
  (standalone_iff _ _ _).mp (vcl_standaloneW δF hT hP hC kr)

end
end Nock.NockVMROM.Thm54.P8Core.SVFrameG.Live
