/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/RepriceJ9AB.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9A
namespace Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9AB
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
/-- L1 option (b): `DataJ8C` at `g' = g + AX`, `blocks' = blocks + AX + 2 SP` at `cornerC9`. -/
theorem numJ8X_optB_census32 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ8X c { cornerC9.toRowsJ8 with blocks := cornerC9.blocks + 2 ^ 31 + 2 * 2 ^ 31 } (2 ^ 66) (2 ^ 32 + 2 ^ 31)
      * 2 ^ 155 < c ^ 4 := by
  subst hc
  unfold numJ8X numJ8Pin cornerC9 numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound
  decide +kernel
end Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9AB
open Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9AB in
#print axioms numJ8X_optB_census32
