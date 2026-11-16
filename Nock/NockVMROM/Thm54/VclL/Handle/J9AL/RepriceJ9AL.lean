/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RepriceJ9AL.lean

  **Reprice bound**: the 155-bit figure with the ALU, twin of `J9A/RepriceJ9AB.lean`.  With `calls = 2^31` ALU calls
  (= ALU rows `AL`), `c₁ = 2`, `c₂ = 1`, `c₃ = 5`:
  `g' = 2^33 + 2^31 + 2·calls` (= `g + N + AX + c₁·calls` with the extra `N` kept, conservative),
  `blocks' = blocks + AX + 2·SP + calls`, the validity-consumer term `ioFailureUnionBound 5 (3 + 2A + 5·calls) A c²`
  added IN FULL on top of `numJ8X` (it double counts the unchanged `3 + 2A` term: an over-bound), and the `AluSZEvent`
  `arithSZ` numerator `weightC · c²` with `weightC = C·(2A + 32·AL + 2)` (`AluSZEvent.weightC`), `C = AL = 2^31`,
  `A = 2^31`.  Still `< 2^-155`, and not `≤ 2^-156`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9A
namespace Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9AL
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
/-- `< 2^-155` with the ALU at `calls = AL = 2^31`. -/
theorem numJ8X_optL_census32 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    (numJ8X c { cornerC9.toRowsJ8 with blocks := cornerC9.blocks + 2 ^ 31 + 2 * 2 ^ 31 + 2 ^ 31 } (2 ^ 66)
        (2 ^ 33 + 2 ^ 31 + 2 * 2 ^ 31)
      + ioFailureUnionBound 5 (3 + 2 * 2 ^ 31 + 5 * 2 ^ 31) (2 ^ 31) (c ^ 2)
      + 2 ^ 31 * (2 * 2 ^ 31 + 32 * 2 ^ 31 + 2) * c ^ 2) * 2 ^ 155 < c ^ 4 := by
  subst hc
  unfold numJ8X numJ8Pin cornerC9 numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound
  decide +kernel
/-- Not `≤ 2^-156` (the figure is `155.75` bits). -/
theorem numJ8X_optL_not_156 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < (numJ8X c { cornerC9.toRowsJ8 with blocks := cornerC9.blocks + 2 ^ 31 + 2 * 2 ^ 31 + 2 ^ 31 } (2 ^ 66)
        (2 ^ 33 + 2 ^ 31 + 2 * 2 ^ 31)
      + ioFailureUnionBound 5 (3 + 2 * 2 ^ 31 + 5 * 2 ^ 31) (2 ^ 31) (c ^ 2)
      + 2 ^ 31 * (2 * 2 ^ 31 + 32 * 2 ^ 31 + 2) * c ^ 2) * 2 ^ 156 := by
  subst hc
  unfold numJ8X numJ8Pin cornerC9 numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound
  decide +kernel
end Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9AL in
#print axioms numJ8X_optL_census32
open Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9AL in
#print axioms numJ8X_optL_not_156
