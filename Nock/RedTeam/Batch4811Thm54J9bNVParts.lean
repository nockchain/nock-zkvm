/-
  Kernel-decided checks of the component tables (`i9_*`) of the instance `I9`, and the claim fact
  `claimBigs p c9 = [2]`.
-/
import Nock.RedTeam.Batch4810Thm54J9bNVData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.V1J9 Nock.V1J9.Exe9 Nock.V1J9.Check9
open Nock.RedTeam.Batch4810

namespace Nock.RedTeam.Batch4811

open Nock.V1J8.MemX Nock.V1J8.CompX

theorem i9_valid : validB I9 = true := by decide +kernel

theorem i9_static : checkStaticJ9 (mkPb I9 ((validB_iff I9).mp i9_valid)) I9.c I9.M.m I9.r I9.g = true := by
  decide +kernel

theorem i9_pub : checkPubJ9E (mkPb I9 ((validB_iff I9).mp i9_valid)) I9.c I9.χ I9.M = true := by
  decide +kernel

theorem i9_X : checkCompX (tabX9 I9) = true := by decide +kernel
theorem i9_C : checkCellKW (tabC I9) = true := by decide +kernel
theorem i9_W : checkWalkJ8 I9.kroots (tabW I9) = true := by decide +kernel
theorem i9_J : checkJOK (tabJ I9) = true := by decide +kernel
theorem i9_A : checkAtomHQ (tabA I9) = true := by decide +kernel
theorem i9_AW : checkAWOK I9.krootsV (tabV I9) = true := by decide +kernel
theorem i9_AL : checkAtomHQL (tabA I9) = true := by decide +kernel

/-- The claim's only big position is the result. -/
theorem c9_bigs : Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9.claimBigs Nock.Field.p c9 = [2] := by decide +kernel

/-- The result `p + 5` is a big atom (`≥ p`). -/
theorem c9_result_big : Nock.Field.p ≤ Nock.Field.p + 5 := by omega

end Nock.RedTeam.Batch4811

#print axioms Nock.RedTeam.Batch4811.i9_static
#print axioms Nock.RedTeam.Batch4811.i9_pub
#print axioms Nock.RedTeam.Batch4811.i9_X
#print axioms Nock.RedTeam.Batch4811.i9_C
#print axioms Nock.RedTeam.Batch4811.c9_bigs
