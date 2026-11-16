import Nock.RedTeam.Batch4771Thm54NVJetData

/-!
Kernel-checked component checks of the literal jetted-program input `Ijet`: validity, the static and public checks, and the compute, jet, walk, atom and atom-walk table checks, each proved by `decide +kernel`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.RedTeam.Batch4771

namespace Nock.RedTeam.Batch4772

open Nock.V1J8.MemX Nock.V1J8.CompX

theorem ijet_valid : validB Ijet = true := by decide +kernel

theorem ijet_static : checkStaticJ8 (mkPb Ijet ((validB_iff Ijet).mp ijet_valid)) Ijet.c Ijet.M.m Ijet.r Ijet.g = true := by
  decide +kernel

theorem ijet_pub : checkPubJ8E (mkPb Ijet ((validB_iff Ijet).mp ijet_valid)) Ijet.c Ijet.χ Ijet.M = true := by
  decide +kernel

theorem ijet_X : checkCompX (tabX Ijet) = true := by decide +kernel
theorem ijet_J : checkJOK (tabJ Ijet) = true := by decide +kernel
theorem ijet_W : checkWalkJ8 Ijet.kroots (tabW Ijet) = true := by decide +kernel
theorem ijet_A : checkAtomHQ (tabA Ijet) = true := by decide +kernel
theorem ijet_AW : checkAWOK Ijet.krootsV (tabV Ijet) = true := by decide +kernel
theorem ijet_AL : checkAtomHQL (tabA Ijet) = true := by decide +kernel

end Nock.RedTeam.Batch4772

#print axioms Nock.RedTeam.Batch4772.ijet_static
#print axioms Nock.RedTeam.Batch4772.ijet_pub
