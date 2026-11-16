/-
  Nock/RedTeam/Batch379Thm54FamilyDecodeAndSeed.lean

  **Family decode + `seed_ne` from the event.**

  `lblCAt` / `decodeMemPub` read `rowEnvAt` / `memorySourceEnvAt`
  (family chip at `c`).  `seed_ne_of_not_hostile` is
  `nprSeed_ne_of_good` — no extra `hz`.
-/
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.FamilyComputeRows

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch379

open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows

noncomputable abbrev seed_ne_of_not_hostile :=
  @Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.seed_ne_of_not_hostile

noncomputable abbrev specializedExec_eq :=
  @Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.specializedExec_eq

noncomputable abbrev specialized_computeRows_map :=
  @Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.specialized_computeRows_map

noncomputable abbrev decodeInputs_eq_specialized :=
  @Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.decodeInputs_eq_specialized

noncomputable abbrev lblCAt_eq_rowEnvAt :=
  @Nock.NockVMROM.Thm54.ExecOfTraces.lblCAt_eq_rowEnvAt

#check seed_ne_of_not_hostile
#check specializedExec_eq
#check decodeInputs_eq_specialized
#check lblCAt_eq_rowEnvAt

end Nock.RedTeam.Batch379

#print axioms Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.seed_ne_of_not_hostile
#print axioms Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.decodeInputs_eq_specialized
#print axioms Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.specialized_computeRows_map
