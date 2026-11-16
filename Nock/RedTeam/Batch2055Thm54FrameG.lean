/-
  Nock/RedTeam/Batch2055Thm54FrameG.lean

  **The generalized generic soundness frame and
  its bridge.**  F1 `Thm54/P8Core/SVFrameG/{CompCore,StandaloneG,Ground,IO}`: `CompCore`/`MemCore`, `MessagesG`,
  `AcceptsG`, `allSummandsG`, `StandaloneG`, `standaloneG_of_sound` (one obligation per instance),
  grounding (`TreeRel`, `Grounded`, `holdsF_of_grounded`, `genuine_of_local`; root uniqueness about
  the constructed tree's own root), IO layer `CompIO`/`MemIO`/`ioSummandG` without Kfp.
  F2 `Bridge`, `Live`: `standalone_iff`, `ioSummand = ioSummandG` by `rfl`, `standalone_generic_G`,
  `vcl_standaloneW_G`.  NOT DONE: the fingerprint instance of `Grounded` (UNCONFIRMED; see REPORT-F12).
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrameG.Live
import Nock.NockVMROM.Thm54.P8Core.SVFrameG.Ground

set_option autoImplicit false

namespace Nock.RedTeam.Batch2055

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG

#print axioms standalone_iff
#print axioms standalone_generic_G
#print axioms ioSummand_eq_G
#print axioms ioEventAt_eq_G
#print axioms standaloneG_of_sound
#print axioms holdsF_of_grounded
#print axioms genuine_of_local
#print axioms holdsF_of_local
#print axioms Nock.NockVMROM.Thm54.P8Core.SVFrameG.Live.vcl_standaloneW_G

end Nock.RedTeam.Batch2055
