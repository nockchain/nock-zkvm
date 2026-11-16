/-
  Nock/RedTeam/Batch4071Thm54J8q1LinkL2.lean

  `walkDataOf` ignores the certificate block
  `14..20`, so `bitFix` is invisible to the walk data (`rdWW`, no retarget, no figure change); `rdWC` from
  `AcceptsJ8.hsatX` and `17 < p`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1

namespace Nock.RedTeam.Batch4071

#check @Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1.linkJ8_L2
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1.walkDataOf_congr_off
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1.walkDataOf_bitFix
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1.rdWW_realize40
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1.rdWC_realize40
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1.linkJ8_L2

end Nock.RedTeam.Batch4071
