import Nock.NockVMROM.Thm54.VclL.Handle.HonestPairX


namespace Nock.RedTeam.Batch3701

open Nock.NockVMROM.Thm54.VclL.Handle.HonestPairX

/-- A small sanity instance of the comb first difference (`[1, 2, 3]` vs `[1, 5]`: depth 0 limbs agree,
then a suffix row against the inline top limb, at axis `3`). -/
example : combFD (fun _ => 7) (fun _ => 9) 0 1 [1, 2, 3] [1, 5] = (3, (1, 7), (0, 5)) := rfl

#print axioms combFD_spec
#print axioms pairOK_pdX
#print axioms pdX_records
#print axioms pairOK_of_genX
#print axioms smallX_of_tree
#print axioms computeChipVCLHX_honest_sat_pd
#print axioms computeChipVCLHX_honest_sat_tree

end Nock.RedTeam.Batch3701
