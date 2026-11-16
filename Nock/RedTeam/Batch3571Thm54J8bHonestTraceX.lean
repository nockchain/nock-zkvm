import Nock.NockVMROM.Thm54.VclL.Handle.HonestTraceX


namespace Nock.RedTeam.Batch3571

open Nock.NockVMROM.Thm54.VclL.HonestTraceX

/-- The template read-set facts the congruences rest on (compiled, by `rfl`). -/
example : (Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.walkGatesX (F := ℚ)).all (okM okKw okFw) = true :=
  walk_ok

#print axioms slotsDA_ok
#print axioms slotsAct_ok
#print axioms arith_ok
#print axioms eq_ok
#print axioms walk_ok
#print axioms walk_shape
#print axioms dVal_aVal_congr
#print axioms termVal_congr
#print axioms evalQX_congr
#print axioms accGatesX_map
#print axioms polyX_first
#print axioms polyX_last
#print axioms computeChipVCLHX_honest_sat

end Nock.RedTeam.Batch3571
