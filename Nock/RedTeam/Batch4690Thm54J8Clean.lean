/-
  Nock/RedTeam/Batch4690Thm54J8Clean.lean

  `probJ8V_final_clean` and
  `probJ8V_nonvacuous_clean`: the duplicate binders `[Fact (ringChar (ZMod p)).Prime]` and
  `[Algebra (ZMod (ringChar (ZMod p))) K]` removed, derived via `ringChar (ZMod p) = p`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8

namespace Nock.RedTeam.Batch4690

open Nock.NockVMROM.Thm54.VclL.Handle

#check @CleanJ8.probJ8V_final_clean
#print axioms CleanJ8.probJ8V_final_clean
#check @CleanJ8.probJ8V_nonvacuous_clean
#print axioms CleanJ8.probJ8V_nonvacuous_clean

end Nock.RedTeam.Batch4690
