/-
  Nock/RedTeam/Batch3643Thm54J8aFinal.lean

  At `frameJ8`'s verifier data, an accepted J-8 compute trace and the five accepted memory-side
  traces, under the verifier's public equations, outside the compute walk events and the balances' IO events, prove
  `HoldsN` of the claim.  `axOK_x` / `axOK_s`: `AxOK` is vacuous off the path balance.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8

namespace Nock.RedTeam.Batch3643

open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8

#print axioms axOK_x
#print axioms axOK_s
#print axioms acceptsJ8_holdsN

end Nock.RedTeam.Batch3643
