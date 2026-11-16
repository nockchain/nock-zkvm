/-
  Nock/RedTeam/Batch4884Thm54GenPortJ9.lean

  Axiom audit of the `GenPortJ9` pointer-data lemmas (`ptrE_eq`, `infoOfE_eq`, `sxE_eq`, `mvE_getD`,
  `genJ9A_pointer_data`): prints the axioms each one depends on.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9

set_option autoImplicit false

namespace Nock.RedTeam.Batch4884

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms GenPortJ9.ptrE_eq
#print axioms GenPortJ9.infoOfE_eq
#print axioms GenPortJ9.sxE_eq
#print axioms GenPortJ9.mvE_getD
#print axioms GenPortJ9.genJ9A_pointer_data

end Nock.RedTeam.Batch4884
