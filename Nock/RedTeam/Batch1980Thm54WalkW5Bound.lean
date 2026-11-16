/-
  Nock/RedTeam/Batch1980Thm54WalkW5Bound.lean

  **`boundVCLW''` and its figures at VCL-L's budgets.**
  Production: `VclL/Events/BoundW.lean`.

  * Tightness: `2^-156` not reached at `2^31`, `2^-155` not at `2^32`, `2^-165` not at the kernel row
    (figures, not floors).
  * NC (discriminating): pricing the walk event at `30W` instead of `15W` loses 155 at the `2^31` corner
    (`figVCLW_double_walk_fails`): the walk event's price is load-bearing in the margin.
-/
import Nock.NockVMROM.Thm54.VclL.Events.BoundW

set_option autoImplicit false

namespace Nock.RedTeam.Batch1980

open Nock.NockVMROM.Thm54.VclL.Events

#print axioms boundVCLW''_eq
#print axioms numGenW_corner
#print axioms figVCLW''_two_pow_31
#print axioms figVCLW''_two_pow_32
#print axioms figVCLW''_kernel
#print axioms figVCLW''_not_156
#print axioms figVCLW''_not_155_at_32
#print axioms figVCLW''_not_165_kernel
#print axioms figVCLW_double_walk_fails

end Nock.RedTeam.Batch1980
