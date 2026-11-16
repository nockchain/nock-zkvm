/-
  Nock/RedTeam/Batch1780Thm54VclLLogUpAcc.lean

  **The LogUp accumulator gadget, parametric in the IO
  field.**  Production `Thm54/VclL/Compute/LogUpAcc.lean`: generic in
  `Kio` and its limb count (`Basis (Fin e) F Kio`), the column positions, the slot selectors.
  `accGates` (`isFirst·acc = 0`, `(1−isLast)(acc′−acc−Σ act·inv) = 0`, `isLast(acc+Σ act·inv−ρ) = 0`,
  degree ≤ 3), row soundness (`accInit_zero`, `accStep_eq`, `accTerm_eq`), `acc_telescope`,
  `acc_rows` (Σ rows = public ρ), `sum_active_inv`, `reqIOFacts_of_rows` (the frame's `ReqIOFacts`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.LogUpAcc
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1780

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp

#print axioms coord_limbVal
#print axioms accGates_degree
#print axioms coord_termVal
#print axioms accInit_zero
#print axioms accStep_eq
#print axioms accTerm_eq
#print axioms acc_telescope
#print axioms acc_rows
#print axioms sum_active_inv
#print axioms reqIOFacts_of_rows

end Nock.RedTeam.Batch1780
