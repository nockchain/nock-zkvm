/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestDemandToys.lean

  `decide` on the two toys of `HonestToys`.  Additive.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestDemand
import Nock.NockVMROM.Thm54.VclL.Handle.HonestToys

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL

/-- Toy 1 (`*[0 [1 0]]`): old and VS demand have the same cell rows (one: the formula). -/
theorem toy1_demand_cells :
    (demandH [toy1Row]).cells = (demandOfRowsD [toy1Row]).cells ∧
    (demandH [toy1Row]).cells.length = 1 := by
  decide +kernel

/-- Toy 2 (`*[0 [0 1]]`). -/
theorem toy2_demand_cells :
    (demandH [toy2Row]).cells = (demandOfRowsD [toy2Row]).cells ∧
    (demandH [toy2Row]).cells.length = 1 := by
  decide +kernel

end Nock.NockVMROM.Thm54.VclL.Handle
