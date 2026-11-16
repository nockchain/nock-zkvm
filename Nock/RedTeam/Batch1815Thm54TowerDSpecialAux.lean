/-
  Nock/RedTeam/Batch1815Thm54TowerDSpecialAux.lean

  **Route (d) phase 2, items 1-2 — the width-309 append-only
  theory, the special core ids, the aux and endpoint twins.**  Production
  `Thm54/VclL/Compute/TowerGates`: `appendOnlyW_iff` / `imFreeW_iff` / `imFree_iff` (the `WTyped`
  and Im-free twins of `appendOnly_iff`), `mask_pair_iff`, `specialGate_iff` (core 72..77, 81: the
  chip bodies, plus the Im twin at 75, vanish iff the masked / queue / chain target holds in `𝕂′`),
  `gateW_iff` for the aux targets (`auxTarget`, `auxRe_eq`) and endpoints (`towerWGates`: all
  `qLinearW`; Im twins at aux1, ep2 `Out`, ep4).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGates
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1815

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

/-- Receipt: the 10 aux / endpoint gates are `qLinearW`; Im twins at positions 1 (aux1), 5 (ep2 Out),
9 (ep4). -/
theorem towerW_receipt :
    (∀ g ∈ towerWGates, qLinearW towerM g = true) ∧
      towerWGates.map (hasImW towerM) =
        [false, true, false, false, false, true, false, false, false, true] :=
  ⟨towerWGates_qLinear, towerWGates_hasIm⟩

end Nock.RedTeam.Batch1815

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.specialGate_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.gateW_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.appendOnlyW_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.auxRe_eq
#print axioms Nock.RedTeam.Batch1815.towerW_receipt
