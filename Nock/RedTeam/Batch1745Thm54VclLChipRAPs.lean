/-
  Nock/RedTeam/Batch1745Thm54VclLChipRAPs.lean

  **The VCL-L cell table and path chip as
  `FixedPreprocessingRAP`s at `𝕂′` IO coins.**  Production:
  `Thm54/VclL/Chips/ChipRAP.lean`.

  * degree `≤ 4` at the chips: `cellChip_deg` / `pathChip_deg` (the `Def:RAP` `C_deg` field, from
    the per-gate checks `cellBase_deg` … `pathMixed_deg`).
  * NOT here (unconfirmed): chip satisfaction ⇒ `Table.TableAccepts` / `Chain` (the bridge
    `response_sound` needs), honest acceptance, `vclMemFamily`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1745

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms cellBase_deg
#print axioms cellMixed_deg
#print axioms pathBase_deg
#print axioms pathMixed_deg
#print axioms cellChip_fingerprint
#print axioms pathChip_fingerprint
#print axioms cellChip_deg
#print axioms pathChip_deg
#print axioms cellBase_length
#print axioms pathMixed_length

end Nock.RedTeam.Batch1745
