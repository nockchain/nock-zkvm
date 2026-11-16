/-
  Nock/RedTeam/Batch1973Thm54WalkW3Export.lean

  Module `VclL/Chips/ExportTelescopeW.lean` (twins of `ExportTelescope.lean` §PathX / §Both / §PathP
  with `walkChip` in place of `pathChip`):
  * `walk_export_telescope` / `walk_internal_sum`: ONE export consume per walk row, key
    `(p, l, r, idx, 0)` (constant side slot `0`), `Σ_j den⁻¹ = y` (publics `0 / 1`);
  * `walk_provider_telescope` / `walkProviderFacts`: the path accumulator with TWO records per walk
    row `(root, l, 2·prefix, rootIdx)·mL`, `(root, r, 2·prefix + 1, rootIdx)·mR` (unconditional
    inverses), at `m = 8` — the path chip's record type, unchanged.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ExportTelescopeW

set_option autoImplicit false

namespace Nock.RedTeam.Batch1973

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms lblRow_congr
#print axioms keyRow_congr
#print axioms walkEnv_congr
#print axioms walkDataOf_congr
#print axioms walk_ev_next
#print axioms walk_export_telescope
#print axioms walk_xinv
#print axioms walk_internal_sum
#print axioms walk_provider_telescope
#print axioms walk_pinv
#print axioms walkProviderFacts
#print axioms cellExportFactsW
#print axioms xKey_decodeW
#print axioms walk_keys_exported

end Nock.RedTeam.Batch1973
