/-
  Nock/RedTeam/Batch2163Thm54VSHonestMh2.lean

  New module `HonestMh2`; additive.

  `mhH2` = compute consumers + walk-row consumers of a cell's export key, over the one cell list
  `(demandH2 rows).cells`; `export_total_link2` / `_inv` (any weight); `run_rows_pks`.  Positive control
  `toy1_mhH_ne_mhH2`: at `*[0 [1 0]]`, `mhH = 1` and `mhH2 = 2` for the formula cell.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestMh2

namespace Nock.RedTeam.Batch2163

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms export_total_link2
#print axioms export_total_link2_inv
#print axioms run_rows_pks
#print axioms toy1_mhH_ne_mhH2

end Nock.RedTeam.Batch2163
