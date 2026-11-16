/-
  Nock/RedTeam/Batch2061Thm54VSTeleH.lean

  **2 (memory side).**  Additive; no existing
  module changed.  New module `Thm54/VclL/Handle/TeleH.lean`: the generic `𝕂` telescope
  `kTelescope`, gathered-leaf lemmas for any template, and on the twins `cellChipH` / `walkChipH`:
  row gates, endpoint masks, the handle provide/consume inverses (`invH·den = 1`, so no pole), and
  the three handle telescopes `Σ mh·invH = pubs 4` (cell), `Σ hxInv = pubs 4`,
  `Σ (mL·invL + mR·invR) = pubs 5` (walk).  Compute side (`accGatesH`, slot batching): NOT here.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleH

namespace Nock.RedTeam.Batch2061

open Nock.NockVMROM.Thm54.VclL.Handle.TeleH

#print axioms kTelescope
#print axioms cellH_masks
#print axioms cellH_inv
#print axioms cellH_export_telescope
#print axioms walkH_masks
#print axioms walkH_inv
#print axioms walkH_export_telescope
#print axioms walkH_path_telescope

end Nock.RedTeam.Batch2061
