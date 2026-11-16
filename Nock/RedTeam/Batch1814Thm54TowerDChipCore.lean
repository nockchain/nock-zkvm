/-
  Nock/RedTeam/Batch1814Thm54TowerDChipCore.lean

  **The core twin gates of the
  Q7S chip.**  Production `Thm54/VclL/Compute/TowerChip`: the Im map
  named in the SOURCE layout (`towerM = shiftIm fullImMap`, `vclCol (c + 95) = c`, so no existing
  column constant moves under `reindexE`), column support of every translated twin (`toQ_colsOk`,
  `colsIn_mixedCompile`), `coreRe` / `coreIm` / `coreImIds`, and the per-gate transport
  `coreGate_iff` (a non-special core gate holds in `𝕂′` at `towerEnv` iff its Re body and its Im
  twin vanish).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerChip
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1814

open Nock.NockVMROM.Thm54.VclL.Compute
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

/-- The Im twins of the kept Q7 core: the non-special Im-carrying ids plus the walk-acc residual. -/
theorem coreImIds_towerM :
    (coreImIds towerM).map (·.val) =
      ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 66, 67, 68, 69, 70, 71, 75]) := by
  decide +kernel

end Nock.RedTeam.Batch1814

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.coreGate_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.toQ_colsOk
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.toQW_colsOk
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.colsIn_mixedCompile
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerM_cols
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.vclCol_im
