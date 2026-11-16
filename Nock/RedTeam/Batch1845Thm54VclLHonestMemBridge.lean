/-
  Nock/RedTeam/Batch1845Thm54VclLHonestMemBridge.lean

  **The honest side of the VCL memory family,
  first layers.**  Production: `VclL/Chips/HonestMemBridge.lean`,
  `HonestMemQ.lean`, `HonestMemCell.lean`.

  * `cellChipOk_sat_of_rows` / `pathChipOk_sat_of_rows` — chip acceptance from the endpoint masks
    plus row-local base / mixed gate equations (the converse of `RowBridge.*_rowLocal`).
  * `honestQ` — the interpolated trace of an explicit column function; `honestQ_zero` / `_one`
    (the preprocessing binds by construction), `honestQ_eval`, `env_trace` / `env_traceNext`.
  * `cell_base_gates_hold` — the `123` cell base gates vanish at the honest environment given the
    row-level facts `CellBaseFacts`.

  **Labelled.**
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemCell
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1845

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms cellChipOk_sat_of_rows
#print axioms pathChipOk_sat_of_rows
#print axioms honestQ_zero
#print axioms honestQ_one
#print axioms honestQ_eval
#print axioms env_trace
#print axioms env_traceNext
#print axioms cell_base_gates_hold

end Nock.RedTeam.Batch1845
