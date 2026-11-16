/-
  Nock/RedTeam/Batch2470Thm54A3CellTwin.lean

  Additive; see `Handle/CellTwinK.lean`.

  * F1 (a) `cellRow_rank_pos`; F1 (b) `rank0_child_from_outside_left/right` (+ `no_cell_provides_rank0`,
    `cellOnly_child_rank_pos_*`);
  * `cellChipHQK`: width `242` (`rfl`), `restrict`, the kind lemma `sideGates_kind`, honest
    completeness `sideGates_honest` / `kindGates_honest` (gate level);
  * DEVIATION: a fifth gate `kb(1-w)` per side (counterexample without it: `sideGates_kind_without_fifth_cex`);
  * F2 is FALSE as stated: `walkBaseH_rejects_kind2`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK

namespace Nock.RedTeam.Batch2470

open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK

#print axioms cellRow_rank_pos
#print axioms no_cell_provides_rank0
#print axioms rank0_child_from_outside_left
#print axioms rank0_child_from_outside_right
#print axioms cellOnly_child_rank_pos_left
#print axioms cellOnly_child_rank_pos_right
#print axioms kindGates_deg
#print axioms cellChipHQK_width
#print axioms cellChipHQK_restrict_sat
#print axioms sideGates_kind
#print axioms sideGates_kind_without_fifth_cex
#print axioms sideGates_honest
#print axioms kindGates_honest
#print axioms walkBaseH_in_template
#print axioms walkBaseH_rejects_kind2

end Nock.RedTeam.Batch2470
