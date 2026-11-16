/-
  Nock/RedTeam/Batch4341Thm54J8r4bAtomChipL.lean

  The atom-chip variant `atomChipHQL`: `atomChipHQ` plus the ruled base gate `gL = isL · c_out` (no column).
  Width `349` (`rfl`), degree `≤ 4`; `atomChipHQL_sat_iff` (variant-accepted iff `atomChipHQ`-accepted on the
  same `349` columns and `gL` at every row); restrictions to `cellChipHQ` / `cellChip`; `cout_last`; honest
  acceptance from J-8b's `HonestA8.atomChipHQ_accepts_honest` plus `hlast`; `gL_load_bearing`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL

namespace Nock.RedTeam.Batch4341

open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL

#print axioms gL_deg
#print axioms atomGatesL_deg
#print axioms atomGatesL_below
#print axioms atomTemplateHQL_baseCols
#print axioms atomTemplateHQL_extCols
#print axioms atomChipHQL_width
#print axioms aEF_toHQ
#check @atomChipHQL_sat_iff
#print axioms atomChipHQL_sat_iff
#print axioms atomChipHQL_sat
#print axioms atomChipHQL_bind
#print axioms atomChipHQL_restrict_sat
#print axioms atomChipHQL_restrict_cell_sat
#check @cout_last
#print axioms cout_last
#print axioms gL_load_bearing
#check @atomChipHQL_accepts_honest
#print axioms atomChipHQL_accepts_honest

end Nock.RedTeam.Batch4341
