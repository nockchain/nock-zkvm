/-
  Nock/RedTeam/Batch2943Thm54J8aWalkJ8.lean

  * `walkChipJ8`: `walkTemplateHQK` with the depth certificate retyped to
    `len + Σ_{i<5} 2^i bᵢ + 29·b₅ − 60` and the exclusion `u·b₃·b₄·b₅` dropped; every other list
    literally `walkTemplateHQK`'s (`walkJ8_unchanged`, `rfl`); width `166` (`walkChipJ8_width`).
  * The narrowed bound: `walkJ8_len_le_60` (every row `natOf len ≤ 60`) and the U step of step 0,
    compiled: `walkHQK_axis_lt` / `walkJ8_axis_lt` (every provided record axis is in `[2, 2^62)`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8

namespace Nock.RedTeam.Batch2943

open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8

#print axioms walkJ8_unchanged
#print axioms walkChipJ8_width
#print axioms baseGatesJ8_deg
#print axioms walkChipJ8_bitFix_sat
#print axioms walkChipJ8_bitFix_bind
#print axioms walkJ8_len_le_60
#print axioms walkHQK_axis_lt
#print axioms walkJ8_axis_lt
#print axioms walkJ8_records_genuine

end Nock.RedTeam.Batch2943
