/-
  Nock/RedTeam/Batch3131Thm54J8bHonestCellWalk.lean

  * `cellChipHQK_accepts_honest` / `_pp` / `cellTwinK_accepted`: the 242-column cell twin accepts the
    honest trace (round-1 `𝕂′` columns included) extended by `kb` and `inv = (lo+hi)⁻¹`, under
    `SideOK` per side (`kb = 0` and a nonzero-rank weighted child, or `kb = 1` and a rank-(0,0)
    weighted child).  `sideOK_zero`: the `kb ≡ 0` case.
  * `walkChipJ8_accepts_honest` / `_pp` / `walkTwinJ8_accepted`: `walkChipJ8` (the narrowed depth
    certificate) accepts the honest trace for every row with `len ≤ 60`; certificate columns
    `14..20` re-chosen (`certUp`), every other column the honest one.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestK8

namespace Nock.RedTeam.Batch3131

open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.HonestK8

#print axioms sideGates_honest2
#print axioms cellChipHQK_accepts_honest
#print axioms cellChipHQK_accepts_honest_pp
#print axioms cellTwinK_accepted
#print axioms WalkTraceHQ.walkChipHQK_accepts_honest
#print axioms walkTwinK_accepted
#print axioms cert8_sum
#print axioms walkChipJ8_accepts_honest
#print axioms walkChipJ8_accepts_honest_pp
#print axioms walkTwinJ8_accepted

end Nock.RedTeam.Batch3131
