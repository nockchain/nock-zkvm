/-
  Nock/RedTeam/Batch2100Thm54VSHonestF.lean

  1. `expandChip_extend` (generic in the twin): the converse of `expandChip_restrict`.  The original
     accepts the restriction of `Q'` and every gate of the twin that is not a gate of the original holds
     row by row, then the twin accepts `Q'`.  `expandChip_extend_honest`: the same for the honest
     `honestQ` trace of an extended column function (`extColF`), the restriction computed
     (`honestQ_restrict_extColF`).
  2. `cellChipH_accepts_honest` / `walkChipH_accepts_honest`: `cellTraceH` (232 columns: `mh = mhv`,
     `invH = den^-1`, `accH` = inclusive prefix sum of `mh * den^-1`) and `walkTraceH` (151 columns:
     `kL vL kR vR`, `hxInv hpInvL hpInvR` = `den^-1`, `hxAcc`, `hpAcc` prefix sums) are accepted by
     `cellChipH` / `walkChipH`, from the original's honest acceptance, through `cellH_gates_honest` /
     `walkH_gates_honest`.  Side conditions: no vanishing denominator (the priced pole event), publics equal
     to the totals, boolean kind bits.  `den_indep`: the denominators read only base columns and coins (so
     the fill is well-defined).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TraceAcceptH

set_option autoImplicit false

namespace Nock.RedTeam.Batch2100

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms expandChip_extend
#print axioms honestQ_restrict_extColF
#print axioms expandChip_extend_honest
#print axioms CellTraceH.den_indep
#print axioms CellTraceH.cellChipH_accepts_honest
#print axioms WalkTraceH.den_indep
#print axioms WalkTraceH.walkChipH_accepts_honest
#print axioms cellTwin_accepted
#print axioms walkTwin_accepted

end Nock.RedTeam.Batch2100
