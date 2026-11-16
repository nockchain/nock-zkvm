/-
  Nock/RedTeam/Batch2146Thm54VSQMemCoinCongr.lean

  New module `CpCongr`; additive.

  * `noCP` / `cpOK C P` and their evaluation congruences `noCP_eval` / `cpOK_eval`;
  * `expandChip_cp_congr`: satisfaction of an `expandChip` template (no equality / extension gates, base
    gates `noCP`, mixed gates `cpOK C P`) transfers between challenge / public vectors agreeing on `C / P`;
  * `cellMixed_cp` / `walkMixed_cp` (by `simp` over the gate lists), `cellChip_cp_congr` /
    `walkChip_cp_congr`: the handle leaves `33..36` and the handle terminals (publics `≥ 4`) are invisible to
    the original cell / walk chips.
  * positive controls: `cpOK_flags_33`, `cpOK_flags_pub4` (a read of leaf `33` / public `4` is flagged).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CpCongr

namespace Nock.RedTeam.Batch2146

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms CpCongr.noCP_eval
#print axioms CpCongr.cpOK_eval
#print axioms CpCongr.expandChip_cp_congr
#print axioms CpCongr.cellMixed_cp
#print axioms CpCongr.walkMixed_cp
#print axioms CpCongr.cpOK_flags_33
#print axioms CpCongr.cpOK_flags_pub4
#print axioms CpCongr.cellChip_cp_congr
#print axioms CpCongr.walkChip_cp_congr

end Nock.RedTeam.Batch2146
