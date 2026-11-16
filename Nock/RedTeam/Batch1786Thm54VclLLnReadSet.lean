/-
  Nock/RedTeam/Batch1786Thm54VclLLnReadSet.lean

  **The Q7 read-set instrument.**  Production `Thm54/VclL/Compute/LnReadSet.lean`: the memory-record timestamps are derived by the
  decoder (`lnPrev · α^k`, `computeTraceSubst` 74 / `mr2Field 7` / `mr3Field 7`), so the timestamp
  read set is roles 54 (`lnPrev`) / 55 (`ln`) and challenge slot 0 (`α`) (and 9, `λ`).
  * positive control `readsLn_deleted`: the instrument finds it in core 50, 58, 65, 72, 78 (and the
    dropped 79, 80) and in `finalLnInit`;
  * `kept_no_ln`: NO kept source (`keptCoreIdsQ7` = `keptCoreIds` minus {50, 58, 65, 72, 78}, with
    the 309 retargets and wrappers; the three aux sources; `endpoint2Q7` = `endpoint2_309` minus
    `finalLnInit`; `endpoint4_309`) reads role 54, role 55, challenge 0 or challenge 9.
  `keptCoreIdsQ7_length` (75), `endpoint2Q7_eq`, `lnLimbs_range`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.LnReadSet
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1786

open Nock.NockVMROM.Thm54.VclL.Compute.LnRead

#print axioms readsLn_deleted
#print axioms kept_no_ln
#print axioms keptCoreIdsQ7_length
#print axioms endpoint2Q7_eq
#print axioms lnLimbs_range

end Nock.RedTeam.Batch1786
