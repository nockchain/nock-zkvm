/-
  Nock/RedTeam/Batch2149Thm54VSQPullback.lean

  New module `PullVSQ`;
  additive.

  * `pullS`: a VS summand read at `projQ` / `toVS`, coins mapped into the 17-coin frame, read set
    `dep ∪ {15, 16}`; `mem_pullS`; `staged_proj` (a VSQ-staged strategy projected at fixed Im coins is VS-staged);
  * `sumCVSQ / sumMVSQ / jointVSQ` and **`epsilonVSQ_eq`**: `epsilonOf = boundVCLHQ''` (equality).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ

namespace Nock.RedTeam.Batch2149

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms PullVSQ.extQ_toVS
#print axioms PullVSQ.staged_proj
#print axioms PullVSQ.mem_pullS
#print axioms PullVSQ.pullS_coins_card
#print axioms PullVSQ.epsilonVSQ_eq

end Nock.RedTeam.Batch2149
