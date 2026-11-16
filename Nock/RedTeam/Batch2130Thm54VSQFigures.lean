/-
  Nock/RedTeam/Batch2130Thm54VSQFigures.lean

  Additive.  New module `Thm54/VclL/Handle/EpsFigVSQ.lean`:
  * `boundVCLHQ''` = `boundVCLH''` with the two handle IO summands over `|𝕂′|` and four `𝕂`-coins;
  * `kWalk_dominant`: the dominant summand is now the `𝕂`-coin compute walk + tiling + walk chain;
    `hxq_fits`: the moved handle export summand is below `2⁻³⁰⁰`.
  Scope: the bound FUNCTION only; `epsilonOf (VSQ summands) = boundVCLHQ''` and `hsoundVSQ` are NOT in
  this batch (UNCONFIRMED until compiled).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ

namespace Nock.RedTeam.Batch2130

open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ

#print axioms boundVCLHQ''_eq
#print axioms numHQ_corner
#print axioms figVCLHQ''_156
#print axioms figVCLHQ''_155_at_32
#print axioms figVCLHQ''_166_kernel
#print axioms figVCLHQ''_155
#print axioms figVCLHQ''_154
#print axioms figVCLHQ''_164
#print axioms figVCLHQ''_not_157
#print axioms figVCLHQ''_not_156_at_32
#print axioms figVCLHQ''_not_167_kernel
#print axioms kWalk_dominant
#print axioms hxq_fits

end Nock.RedTeam.Batch2130
