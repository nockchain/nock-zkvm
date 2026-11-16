/-
  Nock/RedTeam/Batch1740Thm54VclLEpsilon11.lean

  **`epsilon_vcll_eq` at the 11-coin `frameVCL`.**
  The generic `epsilonOf` of the joint
  list plus the memory and compute summands equals `boundVCL'` (widths `5/10/8`, `kc = 3`, IO
  coins in `Kio`, `|Kio| = |𝕂|²`), the IO mass going through `ioSummand_mass_ext`.
  Hypotheses beyond V3's: `I.dep.card = 4`, `|Kio| = |𝕂|²` (`Quad δ`), `inlinePairCount = 0`,
  and the totals `(reqBound + internalBound) + respBound = (3D+2, 3N+P+D, N+P)`.
-/
import Nock.NockVMROM.Thm54.VclL.Events.Summands
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1740

open Nock.NockVMROM.Thm54.VclL.Events

#print axioms epsilon_vcll_eq
#print axioms epsilonOf_vclMemSummands
#check @epsilon_vcll_eq

end Nock.RedTeam.Batch1740
