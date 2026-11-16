/-
  Nock/RedTeam/Batch3101Thm54J8WeightsJ8.lean

  * `epsilon_sumJ8` / `epsilon_allJ8`: `ε` of the list is `boundJ8P` (proved weights `weightJ8P`).
  * `figJ8_155` / `epsJ8_lt_155`: `< 2^-155` at every row count `≤ 2^31`; `figJ8_not_156` tight.
  * `jLists_le`: the J chip's slot counts give the #7 budget `(2J, J)`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8

namespace Nock.RedTeam.Batch3101

open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8

#print axioms evIO_card
#print axioms mem_specSummand
#print axioms pairEv_card
#print axioms bivEvent_card
#print axioms leafSum_ne_of_not_mem
#print axioms jLists_le
#print axioms mem_liftJ8
#print axioms epsilonOf_map_liftJ8
#print axioms mem_atomWalkJ8
#print axioms mem_zeroYJ8
#print axioms epsilon_sumJ8
#print axioms epsilon_allJ8
#print axioms boundJ8P_eq
#print axioms numJ8_corner
#print axioms figJ8_155
#print axioms figJ8_not_156
#print axioms epsJ8_lt_155

end Nock.RedTeam.Batch3101

