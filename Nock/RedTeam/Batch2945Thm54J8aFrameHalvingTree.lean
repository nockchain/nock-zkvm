/-
  Nock/RedTeam/Batch2945Thm54J8aFrameHalvingTree.lean

  * `chainChild_state` (an atom-formula row is `s10L`/`s10T`, gate `svG`), `halvingOK_of_child`
    (`HalvingOK` on an `s10L` parent from its chain child: label link + the child's sibling-read axis
    in `[2, 2^62)`, which `WalkJ8.walkJ8_axis_lt` supplies under the narrowed certificate).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
import Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8

namespace Nock.RedTeam.Batch2945

open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8

#print axioms toVSQ_sampled
#print axioms frameJ8_y_round0
#print axioms classJ8_in_frame
#print axioms classJ8_new_coins_only_y
#print axioms summandJ8_card
#print axioms chainChild_state
#print axioms halvingOK_of_child

end Nock.RedTeam.Batch2945
