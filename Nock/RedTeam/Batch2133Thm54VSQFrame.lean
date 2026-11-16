/-
  Nock/RedTeam/Batch2133Thm54VSQFrame.lean

  Additive.  New module `Thm54/VclL/Handle/FrameVSQ.lean`: `frameVSQ` (`frameVS`'s 15 coins + Im `γH`,
  Im `ρH`, all handle coordinates sampled after round 0), coin maps `chalVHQ` / `chalsVSQ`, publics,
  `GoodCVSQ`, `tableVSQ` (85), `shapeVSQ` (238 / 166), `compCoreVSQ` / `memCoreVSQ` (summands a
  parameter; `Honest := Empty`), `compute_factsQ` / `cell_factsQ` / `walk_factsQ`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

namespace Nock.RedTeam.Batch2133

open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

#print axioms toVS_sampled
#print axioms frameVSQ_handle_round0
#print axioms chalVHQ_old
#print axioms chipCVSQ_width
#print axioms chipMVSQ_width
#print axioms compute_factsQ
#print axioms cell_factsQ
#print axioms walk_factsQ

end Nock.RedTeam.Batch2133
