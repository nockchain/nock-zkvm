/-
  Nock/RedTeam/Batch2078Thm54VSHonestWalk.lean

  1. `childNouns` / `inTree_childCols` / `airReorder_childCols` / `child_link_nouns`: the child link of the
     compute walk at nouns (generator induction + `childrenMatchSf`).
  2. `walkGates_hold`, `curL_honest`, `childSum_honest`, `ccL_honest`, `cmL_honest`, `cc_link`, `reads_at`,
     `walkGatesH_honest`: the 9 walk gates at every honest row, over handle labels, via `walkSat_closed`.
     Hypothesis: `h ≤ orderOf α`.
  3. `walk_coin_order_few`: at most `h²` coins `α` violate that hypothesis (finite field).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkGatesH
import Nock.NockVMROM.Thm54.VclL.Handle.WalkCoin

set_option autoImplicit false

namespace Nock.RedTeam.Batch2078

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms inTree_childCols
#print axioms airReorder_childCols
#print axioms child_link_nouns
#print axioms walkGates_hold
#print axioms curL_honest
#print axioms childSum_honest
#print axioms ccL_honest
#print axioms cmL_honest
#print axioms cc_link
#print axioms reads_at
#print axioms walkGatesH_honest
#print axioms walk_coin_order_few

end Nock.RedTeam.Batch2078
