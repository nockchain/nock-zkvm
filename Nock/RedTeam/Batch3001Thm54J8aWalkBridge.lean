/-
  Nock/RedTeam/Batch3001Thm54J8aWalkBridge.lean

  * The chip → label bridge of the J-8 compute walk: `curLX_eval`, `childrenX_eval`, `ccLX_eval`,
    `cmLX_eval` (the walk gate's `𝕂` terms are `rlc γ (encT …)` of the decoded handles; `hdV` values are
    `ZMod.val`, so `SmallR` holds of every decoded row, `smallR_rowW`).
  * `rowW`: the WALK decoding (an `s10L` row read through its chip child label `(s, (0, val v), e)`);
    same `(s, f, e)` (`rowW_trip`), same fanout; equal kids to `rowOfX` under exact halving
    (`kidsX_rowW_of_halving`).  `cwEvent` is generic in `rows`: no priced event changes shape.
  * `cwalkX_sat`: an accepted row sequence (`WalkRowsX`) gives `Walk.WalkSat` over `rowsWX`.
  * `halving_of_tree`, `holdsN_of_walkJ8`: the walk tree yields `HalvingOK` at every `s10L` node (no
    named halving hypothesis left) and, with `RowsAccX` (base, one-hot, served genuine records, the
    `s10L` sibling-read axis), `HoldsN` of the claim.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8

namespace Nock.RedTeam.Batch3001

open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8

#print axioms kidsX_rowW_of_halving
#print axioms smallR_rowW
#print axioms curLX_eval
#print axioms childrenX_eval
#print axioms ccLX_eval
#print axioms cmLX_eval
#print axioms cwalkX_sat
#print axioms halving_of_tree
#print axioms holdsN_of_walkJ8

end Nock.RedTeam.Batch3001
