/-
  Nock/RedTeam/Batch3333Thm54J8bHonestSlotAcc.lean

  * `slotGateQX_honest`: the six coordinate gates of a slot pair vanish at a row whose inverse limbs
    hold `A · D⁻¹`, outside the pole event (`D ≠ 0 ∨ A = 0`).
  * `accGatesX_prefixK`: the `ChipHX` accumulator gates (masks `17 / 18`) vanish at a prefix-sum fill.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX

namespace Nock.RedTeam.Batch3333

open Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX

#print axioms slotGateQX_eq
#print axioms slotGateQX_honest
#print axioms accGatesX_prefixK

end Nock.RedTeam.Batch3333
