/-
  Nock/RedTeam/Batch1715Thm54VclLInlineForge.lean

  Production: `Thm54/VclL/Compute/InlineForge.lean`.  The inline gate gives `f = cons(atomFP z op,
  f_t)` (SV head + cons), which pins `f_t` uniquely (`cons_right_unique`) but NOT nounally: nothing
  forces the formula's head to be the row's opcode.
  * `inline_sound_of_head`: for `rt = [op t]` the axis-3 child `t` has fingerprint `f_t`.
  * `wrong_opcode_inline_forge` (every seed `z ≠ 0`, every `k ≠ op` in `K`, every tail `t`): the
    forged `f_t = (S_t, D_t, L_t + (k − op)·z⁻¹)` satisfies the inline gate at `f = enc z [k t]`, and
    no axis-3 child of `[k t]` has fingerprint `f_t`.  `wrong_opcode_forge_s1`: a row labelled `s1`
    on the formula `[2 [0 1] [0 1]]`.
  So `CF.inline_records` is not dischargeable from the inline gate for ANY `inlinePairs`: the failure is
  a polynomial identity in `z`, and the unique axis-3 child is `t`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.InlineForge
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1715

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms inline_sound_of_head
#print axioms wrong_opcode_inline_forge
#print axioms wrong_opcode_forge_s1

end Nock.RedTeam.Batch1715
