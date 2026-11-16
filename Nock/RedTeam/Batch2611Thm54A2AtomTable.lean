/-
  Nock/RedTeam/Batch2611Thm54A2AtomTable.lean

  Additive; see `Handle/AtomChipHQ.lean`.

  * `inc_chain_carry` / `inc_chain_sound` (`val new = val old + 1`, A-1 `carry_val`), `conv_sound`;
  * `chainOK_of_gates` (field gates ⇒ ℕ chain relations, `2^63 < char`);
  * `OldGenuine` discharged by the consume: `oldGenuine_of_served`, `inc_chain_sound_of_served`, from the
    NAMED hypothesis `ConsumeServedQ` (atom export balance soundness, A-3s class, not proved here);
  * the honest two-row chain `2^64 + B − 1 ↦ 2^64 + B`: gates vanish (`ex_gates`), chain relations from
    the gates (`ex_chainOK_of_gates`), value (`ex_inc_sound_of_gates`, `ex_new`); NC
    `ex_wrong_limb_rejected` / `ex_wrong_limb_gate`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ

namespace Nock.RedTeam.Batch2611

open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ

#print axioms atomChipHQ_width
#print axioms atomGates_deg
#print axioms atomMixed_deg
#print axioms atomChipHQ_restrict_sat
#print axioms atomChipHQ_restrict_cell_sat
#print axioms atomChipHQ_restrict_bind
#print axioms atomTable_accepts
#print axioms inc_chain_carry
#print axioms inc_chain_sound
#print axioms conv_sound
#print axioms chainOK_of_gates
#print axioms ex_gates
#print axioms ex_chainOK_of_gates
#print axioms ex_inc_sound_of_gates
#print axioms ex_new
#print axioms ex_wrong_limb_rejected
#print axioms ex_wrong_limb_gate
#print axioms oldGenuine_of_served
#print axioms inc_chain_sound_of_served
#print axioms ex_served
#print axioms ex_inc_sound_of_served

end Nock.RedTeam.Batch2611
