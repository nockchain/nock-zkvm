/-
  Nock/RedTeam/Batch2721Thm54A3sTwoProvider.lean

  Additive; see `Handle/AtomServedQ.lean`.

  * Item 1 — summand #4 serves the old-export consume: `atom_consume_served`, and A-2's named hypothesis
    `ConsumeServedQ` discharged by `consumeServedQ_of_balance` (outside the weighted IO failure event of the
    lifted records at `(γH′, ρH′)`, under the verifier's balance `(pub₄, pub₅) = (pub₁₀, pub₁₁) + Σ_wreqs` with the
    atom-walk consumers `wreqs` abstract, and the consumer count `< p`).
  * Item 2 (chip level, `Handle/TwoProviderQ.lean`): `served2_of_balanced2`, `rowOK_of_gates2`, the consumer-side
    served lemma for weighted child keys `cell_child_served2`, key decoding `child_key_decode`,
    `cell_validityServed2`, `cellTable_accepts2` (rank-0 match against `RowOK`), `cell_row_genuine2`; the wire
    key `keyHK_eval`; `exportHK_genuine` (`exportH_genuine` at the wire kind on `cellChipHQK`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ
import Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ

namespace Nock.RedTeam.Batch2721

open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ

#print axioms atom_tele
#print axioms atomProvs_sum
#print axioms atomCReqs_sum
#print axioms atom_consume_served
#print axioms consumeServedQ_of_balance

open Nock.NockVMROM.Thm54.VclL in
section
#print axioms decodeTree_leaf1
#print axioms decodeTree_sound
#print axioms decode_sound_of_generic
#print axioms treeOK_leaf2
#print axioms row_genuine2
#print axioms exportRecK_grounded
#print axioms claimK_genuine_cell
#print axioms claimK_genuine_atom
end

open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ in
section
#print axioms served2_of_balanced2
#print axioms rowOK_of_gates2
#print axioms cell_child_served2
#print axioms child_key_decode
#print axioms cell_validityServed2
#print axioms cellTable_accepts2
#print axioms cell_row_genuine2
#print axioms side_kind
#print axioms keyHK_eval
#print axioms cellChipHQK_restrict_cell_sat
#print axioms exportHK_genuine
end

end Nock.RedTeam.Batch2721
