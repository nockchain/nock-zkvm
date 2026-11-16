/-
  Nock/RedTeam/Batch1747Thm54VclLExistenceForm.lean

  Census of the consumers of the ℕ multiset balances (measured by grep over `Nock/` at this commit):
  * `ValidityBalanced` — read only through `TableAccepts.valid`, whose only readers were
    `consumed_left` / `consumed_right` (`P8Core/VclL/Table.lean`), called from `decode_sound` (T1)
    and `Chips/Prelim.decode_exists`.  Both conclude EXISTENCE of a providing row.  Restated:
    `TableAccepts.served : ValidityServed t` (existence), `consumed_left/right` take it;
    `ValidityBalanced.served` (balance ⇒ existence); the balance versions are
    `consumed_left_of_balanced` / `consumed_right_of_balanced`.
  * `ExportBalanced` — read only by `edge_exported_of_balanced`; T3 (`chain_sound`,
    `chain_sound_root`, `chain_sound_of_census`) already takes the existence form
    `∀ e ∈ es, EdgeExported t e`.  Nothing to restate.
  NC kept: the relinking forgery  is REJECTED by the existence form
  (`relink_rejected`) as well as by the balance (`relink_rejected_balanced`).
-/
import Nock.RedTeam.Batch1672Thm54VclLRelink

namespace Nock.RedTeam.Batch1747

open Nock.NockVMROM.Thm54.VclL

#print axioms ValidityBalanced.served
#print axioms consumed_left
#print axioms consumed_right
#print axioms decode_sound
#print axioms preZNounOfTable_sound
#print axioms served_of_b0
#print axioms chain_sound
#print axioms chain_sound_root
#print axioms Nock.RedTeam.Batch1672.relink_rejected
#print axioms Nock.RedTeam.Batch1672.relink_rejected_balanced
#print axioms Nock.RedTeam.Batch1672.honest_accepted

end Nock.RedTeam.Batch1747
