/-
  Nock/RedTeam/Batch2090Thm54VSHonestD.lean

  1. `trie_hSum`, `walk_provide_total` (WalkRecH): the honest walk twin's provided handle-record total,
     for any weight, equals the total over the path-kind reads.
  2. `fdN_slot`, `row_cons_eq`, `compute_walk_balance` (PathConsH): the compute side's walk-handle consumes
     (OP0, OP9, OP5 pair) balance the walk provides.  FINDING: `demandH.preads` lacks the OP5 pair reads;
     the balanced walk is built from `walkReadsH`.
  3. `claim_validity_balanced`, `claim_row_provides`, `claim_denotes_honest` (ClaimBalH): the claim record is
     provided once by the validity balance and consumed once by the `hpub` gates (`pubVec_hdl`).
  4. `cellH_gates_honest`, `walkH_gates_honest`, `den_bad_card`, `cell_terminal_is_consumed`,
     `cellH_gates_wrong_pub` (TwinGatesH): the 4 + 9 twin LogUp gates at the honest fill, the priced pole
     event, the cell twin's public equal to the consumed total, a discriminating negative control.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkRecH
import Nock.NockVMROM.Thm54.VclL.Handle.PathConsH
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimBalH
import Nock.NockVMROM.Thm54.VclL.Handle.TwinGatesH

set_option autoImplicit false

namespace Nock.RedTeam.Batch2090

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms trie_hSum
#print axioms walk_provide_total
#print axioms fdN_chain
#print axioms fdN_slot
#print axioms row_cons_eq
#print axioms compute_walk_balance
#print axioms claim_validity_balanced
#print axioms claim_row_provides
#print axioms claim_denotes_honest
#print axioms pubVec_hdl
#print axioms rlcH_eval
#print axioms denKey_eval
#print axioms cellH_gates_honest
#print axioms cellH_gates_wrong_pub
#print axioms walkH_gates_honest
#print axioms den_bad_card
#print axioms den_ne_zero_of_not_bad
#print axioms cell_terminal_is_consumed

end Nock.RedTeam.Batch2090
