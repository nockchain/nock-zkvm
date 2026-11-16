/-
  Nock/RedTeam/Batch3183Thm54J8aServedAccept.lean

  * `GoodCJ8` / `BalJ8` / `balJ8_of_good`: the three handle-class balance checks on the published
    terminals and the balance identity after the memory telescopes;
  * `ProvP` / `ProvOK` / `AxOK`: the memory providers' obligations, per balance;
  * `consQX_tags` / `reVal_lt`: consumed record entries are `< p` (`4 < p`);
  * `den_prov_ne_of_out`: provider denominators nonzero outside the weighted IO event;
  * `servedP_of_balancesJ8` / `served_of_balancesJ8`: `RowsAccX.served` from the balances;
  * `ax_of_axOK`: `RowsAccX.ax` from the path balance;
  * `goalJ8`, **`acceptsJ8_holdsN_compute`**: an accepted J-8 compute trace proves `HoldsN` of the
    claim, under the memory side's obligations.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8

namespace Nock.RedTeam.Batch3183

open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8

#print axioms slotsX_tags
#print axioms consQX_tags
#print axioms reVal_lt
#print axioms den_prov_ne_of_out
#print axioms balJ8_of_good
#print axioms servedP_of_balancesJ8
#print axioms served_of_balancesJ8
#print axioms ax_of_axOK
#print axioms bctx_of_xctx
#print axioms goalJ8
#print axioms acceptsJ8_holdsN_compute

end Nock.RedTeam.Batch3183
