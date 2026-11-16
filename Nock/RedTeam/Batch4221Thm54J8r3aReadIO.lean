/-
  Nock/RedTeam/Batch4221Thm54J8r3aReadIO.lean

  The handle-balance IO lists read only round-0 base columns (no coin, no public):
  `compReqsX_congr` (< 69), `jLists_congr` (< 29), `cellProvsW_congr` (< 134), `atomIncProvs_congr` (< 205);
  per-row counts `consQX_length_le` (x 3, p 2, s 2), `compReqsX_length_le`. `realIO` / `real40`: `R` / `L` with
  the `cx` / `sv` / `p` lists read off the trace (`dep = ∅` proved); `rdX_realIO`, `rdS_realIO`, `rdP_real40`; the budgets `budX_of` / `budP_of` / `budS_of` and `hcount_of` from the public checks `BudJ8` (note `2·n ≤ N`: an `s5` row consumes two service records).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8

namespace Nock.RedTeam.Batch4221

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms ReadIOJ8.slotsX_read
#print axioms ReadIOJ8.compReqsX_congr
#print axioms ReadIOJ8.jLists_congr
#print axioms ReadIOJ8.cellProvsW_congr
#print axioms ReadIOJ8.atomIncProvs_congr
#print axioms ReadIOJ8.consQX_length_le
#print axioms ReadIOJ8.compReqsX_length_le
#print axioms RealIOJ8.reqsOf_eq
#print axioms RealIOJ8.provsJ8_eq
#print axioms RealIOJ8.realIO
#print axioms RealIOJ8.real40
#print axioms RealIOJ8.rdX_realIO
#print axioms RealIOJ8.rdS_realIO
#print axioms RealIOJ8.rdP_real40
#print axioms RealIOJ8.jRd_length
#print axioms RealIOJ8.jCons_length
#print axioms RealIOJ8.jProv_length
#print axioms RealIOJ8.budX_of
#print axioms RealIOJ8.budP_of
#print axioms RealIOJ8.budS_of
#print axioms RealIOJ8.hcount_of
#print axioms RealIOJ8.hcap_corner

end Nock.RedTeam.Batch4221
