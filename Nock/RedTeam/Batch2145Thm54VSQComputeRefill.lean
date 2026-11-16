/-
  Nock/RedTeam/Batch2145Thm54VSQComputeRefill.lean

  New module `RefillCQ`; additive.

  * `rowSel_congr`, `slotD_eq`, `slotA_eq`, `notBad_of_sel`, `act_mem_reqs`, `notBad_of_reqs`: at a row with
    `RowSel` whose consumed records have nonzero denominators, no slot is bad, so `A / D` fills the slot;
  * `refillP` (the `P` columns outside `43..57` as the SAME polynomials, the fill interpolated on `43..57`),
    `refill_trace_old/new`, `refill_next_old/new`, `fillC_accX/P`;
  * **`computeChipVCLH_of_HQ`**: `computeChipVCLHQ`-acceptance of `P` at `chalVQ / pubVQ` gives
    `computeChipVCLH`-acceptance of `refillP` at `chalV / pubV`, when the walk coins (limbs `6..11`) and the
    publics `< 15` agree, every consumed record of every row has a nonzero denominator at the `𝕂` coins of
    `chalV`, and the handle terminals of `pubV` are the totals of the per-row terms.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RefillCQ

namespace Nock.RedTeam.Batch2145

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms RefillCQ.rowSel_congr
#print axioms RefillCQ.notBad_of_sel
#print axioms RefillCQ.notBad_of_reqs
#print axioms RefillCQ.refill_trace_new
#print axioms RefillCQ.refill_next_new
#print axioms RefillCQ.computeChipVCLH_of_HQ

end Nock.RedTeam.Batch2145
