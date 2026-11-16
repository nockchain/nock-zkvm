/-
  Nock/RedTeam/Batch2064Thm54VSTeleC.lean

  **The compute side of the handle lookups.**
  Additive.  New module `Thm54/VclL/Handle/TeleC.lean`:
  * `computeChipVCLH_sat_iff`, `base_of_sat`, `k_of_sat` (row facts through the `ℚ`-template casts);
  * `onehot` / `rowSel_of_base` (one state on, under `11 < char 𝔽`);
  * `slot_core` / `slot_at`: a slot gate gives `Σ_{active} den⁻¹` (single entries force their own
    denominator nonzero; the batched OP5 read pair needs its two denominators nonzero, which comes from
    outside the IO pole event `den_ne_of_out`, never assumed);
  * `compX_sum` / `compP_sum`: the compute accumulators telescope (`LogUp.acc_rows`) to the public limbs;
  * `export_served` / `path_served` and at VS **`vs_served`**: from `V.Checks`, `AcceptsG` and outside the
    two handle IO failure events at `(χ₁₁, χ₁₂)`, every compute export key and walk-consumed key is a
    cell-twin key, and every compute walk record is a walk-twin provided record;
  * `rowXReqs_len` / `rowPReqs_len`: at most `3` export / `2` path records per row (`reqBoundVS`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleC

namespace Nock.RedTeam.Batch2064

open Nock.NockVMROM.Thm54.VclL.Handle.TeleC

#print axioms computeChipVCLH_sat_iff
#print axioms onehot
#print axioms rowSel_of_base
#print axioms slot_core
#print axioms termX_row
#print axioms termP_row
#print axioms compX_sum
#print axioms compP_sum
#print axioms den_ne_of_out
#print axioms export_served
#print axioms path_served
#print axioms rowXReqs_len
#print axioms rowPReqs_len
#print axioms coinsC_VS
#print axioms vs_served

end Nock.RedTeam.Batch2064
