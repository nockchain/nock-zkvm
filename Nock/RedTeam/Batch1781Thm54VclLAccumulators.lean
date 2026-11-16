/-
  Nock/RedTeam/Batch1781Thm54VclLAccumulators.lean

  **1782: the export / path accumulators on the VCL chip and
  the chip's `reqFacts`.**
  * `computeChipVCLE` = `computeChipVCLD` + two accumulators (export: slot 0 always, slot 1 on
    s2/s5/s6/s7/s8/s9, slot 2 on s6; path: slot 1 on s0, slot 2 on s9), terminals `ρ_export` /
    `ρ_path` at public limbs 42..44 / 45..47; `vclRAPE_fingerprint` `(3, 232, 339, 4, 2)`, degree 4;
    `colRoundVCLE` (IO-coin readers — slot inverses and accumulators — at round 2;
    `colRoundVCL` had the inverses at 1); `colRoundVCLE_zero_iff`;
  * `exportReqFacts` / `pathReqFacts` (`SVFrame.ReqIOFacts (compress coins) ρ`), records `≤ 3N` /
    `≤ 2N`; `acceptedRows_of_sat` (acceptance + injective, adjacent nodes + `hchar` ⇒ the row family;
    no trace premise), `selAt_of_gates`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.AccChip
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1781

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms vclGatesE_degree
#print axioms vclRAPE_fingerprint
#print axioms computeChipVCLE_sat_iff
#print axioms colRoundVCLE_zero_iff
#print axioms export_inv
#print axioms path_inv
#print axioms exportReqFacts
#print axioms pathReqFacts
#print axioms exportRecords_length_le
#print axioms pathRecords_length_le
#print axioms selAt_of_gates
#print axioms acceptedRows_of_sat

end Nock.RedTeam.Batch1781
