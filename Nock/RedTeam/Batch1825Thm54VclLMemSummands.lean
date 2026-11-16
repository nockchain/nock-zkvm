/-
  Nock/RedTeam/Batch1825Thm54VclLMemSummands.lean

  **The seed and the summands of `vclMemFamily`.**
  Production: `VclL/Chips/MemSoundVCL.lean` §4.

  * `seedSpecVCL δ`: `seed χ = Quad.mk δ (χ 2) (χ 3)`, `dep = {2, 3}` (both sampled after B0 = M1),
    injective on `dep`;
  * `summands := vclSummands`: `SVFrame.zeroSummand` at `seedSpecVCL` (the joint list's zero-seed
    object; needed here because `T1`'s cons gate needs `z′ ≠ 0` BEFORE the dyck argument can run),
    `vclCensus` (T2 at `skel := []`, priced at the full `3 + 19N` skeleton majorant), `vclDyck`
    (the dyck-root event); all B0-const (`dep = ∅`, `rowsOfTr_const` from `TracesStaged`);
  * `vclSummands_good`: outside them, `z′ ≠ 0`, `z′ ∉ tableBadSeeds`, `z′ ∉ cellDyckRootSeeds` at the
    trace pair's round-0 rows `rowsOfTr` (read from the B0 columns only).
  * `reqCond := SVFrame.reqCondVCL` (`True`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1825

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms seedSpecVCL
#print axioms rowsOfTr_const
#print axioms vclSummands
#print axioms vclSummands_good
#print axioms vclSummands_shape

end Nock.RedTeam.Batch1825
