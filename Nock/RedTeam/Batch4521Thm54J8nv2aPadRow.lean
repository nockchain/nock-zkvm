/-
  Nock/RedTeam/Batch4521Thm54J8nv2aPadRow.lean

  The atom table's inert
  pad row `(aL, aR) = (0, 1)`, `inc = c_out = mb = mi = wR = 0` passes every added base gate of `atomChipHQ` and
  the ruled gate `isL·c_out` (`pad_atomGates`, `pad_gL`); `aR = 0` is rejected by g3 (`g3_rejects_zero_top`); the
  padded generator `padExt rows padNew` discharges `hlast` by construction (`hlast_padExt`) and contributes `0` to
  the three accumulators (`pad_sum`); `atomChipHQL_accepts_honest_pad` is `atomChipHQL_accepts_honest` with
  `hlast` discharged and `hbase` needed on the list rows only.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomGenJ8

namespace Nock.RedTeam.Batch4521

open Nock.NockVMROM.Thm54.VclL.Handle

#check @AtomGenJ8.pad_atomGates
#check @AtomGenJ8.hlast_padExt
#check @AtomGenJ8.atomChipHQL_accepts_honest_pad
#print axioms AtomGenJ8.g3_rejects_zero_top
#print axioms AtomGenJ8.pad_atomGates
#print axioms AtomGenJ8.pad_gL
#print axioms AtomGenJ8.hlast_padExt
#print axioms AtomGenJ8.pad_sum
#print axioms AtomGenJ8.hbase_pad
#print axioms AtomGenJ8.atomChipHQL_accepts_honest_pad

end Nock.RedTeam.Batch4521
