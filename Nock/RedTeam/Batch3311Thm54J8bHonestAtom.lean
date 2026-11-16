/-
  Nock/RedTeam/Batch3311Thm54J8bHonestAtom.lean

  * `atomChipHQ_accepts_honest`: the 349-column atom twin accepts the honest trace
    (`atomTraceHQ`: base `0..204` plus the twelve round-1 `𝕂′` role limbs `313..348`), under the
    row-level side conditions `hbase` (the atom base gates vanish at the zero-role fill),
    nonzero denominators, and the three terminal publics.
  * `hnewM` is split: `E1` / `EK` role lemmas, `E1_agree`, `EK_den`, and the generic LogUp block
    `atom_block` (one call per triple mb / c / mi).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestA8

namespace Nock.RedTeam.Batch3311

open Nock.NockVMROM.Thm54.VclL.Handle.HonestA8

#print axioms trip_gates
#print axioms atom_block
#print axioms atomChipHQ_accepts_honest

end Nock.RedTeam.Batch3311
