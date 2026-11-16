/-
  Nock/RedTeam/Batch2153Thm54VSQSoundness.lean

  New module `SoundVSQ`;
  additive.

  * **`hsoundVSQ`** (reduction to `hsoundVS` at `toVSV V`; no hypothesis beyond `hsoundVS`'s);
  * **`standaloneVSQ_sound`**, `standaloneVSQ_sound'`, **`standaloneVSQ_soundness_le`** (`≤ boundVCLHQ''`);
  * **`standaloneVSQ_155 / _154 / _164`** at the VS figures' row bounds (`|𝕂| = cK`, `leafBoundF ≤ 2^110`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SoundVSQ

namespace Nock.RedTeam.Batch2153

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms SoundVSQ.hsoundVSQ
#print axioms SoundVSQ.standaloneVSQ_sound
#print axioms SoundVSQ.standaloneVSQ_sound'
#print axioms SoundVSQ.standaloneVSQ_soundness_le
#print axioms SoundVSQ.standaloneVSQ_155
#print axioms SoundVSQ.standaloneVSQ_154
#print axioms SoundVSQ.standaloneVSQ_164

end Nock.RedTeam.Batch2153
