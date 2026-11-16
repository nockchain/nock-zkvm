/-
  Nock/RedTeam/Batch1837Thm54VclLMemSoundnessVCL.lean

  **`MemSoundnessVCL`.**  Production: `VclL/Chips/MemSoundnessVCL.lean`.

  `memSoundnessVCL δF hT hP : MemSoundnessFamily F K (Quad δ) (Quad δ) RV.KeyVCL frameVCL hC (shapeV hT hP)
  C 3 (RV.recordViewVCL …) (seedSpecVCL δ) (ioSpecVCLQuad δ)` — every SOUNDNESS field is a theorem
  (`response_sound := vcl_response_sound`, `serves := vcl_serves`, the IO facts from the three
  accumulators' telescopes, the B0 served-noun decode, the summands `[zero seed, census, dyck-root]`).

  **Labelled: instance level.**  Memory-side coordinates `Kio = Kfp = Quad δ`
  (the compute family `CompSoundnessVCL` is at the test instance `Kio = Kfp = K`; they meet after the
  tower instance of the compute chip).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1837

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms memSoundnessVCL

end Nock.RedTeam.Batch1837
