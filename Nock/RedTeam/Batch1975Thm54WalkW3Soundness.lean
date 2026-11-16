/-
  Nock/RedTeam/Batch1975Thm54WalkW3Soundness.lean

  **`memSoundnessVCLW` — the memory soundness family with
  the paper's walk in place of the path chip, at the interface `frameVCL` consumes.**

  Module `VclL/Chips/MemSoundnessVCLW.lean`:
  * the B0 decode / served-noun fields at `shapeVW` (twins of `MemSoundVCL` §1–§2);
  * `walk_records_sound` (`path_records_sound` twin): every walk record `(root, child, 2·prefix + b,
    rootIdx)` has key `path rootIdx axis`, root `enc (dnn rootIdx)`, child the subtree at `axis`
    (`preZ_some_facts`, `natOf_axis`: no wrap);
  * **`memSoundnessVCLW δF hT hP kr`**: a `MemSoundnessFamily` at `frameVCL` (11 coins),
    `RV.recordViewVCL`, `seedSpecVCL`, `ioSpecVCLQuad` — every soundness field proved.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCLW

set_option autoImplicit false

namespace Nock.RedTeam.Batch1975

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms decodedNounW_leaves
#print axioms vclServedKeysW_length
#print axioms vclServedW_leaves_le
#print axioms round1Coins_of_sampled0
#print axioms walkOfTr_readsOn
#print axioms vclWalkSummandW
#print axioms vclWalkSummandW_shape
#print axioms vclSummandsW_good
#print axioms preZ_some_facts
#print axioms natOf_axis
#print axioms natOf_of_zq
#print axioms wPRec_keys_congr
#print axioms walk_records_sound
#print axioms rowsOfTrW_eq
#print axioms vcl_response_soundW
#print axioms memSoundnessVCLW
#print axioms memSoundnessVCLW_walk_summand

end Nock.RedTeam.Batch1975
