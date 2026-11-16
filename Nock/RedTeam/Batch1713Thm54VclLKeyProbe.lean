/-
  Nock/RedTeam/Batch1713Thm54VclLKeyProbe.lean

  Production: `Thm54/VclL/Compute/Keys.lean`.

  * `colRoundVCL_zero_iff` (`decide +kernel` over the 221 columns): the compute B0 is exactly
    `0..12`, `202..207`, `220`; `roles_not_b0`: every `𝕂`-role column `13..201` is round `≥ 1`.
  * **Export: B0, holds.** `export_key_clause`: at `Key := ℕ × Bool`, the export record's key
    `(natLift slot 9, false)` equals `recKeyExport x (b0 Q) j` (typed on `B0Cols`, reading the
    `vIdxCol j` column) for every trace `Q`, node `x`, lookup `j`.
  * `root_serial_key_unservable` / `key_determines_slot`: a path key reading only the
    root serial (`ℕ`, the addendum's path key) makes `served κ` answer two honest reads of one root at
    axes `2` and `3` — impossible (`honest_two_axes_one_root`), so `MemSoundnessFamily.response_sound`'s
    slot clause fails for one record.  The key must carry the axis; under option R the compute-side
    axis is the formula atom `f_t.leaf` / `f_th.leaf`, a `𝕂`-role column (round `≥ 1`), and
    `nonB0_slot_not_b0_key` / `path_axis_key_needs_b1` show no `B0Cols`-typed `recKey` reproduces a key
    slot read from a non-B0 column (two traces differing only there have the same B0 projection).

  Axioms `{propext, Classical.choice, Quot.sound}`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.Keys
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1713

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms colRoundVCL_zero_iff
#print axioms roles_not_b0
#print axioms export_key_clause
#print axioms honest_two_axes_one_root
#print axioms root_serial_key_unservable
#print axioms key_determines_slot
#print axioms nonB0_slot_not_b0_key
#print axioms path_axis_key_needs_b1
#print axioms inline_record_not_requested

end Nock.RedTeam.Batch1713
