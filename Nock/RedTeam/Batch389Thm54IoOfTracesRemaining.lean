import Nock.NockVMROM.Thm54.RemainingIoObstructions
import Nock.RedTeam.Batch388Thm54OpenConjunctsTransfer

/-!
Re-exports the two remaining-I/O lemmas `specializeMemRec_active_zero_ts` and `wrapMemory_active_ts_recovered`, and records that `io` is still among `Batch388.openConjuncts` (`io_still_open`), so the closed count stays 8 of 21 (`closed_count_unmoved`).
-/

/-!
Re-exports the two remaining-I/O lemmas `specializeMemRec_active_zero_ts` and `wrapMemory_active_ts_recovered`, and records that `io` is still among `Batch388.openConjuncts` (`io_still_open`), so the closed count stays 8 of 21 (`closed_count_unmoved`).
-/

/-!
Re-exports the two remaining-I/O lemmas `specializeMemRec_active_zero_ts` and `wrapMemory_active_ts_recovered`, and records that `io` is still among `Batch388.openConjuncts` (`io_still_open`), so the closed count stays 8 of 21 (`closed_count_unmoved`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch389

noncomputable abbrev specializeMemRec_active_zero_ts :=
  @Nock.NockVMROM.Thm54.RemainingIoObstructions.specializeMemRec_active_zero_ts

noncomputable abbrev wrapMemory_active_ts_recovered :=
  @Nock.NockVMROM.Thm54.RemainingIoObstructions.wrapMemory_active_ts_recovered

/-- `io` is still among the open conjuncts of the transfer. -/
theorem io_still_open :
    "io" ∈ Nock.RedTeam.Batch388.openConjuncts := by
  decide

/-- The closed count remains 8 of 21. -/
theorem closed_count_unmoved :
    21 - Nock.RedTeam.Batch388.openConjuncts.length = 8 :=
  Nock.RedTeam.Batch388.closed_count

#check specializeMemRec_active_zero_ts
#check wrapMemory_active_ts_recovered

end Nock.RedTeam.Batch389

#print axioms Nock.RedTeam.Batch389.io_still_open
#print axioms Nock.NockVMROM.Thm54.RemainingIoObstructions.specializeMemRec_active_zero_ts
