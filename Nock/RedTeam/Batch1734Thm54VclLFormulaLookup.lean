/-
  Nock/RedTeam/Batch1734Thm54VclLFormulaLookup.lean

  Production: `Thm54/VclL/Compute/FormulaLookup.lean`.
  * Slots (`slotAcc`): slot 0 = formula cell `(f, f_h, f_t, fIdx)` on every row; slot 1 = `f_t`
    export (`s2 s5 s6 s7 s8 s9`) / path (`s0`); slot 2 = `f_tt` export (`s6`) / core path (`s9`).
    `activeSlots_eq_recordCount` (every memory record is a lookup, `inlineRecordsD = 0`),
    `kc_eq_three`, `export_consumer_majorant` (`3N`), `path_consumer_majorant` (`N`).
  * Columns: B0 `fIdx = 222`, slot-0 inverse `223..225` (round 1, pre-tower `𝕂`);
    `colRoundVCLD_zero_iff` (B0 = `0..12`, `202..207`, `220`, `221`, `222`).
  * Gates: slot 0 `inv₀·den₀ − 1` (degree 2), slots 1/2 state-multiplexed `inv·den − act` (degree 3,
    one-hot state selectors only); `den = FiniteIO.compress` of the record (`coord_compress`).
    Soundness: `slot0_sound`, `slot1_sound_s0`, `slot1_sound_export`, `slot2_sound_s6`,
    `slot2_sound_s9`; inactive rows are free (`slot2_inactive`).
  * Key: `formula_key_clause` (slot 0's key reads B0 column 222 only).
  * Head: `lookup_binds_head`, `lookup_binds_head_row` (at a `V_comp` row the served formula's head is
    the opcode atom and `f_t` is its axis-3 child).
  * Chip: `computeChipVCLD` (`vclRAPD_fingerprint`: `(3, 226, 321, 4, 2)`), `computeChipVCLD_sat_iff`,
    `computeChipVCLD_slot0` (acceptance ⇒ the formula cell is consumed at every row).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.FormulaLookup
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1734

open Nock.NockVMROM.Thm54.VclL.Compute

/-- The slot table, measured. -/
example : activeSlots .s1 = 1 ∧ activeSlots .s0 = 2 ∧ activeSlots .cons = 1 ∧
    exportSlots .s6 = 3 ∧ pathSlots .s9 = 1 ∧ exportSlots .s9 = 2 := by decide

#print axioms activeSlots_eq_recordCount
#print axioms kc_eq_three
#print axioms slot0_export
#print axioms slot2_shared
#print axioms export_consumer_majorant
#print axioms path_consumer_majorant
#print axioms colRoundVCLD_zero_iff
#print axioms coord_compress
#print axioms slot0Gates_degree
#print axioms slot1Gates_degree
#print axioms slot2Gates_degree
#print axioms slot0_sound
#print axioms slot1_sound_s0
#print axioms slot1_sound_export
#print axioms slot2_sound_s6
#print axioms slot2_sound_s9
#print axioms slot2_inactive
#print axioms formulaRec_decoded
#print axioms formulaRec_val
#print axioms formula_key_clause
#print axioms lookup_binds_head
#print axioms lookup_binds_head_row
#print axioms forge_rejected_by_lookup
#print axioms forge_rejected_at_row
#print axioms forged_tail_not_served
#print axioms forge_accepted_inline_rejected_lookup
#print axioms vclGatesD_degree
#print axioms vclRAPD_fingerprint
#print axioms computeChipVCLD_sat_iff
#print axioms computeChipVCLD_slot0

end Nock.RedTeam.Batch1734
