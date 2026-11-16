/-
  Nock/RedTeam/Batch1990Thm54WalkW4cAccept.lean

  **The honest walk chip's columns, gates and acceptance
  (`VclL/Chips/HonestWalkCol.lean`, `VclL/Chips/HonestWalkAccept.lean`).**

  * `WalkVals` / `walkCol kr` (132 columns: B0 21 with column 2 the root mask `[i < kr]`, B1 the four
    fingerprints, B2 `ln count acc` and the five `𝕂′` IO quantities), `honestWalkQ`.
  * **`walkOk_sat`**: the `ok`-gated walk chip accepts the interpolated honest trace (masks: first,
    last, and `honestWalkQ_two`: the honest column 2 is the preprocessed `rootRowMaskW nodes kr`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestWalkAccept

#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walk_base_gates_hold
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walk_kgates_hold
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walk_qEqs_hold
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walk_mixed_gates_hold
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.honestWalkQ_two
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkChipOk_sat_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkOk_sat
