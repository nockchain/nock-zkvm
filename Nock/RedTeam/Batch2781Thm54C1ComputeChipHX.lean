/-
  Nock/RedTeam/Batch2781Thm54C1ComputeChipHX.lean

  **The J-8 compute chip
  `computeChipVCLHX`** (J-8 SPEC §3).  Additive; see `Handle/ChipHX.lean`.

  Asserted below as `example`s so a change of any figure breaks this file.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ
import Nock.Jet.ChipJ8

namespace Nock.RedTeam.Batch2781

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

example : widthHX = 123 := rfl
example : widthHX = Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ.widthHQ + 38 := rfl

/-- Provider shapes: the compute `TAG_jet` consume has the J-3b `keyJet` shape (8 entries, columns,
then the constant `3` LAST, C-2 step 0); the `TAG_inc` consume has A-2's `incKey` length with `TAG_inc`
the constant `4` last. -/
theorem jetRec_matches_keyJet :
    jetRecX.length = Nock.Jet.ChipJ8.keyJet.length ∧ jetRecX.getLast? = some (.k 3) ∧
      Nock.Jet.ChipJ8.keyJet.getLast? = some (.k 3) ∧
      (jetRecX.dropLast.all fun e => match e with | .col _ => true | .k _ => false) = true ∧
      (Nock.Jet.ChipJ8.keyJet.dropLast.all fun e => match e with | .col _ => true | .k _ => false) = true := by
  decide

theorem incRec_matches_incKey :
    incRecX.length = (Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ.incKey (F := ℚ)).length ∧
      (Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ.tagInc : ℚ) = 4 ∧ incRecX.getLast? = some (.k 4) := by
  refine ⟨rfl, rfl, by decide⟩

#print axioms jetRec_matches_keyJet
#print axioms incRec_matches_incKey
#print axioms widthHX_eq
#print axioms computeChipVCLHX_width
#print axioms layoutX_tiles
#print axioms gatesHX_degree
#print axioms slotPairsX_keyOK
#print axioms walkGatesX_keyOK
#print axioms arithGatesX_serialFree
#print axioms accGatesHX_serialFree
#print axioms eqGatesX_ok
#print axioms keyOKQX_flags
#print axioms serialFreeX_flags_naive_pair
#print axioms serialFreeX_flags_naive_s10L
#print axioms keyOKX_flags
#print axioms slotsX_disjoint
#print axioms consumesX_op4
#print axioms consumesX_op5
#print axioms consumesX_s10
#print axioms consumesX_s10L
#print axioms consumesX_s10T
#print axioms consumesX_s11s
#print axioms consumesX_s11d
#print axioms consumesX_s11j
#print axioms service_consumers
#print axioms incKey_tag_beyond_fourth
#print axioms jetKey_collides_walkRecA
#print axioms fanoutX_new
#print axioms kind_split
#print axioms op4_fast_row
#print axioms op4_slow_row
#print axioms op5_pair_row
#print axioms s10_row
#print axioms s10L_row
#print axioms s10T_row
#print axioms s11_row

end Nock.RedTeam.Batch2781
