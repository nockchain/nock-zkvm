/-
  Nock/RedTeam/Batch2851Thm54C2ComputeSound.lean

  **`ChipJ8.keyJet` /
  `ChipHX.jetRecX` with `TAG_jet` LAST, `serviceKeys_disjoint`) and the modules
  `Nock/Edit/GenuineNX.lean` (the ℕ-level genuine tree, `genuineNX_sem`, the edit chain
  `edit_chain_sound`) and `Handle/LocalVSX.lean` (`RowSemX`, `local_stepX`, `state_of_formulaX`,
  `holdsN_of_rowsVSX`, the FINDING `kidKinds_load_bearing`) and `Handle/LocalOKX.lean` (step 3, first
  case: `op4_fast_sem`).**
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
import Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
import Nock.Jet.ChipJ8
import Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX

namespace Nock.RedTeam.Batch2851

open Nock Nock.Edit
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX

/-- Both sides put `TAG_jet = 3` LAST, 8 entries. -/
example : jetRecX.getLast? = some (.k 3) ∧ Nock.Jet.ChipJ8.keyJet.getLast? = some (.k 3) ∧
    jetRecX.length = 8 ∧ Nock.Jet.ChipJ8.keyJet.length = 8 := by decide

example {F : Type} [Field F] (γ id hk hv : F) :
    keyPoly γ [3, id, hk, hv, 0, 0, 0, 0] = keyPoly γ [3, id, hk, hv] :=
  jetKey_collides_walkRecA γ id hk hv

#print axioms serviceKeys_disjoint
#print axioms serviceTags_distinct
#print axioms keyPoly_eq_eval
#print axioms jetKey_collides_walkRecA
#print axioms genuineNX_sem
#print axioms genuineNX_holdsN
#print axioms holdsN_of_genuineNX
#print axioms edit_chain_sound
#print axioms local_stepX
#print axioms roles_of
#print axioms state_of_formulaX
#print axioms defined_treeX
#print axioms genuineNX_of_rowsX
#print axioms holdsN_of_rowsVSX
#print axioms kidKinds_load_bearing
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX.op4_fast_sem

end Nock.RedTeam.Batch2851
