/-
  Nock/RedTeam/Batch1994Thm54WalkW4dRequest.lean

  **The walk family's honest requests are compute's `honestReqCF`,
  and the joint compute–walk datum.**

  * `HonestVCLW.req_eq` (`HonestVCLWReq.lean`): `vTot = 0`; `xTot − yTot = Σ_{shallowSided} den⁻¹` (every
    walk node is a table cell, `walkRows_node_mem`; a walk row consumes its node's side-0 export record,
    `wxKey_eq`); `pTot = Σ_{pathKind preads} den⁻¹(pReq)` (the trie multiset identity `trie_pSum`).
  * `HonestVCLW.req_eq_CF`: the same as `honestReqCF` (the compute side's closed form is UNCHANGED).
  * `jointMemW` / `jointMemW_honestV` (`rfl`) / `jointMemW_honestReq` (`hslot` from the run).
  * NC `trie_pSum_needs_hslot`: without `hslot` the identity fails — for a read through an ATOM the trie
    still ends a target at the atom (multiplicity `1`) and its record's child is `hd` of the atom, while
    the request's child is the undefined slot's default `0`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointHonestW

set_option autoImplicit false

namespace Nock.RedTeam.Batch1994

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.TraceGen

/-- **NC for the `hslot` premise**: the read `(⟦7 8⟧, 4)` walks `[false, false]` through the ATOM `7`.
The trie descends to the atom (as a walk row) and ends the target there with `mL = 1`; that row's left
record names the child `hdN 7 = 7`, but the read's slot is undefined, so the request record names the
default `0`.  The two records differ in the child, so `trie_pSum`'s per-node step needs the slot defined. -/
theorem trie_pSum_needs_hslot :
    let root : Noun := .cell (.atom 7) (.atom 8)
    targetsOf [(root, 4)] root = [[false, false]] ∧
      (trie root root [] [[false, false]]).children = [trie root (.atom 7) [false] [[false]]] ∧
      (trie root (.atom 7) [false] [[false]]).label.mL = 1 ∧
      hdN (trie root (.atom 7) [false] [[false]]).label.node = .atom 7 ∧
      (Noun.slot 4 root).getD (.atom 0) = .atom 0 ∧ (Noun.atom 7 ≠ Noun.atom 0) := by
  refine ⟨by decide, rfl, rfl, rfl, by rw [slot_eq_chainWalk 4 (by norm_num)]; rfl, by decide⟩

end Nock.RedTeam.Batch1994

#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.axisBits_axisFold
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.sum_regroup_fst
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.trie_pSum
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCLW.walkRows_node_mem
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCLW.vTot_eq_zero
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCLW.xTot_sub_yTot_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCLW.pTot_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCLW.req_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestVCLW.req_eq_CF
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.jointMemW
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.jointMemW_honestV
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.jointMemW_honestReq
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.extraPremises_vclW4
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rowFactsAt_CFvW4
#print axioms Nock.RedTeam.Batch1994.trie_pSum_needs_hslot
