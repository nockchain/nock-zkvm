/-
  Nock/RedTeam/Batch1941Thm54ShdPathRouting.lean

  **Honest-side routing of depth-1 path reads (axes 2/3) to the
  memory path table.**

  * `Demand` gains `preads` (the path-kind reads); `demandOfRowsD` splits the slot keys by `slotAcc`
    (`rowExportKeys` / `rowPathKeys`), so an axis-2/3 read at `s0` / `s9` goes to the path table.
  * `isPathAx a := 1 ≤ depthOf a`, `pathReads := (filter isPathAx).dedup`; `pathTable`, `edgeSided`,
    `edgeParents`, `exportConsumers`, `xs0` / `xs1`, `req_eq`, `honestReqCF` run over `preads`.
  * Not proved; axis 1 is not admissible on the path chip (`shd_axis1_first`).
  * Here: `shd_provides_pathTable` (SHD's `shd_provides` restated against the NEW `pathTable`) and the
    item-7 negative controls on the real generator output for `[0 2]`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.RedTeam.Batch1748Thm54VclLSlotKeys
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 20000

namespace Nock.RedTeam.Batch1941

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.TraceGen

section Provides
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]
variable (z : Quad (algebraMap F K δF)) (cells : List Noun)

theorem shd_bits_ne (a : ℕ) (ha : a = 2 ∨ a = 3) : axisBits a ≠ [] := by
  rcases ha with rfl | rfl <;> decide

/-- **SHD's `shd_provides`, against the new `pathTable`**: every depth-1 read `(root, 2|3)` of `preads`
with a defined slot has a row IN `pathTable δF z cells preads` that is the last row of its (one-row)
chain, carries the multiplicity `preads.count r`, and provides exactly `pReq (root, a)`. -/
theorem shd_provides_pathTable (preads : List (Noun × ℕ)) (r : Noun × ℕ)
    (hr : r ∈ pathReads preads) (ha : r.2 = 2 ∨ r.2 = 3) (hs : (Noun.slot r.2 r.1).isSome) :
    ∃ x ∈ pathTable δF z cells preads, x.last = 1 ∧ x.m = (preads.count r : F) ∧
      pRecOf δF x = pReq δF z cells r := by
  have ha1 : 1 ≤ r.2 := by rcases ha with h | h <;> omega
  obtain ⟨child, hw⟩ : ∃ child, chainWalk r.1 (axisBits r.2) = some child := by
    rw [slot_eq_chainWalk r.2 ha1] at hs
    exact Option.isSome_iff_exists.mp hs
  have hsl : Noun.slot r.2 r.1 = some child := by rw [slot_eq_chainWalk r.2 ha1]; exact hw
  have hlen : (pathSteps r.1 (axisBits r.2)).length = 1 := by
    have := congrArg List.length (pathSteps_sides r.1 (axisBits r.2) (by rw [hw]; rfl))
    simp only [List.length_map] at this
    rw [this]; rcases ha with h | h <;> rw [h] <;> decide
  refine ⟨chainRow δF z cells r.1 (preads.count r) (pathSteps r.1 (axisBits r.2)) 0, ?_, ?_, ?_, ?_⟩
  · unfold pathTable
    rw [List.mem_flatMap]
    refine ⟨r, hr, ?_⟩
    unfold chainRows
    rw [List.mem_map]
    exact ⟨0, List.mem_range.mpr (by omega), rfl⟩
  · simp [chainRow, hlen]
  · simp [chainRow, hlen]
  · have := pRecOf_chain_last z cells r.1 r.2 (preads.count r) child ha1 (shd_bits_ne r.2 ha) hw
    rw [hlen] at this
    exact this

/-- The path table of depth-1 reads (axes 2/3) is `PathGood` (the chip's row/step/tiling facts). -/
theorem pathTable_good_depth1 (preads : List (Noun × ℕ)) (h : ∀ r ∈ preads, r.2 = 2 ∨ r.2 = 3) :
    PathGood (pathTable δF z cells preads) :=
  pathTable_good z cells preads fun r hr => by
    simp only [pathReads, List.mem_dedup, List.mem_filter] at hr
    rcases h r hr.1 with h2 | h2 <;> rw [h2] <;> decide

end Provides

/-! ## Item 7: the old routing was load-bearing (`[0 2]` on the real generator output) -/

section NC

/-- The subject `[7 9]` and the formula `[0 2]` (read the head: depth-1 path read at `s0`). -/
abbrev subj : Noun := .cell (.atom 7) (.atom 9)
abbrev frm : Noun := .cell (.atom 0) (.atom 2)

def rows02 : List (GenComputeRow Rat) :=
  [skelNode (genSkelOp0 subj frm (.atom 0) (.atom 2) (.atom 7) 2)
    [⟨frm, .atom 2, 3, 0⟩, ⟨subj, .atom 7, 2, 0⟩]]

/-- The new demand: ONE row; the formula is an export read `([0 2], 3)`, and the axis-2 slot read
`(subj, 2)` is a PATH read. -/
theorem demand02 :
    rows02.length = 1 ∧ (demandOfRowsD rows02).reads = [(frm, 3)] ∧
      (demandOfRowsD rows02).preads = [(subj, 2)] := by decide +kernel

/-- **NC (the old routing was load-bearing)**: the OLD path filter `deepReads` (depth `≥ 2`) selects NO
path read from the `[0 2]` demand, so the old path table is empty and the old closed form's
path-provide list is `[]`; the new routing selects the read.  The memory side's `req 2` (the sum of
`den⁻¹` over `reqRecs 2`) is thus a sum over `[]` (old) versus over one record `pReq (subj, 2)` (new). -/
theorem nc_old_routing_empty :
    deepReads (demandOfRowsD rows02).preads = [] ∧
    ((demandOfRowsD rows02).preads.filter fun r => isDeep r.2) = [] ∧
    pathReads (demandOfRowsD rows02).preads = [(subj, 2)] ∧
    ((demandOfRowsD rows02).preads.filter fun r => isPathAx r.2) = [(subj, 2)] := by
  decide +kernel

/-- The chain of the read is non-empty (one edge, the root cell, side `0`): the path chip has a row
the old table lacked. -/
theorem nc_chain_row : pathSteps subj (axisBits 2) = [(subj, false)] := by decide +kernel

/-- The export side is unchanged (distinct reads): the export consumers and the per-side counts of
the new routing equal the old routing's (`edgeParents` over the old deep reads, shallow over all). -/
theorem exports_unchanged :
    exportConsumers (demandOfRowsD rows02).preads (demandOfRowsD rows02).reads = [subj, frm] ∧
    xs0 (demandOfRowsD rows02).preads (demandOfRowsD rows02).reads = [subj] ∧
    xs1 (demandOfRowsD rows02).preads (demandOfRowsD rows02).reads = [frm] ∧
    -- the pre-SHD routing: all slot keys as `reads`, no `preads`
    xs0 [] [(frm, 3), (subj, 2)] = [subj] ∧ xs1 [] [(frm, 3), (subj, 2)] = [frm] := by
  decide +kernel

/-- **Disclosed deviation from "counts unchanged"**: for a REPEATED depth-1 path read (two rows both
reading `(subj, 2)`) the new `xs0` counts the parent ONCE (one path row, one unconditional export
consume, `m = 2` on the provide), where the pre-SHD shallow routing counted it per occurrence.  The
chip forces one consume per path row, so this is the completeness-correct count. -/
theorem repeated_read_dedup :
    xs0 (demandOfRowsD (rows02 ++ rows02)).preads (demandOfRowsD (rows02 ++ rows02)).reads = [subj] ∧
    xs0 [] [(frm, 3), (subj, 2), (frm, 3), (subj, 2)] = [subj, subj] ∧
    (pathReads (demandOfRowsD (rows02 ++ rows02)).preads).length = 1 ∧
    (demandOfRowsD (rows02 ++ rows02)).preads.count (subj, 2) = 2 := by decide +kernel

theorem nc_axis1_dropped : pathReads [(subj, 1)] = [] ∧ isPathAx 1 = false ∧ isPathAx 2 = true ∧
    isPathAx 3 = true := by decide +kernel

end NC

end Nock.RedTeam.Batch1941

#print axioms Nock.RedTeam.Batch1941.shd_provides_pathTable
#print axioms Nock.RedTeam.Batch1941.pathTable_good_depth1
#print axioms Nock.RedTeam.Batch1941.demand02
#print axioms Nock.RedTeam.Batch1941.nc_old_routing_empty
#print axioms Nock.RedTeam.Batch1941.nc_chain_row
#print axioms Nock.RedTeam.Batch1941.exports_unchanged
#print axioms Nock.RedTeam.Batch1941.repeated_read_dedup
#print axioms Nock.RedTeam.Batch1941.nc_axis1_dropped
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCL.req_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honestReqCF_eq_req
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.pathTable_good
#print axioms Nock.NockVMROM.Thm54.VclL.demandOfRowsD_reads_le
#print axioms Nock.NockVMROM.Thm54.VclL.demandOfRows_reads_sub
#print axioms Nock.NockVMROM.Thm54.VclL.slot0_in_shallowLookups
#print axioms Nock.NockVMROM.Thm54.VclL.rowSlotKeys_sub
