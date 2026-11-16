/-
  Nock/RedTeam/Batch1915Thm54TowerReadsHonest.lean

  * `nextSrc_of_fill` / `firstSrc_of_fill`: `NextReads.src` / `FirstReads.src` at the honest tower env, from
    `hFn` / `hF`, `V_comp` at the row and the three `K`-valuedness side conditions (A-free; through
    `Row309Reads.semPub`).  `firstSel_of_bank`: `FirstReads.sel`.
  * `genHonestWalk_hroot`: `hroot` (`labelVecOfPub (D.pubAt 0) = claimLabelVec z claim`) from the generator's
    root skeleton; `genWalk_bfsPubAt`: `D.pubAt i` is C1c's `renderNode... (bfsLabelAt (airReorder t) (i+1))` row.
  * `den_noncircular`: `den0Q/den1Q/den2Q` do not read the slot-inverse columns (`den_entries_safe` by `decide`).
  * `nextTag_of_fill` / `firstTag_of_fill` give the read value.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerReadsHonest
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticData

set_option autoImplicit false

namespace Nock.RedTeam.Batch1915

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54 Nock.ComputeTable

/-- NC (`hroot` discriminates): two claims whose root states carry different tags have different label vectors,
so `hroot` for one refutes the other. -/
theorem nc_hroot_state_tag {L : Type} [Field L] (z : L) (c1 c2 : P8PublicClaim)
    (h : (stateTagField (ComputeWalkSeed.rootStateOfFormula c1.formula) : L) ≠
      stateTagField (ComputeWalkSeed.rootStateOfFormula c2.formula)) :
    ComputeWalkSeed.claimLabelVec z c1 ≠ ComputeWalkSeed.claimLabelVec z c2 := fun e =>
  h (congrFun e 0)

/-- NC (the non-circularity check discriminates): a record entry reading an inverse column is NOT safe. -/
theorem nc_entry_reads_inverse : ¬ entrySafe (.f 223) ∧ ¬ entrySafe (.k 221) ∧ ¬ entrySafe (.k 394) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact h (by unfold invColT; omega)
  · intro h; exact h.1 2 (by norm_num) (by unfold invColT; omega)
  · intro h; exact h.1 0 (by norm_num) (by unfold invColT; omega)

/-- NC (`firstSel_of_bank` discriminates): the bank placement distinguishes states. -/
theorem nc_state_tag_ne_null {L : Type} [Field L] (hchar : ∀ n : ℕ, 0 < n → n ≤ 10 → (n : L) ≠ 0) (st : State) :
    (stateTagField st : L) ≠ (nullStateTag : L) := stateTag_ne_null hchar st

end Nock.RedTeam.Batch1915

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms nextSrc_of_fill
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms firstSrc_of_fill
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms firstSel_of_bank
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms nextTag_of_fill
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms firstTag_of_fill
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms genHonestWalk_hroot
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms genWalk_bfsPubAt
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms den_noncircular
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms den_entries_safe
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honestOverlay_tags
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honestOverlay_tag_ne_childStateTagCol
#print axioms Nock.RedTeam.Batch1915.nc_hroot_state_tag
#print axioms Nock.RedTeam.Batch1915.nc_entry_reads_inverse
