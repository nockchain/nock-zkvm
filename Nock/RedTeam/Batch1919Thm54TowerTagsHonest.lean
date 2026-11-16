/-
  Nock/RedTeam/Batch1919Thm54TowerTagsHonest.lean

  **The hosted child-state tags are a parameter of `genRowVals`.**

  * `genRowVals` / `honestOverlay` take the tag vector `tg : Fin 3 → 𝕂′`; instantiated at
    `childStateTagCol W (i+1) k` (the deployed `overlayAt` value).  Every dependent lemma (`honest_rowMatch`,
    `genRow_*`, C1e/C1f lemmas, `TowerRowBridge`) re-proved with `tg` in scope.
  * `honest_rowMatch` (`RowMatchT` + `AgreeOffT`) still holds with real tags: `Row309Reads` is generic in the overlay.
  * `nextTag_honest` / `firstTag_honest`: `NextReads.tag` / `FirstReads.tag` discharged.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerReadsHonest
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowBridge
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticData

set_option autoImplicit false

namespace Nock.RedTeam.Batch1919

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54 Nock.ComputeTable

/-- NC (discriminating): at a live child the honest overlay's tag is NOT the old null tag. -/
theorem nc_tag_live_not_null {L : Type} [Field L] (hchar : ∀ n : ℕ, 0 < n → n ≤ 10 → (n : L) ≠ 0)
    (pub : Nock.ComputeTable.Pub L) (W : List (Nock.Walk.NTree (State × DTcomp L))) (i : ℕ) (k : Fin 3)
    (c : Nock.Walk.NTree (State × DTcomp L))
    (hc : ((W[i]?).bind fun t => t.children[(k : ℕ)]?) = some c) :
    ovTag (honestOverlay (fun k => childStateTagCol W (i + 1) k) pub) k ≠ (nullStateTag : L) := by
  rw [honestOverlay_tags]
  unfold childStateTagCol
  simp only [Nat.add_sub_cancel, hc, Option.map_some, Option.getD_some]
  exact stateTag_ne_null hchar _

end Nock.RedTeam.Batch1919

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honestOverlay_tags
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms nextTag_honest
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms firstTag_honest
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honest_rowMatch
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honest_rowMatch_feeds_rowLocal
#print axioms Nock.RedTeam.Batch1919.nc_tag_live_not_null
