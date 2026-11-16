/-
  Nock/RedTeam/Batch1914Thm54TowerWalkGen.lean

  **The generator's honest BFS walk and `NextReads` assembly.**

  * `genWalkRoot` (the carrier's committed compute tree), `genWalk_htopo` (`HonestWalk.htopo` from the
    generator's `assigned_airReorder_coins_binding`), `genHonestWalk_exists` (an `HonestWalk` over the
    generated tree at any `(α, γ)`), `genHonestWalk_pubAt`, `genHonestWalk_seed_claim` (seed = claim
    seed under the root binding `hroot`).
  * `nextReads_of_fill`: `NextReads` at the honest tower env from the next-row placement and the
    challenge placement; `src` / `tag` remain hypotheses.
  * NC (discriminating): `nc_seed_pins_claim_rlc`: at a nonzero walk coin the seed pins the claim
    label's `RLC^γ`: two claims with different `RLC^γ` give different seeds.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerWalkGen
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign

set_option autoImplicit false

namespace Nock.RedTeam.Batch1914

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

theorem nc_seed_pins_claim_rlc {L : Type} [Field L] (D : HonestWalk L) (z : L)
    (c₁ c₂ : Nock.NockVMROM.Thm54.P8PublicClaim) (hα : D.α ≠ 0)
    (h₁ : D.seed = Nock.Walk.rlc D.γ (Nock.NockVMROM.Thm54.ComputeWalkSeed.claimLabelVec z c₁) * D.α)
    (hne : Nock.Walk.rlc D.γ (Nock.NockVMROM.Thm54.ComputeWalkSeed.claimLabelVec z c₁) ≠
      Nock.Walk.rlc D.γ (Nock.NockVMROM.Thm54.ComputeWalkSeed.claimLabelVec z c₂)) :
    D.seed ≠ Nock.Walk.rlc D.γ (Nock.NockVMROM.Thm54.ComputeWalkSeed.claimLabelVec z c₂) * D.α := by
  rw [h₁]
  intro h
  exact hne (mul_right_cancel₀ hα h)

end Nock.RedTeam.Batch1914

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms genWalk_htopo
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms genHonestWalk_exists
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms genHonestWalk_pubAt
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms genHonestWalk_seed_claim
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms nextReads_of_fill
#print axioms Nock.RedTeam.Batch1914.nc_seed_pins_claim_rlc
