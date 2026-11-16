/-
  Nock/RedTeam/Batch1889Thm54TowerHonestPlace.lean

  **Next-row, challenge and public placement of the honest
  tower fill; `Vcomp_abc_irrel`.**

  * `pullNext_honestQT_trace` (next-row pull-back, given `ω·x_i = x_{i'}`), `towerEnv309_extNext_of_src`,
    `_baseNext_of_src`, `_walk_of_src`, `_walkNext_of_src`.
  * `towerEnv309_chal_placement`: slots `1..6, 10` are `z′, χ8, χ9, χ10, z′⁻¹, χ0, χ1`;
    `towerEnv309_pub_placement`: `E0 = χ0`, `E1 = seedVCLT` (at `pubCFT`).
  * `Vcomp_abc_irrel`: `Vcomp` ignores `(a, b, c)` (definitional).
  * Control `coin_slots_distinct`: at `𝔽 = 𝕂 = ZMod 7`, `δ = 3`, coins `χ i = i`, the slot-2/3/4 coins
    differ, so the chal placement is not a constant map.
  UNCONFIRMED: the generator -> `TowerRowVals` map (not done), `honest_staged`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestPlace
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1889

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute.TowerD

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

instance : Fact (¬ IsSquare ((algebraMap (ZMod 7) (ZMod 7)) (3 : ZMod 7))) :=
  ⟨by simp only [Algebra.algebraMap_self, RingHom.id_apply]; decide⟩

/-- **Control**: the challenge coin slots `2, 3, 4` carry distinct coins (`8, 9, 10` mod 7). -/
theorem coin_slots_distinct :
    let χ : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.SVFrame.frameVCL (ZMod 7) :=
      fun i => (i.val : ZMod 7)
    chalKQ7T (3 : ZMod 7) χ 2 ≠ chalKQ7T (3 : ZMod 7) χ 3 ∧
      chalKQ7T (3 : ZMod 7) χ 3 ≠ chalKQ7T (3 : ZMod 7) χ 4 := by
  intro χ
  simp only [chalKQ7T, Nock.NockVMROM.Thm54.VclL.Compute.chalKQ7, χ]
  decide

end Nock.RedTeam.Batch1889

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.pullNext_honestQT_trace
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerEnv309_extNext_of_src
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerEnv309_baseNext_of_src
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerEnv309_walk_of_src
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerEnv309_walkNext_of_src
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerEnv309_chal_placement
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerEnv309_pub_placement
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.Vcomp_abc_irrel
#print axioms Nock.RedTeam.Batch1889.coin_slots_distinct
