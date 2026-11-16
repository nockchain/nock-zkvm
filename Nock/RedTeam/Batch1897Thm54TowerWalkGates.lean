/-
  Nock/RedTeam/Batch1897Thm54TowerWalkGates.lean

  **The walk gates of the tower compute chip at the honest BFS
  walk.**

  * `WalkGatesT.lean`: `HonestWalk` (BFS rows + `RLC^γ` valuation + `WalkSat` columns, over a generic
    field), `honestWalk_exists` (the walk exists at every `(α, γ)`), the A-free copies of
    `exact_finalWalk_transition_sources` / `walk_steps_eq` / `endpoints_eq` (`walk_transition_sources`,
    `walk_{ln1,count1,accInit,out}_source`, `HonestWalk.acc_last`, `HonestWalk.cnt_last`), and the typed
    gates at `Env309`: core `73..77` (`gate73 … gate77`), aux `0`/`1`, ep2 `walkLn1`/`walkCount1`/`walkOut`,
    ep4 `walkAccInit` (`ep_*`), packaged as `walk_row_holds` from `WalkRowEnv`.
  * Seed: `seed_eq_seedVCLT` (below): `seedVCLT = RLC^{χ1}(root label)·χ0` once the root row carries the
    claim's label at `z′` (the root binding of `genBindsAt`).
  * CONDITIONAL: core `76` at nonterminal rows needs `count ≠ ln` (`HonestWalk.cnt_ne_ln`, `h ≤ orderOf α`),
    a bad-event on the walk coin `χ0` that `GoodCFT` and the DESIGN do not list.  `walk_row_holds` takes
    it as the hypothesis `hne`.
  * Negative controls (concrete, over `ℚ`): `gate76_nc` (`W0 = ln` ⇒ core 76 `= -1`), `ep_out_nc`
    (`acc ≠ 0` at the last row), and the generic `count_step_perturb`.
  UNCONFIRMED: the instances of `WalkRowEnv` / `NextReads` / `FirstReads` at `towerEnv309` of the honest fill
  (C1b/C2d), the root binding at `z′`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.WalkGatesT
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCoins
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1897

open Nock Nock.Reified Nock.ComputeTable Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

section Seed
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The walk seed is `seedVCLT`** once the root row carries the claim's label at `z′ = zQuad δ χ`. -/
theorem seed_eq_seedVCLT (claim : P8PublicClaim) (χ : Coins frameVCL K)
    (pub0 : Pub (Quad (algebraMap F K δ)))
    (hroot : labelVecOfPub pub0 = ComputeWalkSeed.claimLabelVec (zQuad δ χ) claim) :
    seedVCLT δ claim χ =
      Walk.rlc (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨1, by decide⟩)) (labelVecOfPub pub0) *
        algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩) := by
  rw [hroot]; rfl

end Seed

/-- A zero `ℚ` environment: all columns `0`. -/
def zeroEnv (b12 : ℚ) (w1 : ℚ) : Env309 ℚ ℚ where
  base :=
    { baseTrace := fun j => if j.val = 12 then b12 else 0
      baseTraceNext := fun _ => 0
      extTrace := fun _ => 0
      extTraceNext := fun _ => 0
      chal := fun _ => 0
      extensionPublic := fun _ => 0
      scalarPublic := fun _ => 0
      certBase := fun _ => 0
      certExt := fun _ => 0
      expCol := 0 }
  walk := fun j => if j = 1 then w1 else 0
  walkNext := fun _ => 0

/-- **Negative control (queue witness)**: a nonterminal row with `W0 = ln` violates core `76`. -/
theorem gate76_nc : (specialTarget ⟨76, by decide⟩).eval (zeroEnv 0 0) ≠ 0 := by
  rw [gate76_eq_neg_one (zeroEnv 0 0) (by simp [zeroEnv]) (by simp [zeroEnv])]
  norm_num

/-- **Negative control (`out_walk`)**: a nonzero accumulator at the last row violates the terminal endpoint. -/
theorem ep_out_nc : (lowerW finalMaskedWalkOut309).eval (zeroEnv 1 1) ≠ 0 := by
  rw [ep_out_eq (zeroEnv 1 1) (by simp [zeroEnv])]
  simp [zeroEnv]

end Nock.RedTeam.Batch1897

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honestWalk_exists
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.walk_transition_sources
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestWalk.acc_last
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestWalk.cnt_last
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestWalk.cnt_ne_ln
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.gate73
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.gate76
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.walk_row_holds
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.walk_row_holds_of_order
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.count_step_perturb
#print axioms Nock.RedTeam.Batch1897.seed_eq_seedVCLT
#print axioms Nock.RedTeam.Batch1897.gate76_nc
#print axioms Nock.RedTeam.Batch1897.ep_out_nc
