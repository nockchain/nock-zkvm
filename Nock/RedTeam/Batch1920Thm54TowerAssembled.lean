/-
  Nock/RedTeam/Batch1920Thm54TowerAssembled.lean

  **ONE assembled honest row of the VCL compute family at the tower chip.**

  * `rowGen` / `residAt` / `rowFinal`: the final honest rows (C1c's `genRowVals` with tags `childStateTagCol W (j+1)`,
    the walk values of an `HonestWalk`, and the residual roles `58/59` chosen as `residualVal` of the row pair
    with `58/59` zeroed; `residAt_eq` shows this is the row-pair `residualVal` of the FINAL rows, so non-circular).
  * `vclFinal` / `rowsFinal`: the VCL-only columns with the slot inverses `inv_k := den_k'^-1` evaluated at an
    auxiliary env with zero inverses; `inv_final_eq` (via `den_noncircular`) shows they are `den_k'^-1` at the final env.
  * `walkRowEnv_final`: C2b's `WalkRowEnv` at the final rows (cnt/acc/ln/inv, r58/r59, masks, pub0/pub1,
    NextReads and FirstReads including the tags).
  * `assembled_row`: at row `i` of `rowsFinal` the walk gates, the row-local kept core gates, the three slot lookup
    gates, the serial gates and the axis gates all hold.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerAssembled
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

set_option autoImplicit false

namespace Nock.RedTeam.Batch1920

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute Module Nock.NockVMROM.Thm54.T0Tower

/-- NC (the inverse fill discriminates): a nonzero Re limb of the slot-0 inverse changes the VCL column
`inv0Base + k`. -/
theorem nc_vclFill_inv_distinguishes {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
    {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) (ser : F) (ax : ℕ) (fIdx vI0 vI1 : F)
    (inv0 inv1 inv2 accX accP : Quad (algebraMap F K δ)) (k : Fin 3)
    (hk : CoordinateBasis.coord b (Quad.re _ inv0) k ≠ 0) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (inv0Base + k) ≠
      vclFill (δ := δ) b ser ax fIdx vI0 vI1 0 inv1 inv2 accX accP (inv0Base + k) := by
  rw [vclFill_inv0, vclFill_inv0]
  intro h
  apply hk
  have h0 : Quad.re (algebraMap F K δ) (0 : Quad (algebraMap F K δ)) = 0 := by
    have := Quad.re_mk (algebraMap F K δ) (0 : K) 0
    rwa [show Quad.mk (algebraMap F K δ) (0 : K) 0 = 0 by simp [Quad.mk]] at this
  rw [h, h0]
  simp [CoordinateBasis.coord]

end Nock.RedTeam.Batch1920

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms residAt_eq
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms srcChal_eq
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms inv_final_eq
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms walkRowEnv_final
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms assembled_row
#print axioms Nock.RedTeam.Batch1920.nc_vclFill_inv_distinguishes
