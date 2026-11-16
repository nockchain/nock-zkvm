/-
  Nock/RedTeam/Batch1913Thm54TowerWalkHonest.lean

  **The Im-column fill fix and the walk side of the honest
  tower compute env.**

  * Residual roles 58/59: `residual_reads_class` (the sources read no column of roles 58/59),
    `rowSrcEnv` / `residualVal` (non-circular definition), `rowSrcEnv_ext5859_irrel`,
    `residual_eq_of_fill`, `r5859_of_fill`, `residualVal_zero_isK`.
  * 𝕂-valuedness: `HonestWalk.cnt_isK`, `ln_isK`, `inv_isK`.
  * Per-row placement: `honestQT_hF`, `honestQT_hFn`.
  * NCs (discriminating): `nc_im_column_readable` (a row whose VCL column 394 is `1` is read as `1`,
    where the pre-fix `vclColT` read `0` for every row); `nc_residual_reads_role61` (the acc residual
    DOES read the next row's role 61, so the read-class check is not vacuous).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerWalkHonest
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign

set_option autoImplicit false

namespace Nock.RedTeam.Batch1913

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD Nock.Reified Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.T0Tower

/-- **NC (fill fix)**: the appended Im column `394` now carries the row's VCL value (`1 ≠ 0`); before the
fix it read `srcColT 489 = 0` at every row (C3's `vclColT_im_inverse_zero`). -/
theorem nc_im_column_readable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δ : F}
    [Fact (¬ IsSquare (algebraMap F K δ))] (b : Module.Basis (Fin 3) F K)
    (v : TowerRowVals (K := K) δ) (hv : v.vcl 394 = 1) :
    vclColT b (fun _ : Fin 1 => v) 394 0 ≠ 0 := by
  rw [vclColT_imVcl b _ 0 394 (le_refl _), hv]
  exact one_ne_zero

/-- **NC (read class)**: the acc residual reads the next row's role `61` (column `74`). -/
theorem nc_residual_reads_role61 : (VarKind.traceNext, 74) ∈ readsE walkAccStep309 := by decide +kernel

end Nock.RedTeam.Batch1913

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms vclColT_imVcl
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms invQ_val_honestQT
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms vclFill_invQ
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms pull_honestQT_trace
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms residual_reads_class
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms rowSrcEnv_ext5859_irrel
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms residual_eq_of_fill
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms r5859_of_fill
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms residualVal_zero_isK
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms HonestWalk.cnt_isK
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms HonestWalk.ln_isK
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms HonestWalk.inv_isK
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honestQT_hF
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honestQT_hFn
#print axioms Nock.RedTeam.Batch1913.nc_im_column_readable
#print axioms Nock.RedTeam.Batch1913.nc_residual_reads_role61
