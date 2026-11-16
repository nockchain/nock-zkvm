/-
  Nock/RedTeam/Batch1893Thm54TowerRowLocal.lean

  **The row-local kept gates of the tower compute chip.**

  * `RowMatch` restates hypotheses (1)-(3) of DESIGN §(a) on an arbitrary source env `E`: (1) `E` read
    through `computeSubst` is `computeEnvFull inp (opSel st) pub dec ex` on trace `j < 94`, challenges
    `j < 5` (and the public clause `pub = computeEnvFull.pub`, a zero fill), (2) the `computeAIR` constraints
    hold at `computeEnvFull`, (3) the selector columns are one-hot at `st`.
  * `rowLocal_of_rowMatch`: the 72 row-local packed gates (`paperPackingRowLocal`) vanish at such an env
    (A-free copy of the row-local half of `exact_finalNonIOSourceFamilies17`, via `paperPacking_iff_atomic`;
    `RowMatch.refolded` is the A-free `exact_refoldedPerStateGates`).
  * `eval_congr_reads_typed`: read-set congruence over `LnRead.roles/chals` (justified by `kept_no_ln`).
  * `towerHolds_rowLocal`: for each kept core id `i < 72` (69 ids: `0..71` minus `{50, 58, 65}`,
    `rowLocal_kept_count`), `towerHolds δ eK eF (coreTarget i)`, for ANY `E : CorrectedFinalTypedEnv F (Quad δ)`
    with `RowMatch E.toSourceEnv..` that agrees with the tower base env off roles `54`/`55` and challenges
    `0`/`9` (the free generator `α*` fills those).  Generic: C1b supplies the honest `E`.
  * Negative control (`nc_selector_moved`, over a `ℚ` source env): zero data with the selector one-hot at `s0`
    satisfies all 72 row-local gates; moving the one-hot to `s3` breaks gate `42`, to `s1` breaks gate `68` (both
    KEPT ids), so the one-hot hypothesis (3) is load-bearing.  Labelled: the NC is over `ℚ` at the source layout,
    not at `𝕂′`.
  UNCONFIRMED (not compiled here): the honest instance (C1b), the other kept families (C2b/C2c), assembly (C2d).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowLocal
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false
set_option maxRecDepth 300000

namespace Nock.RedTeam.Batch1893

open Nock Nock.Reified Nock.Framework Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD Nock.NockVMROM.Thm54.VclL.Compute.LnRead

/-- Zero data, the listed selector columns `1`. -/
def selEnv (sel : List ℕ) : Env ℚ := ⟨fun i => if i ∈ sel then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem nc_selector_moved :
    (∀ g ∈ paperPackingRowLocal, g.eval (selEnv [0]) = 0) ∧
    (∃ h : 42 < paperPackingRowLocal.length, paperPackingRowLocal[42].eval (selEnv [3]) ≠ 0) ∧
    (∃ h : 68 < paperPackingRowLocal.length, paperPackingRowLocal[68].eval (selEnv [1]) ≠ 0) ∧
    (∀ i ∈ [42, 68], ∀ h : i < 82, (⟨i, h⟩ : CorrectedCoreExtGateId) ∈ Nock.NockVMROM.Thm54.VclL.Compute.LnRead.keptCoreIdsQ7) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · exact ⟨by decide, by decide +kernel⟩
  · exact ⟨by decide, by decide +kernel⟩
  · decide +kernel

end Nock.RedTeam.Batch1893

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rowLocal_of_rowMatch
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.eval_congr_reads_typed
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerHolds_rowLocal
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rowLocal_kept_count
#print axioms Nock.RedTeam.Batch1893.nc_selector_moved
