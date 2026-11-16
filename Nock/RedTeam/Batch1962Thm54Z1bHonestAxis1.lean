/-
  Nock/RedTeam/Batch1962Thm54Z1bHonestAxis1.lean

  **The honest side of axis 1 — `z1 := [axis = 1]`, `hax1` REMOVED.**

  * `vclFill` takes the axis as a NATURAL (`ax : ℕ`; column `221` is its cast) and fills `z1 = [ax = 1]`
    (`vclFill_z1`).  `honestAx = 0` off `s0` / `s9`, so this is `[state ∈ {s0, s9} ∧ ax = 1]`.  The test is on the
    natural, not on its field image: at `ax = p + 1` the field image is `1` but the read is a real path read.
  * honest slot gates `slot1Q_honest` / `slot2Q_honest` / `lookupGatesT_honest` for ANY boolean `z1`: at a
    `z1 = 1` row (`s0`, resp. `s9`) the path activity is `0` and the export selectors are off, so the gate is
    `0 = 0` whatever the inverse; the pole hypotheses `hp` / `h9` are only used at `z1 = 0`.
  * honest accumulators use the tower-local `accSlotsPT` / `accSlotsPImT` (`accPT`, `accGatesT_honest`,
    `termQ_acc_eq`, `hrowP_T`); `termQ_PT_of_z1` (term `0` at `z1 = 1`), `termQ_PT_of_z0` (= the shared term).
  * `hrowP_row` has no `hax1`: at `honestAx = 1` the row has `z1 = 1`, its path term is `0`, and its only path key
    `(·, 1)` is dropped by `isPathAx` (`isPathAx 1 = false`) — both sides are `0`; at `honestAx ≠ 1` (`z1 = 0`)
    the old proof applies (`isPathAx_of_ne`).
  * `z1Gates_row`: the 38 `z1` gates hold at every honest row (any accumulator filling).  `bool z1` and
    `z1·(ax − 1)` by cases; `z1·s0·(e − s)` / `z1·s9·(sf2_f − sf1_e)` because `Noun.slot 1 n = some n`
    (`RowShape`: `slot honestAx subject = some evaluation`, `slot honestAx core = some arm`): the child
    fingerprint is the root's.  No new bad event (equal nouns have equal fingerprints).
  * `HonestVCLT.hax1`, and the `hax1` premise of `honestVCLJ_of_run`, `vcl_completeness_of_run`,
    `vcl_completeness_figure_of_run` are DELETED.
-/
import Nock.RedTeam.Batch1961Thm54Z1aChip
import Nock.RedTeam.Batch1955Thm54VclCompletenessOfRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1962

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.Reified Module Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

section NC
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The honest fill discriminates**: `z1 = 1` at axis `1`, `z1 = 0` at any other axis (in particular at `p + 1`,
whose field image is `1`).  (`1 ≠ 0`.) -/
theorem z1_fill_axis1 (b : Basis (Fin 3) F K) ser fIdx vI0 vI1 inv0 inv1 inv2 accX accP :
    vclFill (δ := δ) b ser 1 fIdx vI0 vI1 inv0 inv1 inv2 accX accP z1Col = 1 := by
  rw [vclFill_z1]; simp

theorem nc_z1_fill_other_axis (b : Basis (Fin 3) F K) ser (a : ℕ) (ha : a ≠ 1) fIdx vI0 vI1 inv0 inv1 inv2 accX accP :
    vclFill (δ := δ) b ser a fIdx vI0 vI1 inv0 inv1 inv2 accX accP z1Col = 0 := by
  rw [vclFill_z1]; simp [ha]

/-- **NC (discriminating): the OLD honest fill `z1 := 0` is wrong at an axis-1 row.**  At an `s0` row (one-hot)
with `z1 = 0` the tower-local path term is the ACTIVE slot inverse, a request the memory side never serves
(`isPathAx 1 = false`); with `z1 = 1` the term is `0` (`termQ_PT_of_z1`). -/
theorem nc_path_term_fires_at_z1_zero (b : Basis (Fin 3) F K) (E : Env F) (hz : E.trace z1Col = 0)
    (hsel : ∀ j, j < 11 → E.trace j = if j = 0 then 1 else 0)
    (hinv : Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) (gatherEnv b E) E ≠ 0) :
    termQ δ b accSlotsPT accSlotsPImT E ≠ 0 := by
  rw [termQ_PT_of_z0 δ b E hz, termQ_P_val δ b E 0 hsel]
  simpa using hinv

theorem path_term_zero_at_z1_one (b : Basis (Fin 3) F K) (E : Env F) (hz : E.trace z1Col = 1) :
    termQ δ b accSlotsPT accSlotsPImT E = 0 :=
  termQ_PT_of_z1 δ b E hz

end NC

end

end Nock.RedTeam.Batch1962

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.vclFill_z1
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.slot1Q_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.slot2Q_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.lookupGatesT_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.accGatesT_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.col_z1
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.termQ_PT_of_z0
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.termQ_PT_of_z1
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.z1Gates_row
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowP_row
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowP_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.hrowX_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestVCLT.hacc
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_staged_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_accepted_T
#print axioms Nock.RedTeam.Batch1938.vcl_completeness'
#print axioms Nock.RedTeam.Batch1938.vcl_completeness_goldilocks
#print axioms Nock.RedTeam.Batch1955.vcl_completeness_of_run
#print axioms Nock.RedTeam.Batch1955.vcl_completeness_figure_of_run
#print axioms Nock.RedTeam.Batch1962.z1_fill_axis1
#print axioms Nock.RedTeam.Batch1962.nc_z1_fill_other_axis
#print axioms Nock.RedTeam.Batch1962.nc_path_term_fires_at_z1_zero
#print axioms Nock.RedTeam.Batch1962.path_term_zero_at_z1_one
