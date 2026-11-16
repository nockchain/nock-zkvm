import Nock.NockVMROM.Thm54.VclL.Compute.TowerSat
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

/-!
# Route (d), TWD-4 item (e) : negative controls

* `nc_qmul_im_sign`: `qmul` with the Im sign flipped is a different `𝕂′` product (a gate built on it
  fires on honest values): at `a = 1 + √δ`, `a·a` has Im `2` and the flipped body has Im `0`.
* `nc_twin75_fires`: the Im twin of core gate `75` (the walk-accumulator residual) is nonzero on a
  hostile Im limb at an unmasked row, so dropping it from `towerCoreIm` admits that limb.
  Label: the Re gate lists' independence of the Im limb is a column-support fact NOT proved here.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section NC1
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `qmul` with the Im sign of the cross term flipped. -/
def qmulBad (δ : F) (a b : Q F) : Q F :=
  (.Add (.Mul a.1 b.1) (.Scale (.const δ) (.Mul a.2 b.2)), .Sub (.Mul a.1 b.2) (.Mul a.2 b.1))

/-- **NC (qmul Im sign).**  At `a = 1 + √δ` (constants) the honest square has Im `2 ≠ 0` and the
flipped body has Im `0`: the flipped body is not the `𝕂′` product, so the pair gate built from it
fires on the honest value. -/
theorem nc_qmul_im_sign (δ : F) (eK : Env K) (eF : Env F) (h2 : (2 : K) ≠ 0) :
    let a : Q F := (.Const 1, .Const 1)
    (qmulBad δ a a).2.eval eK eF = 0 ∧ (qmul F δ a a).2.eval eK eF ≠ 0 := by
  intro a
  simp only [qmulBad, qmul, a, MixedExpr.eval]
  refine ⟨by simp, ?_⟩
  simpa [one_add_one_eq_two] using h2

/-- **NC (dropped Im twin, core gate 75).**  On an unmasked row (`isLast = 0`, trace column `12`) with
a hostile nonzero Im limb of the walk-accumulator residual, the Im twin evaluates to that limb. -/
theorem nc_twin75_fires (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) (e : Env F) (k : Fin 3)
    (h12 : e.trace 12 = 0) :
    (coreIm b δ n towerM packedWalkAccId k).eval e = e.trace (walkAccImCol + (k : ℕ)) := by
  simp [coreIm, OptimizedComputeFinal.notLastCoeff, OptimizedComputeBaseGates.isLastVar,
    OptimizedComputeBaseGates.bv, CoeffExpr.eval, h12]

end NC1

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
