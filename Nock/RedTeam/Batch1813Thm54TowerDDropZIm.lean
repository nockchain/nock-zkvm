/-
  Nock/RedTeam/Batch1813Thm54TowerDDropZIm.lean

  `dropZImMap` is the full map with the Im slot of compute challenge 1 (`z′`'s Im, slot 12, limbs
  `36..38`) removed.
-/
import Nock.RedTeam.Batch1812Thm54TowerDFullMap

set_option autoImplicit false

namespace Nock.RedTeam.Batch1813

open Nock Nock.Reified Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.RedTeam.Batch1810

/-- The full map with `z′`'s Im slot (challenge 1 ↦ limbs 36..38) dropped. -/
def dropZImMap : ImMap := { fullImMap with chal := fun i => if i = 1 then none else towerChal i }

theorem fullImMap_ext39 : fullImMap.ext 39 = some 337 := by decide
theorem fullImMap_chal1 : fullImMap.chal 1 = some 36 := by decide
theorem dropZImMap_ext39 : dropZImMap.ext 39 = some 337 := by decide
theorem dropZImMap_chal1 : dropZImMap.chal 1 = none := by decide

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The honest atom-test row: `b0 = 1`; role 39 Re (raw `130`) and Im (raw `337`) limbs `(1,0,0)`;
`z′` Re (challenge limbs `3..5`) and Im (`36..38`) limbs `(1,0,0)`. -/
def honestAtomF : Env F :=
  ⟨fun c => if c = 0 then 1 else if c = 130 then 1 else if c = 337 then 1 else 0, fun _ => 0,
    fun c => if c = 3 then 1 else if c = 36 then 1 else 0, fun _ => 0⟩

/-- **NC: dropping `z′`'s Im slot fires.**  Under the full map gate 27's Re and Im twins both vanish
at the honest atom row; under `dropZImMap` its Im twin is `b 0 ≠ 0`. -/
theorem drop_z_im_fires (b : Basis (Fin 3) F K) (δ : F) :
    (toQ F fullImMap (MemoryTable.pwScaleExp K) δ g27).1.eval (gatherEnv b honestAtomF)
        honestAtomF = 0 ∧
      (toQ F fullImMap (MemoryTable.pwScaleExp K) δ g27).2.eval (gatherEnv b honestAtomF)
        honestAtomF = 0 ∧
      (toQ F dropZImMap (MemoryTable.pwScaleExp K) δ g27).2.eval (gatherEnv b honestAtomF)
        honestAtomF = b 0 ∧ b 0 ≠ 0 := by
  refine ⟨?_, ?_, ?_, b.ne_zero 0⟩ <;>
    simp [g27, toQ, qadd, qmul, qsub, qlift, qvar, qconst, fullImMap_ext39, fullImMap_chal1,
      dropZImMap_ext39, dropZImMap_chal1, MixedExpr.eval, CoeffExpr.eval, gatherEnv,
      VclL.Compute.LogUp.limbVal, Fin.sum_univ_three, honestAtomF]

/-- The same, compiled: under the full map all six compiled coordinates of gate 27's twins vanish
(the `𝕂′` gate holds at the tower reading); under `dropZImMap` some compiled Im coordinate does not. -/
theorem drop_z_im_fires_compiled [FiniteDimensional F K] (b : Basis (Fin 3) F K) (δ : F)
    [Fact (¬ IsSquare (algebraMap F K δ))] :
    g27.eval (towerEnv δ fullImMap (gatherEnv b honestAtomF) honestAtomF) = 0 ∧
      ¬ (∀ k, (mixedCompile b col0Id
          (toQ F dropZImMap (MemoryTable.pwScaleExp K) δ g27).2 k).eval honestAtomF = 0) := by
  obtain ⟨h1, h2, h3, h0⟩ := drop_z_im_fires (F := F) b δ
  have h := isCoordEnv_gather b (honestAtomF (F := F))
  refine ⟨(toQ_isZero_iff δ fullImMap _ rfl _ _ g27).mp ⟨h1, h2⟩, ?_⟩
  rw [← mixedCompile_zero_iff b col0Id h, h3]
  exact h0

end Nock.RedTeam.Batch1813

#print axioms Nock.RedTeam.Batch1813.drop_z_im_fires
#print axioms Nock.RedTeam.Batch1813.drop_z_im_fires_compiled
