import Nock.NockVMROM.Thm54.VclL.Compute.TowerRecs
import Nock.NockVMROM.Thm54.VclL.Compute.PatchQ7

/-!
# The Q7 source obligations at `𝕂′` from tower acceptance

.

`VclSourceObligationsQ7 n (towerEnv309 …) eF` -- the Q7 obligations with the typed environment at
`Kfp := Quad δ` -- from `TowerKeptHolds` (`towerObl_of_kept`), hence from a satisfied tower chip at
every row (`towerObl_of_rowHolds`, `computeChipVCLQ7T_obl`).  This is the tower twin of
`VclSourceObligationsQ7.of_vclGatesQ7S`; the semantic layer's `Env309 F K` is instantiated at
`K := Quad δ`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section Obl
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The semantic value of a kept core position is its tower target's value. -/
theorem coreSem_eq_target (env : Env309 F (Quad (algebraMap F K δ))) (i : CorrectedCoreExtGateId) :
    coreSemValue309 env i = (coreTarget i).eval env := by
  by_cases hs : specialCore i = true
  · rcases i with ⟨v, hv⟩
    have hv' : v = 72 ∨ v = 73 ∨ v = 74 ∨ v = 75 ∨ v = 76 ∨ v = 77 ∨ v = 81 := by
      simp [specialCore] at hs; omega
    rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp [coreSemValue309, correctedCoreSemanticValue, coreTarget, specialTarget, WTyped.eval,
        packedLnChainId, packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId,
        packedQueueTilingId, packedChainId, packedWalkLnId, maskT, notLastScalar, specialCore,
        CorrectedFinalTypedExpr.eval]
      try (left; rfl)
  · have h72 : i.val ≠ 72 ∧ i.val ≠ 73 ∧ i.val ≠ 74 ∧ i.val ≠ 75 ∧ i.val ≠ 76 ∧ i.val ≠ 77 ∧ i.val ≠ 81 := by
      simp [specialCore] at hs; omega
    have hne : ∀ j : CorrectedCoreExtGateId, j.val ∈ [72, 73, 74, 75, 76, 77, 81] → i ≠ j := by
      intro j hj he; subst he; simp at hj; omega
    simp only [coreSemValue309, correctedCoreSemanticValue, coreTarget, hs]
    rw [if_neg (hne _ (by decide)), if_neg (hne _ (by decide)), if_neg (hne _ (by decide)),
      if_neg (hne _ (by decide)), if_neg (hne _ (by decide)), if_neg (by
        rintro (h | h) <;> exact hne _ (by decide) h)]
    simp [WTyped.eval]


theorem auxSem_eq_target (env : Env309 F (Quad (algebraMap F K δ))) (j : CorrectedResidualWitnessId) :
    auxSemValue309 env j = (auxTarget j).eval env := by
  by_cases h : j = 2
  · simp [auxSemValue309, auxTarget, correctedAuxSemanticValue, h, WTyped.eval]
  · simp [auxSemValue309, auxTarget, h, WTyped.eval, CorrectedFinalTypedExpr.eval]

/-- **The Q7 obligations at `𝕂′`** from the kept typed gates at the tower environment. -/
theorem towerObl_of_kept (n : ℕ) (eK : Env K) (eF : Env F) (H : TowerKeptHolds n δ eK eF) :
    VclSourceObligationsQ7 n (towerEnv309 δ towerM eK eF) eF :=
  ⟨H.base, fun i hi => (coreSem_eq_target δ _ i).trans (H.core i hi),
    fun j => (auxSem_eq_target δ _ j).trans (H.aux j), H.ep2, H.ep4, H.eq⟩

theorem towerObl_of_rowHolds (b : Basis (Fin 3) F K) (n : ℕ) (envV : Env F)
    (H : TowerRowHolds δ b n envV) :
    VclSourceObligationsQ7 n (towerEnv309 δ towerM (gatherEnv b (pullEnv envV)) (pullEnv envV))
      (pullEnv envV) :=
  towerObl_of_kept δ n _ _ H.kept

/-- **Acceptance at the tower chip gives the Q7 obligations in `𝕂′` at every row.** -/
theorem computeChipVCLQ7T_obl
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit) P) :
    ∀ x ∈ rowNodeSet nodes,
      VclSourceObligationsQ7 n
        (towerEnv309 δ towerM (gatherEnv b (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))
          (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)) :=
  fun x hx => towerObl_of_rowHolds δ b n _
    (computeChipVCLQ7T_rowHolds hn nodes b δ chalV pubVal orbit P hsat x hx)

end Obl

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
