import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowFacts
import Nock.NockVMROM.Thm54.VclL.Compute.WalkSatQ7

/-!
# Route (d), GATHER lane : the abstract coordinate gather

.

`CoordGather F K` abstracts what the VCL decoders read of a physical row: the `Env309 F K` decode
and the `𝕂`-valued challenge / public slot readers (`slotK` at the 3-limb instance).  Instances:
`CoordGather.ofBasis b` (reproduces `gather309 b` / `slotK b` by `rfl`) and `towerGather δ b`
(`towerEnv309 δ towerM (gatherEnv b e) e`, Re at the role limbs, Im at the appended columns).
`ChipDataG` is `ChipData` with the basis replaced by a gather; `ChipData.toG` is the 3-limb bridge.
The generic decoder data (`alphaG`,..., `RowFactsG`) are `rfl`-equal to the existing ones at
`ofBasis`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.ComputeTable Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps Nock.NockVMROM.Thm54.ComputePaperPacking

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section Inst
variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable [FiniteDimensional F K] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The tower instance at `Kfp := Quad δ`. -/
def towerGather (b : Basis (Fin 3) F K) : CoordGather F (Quad (algebraMap F K δ)) where
  env309 e := towerEnv309 δ towerM (gatherEnv b e) e
  chalSlot v q := Quad.mk _ (LogUp.limbVal b v (3 * q))
    (if h : q < 12 then imVal (LogUp.limbVal b v) (towerM.chal ⟨q, h⟩) else 0)
  pubSlot v q := Quad.mk _ (LogUp.limbVal b v (3 * q))
    (if h : q < 3 then imVal (LogUp.limbVal b v) (towerM.extPub ⟨q, h⟩) else 0)
  chal_eq e i := by simp [towerEnv309, towerEnv, gatherEnv, i.isLt]
  pub_eq e i := by simp [towerEnv309, towerEnv, gatherEnv, i.isLt]
  base_eq _ _ := rfl
  baseNext_eq _ _ := rfl
  expCol_eq _ := rfl
  scalarPublic_eq _ _ := rfl
  shift e e' h := by
    have hl : LogUp.limbVal b e'.trace = LogUp.limbVal b e.traceNext := by
      funext c; simp [LogUp.limbVal, h]
    refine ⟨?_, ?_⟩ <;> funext j <;>
      simp [towerEnv309, towerEnv, gatherEnv, hl, imVal]

theorem towerGather_env309 (b : Basis (Fin 3) F K) (e : Env F) :
    (towerGather δ b).env309 e = towerEnv309 δ towerM (gatherEnv b e) e := rfl

end Inst

/-! ## The generic Q7 row-facts obligations -/

section Dec
variable {F K : Type} [Field F] [Field K] [Algebra F K] {h : ℕ}
variable (D : ChipDataG F K h) (chalV pubVal : ℕ → F)

/-- **The generic Q7 row-facts obligations**: `RowFactsQ7.obl` at the gather. -/
def RowObl {w : ℕ} (Q : Fin w → F[X]) : Prop :=
  ∀ i : Fin D.N, VclSourceObligationsQ7 D.N (D.G.env309 (pullEnv (envOfTrace Q D.orbit.ω (D.nodes i) chalV pubVal)))
    (pullEnv (envOfTrace Q D.orbit.ω (D.nodes i) chalV pubVal))

end Dec

/-! ## The tower instance of the decoder obligations -/

section TowerInst
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`RowObl` at the tower gather** from acceptance at the tower chip: the Q7 row obligations
at `Kfp := Quad δ`, at every row (`computeChipVCLQ7T_obl`). -/
theorem towerRowObl {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit) P)
    (claim : P8PublicClaim) (pub : ℕ → F) :
    RowObl (⟨n, hn, nodes, towerGather δ b, orbit, claim, pub, chalV⟩ :
        ChipDataG F (Quad (algebraMap F K δ)) h) chalV pubVal P := fun i =>
  computeChipVCLQ7T_obl δ hn nodes b chalV pubVal orbit P hsat (nodes i)
    (by simp [rowNodeSet])

end TowerInst

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
