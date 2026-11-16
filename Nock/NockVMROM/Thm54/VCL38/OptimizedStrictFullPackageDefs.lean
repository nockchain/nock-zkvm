import Nock.RedTeam.Batch1938Thm54VclCompletenessJoint

/-!
The structure `OptimizedFullStrictNockVMROMPackage` and its derived abbreviations. The package is the compiler's honest datum at the VCL-L instance: the tower parameter `δ` (`𝕂′ = Quad δ`, `δ` a non-square of `F` in
`K`), the cell-table and path-chip heights `hT`, `hP` (the compute height is the structure
parameter `hOrb`), the honest run `honest : HonestVCLJ` (its verifier datum `honest.V`, its
generator tree `honest.t`, the size and field facts of the compute side, and the memory-shape
fields), the two field parameters (`F` is its own prime field; `2^63 < char F`) and the three
public size conditions of `vcl_completeness'` (`hleaf`, `hmemRows`, `haxis`).

The chips the statement names are those of the two VCL families at this datum:
`CF P = compSoundnessVCLT` (chip `computeChipVCLQ7T`, width 410) and `MF P = memSoundnessVCL`
(the cell table and the path chip), at the eleven-coin `frameVCL`.

The package has no walk coin (`memoryWalkAlpha`, `αW`, `lam`), no `kMem`, no `memoryChip`,
no `OptimizedStrictNockVMROMPackage` and no `PlusIOSegmentedFamily` as a field or reference.
-/
open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
namespace Nock.VCL38


namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage

open Nock Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD

noncomputable section

structure OptimizedFullStrictNockVMROMPackage
    (F K : Type) [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    [FiniteDimensional F K]
    (hOrb : ℕ) where
  /-- The tower parameter: fingerprints live in `𝕂′ = Quad (algebraMap F K δ)`. -/
  δ : F
  /-- `δ` is not a square in `K` (so `Quad` is a field). -/
  [δ_nonsquare : Fact (¬ IsSquare (algebraMap F K δ))]
  /-- The cell-table height. -/
  hT : ℕ
  /-- The path-chip height. -/
  hP : ℕ
  /-- The honest run of the compiler at this instance (verifier datum, generator tree, sizes). -/
  honest : HonestVCLJ (K := K) δ hT hP hOrb
  /-- `F` is its own prime field. -/
  primeField : GeneratedField.PrimeFieldElems F
  /-- `2^63 < char F`. -/
  char_gt : 2 ^ 63 < ringChar F
  /-- Public size condition: every noun of the run has at most `2^110` leaves. -/
  hleaf : programLeafBound (airReorder honest.t) ≤ 2 ^ 110
  /-- Public size condition: memory row counts below the characteristic. -/
  hmemRows : ∀ k, honest.V.memRows k + 1 < ringChar F
  /-- Public size condition: every read axis below `2^63`. -/
  haxis : programAxisBound (airReorder honest.t) < 2 ^ 63

attribute [instance] OptimizedFullStrictNockVMROMPackage.δ_nonsquare

namespace OptimizedFullStrictNockVMROMPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The fingerprint field `𝕂′ = Quad δ`. -/
abbrev FP := Quad (algebraMap F K P.δ)

/-- The memory shape: the cell table and the path chip at their heights. -/
abbrev shape : MemShape := shapeV P.hT P.hP

/-- The compute family: `compSoundnessVCLT`, chip `computeChipVCLQ7T` (width 410). -/
abbrev CF := Nock.RedTeam.Batch1880.CFv (K := K) P.δ P.hT P.hP hOrb

/-- The memory family: `memSoundnessVCL` (the cell table and the path chip). -/
abbrev MF := Nock.RedTeam.Batch1880.MFv (K := K) P.δ P.hT P.hP hOrb

/-- The compiler-built verifier datum. -/
abbrev verifier : VerifierData F K hOrb (shapeV P.hT P.hP) := P.honest.V

/-- The joint memory facts of the honest run (from the field parameters and the three public
size conditions). -/
abbrev memFacts := jointMemFacts_of P.honest P.primeField P.char_gt P.hleaf P.hmemRows P.haxis

/-- The honest memory datum of the joint run. -/
abbrev honestMem := jointMem P.δ P.honest.toHonestVCLT P.memFacts

end OptimizedFullStrictNockVMROMPackage

end

end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

end Nock.VCL38
