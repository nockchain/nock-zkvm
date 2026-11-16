import Nock.NockVMROM.Thm54.VclL.Compute.TowerPackageW

/-!
The package structure `OptimizedFullStrictNockVMROMPackage` at the walk instance.  The chips the
statement names are those of the two families at this datum: `CF P = compSoundnessVCLT` (chip
`computeChipVCLQ7T`, width 410) and `MF P = memSoundnessVCLW` at `kroots = krT δ honest.t` (the cell
table, width 225, and the walk chip `walkChip`, width 132, in place of the path chip), at the
eleven-coin `frameVCL`.  The two instance arguments of the walk family
(`Fact (ringChar F).Prime`, `Algebra (ZMod (ringChar F)) K`) are derived (`ringCharFactW`,
`algZModW`), not fields.
-/

open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
namespace Nock.Walk39

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage

open Nock Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD

attribute [local instance] ringCharFactW algZModW

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
  /-- The walk-table height. -/
  hP : ℕ
  /-- The honest run of the compiler at the walk instance (verifier datum, generator tree, sizes). -/
  honest : HonestVCLJW (K := K) δ hT hP hOrb
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
  /-- Public size condition (the walk bound): honest walk roots plus walk rows below the
  characteristic. -/
  hkp : krT δ honest.t + honest.V.memRows (tWW hT hP) < ringChar F

attribute [instance] OptimizedFullStrictNockVMROMPackage.δ_nonsquare

namespace OptimizedFullStrictNockVMROMPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The fingerprint field `𝕂′ = Quad δ`. -/
abbrev FP := Quad (algebraMap F K P.δ)

/-- The memory shape: the cell table and the walk table at their heights. -/
abbrev shape : MemShape := shapeVW P.hT P.hP

/-- The honest walk root count (`kroots` of the walk chip). -/
abbrev kr : ℕ := krT P.δ P.honest.t

/-- The compute family: `compSoundnessVCLT`, chip `computeChipVCLQ7T` (width 410). -/
abbrev CF := VclL.StandaloneW.CFvW (K := K) P.δ P.hT P.hP hOrb

/-- The memory family: `memSoundnessVCLW` (the cell table and the walk chip). -/
abbrev MF := VclL.StandaloneW.MFvW (K := K) P.δ P.hT P.hP hOrb P.kr

/-- The compiler-built verifier datum. -/
abbrev verifier : VerifierData F K hOrb (shapeVW P.hT P.hP) := P.honest.V

/-- The honest walk memory datum of the joint run (from the field parameters, the three public
size conditions and the walk bound). -/
abbrev honestMem :=
  jointMemW P.honest P.primeField P.char_gt P.hleaf P.hmemRows P.haxis P.hkp

end OptimizedFullStrictNockVMROMPackage

end

end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

end Nock.Walk39
