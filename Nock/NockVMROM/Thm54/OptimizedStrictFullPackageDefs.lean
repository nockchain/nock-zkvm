import Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH
import Nock.NockVMROM.Thm54.VclL.Compute.TowerPackageW

/-!
`OptimizedFullStrictNockVMROMPackage` is the compiler's honest datum at the VS handle compute chip with the handle-lookup coins in
`𝕂′` (`frameVSQ`, seventeen coins): the tower parameter `δ` (`𝕂′ = Quad δ`), the cell-table and walk-table
heights `hT`, `hP` (the compute height is the structure parameter `hOrb`), the honest walk-root count `kr`,
the honest memory datum `honest : HonestVCLW` over the handle demand `demandH2` (its verifier datum
`honest.V` over `shapeVW`, the field facts `hF`/`hq`, `hrows`, `hrank`, `h62`, `hkp`), the run's generator
tree `t`, its claim message `x`, and the run facts tying them (`hgen`, `hd`, `hm`, `hN`).

The chips the statement names (through `CF` / `MF`) are `compCoreVSQH` (`computeChipVCLHQ`, width 85) and
`memCoreVSQH` (`cellChipHQ` 238, `walkChipHQ` 166): the VSQ cores of `FrameVSQ` with `Honest :=` the VSQ honest
datum.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage

open Nock Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH

attribute [local instance] ringCharFactW algZModW

noncomputable section

@[reducible] def decQ40 {F K : Type} [Field F] [Field K] [Algebra F K] (δ : F) : DecidableEq (Quad (algebraMap F K δ)) :=
  Classical.decEq _

attribute [local instance] decQ40

structure OptimizedFullStrictNockVMROMPackage
    (F K : Type) [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    [FiniteDimensional F K]
    (hOrb : ℕ) where
  /-- The tower parameter: fingerprints and the handle coins live in `𝕂′ = Quad (algebraMap F K δ)`. -/
  δ : F
  /-- `δ` is not a square in `K` (so `Quad` is a field). -/
  [δ_nonsquare : Fact (¬ IsSquare (algebraMap F K δ))]
  /-- The cell-table height. -/
  hT : ℕ
  /-- The walk-table height. -/
  hP : ℕ
  /-- The honest walk root count (`kroots` of the walk twin). -/
  kr : ℕ
  /-- The honest memory datum over the handle demand (verifier datum, demand, field and size facts). -/
  honest : HonestVCLW (K := K) δ hT hP hOrb kr
  /-- The run's generator tree (over `𝕂′`). -/
  t : NTree (GenComputeRow (Quad (algebraMap F K δ)))
  /-- The honest claim message (serial and rank limbs of each claim cell). -/
  x : ClaimMsgVS
  /-- The run's fuel. -/
  fuel : ℕ
  /-- The tree is the generator's run on the claim. -/
  hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel honest.V.claim.subject honest.V.claim.formula =
    .ok (t, honest.V.claim.result)
  /-- The demand is the handle demand of the run's rows. -/
  hd : honest.d = demandH2 (bfsRows (airReorder t))
  /-- The claim message is the honest one at that demand. -/
  hm : HonestClaimMsgFull honest.d.cells honest.V.claim x
  /-- The compute row count is the run's. -/
  hN : honest.V.N = (bfsForest [airReorder t]).length

attribute [instance] OptimizedFullStrictNockVMROMPackage.δ_nonsquare

namespace OptimizedFullStrictNockVMROMPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The fingerprint field `𝕂′ = Quad δ`. -/
abbrev FP := Quad (algebraMap F K P.δ)

/-- The memory shape: the `𝕂′` cell twin (238) and walk twin (166) at their heights. -/
abbrev shape : MemShape := shapeVSQ P.hT P.hP

/-- The compute core: `computeChipVCLHQ` (width 85), summands `sumCVSQ`, the honest datum. -/
abbrev CF := compCoreVSQH (K := K) P.δ P.hT P.hP P.kr hOrb

/-- The memory core: `cellChipHQ` / `walkChipHQ`, summands `sumMVSQ`, the honest datum. -/
abbrev MF := memCoreVSQH (K := K) P.δ P.hT P.hP P.kr hOrb

/-- The joint summands (zero seed, census, validity IO, the two `𝕂′` handle IO summands). -/
abbrev joint := jointVSQ (F := F) (K := K) P.δ P.hT P.hP hOrb

/-- The compiler-built verifier datum. -/
abbrev verifier : VerifierData F K hOrb (shapeVSQ P.hT P.hP) := vsqOf P.honest.V

/-- The honest datum of the cores. -/
abbrev hdat : HonestVSQD (K := K) P.δ P.hT P.hP hOrb P.kr := ⟨P.honest, P.t, P.x⟩

end OptimizedFullStrictNockVMROMPackage

end

end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

