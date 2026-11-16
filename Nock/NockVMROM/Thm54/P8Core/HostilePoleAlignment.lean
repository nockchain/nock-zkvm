/-
  Nock/NockVMROM/Thm54/P8Core/HostilePoleAlignment.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.HostilePoleAlignment`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/HostilePoleAlignment.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.ExecOfTraces
import Nock.NockVMROM.Thm54.P8Core.MemoryInternalPole
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.HostilePoleAlignment

open Nock
open Nock.MemoryTable
open Nock.Walk
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Module
open scoped Polynomial
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

private theorem gather_chal_of_tuple
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (q : Fin 9) :
    (memorySourceEnvAt P c Qm i).chal q =
      memoryKOfTuple c q := by
  have hcol :
      (memorySourceTemplate P.optimized.basis).col0 3 = memoryCol0 :=
    memorySourceTemplate_col0 P.optimized.basis
  simp only [memorySourceEnvAt, hcol, gatherEnv, memoryCol0, memoryBaseEnvAt,
    envOfTrace]
  simp_rw [memoryChalValOfTuple_slot P.optimized.basis c q]
  change reconstruct P.optimized.basis (coord P.optimized.basis (memoryKOfTuple c q)) =
    memoryKOfTuple c q
  exact reconstruct_coord P.optimized.basis (memoryKOfTuple c q)

/-- Family-chip `𝕂` env chal `0` is the NPR seed (`memoryKOfTuple` index 0). -/
theorem memorySourceEnvAt_chal0
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (memorySourceEnvAt P c Qm i).chal 0 = nprSeed c.1 := by
  rw [gather_chal_of_tuple P c Qm i ⟨0, by decide⟩]
  rfl

/-- Family-chip `𝕂` env chal `6` is `interPole`. -/
theorem memorySourceEnvAt_chal6
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (memorySourceEnvAt P c Qm i).chal 6 = c.2.2.2.interPole := by
  rw [gather_chal_of_tuple P c Qm i ⟨6, by decide⟩]
  rfl

/-- Family-chip `𝕂` env chal `4` is IO `γ`. -/
theorem memorySourceEnvAt_chal4
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (memorySourceEnvAt P c Qm i).chal 4 = c.2.1.1 := by
  rw [gather_chal_of_tuple P c Qm i ⟨4, by decide⟩]
  rfl

/-- Family-chip `𝕂` env chal `8` is the sampled accounting `λ` (`memoryKOfTuple` index 8).
    This is `c.lambda`, not the `Pub.lambda` default `1`. -/
theorem memorySourceEnvAt_chal8
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (memorySourceEnvAt P c Qm i).chal 8 = c.2.2.2.lambda := by
  rw [gather_chal_of_tuple P c Qm i ⟨8, by decide⟩]
  rfl

end

end Nock.NockVMROM.Thm54.HostilePoleAlignment
