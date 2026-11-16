/-
  Nock/NockVMROM/Thm54/HostilePoleAlignment.lean

  Algebraic receipt:
  `RLC − (−ι) = ι + RLC`.
-/
import Nock.MemoryTable
import Nock.Walk
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.Framework.NockInstances
import Nock.NockVMROM.Thm54.P8Core.HostilePoleAlignment
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

/-- Algebraic identity of the paper/chip pole conventions: `RLC − (−ι) = ι + RLC`. -/
theorem pole_eq_poleSource_algebra {K : Type} [Field K] (ι rlc : K) :
    rlc - (-ι) = ι + rlc := by
  ring

/-- `MemoryTable.recRLC` at roles `19..26` equals `Walk.rlc` on `memRowRecord`. -/
theorem recRLC_eq_walk_memRowRecord
    {K : Type} [Field K] (γ : K) (envK : Env K) :
    recRLC γ
        ⟨⟨envK.trace 19, envK.trace 20, envK.trace 21⟩,
          ⟨envK.trace 22, envK.trace 23, envK.trace 24⟩,
          envK.trace 25, envK.trace 26⟩
        (envK.trace 57) =
      Walk.rlc γ (memRowRecord envK) := by
  simp only [recRLC, Walk.rlc, memRowRecord]
  repeat rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

/-- Table pole at `β := −ι` equals chip `poleSource` form `ι + RLC`. -/
theorem memoryTable_pole_eq_interPole_add_rlc
    {K : Type} [Field K] (ι γ : K) (envK : Env K) :
    pole ⟨(0 : K), -ι, γ⟩
        ⟨⟨envK.trace 19, envK.trace 20, envK.trace 21⟩,
          ⟨envK.trace 22, envK.trace 23, envK.trace 24⟩,
          envK.trace 25, envK.trace 26⟩
        (envK.trace 57) =
      ι + Walk.rlc γ (memRowRecord envK) := by
  rw [pole, recRLC_eq_walk_memRowRecord, pole_eq_poleSource_algebra]

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Hostile config β is the negation of the sampled internal pole. -/
theorem cfgOfTraces_beta
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces P Qc Qm c).challenges.β = -(c.2.2.2.interPole) :=
  rfl

/-- Label inputs carry the same β. -/
theorem lblMAt_beta
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (lblMAt P Qm c i).2.1.β = -(c.2.2.2.interPole) :=
  rfl

/-- Chip `poleSource` at the family row env equals `ι + RLC^γ(memRowRecord)`. -/
theorem poleSource_eval_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    poleSource.eval (memorySourceEnvAt P c Qm i) =
      c.2.2.2.interPole +
        Walk.rlc c.2.1.1 (memRowRecord (memorySourceEnvAt P c Qm i)) := by
  have h6 := memorySourceEnvAt_chal6 P c Qm i
  have h4 := memorySourceEnvAt_chal4 P c Qm i
  simp only [poleSource, recordRLCExpr, Expr.eval, h6, h4, memRowRecord, Walk.rlc]
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_eight]
  ring

/-- **Receipt.**  Decoded-row `MemoryTable.pole` at hostile `β := −interPole`
equals chip `poleSource`. -/
theorem pole_eq_poleSource
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    pole (lblMAt P Qm c i).2.1 (decodeMemPub P Qm c i).mem
        ((memorySourceEnvAt P c Qm i).trace 57) =
      poleSource.eval (memorySourceEnvAt P c Qm i) := by
  set envK := memorySourceEnvAt P c Qm i
  have hps := poleSource_eval_at P c Qm i
  simp only [lblMAt, decodeMemPub, memoryMemRoot, memoryMemChild, pole]
  change
      recRLC c.2.1.1
          ⟨⟨envK.trace 19, envK.trace 20, envK.trace 21⟩,
            ⟨envK.trace 22, envK.trace 23, envK.trace 24⟩,
            envK.trace 25, envK.trace 26⟩
          (envK.trace 57) -
        (-(c.2.2.2.interPole)) =
        poleSource.eval envK
  rw [recRLC_eq_walk_memRowRecord, pole_eq_poleSource_algebra, hps]

end

end Nock.NockVMROM.Thm54.HostilePoleAlignment

#print axioms Nock.NockVMROM.Thm54.HostilePoleAlignment.pole_eq_poleSource_algebra
#print axioms Nock.NockVMROM.Thm54.HostilePoleAlignment.pole_eq_poleSource
#print axioms Nock.NockVMROM.Thm54.HostilePoleAlignment.cfgOfTraces_beta
