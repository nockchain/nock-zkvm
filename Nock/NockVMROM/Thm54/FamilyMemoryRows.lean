/-
  Nock/NockVMROM/Thm54/FamilyMemoryRows.lean

  Family memory chip → `V_mem` (`eqBlk ∧ interV`)
  under hostile `β := −interPole` (`HostilePoleAlignment`).
-/
import Nock.MemoryTable
import Nock.AIR
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.HostilePoleAlignment
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.MemoryFactorizationScope
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.P8Core.FamilyMemoryRows
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.FamilyMemoryRows

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.HostilePoleAlignment
open Nock.NockVMROM.Thm54.MemoryFactorizationScope
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open ComputeTable
open Module

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem paperAggregator_mem_mixed (b : Basis (Fin 3) F K) :
    paperAggregator (F := F) ∈ mixedTransitionGates (F := F) (K := K) b := by
  change paperAggregator (F := F) ∈ paperKGates (K := K) (F := F) ++ [haltAtomMixed]
  simp [paperKGates, paperKGatesCore, rapMemGates, List.mem_append, List.mem_cons]

/-- The memory table inputs with the row's exponent carrier folded into the LogUp
offset: `β ↦ β − γ⁹ · reqIdx(i)`.  The committed `intermediate` pole is over the ten-slot record
(`poleSourceMixed = interPole + RLC^γ(record) + γ⁹·reqIdx`), so the decoded row's `interV` holds at
these per-row inputs; `eqBlk` reads only `z` and is unchanged (`eqBlk_expShift`). -/
def expShiftInputs (inp : MemoryTable.Inputs K) (x : K) : MemoryTable.Inputs K :=
  { inp with β := inp.β - x }

/-- The row's tenth record slot, scaled: `γ⁹ · algebraMap reqIdx(i)`. -/
def rowExpTerm
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : K :=
  algebraMap F K ((memoryBaseEnvAt P c Qm i).trace OptimizedMemoryGateBasis.reqIdxCol) *
    c.2.1.1 ^ 9

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
theorem eqBlk_expShift (inp : MemoryTable.Inputs K) (x : K) (p : MemoryTable.Pub K) :
    eqBlk (expShiftInputs inp x) p ↔ eqBlk inp p := by
  cases hst : p.st <;> simp [eqBlk, expShiftInputs, hst]

theorem poleSourceMixed_eval_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (MemoryPaperFactorization.poleSourceMixed (F := F)).eval (memorySourceEnvAt P c Qm i)
        (memoryBaseEnvAt P c Qm i) =
      MemoryPaperFactorization.poleSource.eval (memorySourceEnvAt P c Qm i) +
        rowExpTerm P c Qm i := by
  have h4 := memorySourceEnvAt_chal4 P c Qm i
  simp only [MemoryPaperFactorization.poleSourceMixed, MixedExpr.eval, MixedExpr.ofExpr_eval,
    reqIdxRLCTerm, bcur, CoeffExpr.eval, rowExpTerm, h4]

theorem interV_of_paperAggregator
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot (memoryBaseEnvAt P c Qm i) st)
    (hst : (decodeMemPub P Qm c i).st = st)
    (hpole : (poleSourceMixed (F := F)).eval (memorySourceEnvAt P c Qm i)
      (memoryBaseEnvAt P c Qm i) ≠ 0)
    (hagg : (paperAggregator (F := F)).eval
        (memorySourceEnvAt P c Qm i) (memoryBaseEnvAt P c Qm i) = 0) :
    interV (expShiftInputs (lblMAt P Qm c i).2.1 (rowExpTerm P c Qm i))
      (decodeMemPub P Qm c i) := by
  have hps := pole_eq_poleSource P c Qm i
  have hmix := poleSourceMixed_eval_at P c Qm i
  -- Use factorization eval (same gate body as committed `paperAggregator`).
  have heval := MemoryPaperFactorization.paperAggregator_eval
    (memorySourceEnvAt P c Qm i) (memoryBaseEnvAt P c Qm i) st hone
  set Pm := (MemoryPaperFactorization.poleSourceMixed (F := F)).eval
    (memorySourceEnvAt P c Qm i) (memoryBaseEnvAt P c Qm i) with hPm
  have hpole' : Pm ≠ 0 := by
    simpa [hPm, MemoryPaperFactorization.poleSourceMixed, poleSourceMixed,
      MemoryPaperFactorization.poleSource, poleSource] using hpole
  -- Align the two `paperAggregator` / `poleSource` names for `heval`.
  have hagg' : (MemoryPaperFactorization.paperAggregator (F := F)).eval
      (memorySourceEnvAt P c Qm i) (memoryBaseEnvAt P c Qm i) = 0 := by
    change (paperAggregator (F := F)).eval
      (memorySourceEnvAt P c Qm i) (memoryBaseEnvAt P c Qm i) = 0
    exact hagg
  rw [heval, sub_eq_zero] at hagg'
  have hΔ :
      (memorySourceEnvAt P c Qm i).trace 28 -
        (memorySourceEnvAt P c Qm i).trace 27 =
      MemoryPaperFactorization.aggregatorSign st * Pm⁻¹ := by
    calc
      _ = Pm⁻¹ * (Pm * ((memorySourceEnvAt P c Qm i).trace 28 -
                (memorySourceEnvAt P c Qm i).trace 27)) := by
        field_simp [hpole']
      _ = Pm⁻¹ * MemoryPaperFactorization.aggregatorSign st := by rw [hagg']
      _ = MemoryPaperFactorization.aggregatorSign st * Pm⁻¹ := by ring
  have hipre : (decodeMemPub P Qm c i).ipre = (memorySourceEnvAt P c Qm i).trace 27 := rfl
  have hicur : (decodeMemPub P Qm c i).icur = (memorySourceEnvAt P c Qm i).trace 28 := rfl
  have hps' : Pm =
        pole (expShiftInputs (lblMAt P Qm c i).2.1 (rowExpTerm P c Qm i))
          (decodeMemPub P Qm c i).mem ((memorySourceEnvAt P c Qm i).trace 57) := by
    have h0 : MemoryPaperFactorization.poleSource.eval (memorySourceEnvAt P c Qm i) =
        pole (lblMAt P Qm c i).2.1 (decodeMemPub P Qm c i).mem
          ((memorySourceEnvAt P c Qm i).trace 57) := by
      simpa [MemoryPaperFactorization.poleSource, poleSource] using hps.symm
    rw [hmix, h0]
    simp only [pole, expShiftInputs]
    ring
  have hps1 :
      pole (expShiftInputs (lblMAt P Qm c i).2.1 (rowExpTerm P c Qm i))
          (decodeMemPub P Qm c i).mem ((memorySourceEnvAt P c Qm i).trace 57) =
        pole (expShiftInputs (lblMAt P Qm c i).2.1 (rowExpTerm P c Qm i))
          (decodeMemPub P Qm c i).mem (decodeMemPub P Qm c i).cprime :=
    decodeMemPub_cprime P Qm c i ▸ rfl
  simp only [interV, hst, hipre, hicur]
  cases st with
  | decompose =>
    simp only [MemoryPaperFactorization.aggregatorSign, zero_mul] at hΔ
    exact eq_of_sub_eq_zero hΔ
  | halt =>
    simp only [MemoryPaperFactorization.aggregatorSign, zero_mul] at hΔ
    exact eq_of_sub_eq_zero hΔ
  | read_root =>
    simp only [MemoryPaperFactorization.aggregatorSign, one_mul] at hΔ
    rw [hΔ, hps', hps1]
  | verify_child =>
    simp only [MemoryPaperFactorization.aggregatorSign] at hΔ
    have : (memorySourceEnvAt P c Qm i).trace 27 -
        (memorySourceEnvAt P c Qm i).trace 28 = Pm⁻¹ := by
      linear_combination -hΔ
    rw [this, hps', hps1]

theorem deployed_row_interV_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hchar : MemStateTagChar F)
    (hpole : (poleSourceMixed (F := F)).eval (memorySourceEnvAt P c (honestQm P c Qm) i)
      (memoryBaseEnvAt P c (honestQm P c Qm) i) ≠ 0) :
    interV (expShiftInputs (lblMAt P (honestQm P c Qm) c i).2.1
        (rowExpTerm P c (honestQm P c Qm) i))
      (decodeMemPub P (honestQm P c Qm) c i) := by
  obtain ⟨st, hone⟩ := baseOneHot_at_family P c Qm hsat i hchar
  have hagg := mixed_at_family P c Qm hsat i _ (paperAggregator_mem_mixed P.optimized.basis)
  have hst : (decodeMemPub P (honestQm P c Qm) c i).st = st := by
    simp only [decodeMemPub]
    exact memoryStateOf_eq_of_baseOneHot _ _ hone
  exact interV_of_paperAggregator P c (honestQm P c Qm) i st hone hst hpole hagg

theorem deployed_row_vmem_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hchar : MemStateTagChar F)
    (hz : nprSeed c.1 ≠ 0)
    (hpole : (poleSourceMixed (F := F)).eval (memorySourceEnvAt P c (honestQm P c Qm) i)
      (memoryBaseEnvAt P c (honestQm P c Qm) i) ≠ 0) :
    Vmem (expShiftInputs (lblMAt P (honestQm P c Qm) c i).2.1
        (rowExpTerm P c (honestQm P c Qm) i))
      (decodeMemPub P (honestQm P c Qm) c i) := by
  obtain ⟨st, hone⟩ := baseOneHot_at_family P c Qm hsat i hchar
  have hst : (decodeMemPub P (honestQm P c Qm) c i).st = st := by
    simp only [decodeMemPub]
    exact memoryStateOf_eq_of_baseOneHot _ _ hone
  exact ⟨MemoryTable.verBool_holds _,
    (eqBlk_expShift _ _ _).2 (eqBlk_of_paper_classes P c Qm hsat i st hone hst hz),
    deployed_row_interV_at P c Qm hsat i hchar hpole⟩

/-- A6: decoded `C'` is 𝕂-role 57 / `recC'`. -/
theorem decode_cprime_eq_role57
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (decodeMemPub P Qm c i).cprime = (memorySourceEnvAt P c Qm i).trace 57 ∧
      (Expr.subst memorySubst recC').eval (memorySourceEnvAt P c Qm i) =
        (decodeMemPub P Qm c i).cprime := by
  refine ⟨decodeMemPub_cprime P Qm c i, ?_⟩
  rw [recC'_eval_memorySubst, decodeMemPub_cprime]

end

end Nock.NockVMROM.Thm54.FamilyMemoryRows

#print axioms Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_interV_at
#print axioms Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at
#print axioms Nock.NockVMROM.Thm54.FamilyMemoryRows.eqBlk_halt_of_paper
#print axioms Nock.NockVMROM.Thm54.FamilyMemoryRows.decode_lambda_eq_sampled
#print axioms Nock.NockVMROM.Thm54.FamilyMemoryRows.decode_cprime_eq_role57
#print axioms Nock.NockVMROM.Thm54.HostilePoleAlignment.pole_eq_poleSource
