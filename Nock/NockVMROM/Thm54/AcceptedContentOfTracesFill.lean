/-
  Nock/NockVMROM/Thm54/AcceptedContentOfTracesFill.lean

  380 — mechanical closes on `strategyOfTraces`.
  Decode is `rowEnvAt` (family chip).  `seed_ne` is the zero-seed lift,
  not an extra premise.  Relative wrap (`wrapComputeLabel`) changes
  `ln` / record timestamps; `specializedExec_eq` is the bridge.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.DeployedComputeRows
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
import Nock.NockVMROM.Thm54.ExprSubstitution
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent
import Nock.Framework.NockInstances
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

abbrev hostileFailureEvent
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  P.optimizedFailureEvent Qc Qm

/-- `seed_ne` from the priced zero-seed lift (`nprSeed_ne_of_good`).
No extra `hz` premise. -/
theorem seed_ne_of_not_hostile
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ hostileFailureEvent P Qc Qm) :
    nprSeed c.1 ≠ 0 :=
  nprSeed_ne_of_good P Qc Qm c hgood

/-- The specialized execution **is** the wrapped `execOfTraces` at `α = alphaM`. -/
theorem specializedExec_eq
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    (strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda =
      (execTemplateOfTraces P Qc Qm c h (nprSeed c.1)).specialize (alphaM c.1) c.2.2.2.lambda :=
  rfl

theorem specializedCfg_eq
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    (strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda =
      (cfgTemplateOfTraces P Qc Qm c (nprSeed c.1)).specialize (alphaM c.1) c.2.2.2.lambda :=
  rfl

theorem specializedCfg_computeInputs
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).challenges.computeInputs =
      { α := alphaM c.1
        z := nprSeed c.1
        a := c.2.2.1.eqA
        b := c.2.2.1.eqB
        c := c.2.2.1.eqC } :=
  rfl

theorem execTemplate_computeRows_wrap
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) :
    (execTemplateOfTraces P Qc Qm c h z).computeRows =
      (execOfTraces P Qc Qm c h).computeRows.map wrapComputeLabel := by
  simp only [ExactExecutionTemplate.computeRows, execTemplateOfTraces,
    ExactExecution.computeRows]
  rw [show [mapNTree wrapComputeLabel (execOfTraces P Qc Qm c h).computeTree] =
        [(execOfTraces P Qc Qm c h).computeTree].map (mapNTree wrapComputeLabel)
      from rfl, bfsForest_mapNTree]
  simp [List.map_map]

/-- Specialized BFS compute rows are the pointwise wrap-then-specialize of
`execOfTraces` rows. -/
theorem specialized_computeRows_map
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows =
      (execOfTraces P Qc Qm c h).computeRows.map
        (fun row => (wrapComputeLabel row).specialize (alphaM c.1)) := by
  change ((execTemplateOfTraces P Qc Qm c h (nprSeed c.1)).specialize
      (alphaM c.1) c.2.2.2.lambda).computeRows =
    (execOfTraces P Qc Qm c h).computeRows.map
      (fun row => (wrapComputeLabel row).specialize (alphaM c.1))
  rw [ExactExecutionTemplate.specialize_computeRows
        (execTemplateOfTraces P Qc Qm c h (nprSeed c.1)) (alphaM c.1) c.2.2.2.lambda]
  rw [execTemplate_computeRows_wrap]
  simp [List.map_map, Function.comp_def]

theorem specializedExec_compRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows =
      (cfgOfTraces P Qc Qm c).compRows :=
  rfl

/-- Family-chip challenge slots `0..4` are the specialized compute coins.  `computeSubst` is the identity on challenges. -/
theorem decodeInputs_eq_specialized
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    decodeInputs (rowEnvAt P c (familyQc P c Qc) i) =
      { α := alphaM c.1
        z := nprSeed c.1
        a := c.2.2.1.eqA
        b := c.2.2.1.eqB
        c := c.2.2.1.eqC } := by
  have h0 := rowEnvAt_chal P c (familyQc P c Qc) i ⟨0, by decide⟩
  have h1 := rowEnvAt_chal P c (familyQc P c Qc) i ⟨1, by decide⟩
  have h2 := rowEnvAt_chal P c (familyQc P c Qc) i ⟨2, by decide⟩
  have h3 := rowEnvAt_chal P c (familyQc P c Qc) i ⟨3, by decide⟩
  have h4 := rowEnvAt_chal P c (familyQc P c Qc) i ⟨4, by decide⟩
  unfold decodeInputs inpOf decodeSource
  simp [Env.ofSubst, computeSubst, Expr.eval, h0, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Relative wrap does not move `ln_prev` (`lnPrevExponent = 0`). -/
theorem wrap_specialize_ln_prev
    (row : State × DTcomp K) (α : K) :
    ((wrapComputeLabel row).specialize α).2.2.1.ln_prev = row.2.2.1.ln_prev := by
  simp [wrapComputeLabel, ComputeRowTemplate.specialize, computeLineOrigin]

/-- Relative wrap overwrites `Inputs.α` and keeps the other four coins. -/
theorem wrap_specialize_inputs
    (row : State × DTcomp K) (α : K) :
    ((wrapComputeLabel row).specialize α).2.1 = { row.2.1 with α := α } := by
  simp [wrapComputeLabel, ComputeRowTemplate.specialize]

/-- Relative wrap writes `ln = ln_prev · α^{recordCount}`. -/
theorem wrap_specialize_ln
    (row : State × DTcomp K) (α : K) :
    ((wrapComputeLabel row).specialize α).2.2.1.ln =
      row.2.2.1.ln_prev * α ^ Nock.Framework.recordCount row.1 := by
  simp [wrapComputeLabel, ComputeRowTemplate.specialize, computeLineOrigin]

end

end Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill

#print axioms Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.seed_ne_of_not_hostile
#print axioms Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.specializedExec_eq
#print axioms Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.specialized_computeRows_map
#print axioms Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.decodeInputs_eq_specialized
