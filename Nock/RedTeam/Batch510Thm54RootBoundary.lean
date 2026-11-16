/-
  Nock/RedTeam/Batch510Thm54RootBoundary.lean

  `RootAxisBoundaryAt` is evaluation of the
  committed template axis polynomial at `alphaM`
  (`ProductionP8Containment.RootAxisBoundaryAt`).
  `specialized_countsP_eval` rewrites that to
  `(countsP (exactAxisTree specializedCfg specializedExec i)).eval α`.
  Root-row `pt.counts = 0` is the chip gate
  `deployed_root_accumulators_zero`.  The decode bridge
  that identifies `countsP.eval α` with that column is
  `AxisBridge.countsP_eval`, whose `WF` needs `TsNode` / `MemPower`
  (`remainingActiveMemPower`).  Ledger stays **5**.
-/
import Nock.AxisBridge
import Nock.NockVMROM.Thm54.TemplateAxisCounting
import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.RedTeam.Batch409Thm54SeedBoundaryKside
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch509Thm54WrapSpecialize
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch510

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.Framework
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.RedTeam.Batch409
open Nock.RedTeam.Batch509
open MonolithicRAP

/-! ## Ledger stays 5: `rootBoundary` not discharged -/

def openAfterRootBoundary : List String :=
  openConjunctsAfterWrap

theorem openAfterRootBoundary_length :
    openAfterRootBoundary.length = 5 :=
  openConjunctsAfterWrap_length

theorem rootBoundary_still_on_ledger :
    "rootBoundary" ∈ openAfterRootBoundary := by
  decide

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (h : TracesWalkHyps P Qc₀ Qm₀ c)
  (hz : nprSeed c.1 ≠ 0)

/-- Chip half of the decode bridge: every masked root row has
    `pt.counts = 0`. -/
theorem deployed_root_pt_counts_zero
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hi : (i : ℕ) < P.optimized.family.problem.cfg.kMem) :
    (decodeMemPub P (honestQm P c Qm) c i).pt.counts = 0 := by
  have hzero := deployed_root_accumulators_zero P c Qm hsat i hi
  simpa [decodeMemPub] using hzero.1

/-- Chip twin: `pt.indicator = 0` on the same rows. -/
theorem deployed_root_pt_indicator_zero
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hi : (i : ℕ) < P.optimized.family.problem.cfg.kMem) :
    (decodeMemPub P (honestQm P c Qm) c i).pt.indicator = 0 := by
  have hzero := deployed_root_accumulators_zero P c Qm hsat i hi
  simpa [decodeMemPub] using hzero.2

def remainingCountsPEvalZero : Prop :=
  ∀ i : Fin ((strategyOfTraces P Qc₀ Qm₀ c h).specializedCfg
      (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).kMem,
    (countsP_bin (exactAxisTree
        ((strategyOfTraces P Qc₀ Qm₀ c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda)
        ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExecA
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda) i)).eval (alphaM c.1) = 0

/-- Committed template of the traces strategy is `execTemplateOfTraces`. -/
theorem committedTemplate_eq_execTemplate :
    ProductionAxisStructureVerifier.committedTemplate
        (strategyOfTraces P Qc₀ Qm₀ c h).verifier
        (nprSeed c.1) hz =
      execTemplateOfTraces P Qc₀ Qm₀ c h (nprSeed c.1) :=
  rfl

/-- The polynomial boundary is the specialized `countsP` evaluation. -/
theorem rootBoundary_of_countsP_eval_zero
    (hzero : remainingCountsPEvalZero P c Qc₀ Qm₀ h hz) :
    (strategyOfTraces P Qc₀ Qm₀ c h).RootAxisBoundaryAt
      (nprSeed c.1) hz (alphaM c.1) := by
  intro i
  have htmpl := committedTemplate_eq_execTemplate P c Qc₀ Qm₀ h hz
  have heval := specialized_countsP_bin_eval (lmb := c.2.2.2.lambda)
    (execTemplateOfTraces P Qc₀ Qm₀ c h (nprSeed c.1)) (alphaM c.1) i
  rw [htmpl]
  exact heval.symm.trans (hzero i)

/-- **Exact remaining statement.**  `AxisBridge.countsP_eval` is at
    `inp.z`; the axis polynomial evaluates at `α`.  `WF` needs
    `TsNode` / `Batch509.remainingActiveMemPower`. -/
def remainingJoin : String :=
  "countsP.eval α = root pt.counts (AxisBridge.countsP_eval at α, TsNode / remainingActiveMemPower)"

theorem remainingJoin_nonempty : remainingJoin ≠ "" := by
  decide

end

end Nock.RedTeam.Batch510

#print axioms Nock.RedTeam.Batch510.openAfterRootBoundary_length
#print axioms Nock.RedTeam.Batch510.deployed_root_pt_counts_zero
#print axioms Nock.RedTeam.Batch510.rootBoundary_of_countsP_eval_zero
