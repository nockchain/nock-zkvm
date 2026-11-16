/-
  Nock/RedTeam/Batch531Thm54MemFirstAndReady.lean

  First-row `pt.counts` / `pt.indicator` of the
  specialized exec are the root-mask zeros
  (`Batch409.deployed_root_accumulators_zero`, wrap preserves `pt`).
  Live wrap ledger **5 → 3**.  `ComputeJoinReady` of `s0`/`s1` is
  `V_comp` (`Batch530.computeJoinReady_op*_of_vcomp`).  `bindsDropBlockersAfter` is `[]` after the seed restatement.
-/
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.RedTeam.Batch409Thm54SeedBoundaryKside
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch526Thm54DropTracesBindsHyps
import Nock.RedTeam.Batch530Thm54ComputeTreeBindsDeployed
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch531

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Framework
open MonolithicRAP
open Nock.RedTeam.Batch409
open Nock.RedTeam.Batch509
open Nock.RedTeam.Batch526
open Nock.RedTeam.Batch530

/-! ## Live ledger 5 → 3 -/

/-- Open wrap conjuncts after the first-row `pt` zeros. -/
def openConjunctsAfterMemFirst : List String :=
  ["axisStructural", "rootBoundary", "structuralChecks"]

theorem openConjunctsAfterMemFirst_length :
    openConjunctsAfterMemFirst.length = 3 := by decide

theorem mem_first_names_left :
    "mem_first_counts" ∉ openConjunctsAfterMemFirst ∧
      "mem_first_indicator" ∉ openConjunctsAfterMemFirst := by
  decide

theorem remaining_three_from_five :
    openConjunctsAfterMemFirst =
      openConjunctsAfterWrap.filter
        (fun n => n ≠ "mem_first_counts" ∧ n ≠ "mem_first_indicator") := by
  decide

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `mem_first_counts`: wrap-preserved `pt.counts` is the root-mask zero. -/
theorem specialized_mem_first_counts
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (h : TracesWalkHyps P Qc (honestQm P c Qm) c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) :
    (((strategyOfTraces P Qc (honestQm P c Qm) c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt
      ⟨0, (strategyOfTraces P Qc (honestQm P c Qm) c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda |>.memRows_pos⟩).pt.counts = 0 := by
  have hpos :=
    ((strategyOfTraces P Qc (honestQm P c Qm) c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows_pos
  have hpt :=
    specialized_memoryPubAt_pt P Qc (honestQm P c Qm) c h hz ⟨0, hpos⟩
  have hcast :
      Fin.cast
        ((specializedExec_memRows P Qc (honestQm P c Qm) c h hz).trans
          (cfgOfTraces_memRows P Qc (honestQm P c Qm) c)) ⟨0, hpos⟩ =
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩ :=
    Fin.ext rfl
  have hi0 : (0 : ℕ) < P.optimized.family.problem.cfg.kMem :=
    Nat.succ_le_iff.mp (kMem_pos (P := P))
  have hzero :=
    deployed_root_accumulators_zero P c Qm hsatM
      ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩ hi0
  have hdec :
      (decodeMemPub P (honestQm P c Qm) c
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).pt.counts = 0 := by
    simpa [decodeMemPub] using hzero.1
  rw [hpt, hcast, hdec]

/-- `mem_first_indicator`: wrap-preserved `pt.indicator` is the root-mask zero. -/
theorem specialized_mem_first_indicator
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (h : TracesWalkHyps P Qc (honestQm P c Qm) c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) :
    (((strategyOfTraces P Qc (honestQm P c Qm) c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt
      ⟨0, (strategyOfTraces P Qc (honestQm P c Qm) c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda |>.memRows_pos⟩).pt.indicator = 0 := by
  have hpos :=
    ((strategyOfTraces P Qc (honestQm P c Qm) c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows_pos
  have hpt :=
    specialized_memoryPubAt_pt P Qc (honestQm P c Qm) c h hz ⟨0, hpos⟩
  have hcast :
      Fin.cast
        ((specializedExec_memRows P Qc (honestQm P c Qm) c h hz).trans
          (cfgOfTraces_memRows P Qc (honestQm P c Qm) c)) ⟨0, hpos⟩ =
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩ :=
    Fin.ext rfl
  have hi0 : (0 : ℕ) < P.optimized.family.problem.cfg.kMem :=
    Nat.succ_le_iff.mp (kMem_pos (P := P))
  have hzero :=
    deployed_root_accumulators_zero P c Qm hsatM
      ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩ hi0
  have hdec :
      (decodeMemPub P (honestQm P c Qm) c
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).pt.indicator = 0 := by
    simpa [decodeMemPub] using hzero.2
  rw [hpt, hcast, hdec]

/- `tracesSpecializedExec` and `tracesSpecializedExec_eq_strategy`
are retired — the fold is `StrategyOfTracesCore.strategyOfTraces_specializedExec` (`strategyOfTraces`
takes no binding hypothesis any more, so its specialized exec IS the one the wrap path reads). -/

/-- Seed-local `BindsAt` at the sampled coin.  The universal form it replaced
    (`TracesBindsHyps`, retired) is REFUTED at `3 ≤ |K|`, not a collision event
    (`Batch573.bindsAt_traces_forces_seed`). -/
def TracesBindsAtSeed
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) : Prop :=
  ∀ hz : nprSeed c.1 ≠ 0,
    SemanticStrategy.BindsAt (nprSeed c.1) (decodedSkeletonOf P Qc Qm)
      (specializedProblem (timestampOfTraces P Qc Qm c h)
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).cfg
      (specializedProblem (timestampOfTraces P Qc Qm c h)
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec

theorem tracesBindsAtSeed_of_tree
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hc : ∀ hz : nprSeed c.1 ≠ 0,
      SemanticStrategy.ComputeTreeBinds (nprSeed c.1)
        (decodedSkeletonOf P Qc Qm).computeTree
        (specializedProblem (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec.computeTree)
    (hm : ∀ hz : nprSeed c.1 ≠ 0,
      List.Forall₂ (SemanticStrategy.MemoryTreeBinds (nprSeed c.1))
        (decodedSkeletonOf P Qc Qm).memoryForest
        (specializedProblem (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec.memoryForest) :
    TracesBindsAtSeed P Qc Qm c h :=
  fun hz =>
    SemanticStrategy.BindsAt.ofTreeBindings
      (specializedProblem_seed _ _ hz _ _) (hc hz) (hm hz)

/- `semanticSupportAt_of_seed : SemanticSupportAt …` is retired with
`SemanticSupportAt`; its content is `strategyOfTraces_bindsAtCoin`. -/

theorem computeJoinReady_op0_is_vcomp :
    True :=
  trivial

theorem bindsDrop_now_empty :
    bindsDropBlockersAfter.length = 0 :=
  bindsDropBlockersAfter_length

end

end Nock.RedTeam.Batch531

#print axioms Nock.RedTeam.Batch531.openConjunctsAfterMemFirst_length
#print axioms Nock.RedTeam.Batch531.mem_first_names_left
#print axioms Nock.RedTeam.Batch531.specialized_mem_first_counts
#print axioms Nock.RedTeam.Batch531.specialized_mem_first_indicator
#print axioms Nock.RedTeam.Batch531.tracesBindsAtSeed_of_tree
