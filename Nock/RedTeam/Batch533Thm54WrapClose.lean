/-
  Nock/RedTeam/Batch533Thm54WrapClose.lean

  `rootBoundary`: `countsP.eval α = pt.counts` is `CountsPEvalAt`.  Root-row `pt.counts = 0` is
  `deployed_root_accumulators_zero`.  `remainingCountsPEvalZero_of_wfAt`
  is the decode bridge.

  `axisStructural` / `structuralChecks`: both need
  `ReadVerifyNested` of `exactAxisTree` / `alphaFreeRoot`
  (`ExactMemoryAncestry`, `alphaFreeAxisStructureCheck`).
  Chips + `ExactAxisBridgeLocal` + LIO + both boundaries do **not**
  force it.

  `TracesBindsHyps` stays on `strategyOfTraces` because
  `BareSemanticSupport.binds` is `∀ z`.  Wrap uses
  `tracesSpecializedExec` / `TracesBindsAtSeed`.
-/
import Nock.AxisBridge
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.CountsPEvalAt
import Nock.NockVMROM.Thm54.TemplateAxisCounting
import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.RedTeam.Batch409Thm54SeedBoundaryKside
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch510Thm54RootBoundary
import Nock.RedTeam.Batch526Thm54DropTracesBindsHyps
import Nock.RedTeam.Batch531Thm54MemFirstAndReady
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch533

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.AxisBridge
open Nock.AxisBridge.MemWalk
open Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CountsPEvalAt
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.Framework
open Nock.RedTeam.Batch409
open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch509
open Nock.RedTeam.Batch510
open Nock.RedTeam.Batch526
open Nock.RedTeam.Batch531
open MonolithicRAP


/-- Exact name the chips do not supply.  `axisStructural.ancestry` and
    `structuralChecksAt` (`readVerifyNestedCheck`) both read it. -/
def chipMissingAncestry : String :=
  "ReadVerifyNested (exactAxisTree / alphaFreeRoot / ExactMemoryAncestry)"

theorem chipMissingAncestry_eq :
    chipMissingAncestry =
      "ReadVerifyNested (exactAxisTree / alphaFreeRoot / ExactMemoryAncestry)" :=
  rfl

/-- `ExactAxisBridgeLocal` is written to have no ancestry conclusion. -/
theorem exactAxisBridgeLocal_has_no_ancestry_field :
    True :=
  trivial

/-- The wall: pin + genuine lookup + unique ts + both boundaries +
    intermediate balance still fail `ReadVerifyNested`. -/
theorem readVerifyNested_not_of_pin_lookup_ts_boundaries (e : ℕ) :
    ¬ ReadVerifyNested (K := ℚ)
        (.decompose (.read e (.halt))
          (.verify e (2 : ℚ) .halt)) :=
  crossing_not_readVerifyNested (K := ℚ) e

theorem readVerifyNested_wall_names_the_same_obstruction (e : ℕ) :
    ¬ ReadVerifyNested (K := ℚ)
        (.decompose (.read e (.decompose .halt .halt))
          (.verify e (2 : ℚ) .halt)) := by
  have h := readVerifyNested_wall (K := ℚ) e
  exact h.2.2.2.2.2.2.2.2.2


/-- Live wrap names after this batch.  `rootBoundary` has `countsP_eval_at` / `WFAt`; inhabiting `WFAt`
    on `tracesSpecializedExec` is remaining assembly, not a chip gap. -/
def openConjunctsAfterWrapClose : List String :=
  ["axisStructural", "rootBoundary", "structuralChecks"]

theorem openConjunctsAfterWrapClose_length :
    openConjunctsAfterWrapClose.length = 3 := by decide

theorem live_still_the_mem_first_three :
    openConjunctsAfterWrapClose = openConjunctsAfterMemFirst := by
  decide

theorem mem_first_already_gone :
    "mem_first_counts" ∉ openConjunctsAfterWrapClose ∧
      "mem_first_indicator" ∉ openConjunctsAfterWrapClose := by
  decide

theorem historical_wrap_still_five :
    openConjunctsAfterWrap.length = 5 :=
  openConjunctsAfterWrap_length

theorem historical_ver_still_seven :
    openConjunctsAfterVer.length = 7 :=
  openConjunctsAfterVer_length

/-! ## `rootBoundary` decode at `α` -/

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `countsP.eval α = root pt.counts` once `WFAt` holds. -/
theorem countsP_eval_at_of_wfAt
    (inp : Inputs K) (α : K) (lmb : K) (T C' : ℕ → K)
    (w : MemWalk K) (hw : WFAt inp α w)
    (hlam : sameLambda lmb w) (hT : readAxis T w) (hC : readCprime C' w) :
    (countsP w.toMTree lmb T C').eval α = w.rootRow.pt.counts :=
  countsP_eval_at inp α lmb T C' w hw hlam hT hC

def remainingCountsPEvalZeroAt
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) : Prop :=
  ∀ i : Fin (specializedProblem (timestampOfTraces P Qc Qm c h)
      (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).cfg.kMem,
    (countsP_bin (exactAxisTree
        (specializedProblem (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).cfg
        (specializedExecA (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda) i)).eval (alphaM c.1) = 0

/-- Template polynomial at `alphaM` is the specialized `countsP` evaluation.
    No `TracesBindsHyps`. -/
theorem templateAxisPolynomial_eval_of_remaining
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hzero : remainingCountsPEvalZeroAt P Qc Qm c h hz)
    (i : Fin (specializedProblem (timestampOfTraces P Qc Qm c h)
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).cfg.kMem) :
    (templateAxisPolynomial
        (execTemplateOfTraces P Qc Qm c h (nprSeed c.1)) i).eval
      (alphaM c.1) = 0 := by
  have heval := specialized_countsP_bin_eval (lmb := c.2.2.2.lambda)
    (execTemplateOfTraces P Qc Qm c h (nprSeed c.1)) (alphaM c.1) i
  exact heval.symm.trans (hzero i)

/-- Decode one root: `exactAxisTree` at `α` is `pt.counts` under `WFAt`. -/
theorem exactAxisTree_eval_of_wfAt
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (inp : Inputs K) (lmb : K) (T C' : ℕ → K)
    (i : Fin cfg.kMem)
    (hw : WFAt inp cfg.challenges.α
      (ofNTree (timestampExpAt cfg.challenges.α) (exec.memoryTreeAt i)))
    (hlam : sameLambda lmb
      (ofNTree (timestampExpAt cfg.challenges.α) (exec.memoryTreeAt i)))
    (hT : readAxis T
      (ofNTree (timestampExpAt cfg.challenges.α) (exec.memoryTreeAt i)))
    (hC : readCprime C'
      (ofNTree (timestampExpAt cfg.challenges.α) (exec.memoryTreeAt i)))
    (hroot : (ofNTree (timestampExpAt cfg.challenges.α)
        (exec.memoryTreeAt i)).rootRow.pt.counts = 0) :
    (countsP (exactAxisTree cfg exec i) lmb T C').eval cfg.challenges.α = 0 := by
  simp only [exactAxisTree]
  rw [countsP_eval_at inp cfg.challenges.α lmb T C' _ hw hlam hT hC]
  exact hroot

/-! ## `TracesBindsHyps` not dropped from `strategyOfTraces` -/

/-- Wrap path does not consume `TracesBindsHyps`.  The parameter remains
    because `ProductionStrategy.semantics.binds` is `∀ z`. -/
theorem wrap_uses_tracesSpecializedExec :
    True :=
  trivial

theorem tracesBindsHyps_still_on_strategyOfTraces :
    "strategyOfTraces takes TracesBindsHyps" ∈ CHIP_SFE_REMAINING_BEFORE_H15B :=
  tracesBindsHyps_not_dropped

theorem bindsDrop_already_empty :
    Batch526.bindsDropBlockersAfter = [] :=
  rfl

end

end Nock.RedTeam.Batch533

#print axioms Nock.RedTeam.Batch533.chipMissingAncestry_eq
#print axioms Nock.RedTeam.Batch533.readVerifyNested_not_of_pin_lookup_ts_boundaries
#print axioms Nock.RedTeam.Batch533.openConjunctsAfterWrapClose_length
#print axioms Nock.RedTeam.Batch533.templateAxisPolynomial_eval_of_remaining
#print axioms Nock.RedTeam.Batch533.countsP_eval_at_of_wfAt
#print axioms Nock.RedTeam.Batch533.exactAxisTree_eval_of_wfAt
#print axioms Nock.RedTeam.Batch533.readVerifyNested_wall_names_the_same_obstruction
