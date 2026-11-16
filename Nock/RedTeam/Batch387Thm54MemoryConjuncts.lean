/-
  Nock/RedTeam/Batch387Thm54MemoryConjuncts.lean

  **Memory wrap, Vmem case (b).**

  **Vmem case (stated before any step-3 proof):** case (b).
  `Vmem = eqBlk ∧ interV` (`MemoryTable.lean::Vmem`).  `eqBlk` reads
  `mem.ts` on `read_root` / `verify_child`;
  `interV` reads the record through `pole` (`:2072`, `:2080`, `:2123`).
  Live `wrapMemoryLabel` stores `recordExponent := 0`, so specialize
  writes `mem.ts := α^0 = 1` on active rows — not the committed
  timestamp.  Case (b) therefore applies: `memExponent` is the discrete
  log of the committed `ts` in `⟨α⟩`.  Changing
  `MemoryRowTemplate.specialize` to use that exponent would break
  `HonestCommitment.memory_specialize_placeholder_eq`.  The live wrap
  is not the identity on `mem.ts`.  `vmem` / `memoryRows` stay open.

  Closed here (step 3 scalars, wrap-preserved):
  * `mem_first_ipre` — first-row role 27
  * `mem_last_icur` — last-row role 28 (`:1431`)
  * `mem_icur_chain` — `chainMixed` (`:1431`, `:2037`)

  Still open of the seven: `vmem`, `memoryRows` (wrap `ts`),
  `mem_first_counts`, `mem_first_indicator` (no deployed first-row
  pin on roles 3/4; `envF.trace 4` is the first-row *mask*).

  **8/21** (target ≥12 missed; see draft).
  Newly closed: `mem_first_ipre`, `mem_last_icur`, `mem_icur_chain`.
-/
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.RedTeam.Batch386Thm54ComputeConjuncts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch387

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.Framework
open MonolithicRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Vmem case recorded as a named constant so the receipt cannot drift. -/
def vmemCase : String := "b"

theorem vmemCase_is_b : vmemCase = "b" := rfl

/-- Step-3 closed memory *scalar* conjuncts.  Not `vmem` / `memoryRows`. -/
structure ClosedMemoryScalarConjuncts
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatM : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) : Prop where
  mem_first_ipre :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt
      ⟨0, (strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda |>.memRows_pos⟩).ipre = 0
  mem_last_icur :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt
      (((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).orbit.lastIndex
        ((strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows
        ((strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows_pos)).icur = 0
  mem_icur_chain :
    ∀ i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows,
      ∀ hi : (i : ℕ) + 1 <
          ((strategyOfTraces P Qc Qm c h).specializedCfg
              (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows,
        (((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt i).icur =
          (((strategyOfTraces P Qc Qm c h).specializedExec
              (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt
            ⟨(i : ℕ) + 1, hi⟩).ipre

theorem closedMemoryScalarConjuncts_of_accepted
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatM : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) :
    ClosedMemoryScalarConjuncts P Qc Qm c h hz hsatM where
  mem_first_ipre := specialized_mem_first_ipre P Qc Qm c h hz hsatM
  mem_last_icur := specialized_mem_last_icur P Qc Qm c h hz hsatM
  mem_icur_chain := specialized_mem_icur_chain P Qc Qm c h hz hsatM

/-- Names closed at step 3.  Starting 5/21 + these three = **8/21**. -/
def newlyClosed : List String :=
  ["mem_first_ipre", "mem_last_icur", "mem_icur_chain"]

theorem newlyClosed_length : newlyClosed.length = 3 := by decide

theorem closed_count_after_step3 : 5 + newlyClosed.length = 8 := by decide

/-- Of the ten named transfer conjuncts, these four stay open. -/
def stillOpenOfTen : List String :=
  ["vmem", "memoryRows", "mem_first_counts", "mem_first_indicator"]

theorem stillOpenOfTen_length : stillOpenOfTen.length = 4 := by decide

end

end Nock.RedTeam.Batch387

#print axioms Nock.RedTeam.Batch387.closedMemoryScalarConjuncts_of_accepted
#print axioms Nock.RedTeam.Batch387.closed_count_after_step3
#print axioms Nock.RedTeam.Batch387.vmemCase_is_b
