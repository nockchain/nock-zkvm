/-
  Nock/RedTeam/Batch491Thm54WrongChildLink.lean

  Wrong-child-link / self-caller
  receipts at the deployed chips.**
-/
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.RedTeam.Batch469Thm54GarbageWitness
import Nock.RedTeam.Batch470Thm54MemoryPrefix
import Nock.RedTeam.Batch485Thm54WalkQueueReceipts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch491

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch459
open Nock.RedTeam.Batch485
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

theorem compute_self_caller_rejected
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hrows : P.optimized.family.problem.cfg.compRows = 5) :
    foW P c Qc hsat ≠ Nock.RedTeam.Batch469.fo5 :=
  accepted_compute_fo_ne_fo5 P c Qc hsat hax hbasis hwidth hrows

theorem memory_self_child_rejected
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hchar : MemStateTagChar F)
    (hk : MemoryWalkDeployed.kMem P = 1)
    (hrows : MemoryWalkDeployed.memRows P = 3) :
    MemoryWalkDeployed.foW P c Qm ≠ Nock.RedTeam.Batch470.fo3 :=
  accepted_memory_fo_ne_fo3 P c Qm hsat hchar hk hrows

end Nock.RedTeam.Batch491

#print axioms Nock.RedTeam.Batch491.compute_self_caller_rejected
#print axioms Nock.RedTeam.Batch491.memory_self_child_rejected
