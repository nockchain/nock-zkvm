/-
  Nock/NockVMROM/Thm54/FamilyIOChainMemory.lean

  Family-chip twins of the
  hostile memory accumulator (`OptimizedMemoryHostileAccumulator` §B–§E), of the IO assembly
  (`OptimizedHostileIOAssembly` §A–§F) and of `OptimizedHostileTimestamps.hostile_LIO'`, stated
  at `memoryChipAt c` / `computeChipAt c` (the chips `DeployedAcceptanceAt` reads).

  The memory row environments are `FamilyComputeRows.memoryBaseEnvAt` /
  `memorySourceEnvAt` at the reindexed trace `FamilyMemoryRows.honestQm P c Qm` (the same
  polynomials; only the challenge/public maps are the tuple's).  The IO coins are the tuple's
  `c.2.1` **by definition** on both chips (compute slots `7`/`8`, memory slots `4`/`5`), so no
  `sampled_io_coins` / `memory_sampled_coins` pin is read.
-/
import Nock.NockVMROM.Thm54.FamilyIOChainCompute
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainMemory
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.FamilyIOChain

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeCorrectedFinal
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemoryHostileAccumulator (memRowCoins memRowRecord10 memRowTerm
  rowRecord_eq_memRowRecord10 denominatorPin_eval_iff contribution_eq_memRowTerm_of_io
  memRowTerm_eq_rowResponseTerms DenominatorPinned denominatorPinned_iff rowResponseTerms
  rowResponses rowDenominator accInit_mem accTerminal_mem accStep_mem contribution_mem
  verBool_mem safeNormalisation_mem safeInverse_mem denominatorPinMixed_mem
  intermediateInit_mem intermediateTerminal_mem chainMixed_mem)
open DeployedChipFamily
open FamilyComputeRows
open FamilyMemoryRows
open Module

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-! ## A. The family memory row environments -/

variable (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-! ## B. What every accepted family memory trace commits (twin of §B) -/

section Rows

variable (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
include hsat

/-! ### The response list (twin of §E) -/

end Rows

/-- **Twin of `OptimizedMemoryHostileAccumulator.hostileResponseTerms`.** -/
def hostileResponseTermsAt : List ((Fin 10 → K) × K) :=
  (List.ofFn fun i : Fin (memRows P) =>
    rowResponseTerms (memEnvK P c Qm i) (memEnvF P c Qm i)).flatten

theorem hostileResponsesAt_eq_map_fst :
    hostileResponsesAt P c Qm = (hostileResponseTermsAt P c Qm).map Prod.fst := by
  simp only [hostileResponsesAt, hostileResponseTermsAt, rowResponses, List.map_flatten,
    List.map_ofFn]
  rfl

/-! ## C. The family records and the IO assembly (twin of `OptimizedHostileIOAssembly`) -/

variable (Qc : Fin (P.computeChipAt c).rap.w → F[X])

end

end Nock.NockVMROM.Thm54.FamilyIOChain
