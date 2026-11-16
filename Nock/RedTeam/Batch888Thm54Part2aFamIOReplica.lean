/-
  Nock/RedTeam/Batch888Thm54Part2aFamIOReplica.lean

  This module has FamilyEnvCore's imports (plus FamilyEnvCore itself, whose
  `hostileRecordsAt` / `familyQm` / `familyQc` the body names) and FamilyEnvCore's header verbatim
  (opens, options, local notation, `noncomputable section`, the variable block), then the body of
  `FamilyEnvCore.famIOEventOf` verbatim (`famIOLive`) and its `+0` perturbation (`famIOPert`).  The
  fingerprints are read from a second module, `Batch886` §A′.
-/
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.FamilyEnvCore

namespace Nock.RedTeam.Batch888

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FamilyEnvCore

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open OptimizedStrictPackage
open OptimizedComputeHostileAccumulator
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open DeployedChipFamily
open CoordinateBasis
open CoordinateCompiler
open Module
open MonolithicRAP
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryCanonicalSatisfaction
open OptimizedComputeCollisionBound
open OptimizedMemoryCollisionAccounting

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false


set_option quotPrecheck false

/-- `P.computeChip` at `O := P.optimized`. -/
local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

/-- `P.memoryChip` at `O := P.optimized`. -/
local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

/-- `P.familyComputePublic c` at `O := P.optimized`. -/
local notation "FCP[" O ", " c "]" =>
  computePublicOfTuple (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.verifier O).raw.claim
    (OptimizedStrictNockVMROMPackage.computePublic O) c

/-- `P.familyMemoryPublic c` at `O := P.optimized`. -/
local notation "FMP[" O ", " c "]" =>
  memoryPublicOfTuple (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.verifier O).raw.claim
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem
    (OptimizedStrictNockVMROMPackage.memoryPublic O) c

/-- `P.computeChipAt c` at `O := P.optimized`. -/
local notation "CCA[" O ", " c "]" =>
  DeployedChipFamily.computeChipAt
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (FCP[O, c]) (OptimizedStrictNockVMROMPackage.orbit O) c

/-- `P.memoryChipAt c` at `O := P.optimized`. -/
local notation "MCA[" O ", " c "]" =>
  DeployedChipFamily.memoryChipAt
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (FMP[O, c]) (OptimizedStrictNockVMROMPackage.orbit O) c
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

local notation "NSM[" O "]" =>
  (namedSourceMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- Verbatim replica of `FamilyEnvCore.famIOEventOf`. -/
def famIOLive (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    c.2.1 ∈ FiniteIO.IOFailureEvent (hostileRecordsAt O c (familyQm O c Qm) (familyQc O c Qc))

/-- The `+0` perturbation of the same body. -/
def famIOPert (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    (c.2.1.1 + 0, c.2.1.2) ∈
      FiniteIO.IOFailureEvent (hostileRecordsAt O c (familyQm O c Qm) (familyQc O c Qc))

end

end Nock.RedTeam.Batch888
