/-
  Nock/RedTeam/Batch364Thm54AcceptedContentOfDeployed.lean

  **Deployed bridge.**  Data-only bundle
  `` `StrategyOfTraces.lean::strategyOfTracesData` `` (not
  `ProductionStrategy`).
-/
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch364

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SemanticStrategy

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## Deployed-side content (data bundle, not `ProductionStrategy`) -/

/-- What we can *state* on `strategyOfTracesData` without inhabiting
`ProductionStrategy`.  This is the deployed reading of
`AcceptedContent (strategyOfTracesData Qc Qm) ω`. -/
structure DeployedAcceptedContent
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (ω : JointCoins K) : Prop where
  seed_ne : nprSeed ω ≠ 0
  computeVcomp : computeRowsAreVcomp P Qc
  claim_eq :
    (strategyOfTracesData P Qc Qm).claim =
      (strategyOfTracesData P Qc Qm).skeleton.publicClaim

theorem deployed_gives_compute_vcomp
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : DeployedAcceptance P Qc Qm c)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0) :
    computeRowsAreVcomp P Qc :=
  computeRowsAreVcomp_of_sat P Qc hacc.compute_satisfies hz0

/-- Closed: claim of the data bundle is the decoded skeleton's public
claim (`same_problem_claim`, vacuous `rfl`). -/
theorem deployed_gives_claim
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (strategyOfTracesData P Qc Qm).claim =
      (strategyOfTracesData P Qc Qm).skeleton.publicClaim :=
  (strategyOfTracesData P Qc Qm).publicClaim_eq.symm

/-- The closed half of `acceptedContent_of_deployed`. -/
theorem acceptedContent_of_deployed_closed
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : DeployedAcceptance P Qc Qm c)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (hseed : nprSeed c.1 ≠ 0) :
    DeployedAcceptedContent P Qc Qm c.1 where
  seed_ne := hseed
  computeVcomp := deployed_gives_compute_vcomp P Qc Qm c hacc hz0
  claim_eq := deployed_gives_claim P Qc Qm


/-- OPEN — memory-half `BindsAt`. -/
def missing_memory_binds
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (z : K) : Prop :=
  ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
    List.Forall₂ (SemanticStrategy.MemoryTreeBinds z)
      (decodedSkeletonOf P Qc Qm).memoryForest exec.memoryForest

/-- Until then `z` is the package
constant, so `nprSeed c.1 = pkg.z` is not a theorem of
`DeployedAcceptance`. -/
def missing_chips_read_c
    (c : OptimizedProductionChallengeTuple K F) : Prop :=
  nprSeed c.1 = P.optimized.family.problem.cfg.challenges.z

/-- OPEN — identify decoded compute rows with a family's
`exec.computeRows` (`ComputeRowsAccepted`). -/
def missing_compute_rows_family
    (_Qc : Fin P.computeChip.rap.w → F[X]) : Prop :=
  ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
    exec.ComputeRowsAccepted ∧
      exec.computeRows.length = P.optimized.family.problem.cfg.compRows

/-- OPEN — memory `Vmem` / `MemoryRowsAccepted` at a trace-built family. -/
def missing_memory_rows_family
    (_Qm : Fin P.memoryChip.rap.w → F[X]) : Prop :=
  ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
    exec.MemoryRowsAccepted ∧
      exec.memoryRows.length = P.optimized.family.problem.cfg.memRows

def missing_topology_family : Prop :=
  ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
    ComputeExactTopology exec ∧ MemoryExactTopology exec

/-- The full deployed statement.  `hgood` is the census
exclusion the spine already takes via `FailureUnion`. -/
theorem acceptedContent_of_deployed
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : DeployedAcceptance P Qc Qm c)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (hseed : nprSeed c.1 ≠ 0)
    (_hgood : True)
    (_hmemBinds : missing_memory_binds P Qc Qm (nprSeed c.1))
    (_hread : missing_chips_read_c P c)
    (_hcompFam : missing_compute_rows_family P Qc)
    (_hmemFam : missing_memory_rows_family P Qm)
    (_htop : missing_topology_family (F := F) (K := K)) :
    DeployedAcceptedContent P Qc Qm c.1 :=
  acceptedContent_of_deployed_closed P Qc Qm c hacc hz0 hseed

/-! ## Matmul-field instantiation of the closed conjunct -/

open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks

abbrev GF := Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.F
abbrev GK := Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.K

theorem matmul_deployed_gives_compute_vcomp
    {h : ℕ} (P : OptimizedFullStrictNockVMROMPackage GF GK h)
    (Qc : Fin P.computeChip.rap.w → GF[X])
    (Qm : Fin P.memoryChip.rap.w → GF[X])
    (c : OptimizedProductionChallengeTuple GK GF)
    (hacc : DeployedAcceptance P Qc Qm c)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0) :
    computeRowsAreVcomp P Qc :=
  deployed_gives_compute_vcomp P Qc Qm c hacc hz0

end

end Nock.RedTeam.Batch364

#print axioms Nock.RedTeam.Batch364.deployed_gives_compute_vcomp
#print axioms Nock.RedTeam.Batch364.acceptedContent_of_deployed_closed
#print axioms Nock.RedTeam.Batch364.acceptedContent_of_deployed
#print axioms Nock.RedTeam.Batch364.matmul_deployed_gives_compute_vcomp
