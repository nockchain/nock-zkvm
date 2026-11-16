/-
  Nock/RedTeam/Batch367Thm54FamilyOfTraces.lean

  **`familyOfTraces` and the strategy interface.**

  `familyOfTraces P Qc Qm c` is the package walk family with the three walk
  coins replaced by the sampled tuple (`alphaC`, `alphaM`, `gamma` of `c.1`).

  `strategyOfTraces : ProductionStrategy` is **not** inhabited.  Reason 1 of
  NL still stands: `BareSemanticSupport.binds` is `∀ z`, and a committed
  fingerprint is at one seed.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch367

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Walk-coin overwrite of the package family.  Exec / encoders / IO are
`P.walkFamily` (disclosed honest-side geometry). -/
def familyOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    RawPlusIOSegmentedFamily F K :=
  { problem := P.walkFamily.problem
    computeWalkAlpha := alphaC c.1
    memoryWalkAlpha := alphaM c.1
    walkGamma := gamma c.1
    compNodeWidth := P.walkFamily.compNodeWidth
    compNodeEncode := P.walkFamily.compNodeEncode
    memNodeWidth := P.walkFamily.memNodeWidth
    memNodeEncode := P.walkFamily.memNodeEncode
    requests := P.walkFamily.requests
    responses := P.walkFamily.responses
    outMem := P.walkFamily.outMem }

theorem familyOfTraces_computeWalkAlpha
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (familyOfTraces P Qc Qm c).computeWalkAlpha = alphaC c.1 :=
  rfl

theorem familyOfTraces_memoryWalkAlpha
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (familyOfTraces P Qc Qm c).memoryWalkAlpha = alphaM c.1 :=
  rfl

theorem familyOfTraces_walkGamma
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (familyOfTraces P Qc Qm c).walkGamma = gamma c.1 :=
  rfl

theorem familyOfTraces_problem
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (familyOfTraces P Qc Qm c).problem = P.walkFamily.problem :=
  rfl

/-- Positive control: at `honestTuple` the overwritten coins are the
honest joint coins.  `computeWalkAlpha` matches `P.optimized.family`
by `honestJointCoins`; `P.walkFamily.computeWalkAlpha` is **not** `rfl`
against that (the walk family is a separate object) — disclosed. -/
theorem familyOfTraces_honest_alphaC
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (familyOfTraces P Qc Qm P.honestTuple).computeWalkAlpha =
      P.optimized.family.computeWalkAlpha :=
  rfl

theorem familyOfTraces_honest_alphaM
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (familyOfTraces P Qc Qm P.honestTuple).memoryWalkAlpha =
      P.objects.cfg.challenges.α :=
  rfl

/-- The honest joint `γ` is the family's walk-node RLC coin `walkGamma`
(read at compute slot `10`), no longer the table's record-RLC `challenges.γ`. -/
theorem familyOfTraces_honest_gamma
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (familyOfTraces P Qc Qm P.honestTuple).walkGamma =
      P.optimized.family.walkGamma :=
  rfl

/-- Not `ProductionStrategy`. -/
abbrev tracesData
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    StrategyOfTracesData P Qc Qm :=
  strategyOfTracesData P Qc Qm

theorem tracesData_claim
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (tracesData P Qc Qm).claim = publicClaimOf P Qc Qm :=
  rfl

def strategyOfJoin
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (hclaim : (decodedSkeletonOf P Qc Qm).publicClaim = V.raw.claim) :
    ProductionStrategy F K where
  verifier := V
  skeleton := decodedSkeletonOf P Qc Qm
  publicClaim_eq := hclaim

/-- Its seed-local binding at the sampled coin is exactly the compute/memory join premise. -/
theorem strategyOfJoin_bindsAtCoin
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) (lmb : K)
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (hclaim : (decodedSkeletonOf P Qc Qm).publicClaim = V.raw.claim)
    (hbinds :
      ∀ hz : nprSeed c.1 ≠ 0,
        SemanticStrategy.BindsAt (nprSeed c.1) (decodedSkeletonOf P Qc Qm)
          (specializedProblem V.raw.timestamp (nprSeed c.1) hz (alphaM c.1) lmb).cfg
          (specializedProblem V.raw.timestamp (nprSeed c.1) hz (alphaM c.1) lmb).exec) :
    (strategyOfJoin P Qc Qm V hclaim).BindsAtCoin c.1 lmb :=
  hbinds

end

end Nock.RedTeam.Batch367

#print axioms Nock.RedTeam.Batch367.familyOfTraces_honest_alphaC
#print axioms Nock.RedTeam.Batch367.familyOfTraces_problem
#print axioms Nock.RedTeam.Batch367.tracesData_claim
#print axioms Nock.RedTeam.Batch367.strategyOfJoin_bindsAtCoin
