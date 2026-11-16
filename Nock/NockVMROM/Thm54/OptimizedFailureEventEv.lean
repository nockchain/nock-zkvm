/-
  Nock/NockVMROM/Thm54/OptimizedFailureEventEv.lean

  Additive: `optimizedFailureEvent` and every consumer stay; nothing is re-pointed.

  The event, summand by summand (2b-ii's §5 shape):
  * **the root-result 1-pair event**: `rootResultEv P Qc Qm := liftSeed (pairBadSeeds Λg
    [(e_built, claim.result)])`, card `≤ (2Λg − 1)·|𝕂|³`;
  * every other summand of `optimizedFailureEvent` verbatim (family IO, timestamps, inter-pole,
    the six walk events, the decoded λ-event); **no S3 summand**.
  |𝔽| (workloadEv P Λ) P.hostileIOWork N M` with
  `workloadEv P Λ = p8WorkEv N M Λ + formRUniformWorkload P.strategy + M·(2Λg − 1) + (2Λg − 1) + 1`,
  at every `(Qc, Qm)`, with no premise (rule 8(b)).  Read-set receipts: every new summand reads
  round-0 columns only (`reqPairEv_eq_at`, `rootResultEv` from the C2 join, `alphaZeroEvent` a coin
  set); the figures are in `Batch1040`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.P8EventEv
import Nock.NockVMROM.Thm54.P8Core.OptimizedFailureEventEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.OptimizedFailureEventEv

open scoped Polynomial BigOperators Classical
open Polynomial
open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## §A  The `α = 0` event on `JointCoins` -/

section AlphaZero

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end AlphaZero

/-! ## §B  The lifted summands at `P` -/

section AtP

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

theorem builtStrategyEv_skeleton : (builtStrategyEv P Qc Qm).skeleton = builtSkeletonEv P Qc Qm :=
  rfl

/-- **Read-set receipt**: the built pair event is the same at the family base envs of any tuple. -/
theorem reqPairEv_eq_at (c : OptimizedProductionChallengeTuple K F) :
    reqPairEv P Qc Qm =
      PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem (Λg P)
        (memoryEnvsR0 P.optimized Qm c) P.optimized.family.problem.cfg.memRows_pos
        (builtRequestTargets P Qc Qm) := by
  unfold reqPairEv PreSeedCensus.reqPairEventOfEnvs PreSeedCensus.reqPairsOfEnvs
  have hN := PreZComputeCore.Served.preZNounOfEnvs_congr K P.q P.optimized.family.problem.cfg.kMem
    (envs := P.memoryBaseEnv Qm) (envs' := memoryEnvsR0 P.optimized Qm c)
    (fun i col _ => by rw [memoryBaseEnv_trace P Qm c i]) P.optimized.family.problem.cfg.memRows_pos
  have hT := PreZComputeCore.Served.reqTgtOfEnvs_congr
    (envs := P.memoryBaseEnv Qm) (envs' := memoryEnvsR0 P.optimized Qm c)
    (fun i col _ => by rw [memoryBaseEnv_trace P Qm c i]) P.optimized.family.problem.cfg.memRows_pos
    (builtRequestTargets P Qc Qm)
  simp only [hN, hT]

/-- Outside the root-result event, when the built root's fingerprint equals the claimed result's
(both within the window), the two are one field-noun. -/
theorem rootResult_of_not_mem {ω : JointCoins K} (hout : ω ∉ rootResultEv P Qc Qm)
    (hΛ1 : (builtSkeletonEv P Qc Qm).publicClaim.result.leaves ≤ Λg P)
    (hΛ2 : P.optimized.verifier.raw.claim.result.leaves ≤ Λg P)
    (henc : GlobalCarryRecognizer.enc (nprSeed ω) (builtSkeletonEv P Qc Qm).publicClaim.result =
      GlobalCarryRecognizer.enc (nprSeed ω) P.optimized.verifier.raw.claim.result) :
    (NPR.leafF (K := K) (builtSkeletonEv P Qc Qm).publicClaim.result,
        NPR.dyckBits (K := K) (builtSkeletonEv P Qc Qm).publicClaim.result) =
      (NPR.leafF (K := K) P.optimized.verifier.raw.claim.result,
        NPR.dyckBits (K := K) P.optimized.verifier.raw.claim.result) := by
  have hz : nprSeed ω ∉ PreSeedCensus.pairBadSeeds (K := K) (Λg P)
      [((builtSkeletonEv P Qc Qm).publicClaim.result, P.optimized.verifier.raw.claim.result)] := by
    intro hmem
    exact hout (by rw [rootResultEv, mem_liftSeed_iff]; exact hmem)
  exact PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hz (by simp) hΛ1 hΛ2 henc


end AtP

end

end Nock.NockVMROM.Thm54.OptimizedFailureEventEv
