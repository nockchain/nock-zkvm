/-
  Nock/NockVMROM/Thm54/StrictContainment.lean

  Packet 2 of the Theorem 5.4 north star: wiring the "hcast-free at the characteristic" fact
  (Packet 2A, `StrictRawReconstruction.charCast_injOn`) into the production false-acceptance
  containment bound.

  `ProductionP8Containment.production_jointProbability_falseAcceptance_le` already proves the
  false-acceptance probability bound, but it carries an explicit cast-injectivity premise
  `hcast : Set.InjOn (·:ℕ→K) (Iio q)`.  When the atom range is the field characteristic — exactly the
  canonical-field-noun choice fixed in Packet 0 — that premise is *free*.

  `production_falseAcceptance_le_at_char` is the same bound instantiated at `q = ringChar K` with the
  `hcast` premise discharged, so the caller supplies one fewer hypothesis.  This does not weaken the
  result: it fixes the honest canonical-residue bound and removes an assumption that Packet 2A proves.
-/

import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.StrictRawReconstruction

namespace Nock.NockVMROM.Thm54
namespace StrictContainment

open scoped Classical BigOperators
open Nock Nock.Walk
open Nock.AxisBridge AxisBatching.MTree
open SemanticTimestampStrategy
open TemplateRawJointSoundness
open TemplateAxisCounting
open ProductionAxisStructureVerifier
open SizeWindowCounting
open ProductionP8Containment

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]
variable {Λ : ℕ}

/-- **Production false-acceptance bound at the characteristic, with `hcast` discharged.**  Identical
to `production_jointProbability_falseAcceptance_le` at `q = ringChar K`, except the cast-injectivity
premise is supplied automatically by `StrictRawReconstruction.charCast_injOn` (Packet 2A). -/
theorem production_falseAcceptance_le_at_char
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (topologyBound axisWorkload : ℕ)
    (hchar : NodeEncoding.StateTagChar K)
    (hqchar : 1 < ringChar K)
    (hbound : T.skeleton.BoundedBy (ringChar K))
    (hcombined : FixedCombinedBoundedBy (ringChar K) T)
    (hop : ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.Ksz < ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (htopology : ∀ z (hz : z ≠ 0) α lmb,
      topologyWorkload
        (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis : ∀ z (hz : z ≠ 0),
      templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (hlam : ∀ ω (hz : nprSeed ω ≠ 0) i,
      ((T.verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.verifier.familyAt ω lmb hz).cfg.challenges.lam)
    (hbinds : T.BindsAll) :
    |jointProbability (FalseAcceptanceSet T (ringChar K) Λ lmb)| ≤
      (workload T Λ topologyBound axisWorkload : ℝ) / (Fintype.card K : ℝ) :=
  production_jointProbability_falseAcceptance_le h2 T lmb C (ringChar K) topologyBound axisWorkload
    hchar hqchar rfl (StrictRawReconstruction.charCast_injOn (ringChar K)) hbound hcombined
    hop hwindowBound hKp hProgCap hMemCap htopology haxis hlam hbinds

end

end StrictContainment
end Nock.NockVMROM.Thm54
