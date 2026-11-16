/-
  Nock/RedTeam/Batch362Thm54SemanticSupportAt.lean

  **`SemanticSupportAt`.**  Seed-local semantic support:
  `binds` only at `nprSeed ω`.  Positive control `ofBare`; converse control
  the original spine as a corollary of the restatement.

  The seed-local binding is now the
  predicate `ProductionStrategy.BindsAtCoin T ω λ`; the honest map is
  `ProductionStrategy.ofBare : BareSemanticSupport F K V → ProductionStrategy F K`.  Same three
  theorem names, restated on those objects.

  Paper: the paper (`Thm:NockVMROM`), `:1413` (timestamps / unique
  request), `:1188-1204` (`fn` / seed).  Lean:
  `` `ProductionP8Containment.lean::ProductionStrategy.BindsAtCoin` ``,
  `` `::ProductionStrategy.ofBare` ``,
  `` `::accepted_outside_failureUnion_at` ``,
  `` `::accepted_outside_failureUnion` ``.
-/
import Nock.NockVMROM.Thm54.ProductionP8Containment

namespace Nock.RedTeam.Batch362

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]
variable {Λ : ℕ}

/-! ## Positive control: `ofBare` specialises `∀ z` to the sampled seed -/

theorem ofBare_skeleton_eq
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (sem : BareSemanticSupport F K V) :
    (ProductionStrategy.ofBare sem).skeleton = sem.skeleton :=
  ProductionStrategy.ofBare_skeleton sem

theorem ofBare_publicClaim
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (sem : BareSemanticSupport F K V) :
    (ProductionStrategy.ofBare sem).publicClaim_eq = sem.publicClaim_eq :=
  rfl

/-- The honest seed-local binding is exactly `sem.binds` at `nprSeed ω` / `alphaM ω`. -/
theorem ofBare_binds_at_sampled
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (sem : BareSemanticSupport F K V) (ω : JointCoins K) (lmb : K)
    (hz : nprSeed ω ≠ 0) :
    ProductionStrategy.honestBinds sem ω lmb hz =
      sem.binds (nprSeed ω) hz (alphaM ω) lmb :=
  rfl

/-! ## Converse control: the `BindsAll` spine via `atCoin` -/

/-- The `BindsAll` statement is the seed-local restatement at `hbinds.atCoin ω lmb`. -/
theorem original_is_ofBare_specialisation
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (q : ℕ)
    (hchar : NodeEncoding.StateTagChar K)
    (hq : 1 < q)
    (hqChar : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : T.skeleton.BoundedBy q)
    (hcombined : FixedCombinedBoundedBy q T)
    (hop : ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.Ksz <
        ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hbinds : T.BindsAll)
    (ω : JointCoins K) (lmb : K)
    (hacc : T.Accepts ω lmb)
    (hout : ω ∉ FailureUnion T C lmb)
    (hlam : ∀ (hz : nprSeed ω ≠ 0) i,
      ((T.verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda =
        (T.verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    accepted_outside_failureUnion T C q hchar hq hqChar hcast hbound
        hcombined hop hKp hProgCap hMemCap hbinds ω lmb hacc hout hlam =
      accepted_outside_failureUnion_at T C q hchar hq hqChar hcast hbound
        hcombined hop hKp hProgCap hMemCap ω
        lmb (hbinds.atCoin ω lmb) hacc hout hlam :=
  rfl

end

end Nock.RedTeam.Batch362

#print axioms Nock.RedTeam.Batch362.ofBare_skeleton_eq
#print axioms Nock.RedTeam.Batch362.ofBare_binds_at_sampled
#print axioms Nock.RedTeam.Batch362.original_is_ofBare_specialisation
