/-
  Nock/NockVMROM/Thm54/GenuineEvalN.lean

  **What an accepted proof certifies, upgraded from `evalFBy q` to `Nock.evalN`.**

  `ProductionP8Containment.GenuineWitness` (`ProductionP8Containment.lean:314`) carries two
  evaluator conclusions about the *public* claim nouns, and both are modular:

  * `evalFByPublic` (`ProductionP8Containment.lean:355`), and
  * `publicClaimHoldsMod` (`ProductionP8Containment.lean:358`), i.e.
    `P8PublicClaim.HoldsMod q` (`JointSoundness.lean:61`).

  `FieldEmbedding.evalFBy q` (`Nock/FieldEmbedding.lean:104`) is `Nock.evalN` verbatim except at
  OP_4, where it uses `lusFBy q`, the paper's modular increment `+(n) = (1+n) mod p`.  That is paper-faithful, not a defect; but a
  *soundness* consumer — "accepted and outside the failure event, therefore the claim is genuine" —
  then learns a statement about the modular evaluator, while `P8PublicClaim.Holds`
  (`JointSoundness.lean:56`) is the `Nock.evalN` statement.  The two evaluators genuinely differ:
  `Batch15Thm54ScopeGuards.b15_evalFBy_ne_evalN_at_top` exhibits a separating program.

  This module bridges the seam with the evaluator-level theorem that was already in the tree and
  unused on this path, `FieldEmbedding.noOverflow_agreeBy` (`Nock/FieldEmbedding.lean:603`), under
  one honest side condition:

  * `NoOverflowRun q subject formula` — the *guarded* evaluator `evalGBy q`, which crashes rather
    than wrapping at `q`, terminates on this program.  This says "the computation performs no
    modular reduction", and it does **not** name the result, so it cannot smuggle in the
    conclusion.
  * `FieldEmbedding.BoundedBy q subject` / `... formula` — the leaves of the public nouns are field
    elements.  This is the paper's own typing of a Nock program, not an extra restriction:
    the paper define a noun's leaves to be elements of `𝔽`, and Def[Nock Program]
    the paper requires `subject, formula ∈ 𝒩^λ(𝔽)`.

  Nothing existing is edited or weakened: every statement here is additive, and both modular
  fields of `GenuineWitness` stay exactly as they are.
-/
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.GenuineEvalN

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

/-! ## 1. The no-overflow side condition -/

/-- **The no-overflow side condition.**  The guarded evaluator `FieldEmbedding.evalGBy q`
(`Nock/FieldEmbedding.lean:180`) is `Nock.evalN` with an OP_4 that *crashes* instead of reducing
modulo `q`.  So a terminating guarded run is exactly the statement "this Nock computation never
wraps the field".

Note what this predicate does **not** say: it does not mention the claimed result.  Only the
existence of *some* guarded value is assumed; the identification of that value with the claim's
`result` is what the accepted proof contributes. -/
def NoOverflowRun (q : ℕ) (subject formula : Noun) : Prop :=
  ∃ (fuel : ℕ) (r : Noun), FieldEmbedding.evalGBy q fuel subject formula = some r

theorem noOverflowRun_of_guarded {q fuel : ℕ} {subject formula r : Noun}
    (h : FieldEmbedding.evalGBy q fuel subject formula = some r) :
    NoOverflowRun q subject formula :=
  ⟨fuel, r, h⟩

/-! ## 2. The evaluator bridge: `HoldsMod q` + no overflow ⟹ `Holds` -/

/-- **The bridge, at the level of the public claim.**

From the modular conclusion `claim.HoldsMod q` (`JointSoundness.lean:61`) — which is exactly what
an accepted, non-failing proof yields — plus the no-overflow side condition and the paper's field
typing of the public nouns, the claim is a genuine `Nock.evalN` conclusion, and the claimed result
is itself a field noun.

The argument is not circular: `NoOverflowRun` supplies *some* guarded value `r`,
`FieldEmbedding.noOverflow_agreeBy` (`Nock/FieldEmbedding.lean:603`) says that `r` is simultaneously
the `evalN` value and the `evalFBy q` value, and the accepted proof's `HoldsMod` is what forces
`r = claim.result` (via fuel padding, `GlobalOpcodeScheduling.evalFBy_mono`). -/
theorem holds_and_bounded_of_holdsMod {q : ℕ} (hq : 1 < q) (claim : P8PublicClaim)
    (hs : FieldEmbedding.BoundedBy q claim.subject)
    (hf : FieldEmbedding.BoundedBy q claim.formula)
    (hno : NoOverflowRun q claim.subject claim.formula)
    (hmod : claim.HoldsMod q) :
    claim.Holds ∧ FieldEmbedding.BoundedBy q claim.result := by
  obtain ⟨fuel₁, r, hg⟩ := hno
  obtain ⟨hN, hF, hB⟩ := FieldEmbedding.noOverflow_agreeBy hq hs hf hg
  obtain ⟨fuel₂, hF2⟩ := hmod
  have h1 := GlobalOpcodeScheduling.evalFBy_mono (Nat.le_max_left fuel₁ fuel₂) hF
  have h2 := GlobalOpcodeScheduling.evalFBy_mono (Nat.le_max_right fuel₁ fuel₂) hF2
  have hr : r = claim.result := Option.some.inj (h1.symm.trans h2)
  subst hr
  exact ⟨⟨fuel₁, hN⟩, hB⟩

/-- The `Nock.evalN` half of `holds_and_bounded_of_holdsMod`. -/
theorem holds_of_holdsMod {q : ℕ} (hq : 1 < q) (claim : P8PublicClaim)
    (hs : FieldEmbedding.BoundedBy q claim.subject)
    (hf : FieldEmbedding.BoundedBy q claim.formula)
    (hno : NoOverflowRun q claim.subject claim.formula)
    (hmod : claim.HoldsMod q) :
    claim.Holds :=
  (holds_and_bounded_of_holdsMod hq claim hs hf hno hmod).1

/-- Unfolded form: the accepted claim's result is the real Nock result. -/
theorem evalN_of_holdsMod {q : ℕ} (hq : 1 < q) (claim : P8PublicClaim)
    (hs : FieldEmbedding.BoundedBy q claim.subject)
    (hf : FieldEmbedding.BoundedBy q claim.formula)
    (hno : NoOverflowRun q claim.subject claim.formula)
    (hmod : claim.HoldsMod q) :
    ∃ fuel : ℕ, Nock.evalN fuel claim.subject claim.formula = some claim.result :=
  holds_of_holdsMod hq claim hs hf hno hmod

end

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]

noncomputable section

/-! ## 3. The `evalN` companion of `GenuineWitness` -/

omit [Fintype K] [DecidableEq K] in
/-- **`evalN` companion to `GenuineWitness`'s modular conclusion.**

`GenuineWitness` is untouched; this reads its existing `publicClaimHoldsMod` field
(`ProductionP8Containment.lean:358`) and upgrades it. -/
theorem holds_of_genuineWitness
    {T : ProductionStrategy F K} {q Λ : ℕ} {z : K} {hz : z ≠ 0} {α lmb : K}
    (W : GenuineWitness T q Λ z hz α lmb) (hq : 1 < q)
    (hs : FieldEmbedding.BoundedBy q T.verifier.raw.claim.subject)
    (hf : FieldEmbedding.BoundedBy q T.verifier.raw.claim.formula)
    (hno : NoOverflowRun q T.verifier.raw.claim.subject T.verifier.raw.claim.formula) :
    T.verifier.raw.claim.Holds :=
  holds_of_holdsMod hq _ hs hf hno W.publicClaimHoldsMod

omit [Fintype K] in
/-- **`evalN` companion to `GenuineTargetAt`.**  `GenuineTargetAt`
(`ProductionP8Containment.lean:368`) is `Nonempty (GenuineWitness …)` under a nonzero NPR seed. -/
theorem holds_of_genuineTargetAt
    {T : ProductionStrategy F K} {q Λ : ℕ} {ω : JointCoins K} {lmb : K}
    (hgen : GenuineTargetAt T q Λ ω lmb) (hq : 1 < q)
    (hs : FieldEmbedding.BoundedBy q T.verifier.raw.claim.subject)
    (hf : FieldEmbedding.BoundedBy q T.verifier.raw.claim.formula)
    (hno : NoOverflowRun q T.verifier.raw.claim.subject T.verifier.raw.claim.formula) :
    T.verifier.raw.claim.Holds := by
  by_cases hz : nprSeed ω ≠ 0
  · rw [GenuineTargetAt, dif_pos hz] at hgen
    exact holds_of_genuineWitness hgen.some hq hs hf hno
  · rw [GenuineTargetAt, dif_neg hz] at hgen
    exact hgen.elim

/-! ## 4. The soundness headline at the containment entry point

`ProductionP8Containment.accepted_outside_failureUnion` (`ProductionP8Containment.lean:598`) is the
soundness entry point: an accepting coin outside the five-class failure union yields
`GenuineTargetAt`.  This restates it with the `Nock.evalN` conclusion added, hypothesis list
verbatim plus the three side conditions of §1-2.  The `GenuineTargetAt` conjunct is retained, so
nothing the original theorem certified is lost. -/

set_option maxHeartbeats 800000 in
theorem accepted_outside_failureUnion_holds
    {Λ : ℕ}
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
    (hs : FieldEmbedding.BoundedBy q T.verifier.raw.claim.subject)
    (hf : FieldEmbedding.BoundedBy q T.verifier.raw.claim.formula)
    (hno : NoOverflowRun q T.verifier.raw.claim.subject T.verifier.raw.claim.formula)
    (hbinds : T.BindsAll)
    (ω : JointCoins K) (lmb : K)
    (hacc : T.Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion T C lmb)
    (hlam : ∀ (hz : nprSeed ω ≠ 0) i,
      ((T.verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    GenuineTargetAt T q Λ ω lmb ∧
      ∃ fuel : ℕ, Nock.evalN fuel T.verifier.raw.claim.subject
        T.verifier.raw.claim.formula = some T.verifier.raw.claim.result := by
  have hgen : GenuineTargetAt T q Λ ω lmb :=
    accepted_outside_failureUnion T C q hchar hq hqChar hcast hbound hcombined
      hop hKp hProgCap hMemCap hbinds ω lmb hacc hout hlam
  exact ⟨hgen, holds_of_genuineTargetAt hgen hq hs hf hno⟩

end

/-! ## 5. The soundness headline at the assembled package

`OptimizedFullStrictNockVMROMPackage.containment` (`OptimizedStrictFullPackage.lean:149`) is the
packaged form of §4: it discharges every structural hypothesis from the package's own fields, so
the only inputs left are acceptance, non-failure, and the three side conditions.  `1 < q` is the
package field `q_gt_one` (`OptimizedStrictFullPackage.lean:72`) and costs nothing. -/

variable [FiniteDimensional F K]

/-- The strategy's verifier is the package's verifier. -/
theorem package_strategy_verifier {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.strategy.verifier = P.optimized.verifier := rfl

/-- **Headline.**  An accepted coin outside the failure union certifies a genuine `Nock.evalN`
evaluation of the committed public claim, provided the committed program is a field-noun program whose evaluation performs no modular wrap.

Compare `P.containment`, which concludes only `GenuineTargetAt`, whose evaluator content is the
modular `HoldsMod P.q`. -/
theorem package_accepted_evalN {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) (ω : JointCoins K) (lmb : K)
    (hacc : P.strategy.Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census lmb)
    (hs : FieldEmbedding.BoundedBy P.q P.optimized.verifier.raw.claim.subject)
    (hf : FieldEmbedding.BoundedBy P.q P.optimized.verifier.raw.claim.formula)
    (hno : NoOverflowRun P.q P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula) :
    ∃ fuel : ℕ, Nock.evalN fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result :=
  holds_of_genuineTargetAt (P.containment ω lmb hacc hout) P.q_gt_one hs hf hno

/-- The packaged form keeping both conclusions: the original `GenuineTargetAt` and the upgraded
`Nock.evalN` statement. -/
theorem package_accepted_genuine_and_evalN {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) (ω : JointCoins K) (lmb : K)
    (hacc : P.strategy.Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census lmb)
    (hs : FieldEmbedding.BoundedBy P.q P.optimized.verifier.raw.claim.subject)
    (hf : FieldEmbedding.BoundedBy P.q P.optimized.verifier.raw.claim.formula)
    (hno : NoOverflowRun P.q P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula) :
    ProductionP8Containment.GenuineTargetAt P.strategy P.q P.optimized.Λ ω lmb ∧
      P.optimized.verifier.raw.claim.Holds :=
  ⟨P.containment ω lmb hacc hout,
    holds_of_genuineTargetAt (P.containment ω lmb hacc hout) P.q_gt_one hs hf hno⟩

end Nock.NockVMROM.Thm54.GenuineEvalN

#print axioms Nock.NockVMROM.Thm54.GenuineEvalN.holds_and_bounded_of_holdsMod
#print axioms Nock.NockVMROM.Thm54.GenuineEvalN.holds_of_genuineWitness
#print axioms Nock.NockVMROM.Thm54.GenuineEvalN.holds_of_genuineTargetAt
#print axioms Nock.NockVMROM.Thm54.GenuineEvalN.accepted_outside_failureUnion_holds
#print axioms Nock.NockVMROM.Thm54.GenuineEvalN.package_accepted_evalN
#print axioms Nock.NockVMROM.Thm54.GenuineEvalN.package_accepted_genuine_and_evalN
