/-
  Nock/RedTeam/Batch43Thm54ExactFixedFieldSoundness.lean

  Paper frame:
  * collision arithmetic and concrete examples: the paper
  * assembled NockVMROM and Theorem 5.4 soundness: the paper
  * consumed theorem and efficiency statement: the paper.

  Scope is narrow.  The Layer-1 capstone consumes the universal
  `ExactProductionFixedFieldSoundness F K`; strict package consumers instead consume
  `FixedFieldSoundnessClaim P.strategy q Λ` and its exact proof.  The old
  `ConcreteSoundnessModel` / `HasConcreteSoundness` API remains a positive diagnostic control but
  is rejected from both consumed S7 slots.

  No concrete inhabitant of `StrictNockVMROMPackage` or of the full production-strategy/census/
  containment package is claimed here.  The fixed-field theorem is an honest universal implication:
  it fires for real strategy data once the same strategy's census, noun-size premise, and same-event
  containment are supplied.
-/

import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.Batch34Thm54FixedFieldD2
import Nock.RedTeam.SecondWave.RtMore

namespace Nock.RedTeam.Batch43

open scoped Classical
open Nock Nock.Walk Nock.Framework Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

/-! ## 1. Exact type expansion: one strategy, event, census, workload, and field -/

/-- Definitional expansion of the exact universal S7 proposition.  The same `T`, `q`, and `Λ`
occur in the census index, containment target, false-acceptance event, and conclusion. -/
theorem exactProductionFixedFieldSoundness_exact_shape
    (F K : Type) [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] :
    ExactProductionFixedFieldSoundness F K ↔
      ∀ (Λ q : ℕ) (T : ProductionStrategy F K)
        (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ),
        (2 : K) ≠ 0 →
        SizeWindowNounsBoundedBy T.skeleton Λ →
        ∀ lmb : K,
        (∀ ω, T.Accepts ω lmb → ω ∉ FailureUnion T C lmb →
          GenuineTargetAt T q Λ ω lmb) →
        |jointProbability (FalseAcceptanceSet T q Λ lmb)| ≤
          (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) : ℝ) /
            (Fintype.card K : ℝ) :=
  Iff.rfl

/-- Definitional expansion of the fixed-strategy conclusion.  There is no independently chosen
event or workload hidden behind `FixedFieldSoundnessClaim`. -/
theorem fixedFieldSoundnessClaim_exact_shape
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (T : ProductionStrategy F K) (q Λ : ℕ) (lmb : K) :
    FixedFieldSoundnessClaim T q Λ lmb ↔
      |jointProbability (FalseAcceptanceSet T q Λ lmb)| ≤
        (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) : ℝ) /
          (Fintype.card K : ℝ) :=
  Iff.rfl

/-- The production theorem can be applied only with the census and containment indexed by the
same strategy and the same `q`/`Λ` as its conclusion. -/
theorem exact_universal_threads_same_objects
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (Λ q : ℕ) (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (h2 : (2 : K) ≠ 0)
    (hwindow : SizeWindowNounsBoundedBy T.skeleton Λ) (lmb : K)
    (hcontain : ∀ ω, T.Accepts ω lmb → ω ∉ FailureUnion T C lmb →
      GenuineTargetAt T q Λ ω lmb) :
    FixedFieldSoundnessClaim T q Λ lmb :=
  exactProductionFixedFieldSoundness F K Λ q T C h2 hwindow lmb hcontain

/-- Membership in the counted union expands to exactly the five advertised classes. -/
theorem failureUnion_has_exactly_five_classes
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (ω : JointCoins K) (lmb : K) :
    ω ∈ ProductionP8Containment.FailureUnion T C lmb ↔
      ω ∈ zeroSeedFailureEvent ∨
      ω ∈ collisionFailureEvent C.census ∨
      ω ∈ specializedTopologyFailureEvent T.verifier.raw lmb ∨
      ω ∈ guardedAxisFailureEvent T lmb ∨
      ω ∈ SizeWindowFailure T.skeleton := by
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union]
  tauto

/-! ## 2. Feasibility and honest conditionality -/

instance batch43_prime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩
abbrev K17 := ZMod 17
local instance : CharP K17 (ringChar K17) := ringChar.charP K17

theorem zmod17_size_window_premise_nonvacuous :
    Fintype.card K17 = 17 ∧
      skeletonSizeWindowNouns Batch34.windowSkeleton =
        [.cell (.atom 0) (.atom 0)] ∧
      SizeWindowNounsBoundedBy Batch34.windowSkeleton 2 := by
  refine ⟨by norm_num [K17], ?_⟩
  exact Batch34.b34_sizeWindowBound_nonvacuous

/-- On the real finite field `ZMod 17`, both canonical majorants cover every specialization, the
full five-class workload is positive, and the denominator is the actual field cardinality. -/
theorem zmod17_canonical_majorants_are_genuine
    (T : ProductionStrategy K17 K17)
    (z : K17) (hz : z ≠ 0) (α lmb : K17) (Λ : ℕ) :
    topologyWorkload
          (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤
        fixedTopologyWorkload T ∧
      TemplateAxisCounting.templateAxisWorkload
          (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) ≤
        fixedAxisWorkload T ∧
      0 < workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) ∧
      Fintype.card K17 = 17 := by
  refine ⟨topologyWorkload_le_fixedTopologyWorkload T z hz α lmb,
    templateAxisWorkload_le_fixedAxisWorkload T z hz, ?_, by norm_num [K17]⟩
  unfold workload
  omega

/-- Honest real-field instantiation of the universal theorem.  Strategy, census, noun-size, and
same-event containment remain explicit inputs; no unconditional package inhabitant is fabricated. -/
theorem zmod17_exact_theorem_fires_on_supplied_strategy
    (Λ q : ℕ) (T : ProductionStrategy K17 K17)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K17 T.skeleton Λ)
    (hwindow : SizeWindowNounsBoundedBy T.skeleton Λ) (lmb : K17)
    (hcontain : ∀ ω, T.Accepts ω lmb → ω ∉ FailureUnion T C lmb →
      GenuineTargetAt T q Λ ω lmb) :
    FixedFieldSoundnessClaim T q Λ lmb :=
  exactProductionFixedFieldSoundness K17 K17 Λ q T C
    (by decide) hwindow lmb hcontain

/-- The strict capstone is conditional on a genuine package: an inhabitant necessarily projects
the Nock slot-semantics, exact row-count balance, semantic-template, and size-window residuals. -/
theorem strict_package_remains_conditional
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (h : Nonempty (StrictNockVMROMPackage F K hOrb q Λ)) :
    ∃ (C : SkeletonCommitment) (cfg : ExactConfig F K) (exec : ExactExecution cfg)
      (Lc Lm : Nock.Reified.Env K → Prop),
      (∀ s ∈ computeSkeletonRows C.skeleton,
          ServedLookupBridge.SkeletonSlotSemantics s) ∧
      RowLayout.RecordCountBalanced exec ∧
      Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (MonolithicRAP.compTemplate F) Lc ∧
      Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (MonolithicRAP.memTemplate F) Lm ∧
      SizeWindowNounsBoundedBy C.skeleton Λ :=
  package_nonempty_only_under_residuals h

/-! ## 3. -/

instance batch43_prime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
abbrev Z7 := ZMod 7
abbrev T7 := Tag Z7 Z7 0 1 1
local instance : CharP Z7 (ringChar Z7) := ringChar.charP Z7

/-- A deliberately unrelated empty event; it is true but is not the production S7 proposition. -/
def WrongEventSoundness : Prop :=
  |jointProbability (∅ : Finset (JointCoins Z7))| ≤ 0

theorem wrongEventSoundness_inhabited : WrongEventSoundness := by
  simp [WrongEventSoundness, jointProbability]

/-- A deliberately independently quantified strategy/event/workload proposition. -/
def IndependentlyQuantifiedSoundness : Prop :=
  ∀ (_T : ProductionStrategy Z7 Z7) (_E : Finset (JointCoins Z7)) (_W : ℕ), True

theorem independentlyQuantifiedSoundness_inhabited : IndependentlyQuantifiedSoundness :=
  fun _ _ _ => trivial

/-- The former walk-only S7 proposition remains available as a positive diagnostic control. -/
abbrev LegacyWalkOnlyS7 : Prop :=
  HasConcreteSoundness T7
    (nockConcreteSoundness.{0, 1, 0, 0} Z7 Z7 0 1 1)

abbrev TransportedLegacyS7 : Prop :=
  HasConcreteSoundness T7
    (RTMore.n11_sound_transport (ι₂ := T7)
      (nockConcreteSoundness.{0, 1, 0, 0} Z7 Z7 0 1 1))

theorem legacy_controls_still_compile :
    LegacyWalkOnlyS7 ∧ TransportedLegacyS7 ∧
      HasConcreteSoundness T7
        ⟨Unit, fun _ => 1, fun _ => 1⟩ :=
  ⟨nock_hasConcreteSoundness Z7 Z7 0 1 1,
    RTMore.n11_nock_sound_model_on_other_vm T7,
    RTMore.n8_soundness_error_one T7⟩

/-- Change only the Layer-1 S7 parameter, keeping every other real capstone object fixed. -/
@[reducible] noncomputable def alternateLayerS7 (C : Prop) (c : C) :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      C c
      (ExactSegmentedCostVerification Z7 Z7)
      (exactSegmentedCostVerification Z7 Z7)
      (ExactChainedHasPerfectCompleteness Z7 Z7)
      (exactChainedHasPerfectCompleteness Z7 Z7)
      (ExactTwoRAPVerification Z7 Z7)
      (exactTwoRAPVerification Z7 Z7)
      (nock_uniqueMES Z7 Z7 0 1 1)
      (ExactChainedHasCanonicalRAP2 Z7 Z7)
      (exactChainedHasCanonicalRAP2 Z7 Z7)
      (ExactChainedOneHot Z7 Z7)
      (exactChainedOneHot Z7 Z7)
      (ExactDefTraversable Z7 Z7)
      (exactDefTraversable Z7 Z7)
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

/-- `True`, the walk-only class, G7's unit-error model, G9 transport, wrong events/workloads, and
the old model object itself all fail in the real S7 slot.  The genuine exact capstone compiles. -/
theorem layer1_rejects_all_legacy_and_wrong_S7_substitutions :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (ExactProductionFixedFieldSoundness Z7 Z7)
      (exactProductionFixedFieldSoundness Z7 Z7)
      (ExactSegmentedCostVerification Z7 Z7)
      (exactSegmentedCostVerification Z7 Z7)
      (ExactChainedHasPerfectCompleteness Z7 Z7)
      (exactChainedHasPerfectCompleteness Z7 Z7)
      (ExactTwoRAPVerification Z7 Z7)
      (exactTwoRAPVerification Z7 Z7)
      (nock_uniqueMES Z7 Z7 0 1 1)
      (ExactChainedHasCanonicalRAP2 Z7 Z7)
      (exactChainedHasCanonicalRAP2 Z7 Z7)
      (ExactChainedOneHot Z7 Z7)
      (exactChainedOneHot Z7 Z7)
      (ExactDefTraversable Z7 Z7)
      (exactDefTraversable Z7 Z7)
      (nock_languageInhabited Z7 Z7 0 1 1) := by
  fail_if_success exact alternateLayerS7 True trivial
  fail_if_success
    exact alternateLayerS7 LegacyWalkOnlyS7
      (nock_hasConcreteSoundness Z7 Z7 0 1 1)
  fail_if_success
    exact alternateLayerS7 TransportedLegacyS7
      (RTMore.n11_nock_sound_model_on_other_vm T7)
  fail_if_success
    exact alternateLayerS7
      (HasConcreteSoundness T7 ⟨Unit, fun _ => 1, fun _ => 1⟩)
      (RTMore.n8_soundness_error_one T7)
  fail_if_success exact alternateLayerS7 WrongEventSoundness wrongEventSoundness_inhabited
  fail_if_success
    exact alternateLayerS7 IndependentlyQuantifiedSoundness
      independentlyQuantifiedSoundness_inhabited
  fail_if_success
    exact alternateLayerS7
      (nockConcreteSoundness Z7 Z7 0 1 1)
      (nock_hasConcreteSoundness Z7 Z7 0 1 1)
  exact NockVMROM_Thm54_structural Z7 Z7 0 1 1

/-! ## 4. Strict consumers: exact package strategy, `q`, `Λ`, event, and sibling proof -/

/-- The exact strict structural type, named once so both strict consumers can be compared without
weakening or independently quantifying any S7 object. -/
abbrev StrictS7StructuralType
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) : Prop :=
  VerifiableVMCompilation
    (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
    (nmrMEF F K) K 10 3
    (∀ lmb : K, FixedFieldSoundnessClaim P.strategy q Λ lmb)
    P.fixedField_falseAcceptance_le
    (StrictCostRealization P)
    P.strictCostRealization
    (CombinedCompletenessAt P.objects.cfg P.objects.exec)
    (exactChainedHasPerfectCompleteness F K P.objects.cfg P.objects.exec)
    (StrictTwoRAPRealization P)
    P.strictTwoRAPRealization
    (nock_uniqueMES F K _ _ _)
    (ExactChainedHasCanonicalRAP2 F K)
    (exactChainedHasCanonicalRAP2 F K)
    (OneHotRealization P.objects.cfg P.objects.exec)
    P.chained.oneHotRealization
    (DefTraversableRealization P.objects.cfg)
    (defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos)
    ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩

/-- Both strict structural consumers have literally the same S7-indexed type, and the sibling
field projects the same fixed-field proposition. -/
theorem strict_consumers_and_sibling_thread_same_S7
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictS7StructuralType P ∧
      StrictS7StructuralType P ∧
      (∀ lmb : K, FixedFieldSoundnessClaim P.strategy q Λ lmb) :=
  ⟨P.structural, (strictNockVMROM_of_package P).structural,
    (strictNockVMROM_of_package P).fixed_field_soundness⟩

/-- Change only strict S7 while retaining all other package-indexed strict objects. -/
@[reducible] noncomputable def alternateStrictS7
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ)
    (C : Prop) (c : C) :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3 C c
      (StrictCostRealization P)
      P.strictCostRealization
      (CombinedCompletenessAt P.objects.cfg P.objects.exec)
      (exactChainedHasPerfectCompleteness F K P.objects.cfg P.objects.exec)
      (StrictTwoRAPRealization P)
      P.strictTwoRAPRealization
      (nock_uniqueMES F K _ _ _)
      (ExactChainedHasCanonicalRAP2 F K)
      (exactChainedHasCanonicalRAP2 F K)
      (OneHotRealization P.objects.cfg P.objects.exec)
      P.chained.oneHotRealization
      (DefTraversableRealization P.objects.cfg)
      (defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos)
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩ :=
  ⟨⟩

/-- Wrong strategy, wrong `q`, and wrong `Λ` propositions elaborate at their own types but cannot
replace `FixedFieldSoundnessClaim P.strategy q Λ` in the strict structural slot. -/
theorem strict_consumer_rejects_wrong_strategy_q_and_Lambda
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ)
    (U : ProductionStrategy F K) (q' Λ' : ℕ)
    (_hU : ∀ lmb : K, FixedFieldSoundnessClaim U q Λ lmb)
    (_hq : ∀ lmb : K, FixedFieldSoundnessClaim P.strategy q' Λ lmb)
    (_hΛ : ∀ lmb : K, FixedFieldSoundnessClaim P.strategy q Λ' lmb) :
    StrictS7StructuralType P := by
  fail_if_success
    exact alternateStrictS7 P (∀ lmb : K, FixedFieldSoundnessClaim U q Λ lmb) _hU
  fail_if_success
    exact alternateStrictS7 P (∀ lmb : K, FixedFieldSoundnessClaim P.strategy q' Λ lmb) _hq
  fail_if_success
    exact alternateStrictS7 P (∀ lmb : K, FixedFieldSoundnessClaim P.strategy q Λ' lmb) _hΛ
  exact P.structural

/-- The strict sibling bit theorem uses exactly the same event and full workload and requires the
explicit support inequality. -/
theorem strict_bits_same_event_and_requires_support
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ)
    (lmb : K) (b : ℕ)
    (hsupport :
      workload P.strategy Λ (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) *
          2 ^ b ≤ Fintype.card K) :
    |jointProbability (FalseAcceptanceSet P.strategy q Λ lmb)| ≤ 1 / 2 ^ b :=
  (strictNockVMROM_of_package P).fixed_field_bits lmb b hsupport

/-- No unconditional `120`-bit theorem is available from the strict package: omitting the full
workload support premise fails elaboration. -/
theorem strict_does_not_smuggle_unconditional_120_bits
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (_P : StrictNockVMROMPackage F K hOrb q Λ) : True := by
  fail_if_success
    exact (strictNockVMROM_of_package _P).fixed_field_bits 120
  trivial

/-! ## 5. F8 boundary: fixed field, varying family, and collision-only results stay separate -/

/-- Fixed-field exact production signature. -/
abbrev fixed_field_signature := @exactProductionFixedFieldSoundness

/-- Standalone varying-family signature; it is not a field or consequence of the fixed-field
strict package without its own family hypotheses. -/
abbrev varying_family_signature :=
  @StrictAsymptoticSecurity.strict_asymptotic_soundness_of_strategyData

theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end

end Nock.RedTeam.Batch43

#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness
#print axioms Nock.NockVMROM.NockVMROM_Thm54_structural
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.fixedField_falseAcceptance_le
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.fixedField_falseAcceptance_le_two_pow_neg
#print axioms Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package

#print axioms Nock.RedTeam.Batch43.exactProductionFixedFieldSoundness_exact_shape
#print axioms Nock.RedTeam.Batch43.fixedFieldSoundnessClaim_exact_shape
#print axioms Nock.RedTeam.Batch43.exact_universal_threads_same_objects
#print axioms Nock.RedTeam.Batch43.failureUnion_has_exactly_five_classes
#print axioms Nock.RedTeam.Batch43.zmod17_size_window_premise_nonvacuous
#print axioms Nock.RedTeam.Batch43.zmod17_canonical_majorants_are_genuine
#print axioms Nock.RedTeam.Batch43.zmod17_exact_theorem_fires_on_supplied_strategy
#print axioms Nock.RedTeam.Batch43.strict_package_remains_conditional
#print axioms Nock.RedTeam.Batch43.legacy_controls_still_compile
#print axioms Nock.RedTeam.Batch43.layer1_rejects_all_legacy_and_wrong_S7_substitutions
#print axioms Nock.RedTeam.Batch43.strict_consumers_and_sibling_thread_same_S7
#print axioms Nock.RedTeam.Batch43.strict_consumer_rejects_wrong_strategy_q_and_Lambda
#print axioms Nock.RedTeam.Batch43.strict_bits_same_event_and_requires_support
#print axioms Nock.RedTeam.Batch43.strict_does_not_smuggle_unconditional_120_bits
#print axioms Nock.RedTeam.Batch43.fixed_field_signature
#print axioms Nock.RedTeam.Batch43.varying_family_signature
#print axioms Nock.RedTeam.Batch43.paper_alias_remains_forest

#check @Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocks_concrete_falseAcceptance_le_two_pow_neg_120
