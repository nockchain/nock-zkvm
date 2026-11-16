import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.Thm54P7JointRegression
import Nock.RedTeam.SecondWave.RtMore
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper scope: the paper.  The positive receipts below establish one same-execution
`JointAssignment` carrying all six segmented families and `SharedIOSat`.  The negative controls
retain the old compute-only/vacuous `CompletenessModel` attacks but prove that they no longer
elaborate in the consumed S6 slot.

The established construction remains the segmented `102/44`, `e = 1` object.  It is deliberately
not identified with the paper's monolithic `199/196`, `e = 3` RAP pair.
-/

namespace Nock.RedTeam.Batch41

open scoped Classical
open Nock Nock.Framework Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictPackage
open Nock.RedTeam.Thm54P3Nonvacuity
open Nock.RedTeam.Thm54P7PlusIORegression
open Nock.RedTeam.Thm54NodeEncodingRegression

noncomputable section

abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17

/-! ## 1. Concrete ZMod-17 non-vacuity -/

/-- The concrete endpoint-specialized production family used by the ZMod-17 receipt. -/
abbrev endpointFamily (requests responses outMem : IOField K17) :
    PlusIOSegmentedFamily K17 K17 :=
  productionFamily.withIOEndpoints requests responses outMem

/-- Every substantive premise of the new S6 constructor is concretely inhabited on the committed
`ZMod 17` problem: chained semantics, the stronger semantic-IO witness, state-tag separation,
both active-prefix capacities, characteristic 17, and `Ksz < 17`. -/
theorem zmod17_new_S6_hypotheses_inhabited :
    ChainedSemanticExactLanguage productionFamily.problem.cfg productionFamily.problem.exec ∧
      Nonempty (SemanticIOWitness productionFamily.problem.cfg productionFamily.problem.exec) ∧
      NodeEncoding.StateTagChar K17 ∧
      productionFamily.problem.exec.derivedRequestIO.length + 1 ≤
        2 ^ productionFamily.problem.cfg.orbit.h ∧
      productionFamily.problem.exec.derivedResponseIO.length + 1 ≤
        2 ^ productionFamily.problem.cfg.orbit.h ∧
      CharP K17 17 ∧ productionFamily.problem.cfg.Ksz < 17 := by
  refine ⟨?_, ?_, production_stateTagChar, productionFamily.progIO_capacity,
    productionFamily.memIO_capacity, inferInstance, ?_⟩
  · change ChainedSemanticExactLanguage cfg exec
    exact production_chained
  · change Nonempty (SemanticIOWitness cfg exec)
    exact ⟨semanticWitness⟩
  · change cfg.Ksz < 17
    norm_num [cfg]

/-- A real `ZMod 17` execution inhabits one assignment containing all six RAP-family
satisfactions and the shared-IO proposition.  Every displayed family is indexed by the same
`endpointFamily requests responses outMem`, hence by the same dependent `cfg`/`exec`. -/
theorem zmod17_all_six_families_and_shared_io_nonvacuous :
    ∃ requests responses outMem : IOField K17,
      ∃ A : JointAssignment (endpointFamily requests responses outMem) 17,
        ((∀ kind, ((endpointFamily requests responses outMem).computeTableRAP kind).Satisfies
              A.sameExecution.computeTableTrace) ∧
          (∀ kind, ((endpointFamily requests responses outMem).memoryTableRAP kind).Satisfies
              A.sameExecution.memoryTableTrace) ∧
          (∀ kind, ((endpointFamily requests responses outMem).computeWalkRAP kind).Satisfies
              A.sameExecution.computeWalkTrace) ∧
          (∀ kind, ((endpointFamily requests responses outMem).memoryWalkRAP kind).Satisfies
              A.sameExecution.memoryWalkTrace) ∧
          (∀ kind, ((endpointFamily requests responses outMem).computeIORAP kind).Satisfies
              A.sameExecution.computeIOTrace) ∧
          (∀ kind, ((endpointFamily requests responses outMem).memoryIORAP kind).Satisfies
              A.sameExecution.memoryIOTrace)) ∧
        SharedIOSat (endpointFamily requests responses outMem) 17 ∧
        ChainedSemanticExactLanguage
          (endpointFamily requests responses outMem).problem.cfg
          (endpointFamily requests responses outMem).problem.exec ∧
        requests = responses ∧ outMem = 0 := by
  obtain ⟨requests, responses, outMem, A, hfamilies, hrequests, hout, hchained, -, -, -⟩ :=
    Nock.RedTeam.Thm54P7JointRegression.balanced_jointVerification_nonempty
  exact ⟨requests, responses, outMem, A, A.six_family_satisfaction,
    A.sharedIO, hchained, hrequests, hout⟩

/-! ## 2. Exact statement shape and same-object threading -/

/-- Unfolding the new claim exposes every constructor premise and their exact order:
`ChainedSemanticExactLanguage`, `SemanticIOWitness`, `StateTagChar`, three walk challenges,
both active-prefix capacities, `CharP`, `Ksz < p`, and the one joint conclusion. -/
theorem combinedCompletenessAt_exact_type
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    CombinedCompletenessAt cfg exec ↔
      ∀ (hchained : ChainedSemanticExactLanguage cfg exec)
        (_w : SemanticIOWitness cfg exec)
        (hchar : NodeEncoding.StateTagChar K)
        (computeWalkAlpha walkGamma memoryWalkAlpha : K)
        (progIO_capacity :
          exec.derivedRequestIO.length + 1 ≤ 2 ^ cfg.orbit.h)
        (memIO_capacity :
          exec.derivedResponseIO.length + 1 ≤ 2 ^ cfg.orbit.h)
        (p : ℕ) [CharP K p],
        cfg.Ksz < p →
          ∃ requests responses outMem : IOField K,
            JointVerificationProblem
              (PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
                (ExactCanonicalRAPProblem.ofChained hchained)
                hchar computeWalkAlpha walkGamma memoryWalkAlpha
                requests responses outMem progIO_capacity memIO_capacity) p :=
  Iff.rfl

/-- Independent replay of the production theorem: the exact universal claim specializes directly
to `jointVerification_complete_with_concreteNodeEncoders` with the same cfg/exec-dependent
problem, in the same argument order, and with no discarded premise. -/
theorem exact_claim_is_the_concrete_constructor
    (F K : Type) [Field F] [Field K] [Algebra F K] :
    ExactChainedHasPerfectCompleteness F K := by
  intro cfg exec hchained w hchar computeWalkAlpha walkGamma memoryWalkAlpha
    progIO_capacity memIO_capacity p _ hKp
  exact
    jointVerification_complete_with_concreteNodeEncoders
      (ExactCanonicalRAPProblem.ofChained hchained) hchar
      computeWalkAlpha walkGamma memoryWalkAlpha
      progIO_capacity memIO_capacity hchained w hKp

/-- The new claim yields one `JointAssignment`; opening that single object gives all six family
satisfactions and `SharedIOSat`, without independently re-quantifying any configuration or
execution. -/
theorem combined_claim_concludes_one_same_execution_assignment
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (claim : CombinedCompletenessAt cfg exec)
    (hchained : ChainedSemanticExactLanguage cfg exec)
    (w : SemanticIOWitness cfg exec)
    (hchar : NodeEncoding.StateTagChar K)
    (computeWalkAlpha walkGamma memoryWalkAlpha : K)
    (progIO_capacity : exec.derivedRequestIO.length + 1 ≤ 2 ^ cfg.orbit.h)
    (memIO_capacity : exec.derivedResponseIO.length + 1 ≤ 2 ^ cfg.orbit.h)
    (p : ℕ) [CharP K p] (hKp : cfg.Ksz < p) :
    ∃ requests responses outMem : IOField K,
      ∃ A : JointAssignment
          (PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
            (ExactCanonicalRAPProblem.ofChained hchained)
            hchar computeWalkAlpha walkGamma memoryWalkAlpha
            requests responses outMem progIO_capacity memIO_capacity) p,
        A.sameExecution.Satisfies ∧
          SharedIOSat
            (PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
              (ExactCanonicalRAPProblem.ofChained hchained)
              hchar computeWalkAlpha walkGamma memoryWalkAlpha
              requests responses outMem progIO_capacity memIO_capacity) p := by
  obtain ⟨requests, responses, outMem, ⟨A⟩⟩ :=
    claim hchained w hchar computeWalkAlpha walkGamma memoryWalkAlpha
      progIO_capacity memIO_capacity p hKp
  exact ⟨requests, responses, outMem, A, A.sixFamilies, A.sharedIO⟩

/-! ## 3. Consumed-capstone pinning and negative controls -/

instance batch41_prime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
abbrev Z7 := ZMod 7
abbrev T7 := Tag Z7 Z7 0 1 1

local instance : CharP Z7 (ringChar Z7) := ringChar.charP Z7

/-- Generic framework control: an explicitly different S6 proposition can still build an
explicitly different bundle.  This is expected; the attack below checks that it cannot inhabit
the real consumed capstone type. -/
@[reducible] noncomputable def alternateS6Bundle (C : Prop) (c : C) :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness Z7 Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness Z7 Z7)
      (ExactSegmentedCostVerification Z7 Z7)
      (exactSegmentedCostVerification Z7 Z7)
      C c
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

/-- A deliberately independently-quantified cfg/exec placeholder, retained solely as a negative
control.  It is inhabited but is not the dependent same-execution S6 proposition. -/
def IndependentCfgExecClaim : Prop :=
  ∀ (cfg₁ cfg₂ : ExactConfig Z7 Z7)
    (_exec₁ : ExactExecution cfg₁) (_exec₂ : ExactExecution cfg₂), True

theorem independentCfgExecClaim_inhabited : IndependentCfgExecClaim :=
  fun _ _ _ _ => trivial

abbrev LegacyComputeOnlyClaim : Prop :=
  HasPerfectCompleteness T7 (nmrMEF Z7 Z7) Z7
    (nockCompletenessModel Z7 Z7 0 1 1)

@[reducible] noncomputable def legacyComputeOnlyClaim_inhabited : LegacyComputeOnlyClaim :=
  nock_hasPerfectCompleteness Z7 Z7 0 1 1

/-- Only the exact universal same-execution claim fits. -/
theorem real_capstone_rejects_weaker_S6_substitutions :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness Z7 Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness Z7 Z7)
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
  fail_if_success exact alternateS6Bundle True trivial
  fail_if_success
    exact alternateS6Bundle IndependentCfgExecClaim independentCfgExecClaim_inhabited
  fail_if_success
    exact alternateS6Bundle LegacyComputeOnlyClaim legacyComputeOnlyClaim_inhabited
  exact NockVMROM_Thm54_structural Z7 Z7 0 1 1

structure OtherVM : Type

instance otherVMSystem : VMSystem OtherVM where
  Statement := Unit
  Witness := Unit
  accepts := fun _ _ => False

theorem legacy_G9_transport_still_compiles :
    Nonempty (CompletenessModel.{0, 0, 0, 0, 0} OtherVM (nmrMEF Z7 Z7) Z7) :=
  ⟨RTMore.n11_comp_transport.{0, 0, 0, 0, 0}
    (ι₁ := T7) (ι₂ := OtherVM)
    (M₁ := nmrMEF Z7 Z7) (M₂ := nmrMEF Z7 Z7)
    (F₁ := Z7) (F₂ := Z7)
    (nockCompletenessModel Z7 Z7 0 1 1)⟩

/-- This closes only S6's slice of G9. -/
theorem new_S6_slot_rejects_legacy_G9_transport :
    ExactChainedHasPerfectCompleteness Z7 Z7 := by
  fail_if_success
    exact RTMore.n11_comp_transport.{0, 0, 0, 0, 0}
      (ι₁ := T7) (ι₂ := T7)
      (M₁ := nmrMEF Z7 Z7) (M₂ := nmrMEF Z7 Z7)
      (F₁ := Z7) (F₂ := Z7)
      (nockCompletenessModel Z7 Z7 0 1 1)
  fail_if_success
    exact RTMore.n9_vacuous_completeness T7 (nmrMEF Z7 Z7) Z7 Unit
  exact exactChainedHasPerfectCompleteness Z7 Z7

/-- The conditional strict package consumes `CombinedCompletenessAt` on its own shared dependent
configuration/execution. -/
theorem strict_package_structural_pins_exact_S6
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, ProductionP8Containment.FixedFieldSoundnessClaim P.strategy q Λ lmb)
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
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩ :=
  P.structural

/-- The statement wrapper preserves that exact structural field unchanged. -/
theorem strict_statement_structural_pins_exact_S6
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} {P : StrictNockVMROMPackage F K hOrb q Λ}
    (S : StrictThm54Statement P) :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, ProductionP8Containment.FixedFieldSoundnessClaim P.strategy q Λ lmb)
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
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩ :=
  S.structural

/-! ## 4. Wrong-layer guard -/

/-- The concrete S6 witness is exactly the segmented `102/44`, `e = 1` object and is numerically
distinct from the monolithic `199/196`, `e = 3` R6/G10 target. -/
theorem segmented_S6_is_not_monolithic_R6_G10 :
    Fintype.card ComputePlusIOColumn = 102 ∧
      Fintype.card MemoryPlusIOColumn = 45 ∧
      Fintype.card ComputePlusIOColumn < 199 ∧
      Fintype.card MemoryPlusIOColumn < 196 ∧
      productionFamily.problem.cfg.eDeg = 1 ∧
      productionFamily.problem.cfg.eDeg ≠ 3 :=
  productionFamily.one_to_one_star_scope

theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end

end Nock.RedTeam.Batch41

#print axioms Nock.RedTeam.Batch41.zmod17_all_six_families_and_shared_io_nonvacuous
#print axioms Nock.RedTeam.Batch41.zmod17_new_S6_hypotheses_inhabited
#print axioms Nock.RedTeam.Batch41.combinedCompletenessAt_exact_type
#print axioms Nock.RedTeam.Batch41.exact_claim_is_the_concrete_constructor
#print axioms Nock.RedTeam.Batch41.combined_claim_concludes_one_same_execution_assignment
#print axioms Nock.RedTeam.Batch41.real_capstone_rejects_weaker_S6_substitutions
#print axioms Nock.RedTeam.Batch41.legacy_G9_transport_still_compiles
#print axioms Nock.RedTeam.Batch41.new_S6_slot_rejects_legacy_G9_transport
#print axioms Nock.RedTeam.Batch41.strict_package_structural_pins_exact_S6
#print axioms Nock.RedTeam.Batch41.strict_statement_structural_pins_exact_S6
#print axioms Nock.RedTeam.Batch41.segmented_S6_is_not_monolithic_R6_G10
#print axioms Nock.RedTeam.Batch41.paper_alias_remains_forest
#print axioms Nock.NockVMROM.Thm54.exactChainedHasPerfectCompleteness
#print axioms Nock.NockVMROM.NockVMROM_Thm54_structural
