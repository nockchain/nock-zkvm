import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.Thm54P7JointRegression
import Nock.RedTeam.SecondWave.AtkPackage
import Nock.RedTeam.SecondWave.RtEasy
import Nock.RedTeam.SecondWave.RtMore
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
The Layer-1 capstone consumes the segmented `102/44`, `e = 1`
`ExactTwoRAPVerification` projection.  This batch checks both
surfaces but deliberately does not identify them; that R6/G10 semantic identity remains open.
-/

namespace Nock.RedTeam.Batch42

open scoped Classical
open Nock Nock.Framework Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.RedTeam.Thm54P3Nonvacuity
open Nock.RedTeam.Thm54P7PlusIORegression
open Nock.RedTeam.Thm54NodeEncodingRegression

noncomputable section

abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17

/-! ## 1. Concrete `ZMod 17` non-vacuity and exact S5 projection -/

abbrev endpointFamily (requests responses outMem : IOField K17) :
    PlusIOSegmentedFamily K17 K17 :=
  productionFamily.withIOEndpoints requests responses outMem

/-- A concrete accepted `JointVerificationProblem` is projected through the new S5 theorem.
Opening the projected realization gives one `JointAssignment` carrying all six satisfaction
families, `SharedIOSat` on the same family, and the public endpoint equalities. -/
theorem zmod17_joint_problem_and_exact_S5_nonvacuous :
    ∃ requests responses outMem : IOField K17,
      JointVerificationProblem (endpointFamily requests responses outMem) 17 ∧
      TwoRAPRealization (endpointFamily requests responses outMem) 17 ∧
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
        (endpointFamily requests responses outMem).requests =
          (endpointFamily requests responses outMem).responses ∧
        (endpointFamily requests responses outMem).outMem = 0 := by
  obtain ⟨requests, responses, outMem, A, -, -, -, -, -, -, -⟩ :=
    Nock.RedTeam.Thm54P7JointRegression.balanced_jointVerification_nonempty
  let R := endpointFamily requests responses outMem
  have hproblem : JointVerificationProblem R 17 := ⟨A⟩
  have hrealization : TwoRAPRealization R 17 :=
    exactTwoRAPVerification K17 K17 R 17 hproblem
  obtain ⟨A', hsix, hio, hendpoints⟩ := hrealization
  refine ⟨requests, responses, outMem, hproblem, ?_, A',
    A'.six_family_satisfaction, hio, hendpoints.1, hendpoints.2⟩
  exact ⟨A', hsix, hio, hendpoints⟩

/-! ## 2. Exact statement shape and anti-bundling controls -/

/-- The realization is definitionally one witness on one fixed `R` and `p`. -/
theorem twoRAPRealization_exact_shape
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (R : PlusIOSegmentedFamily F K) (p : ℕ) [CharP K p] :
    TwoRAPRealization R p ↔
      ∃ A : JointAssignment R p,
        A.sameExecution.Satisfies ∧
          SharedIOSat R p ∧
          (R.requests = R.responses ∧ R.outMem = 0) :=
  Iff.rfl

/-- The universal S5 claim preserves the same `R`, characteristic, and joint problem in its
conclusion; no independently chosen family occurs in the exact type. -/
theorem exactTwoRAPVerification_exact_shape
    (F K : Type) [Field F] [Field K] [Algebra F K] :
    ExactTwoRAPVerification F K ↔
      ∀ (R : PlusIOSegmentedFamily F K) (p : ℕ) [CharP K p],
        JointVerificationProblem R p →
          ∃ A : JointAssignment R p,
            A.sameExecution.Satisfies ∧
              SharedIOSat R p ∧
              (R.requests = R.responses ∧ R.outMem = 0) :=
  Iff.rfl

instance batch42_prime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
abbrev Z7 := ZMod 7
abbrev T7 := Tag Z7 Z7 0 1 1

local instance : CharP Z7 (ringChar Z7) := ringChar.charP Z7

/-- Deliberately wrong statement shape: each table, walk, and IO clause may choose a different
family and assignment.  It is inhabited as a diagnostic proposition, but it is not the exact S5
claim consumed by the capstone. -/
def IndependentFamiliesS5 : Prop :=
  ∀ (Rc Rm Rcw Rmw Rcio Rmio : PlusIOSegmentedFamily Z7 Z7)
    (p : ℕ) [CharP Z7 p],
    JointVerificationProblem Rc p →
    JointVerificationProblem Rm p →
    JointVerificationProblem Rcw p →
    JointVerificationProblem Rmw p →
    JointVerificationProblem Rcio p →
    JointVerificationProblem Rmio p →
      (∃ A : JointAssignment Rc p,
          ∀ kind, (Rc.computeTableRAP kind).Satisfies A.sameExecution.computeTableTrace) ∧
      (∃ A : JointAssignment Rm p,
          ∀ kind, (Rm.memoryTableRAP kind).Satisfies A.sameExecution.memoryTableTrace) ∧
      (∃ A : JointAssignment Rcw p,
          ∀ kind, (Rcw.computeWalkRAP kind).Satisfies A.sameExecution.computeWalkTrace) ∧
      (∃ A : JointAssignment Rmw p,
          ∀ kind, (Rmw.memoryWalkRAP kind).Satisfies A.sameExecution.memoryWalkTrace) ∧
      (∃ A : JointAssignment Rcio p, SharedIOSat Rcio p) ∧
      (∃ A : JointAssignment Rmio p, Rmio.requests = Rmio.responses ∧ Rmio.outMem = 0)

theorem independentFamiliesS5_inhabited : IndependentFamiliesS5 := by
  intro Rc Rm Rcw Rmw Rcio Rmio p _ hc hm hcw hmw hcio hmio
  obtain ⟨Ac⟩ := hc
  obtain ⟨Am⟩ := hm
  obtain ⟨Acw⟩ := hcw
  obtain ⟨Amw⟩ := hmw
  obtain ⟨Acio⟩ := hcio
  obtain ⟨Amio⟩ := hmio
  exact
    ⟨⟨Ac, Ac.six_family_satisfaction.1⟩,
      ⟨Am, Am.six_family_satisfaction.2.1⟩,
      ⟨Acw, Acw.six_family_satisfaction.2.2.1⟩,
      ⟨Amw, Amw.six_family_satisfaction.2.2.2.1⟩,
      ⟨Acio, Acio.sharedIO⟩,
      ⟨Amio, Amio.public_endpoints⟩⟩

/-- An exact-looking but weaker same-family proposition that drops shared IO and endpoints. -/
def FakeExactLookingS5 : Prop :=
  ∀ (R : PlusIOSegmentedFamily Z7 Z7) (p : ℕ) [CharP Z7 p],
    JointVerificationProblem R p →
      ∃ A : JointAssignment R p, A.sameExecution.Satisfies

theorem fakeExactLookingS5_inhabited : FakeExactLookingS5 := by
  intro R p _ h
  obtain ⟨A⟩ := h
  exact ⟨A, A.sixFamilies⟩

/-! ## 3. -/

@[reducible] noncomputable def alternateS5Bundle (C : Prop) (c : C) :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness Z7 Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness Z7 Z7)
      (ExactSegmentedCostVerification Z7 Z7)
      (exactSegmentedCostVerification Z7 Z7)
      (ExactChainedHasPerfectCompleteness Z7 Z7)
      (exactChainedHasPerfectCompleteness Z7 Z7)
      C c
      (nock_uniqueMES Z7 Z7 0 1 1)
      (ExactChainedHasCanonicalRAP2 Z7 Z7)
      (exactChainedHasCanonicalRAP2 Z7 Z7)
      (ExactChainedOneHot Z7 Z7)
      (exactChainedOneHot Z7 Z7)
      (ExactDefTraversable Z7 Z7)
      (exactDefTraversable Z7 Z7)
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

abbrev LegacyUnitBoundClaim : Prop :=
  HasTwoRAPVerification T7 (nmrMEF Z7 Z7) Z7
    (⟨Unit, Unit, Unit, (fun _ => 1), (fun _ => 1), (fun _ => 1), (fun _ => 1),
      (fun _ => True), 0⟩ :
      TwoRAPVerificationModel.{0, 0, 0, 0, 0, 0, 0} T7 (nmrMEF Z7 Z7) Z7)

@[reducible] def legacyUnitBoundClaim_inhabited : LegacyUnitBoundClaim :=
  RTMore.n8_twoRAP_bound_eq_badProb T7 (nmrMEF Z7 Z7) Z7 (fun _ => 1) (fun _ => 1)

noncomputable def legacyTransportedModel :
    TwoRAPVerificationModel.{0, 0, 0, 0, 0, 0, 0} T7 (nmrMEF Z7 Z7) Z7 :=
  RTMore.n11_twoRAP_transport
    (ι₂ := T7) (M₂ := nmrMEF Z7 Z7) (F₂ := Z7)
    RTBundle.rejTwoRAPModel

abbrev LegacyTransportedClaim : Prop :=
  HasTwoRAPVerification T7 (nmrMEF Z7 Z7) Z7 legacyTransportedModel

@[reducible] noncomputable def legacyTransportedClaim_inhabited : LegacyTransportedClaim :=
  RTMore.n11_twoRAP_prop_transport
    (ι₂ := T7) (M₂ := nmrMEF Z7 Z7) (F₂ := Z7)
    RTBundle.rejTwoRAPModel RTBundle.rejTwoRAP

theorem legacy_S5_controls_still_compile :
    Nonempty
        (TwoRAPVerificationModel.{0, 0, 0, 0, 0, 0, 0}
          RTBundle.RejVM (nmrMEF ℚ ℚ) ℚ) ∧
      Nonempty
        (TwoRAPVerificationModel.{0, 0, 0, 0, 0, 0, 0}
          T7 (nmrMEF Z7 Z7) Z7) ∧
      HasTwoRAPVerification RTBundle.RejVM (nmrMEF ℚ ℚ) ℚ
        RTBundle.rejTwoRAPModel ∧
      LegacyUnitBoundClaim ∧ LegacyTransportedClaim :=
  ⟨⟨RTBundle.rejTwoRAPModel⟩,
    ⟨legacyTransportedModel⟩, RTBundle.rejTwoRAP, legacyUnitBoundClaim_inhabited,
    legacyTransportedClaim_inhabited⟩

/-- The genuine capstone compiles. -/
theorem real_capstone_rejects_S5_substitutions :
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
  fail_if_success exact alternateS5Bundle True trivial
  fail_if_success
    exact alternateS5Bundle IndependentFamiliesS5 independentFamiliesS5_inhabited
  fail_if_success
    exact alternateS5Bundle FakeExactLookingS5 fakeExactLookingS5_inhabited
  fail_if_success
    exact alternateS5Bundle _
      (RTNew.n4_nock_model_zero_ioBound Z7 Z7 0 1 (Ksz := 1) (by norm_num))
  fail_if_success exact alternateS5Bundle LegacyUnitBoundClaim legacyUnitBoundClaim_inhabited
  fail_if_success
    exact alternateS5Bundle LegacyTransportedClaim legacyTransportedClaim_inhabited
  fail_if_success
    exact alternateS5Bundle
      (HasTwoRAPVerification RTBundle.RejVM (nmrMEF ℚ ℚ) ℚ RTBundle.rejTwoRAPModel)
      RTBundle.rejTwoRAP
  fail_if_success
    exact alternateS5Bundle
      (TwoRAPVerificationModel.{0, 0, 0, 0, 0, 0, 0}
        RTBundle.RejVM (nmrMEF ℚ ℚ) ℚ)
      RTBundle.rejTwoRAPModel
  exact NockVMROM_Thm54_structural Z7 Z7 0 1 1

/-! ## 4. Strict package consumer and sibling consistency -/

section Strict

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb q Λ : ℕ}

/-- Every field of `StrictTwoRAPRealization` projects at exactly the package index `P`. -/
theorem strict_S5_projects_every_field (P : StrictNockVMROMPackage F K hOrb q Λ) :
    (P.compRAP = RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc ∧
      P.memRAP = RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm) ∧
    P.compRAP.H = P.Hc ∧
    P.memRAP.H = P.Hm ∧
    P.Hc.card = P.objects.exec.computeRows.length ∧
    P.Hm.card = P.objects.exec.memoryRows.length ∧
    P.walkFamily.problem = ⟨P.objects.cfg, P.objects.exec⟩ ∧
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs ∧
    P.computeWalkBadRatio ≤ P.computeWalkBound ∧
    P.memoryWalkBadRatio ≤ P.memoryWalkBound := by
  let h : StrictTwoRAPRealization P := P.strictTwoRAPRealization
  exact ⟨h.named_raps, h.compute_chip_domain, h.memory_chip_domain,
    h.compute_row_domain, h.memory_row_domain, h.walk_family, h.shared_io,
    h.compute_walk_bound, h.memory_walk_bound⟩

@[reducible] noncomputable def alternateStrictS5Bundle
    (P : StrictNockVMROMPackage F K hOrb q Λ) (C : Prop) (c : C) :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, ProductionP8Containment.FixedFieldSoundnessClaim P.strategy q Λ lmb)
      P.fixedField_falseAcceptance_le
      (StrictCostRealization P)
      P.strictCostRealization
      (CombinedCompletenessAt P.objects.cfg P.objects.exec)
      (exactChainedHasPerfectCompleteness F K P.objects.cfg P.objects.exec)
      C c
      (nock_uniqueMES F K _ _ _)
      (ExactChainedHasCanonicalRAP2 F K)
      (exactChainedHasCanonicalRAP2 F K)
      (OneHotRealization P.objects.cfg P.objects.exec)
      P.chained.oneHotRealization
      (DefTraversableRealization P.objects.cfg)
      (defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos)
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩ :=
  ⟨⟩

theorem strict_rejects_wrong_problem
    (P : StrictNockVMROMPackage F K hOrb q Λ)
    (Q : RawProblem F K)
    (hwrong : Q ≠ ⟨P.objects.cfg, P.objects.exec⟩) :
    P.walkFamily.problem ≠ Q := by
  intro h
  exact hwrong (h.symm.trans P.strictTwoRAPRealization.walk_family)

theorem strict_rejects_wrong_compute_chip
    (P : StrictNockVMROMPackage F K hOrb q Λ)
    (Rcomp : RAP F)
    (hwrong : Rcomp ≠ RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc) :
    P.compRAP ≠ Rcomp := by
  intro h
  exact hwrong (h.symm.trans P.strictTwoRAPRealization.named_raps.1)

theorem strict_rejects_wrong_memory_chip
    (P : StrictNockVMROMPackage F K hOrb q Λ)
    (Rmem : RAP F)
    (hwrong : Rmem ≠ RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm) :
    P.memRAP ≠ Rmem := by
  intro h
  exact hwrong (h.symm.trans P.strictTwoRAPRealization.named_raps.2)

theorem strict_rejects_wrong_compute_domain
    (P : StrictNockVMROMPackage F K hOrb q Λ)
    (Hbad : Finset F) (hwrong : Hbad ≠ P.Hc) :
    P.compRAP.H ≠ Hbad := by
  intro h
  exact hwrong (h.symm.trans P.strictTwoRAPRealization.compute_chip_domain)

theorem strict_rejects_wrong_memory_domain
    (P : StrictNockVMROMPackage F K hOrb q Λ)
    (Hbad : Finset F) (hwrong : Hbad ≠ P.Hm) :
    P.memRAP.H ≠ Hbad := by
  intro h
  exact hwrong (h.symm.trans P.strictTwoRAPRealization.memory_chip_domain)

theorem strict_rejects_wrong_row_cards
    (P : StrictNockVMROMPackage F K hOrb q Λ)
    (nc nm : ℕ)
    (hc : nc ≠ P.objects.exec.computeRows.length)
    (hm : nm ≠ P.objects.exec.memoryRows.length) :
    P.Hc.card ≠ nc ∧ P.Hm.card ≠ nm := by
  constructor
  · intro h
    exact hc (h.symm.trans P.strictTwoRAPRealization.compute_row_domain)
  · intro h
    exact hm (h.symm.trans P.strictTwoRAPRealization.memory_row_domain)

theorem strict_structural_rejects_wrong_substitutions
    (P QP : StrictNockVMROMPackage F K hOrb q Λ)
    (Q : RawProblem F K)
    (Rcomp Rmem : RAP F) (HcBad HmBad : Finset F) (nc nm : ℕ)
    (hQ : Q ≠ ⟨P.objects.cfg, P.objects.exec⟩)
    (hc : Rcomp ≠ RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc)
    (hm : Rmem ≠ RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm)
    (hHc : HcBad ≠ P.Hc) (hHm : HmBad ≠ P.Hm)
    (hnc : nc ≠ P.objects.exec.computeRows.length)
    (hnm : nm ≠ P.objects.exec.memoryRows.length) :
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
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩ := by
  fail_if_success exact QP.structural
  fail_if_success
    exact alternateStrictS5Bundle P (P.walkFamily.problem ≠ Q)
      (strict_rejects_wrong_problem P Q hQ)
  fail_if_success
    exact alternateStrictS5Bundle P (P.compRAP ≠ Rcomp)
      (strict_rejects_wrong_compute_chip P Rcomp hc)
  fail_if_success
    exact alternateStrictS5Bundle P (P.memRAP ≠ Rmem)
      (strict_rejects_wrong_memory_chip P Rmem hm)
  fail_if_success
    exact alternateStrictS5Bundle P (P.compRAP.H ≠ HcBad)
      (strict_rejects_wrong_compute_domain P HcBad hHc)
  fail_if_success
    exact alternateStrictS5Bundle P (P.memRAP.H ≠ HmBad)
      (strict_rejects_wrong_memory_domain P HmBad hHm)
  fail_if_success
    exact alternateStrictS5Bundle P
      (P.Hc.card ≠ nc ∧ P.Hm.card ≠ nm)
      (strict_rejects_wrong_row_cards P nc nm hnc hnm)
  exact P.structural

/-- Every relevant sibling field of `StrictThm54Statement` is indexed by the same package `P`;
none independently quantifies chips, IO, bounds, or row budgets. -/
theorem strict_statement_siblings_use_same_package
    {P : StrictNockVMROMPackage F K hOrb q Λ} (S : StrictThm54Statement P) :
    (VerifiableVMCompilation
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
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩) ∧
    (P.compRAP = RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc ∧
      P.memRAP = RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm) ∧
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs ∧
    (P.computeWalkBadRatio ≤ P.computeWalkBound ∧
      P.memoryWalkBadRatio ≤ P.memoryWalkBound) ∧
    (P.compRAP.H.card = P.objects.cfg.compRows ∧
      P.memRAP.H.card =
        RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec) :=
  ⟨S.structural, S.named_raps, S.shared_io, S.walk_bounds, S.row_budgets⟩

/-! ## 5. Wrong-layer guard -/

/-- The segmented exact-S5/S6 family and the strict monolithic package chips retain their compiled
`102/44, e = 1` versus `199/196, e = 3` distinction.  This is a scope guard, not a negative verdict:
their semantic identity is the open R6/G10 connective residual. -/
theorem segmented_S5_and_monolithic_strict_S5_are_distinct_layers
    (P : StrictNockVMROMPackage F K hOrb q Λ) :
    Fintype.card ComputePlusIOColumn = 102 ∧
    Fintype.card MemoryPlusIOColumn = 45 ∧
    productionFamily.problem.cfg.eDeg = 1 ∧
    productionFamily.problem.cfg.eDeg ≠ 3 ∧
    P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧
    P.compRAP.e = 3 ∧ P.memRAP.e = 3 := by
  obtain ⟨hc102, hm44, -, -, he1, hne3⟩ := productionFamily.one_to_one_star_scope
  exact ⟨hc102, hm44, he1, hne3, P.chip_shape.1, P.chip_shape.2.1,
    P.chip_shape.2.2.1, P.chip_shape.2.2.2.1⟩

end Strict

theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end

end Nock.RedTeam.Batch42

#print axioms Nock.RedTeam.Batch42.zmod17_joint_problem_and_exact_S5_nonvacuous
#print axioms Nock.RedTeam.Batch42.twoRAPRealization_exact_shape
#print axioms Nock.RedTeam.Batch42.exactTwoRAPVerification_exact_shape
#print axioms Nock.RedTeam.Batch42.independentFamiliesS5_inhabited
#print axioms Nock.RedTeam.Batch42.fakeExactLookingS5_inhabited
#print axioms Nock.RedTeam.Batch42.legacy_S5_controls_still_compile
#print axioms Nock.RedTeam.Batch42.real_capstone_rejects_S5_substitutions
#print axioms Nock.RedTeam.Batch42.strict_S5_projects_every_field
#print axioms Nock.RedTeam.Batch42.strict_rejects_wrong_problem
#print axioms Nock.RedTeam.Batch42.strict_rejects_wrong_compute_chip
#print axioms Nock.RedTeam.Batch42.strict_rejects_wrong_memory_chip
#print axioms Nock.RedTeam.Batch42.strict_rejects_wrong_compute_domain
#print axioms Nock.RedTeam.Batch42.strict_rejects_wrong_memory_domain
#print axioms Nock.RedTeam.Batch42.strict_rejects_wrong_row_cards
#print axioms Nock.RedTeam.Batch42.strict_structural_rejects_wrong_substitutions
#print axioms Nock.RedTeam.Batch42.strict_statement_siblings_use_same_package
#print axioms Nock.RedTeam.Batch42.segmented_S5_and_monolithic_strict_S5_are_distinct_layers
#print axioms Nock.RedTeam.Batch42.paper_alias_remains_forest
#print axioms Nock.NockVMROM.Thm54.exactTwoRAPVerification
#print axioms Nock.NockVMROM.NockVMROM_Thm54_structural
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.strictTwoRAPRealization
#print axioms Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package
