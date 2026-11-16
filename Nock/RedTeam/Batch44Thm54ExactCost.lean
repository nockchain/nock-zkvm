import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.NockVMROM.Thm54.PaperCensusArithmetic
import Nock.RedTeam.Thm54NodeEncodingRegression
import Nock.RedTeam.Batch12Thm54Independent
import Nock.RedTeam.Batch13Thm54FixAudit
import Nock.RedTeam.SecondWave.RtEasy

/-!
The paper frame is the generic IO cost list, the already-walk-composed compute and memory source counts, and Theorem 5.4's final cost clauses.

The Layer-1 consumer uses the exact six-production-AIR segmented certificate at `102/44`, `e = 1`.
The strict consumers instead use the package-indexed monolithic `199/196`, `e = 3`, `87/88`
realization.  The two layers are deliberately not identified here: the R6/G10 semantic/census
bridge and the overall paper theorem remain open.
-/

namespace Nock.RedTeam.Batch44

open scoped Classical
open Nock Nock.Framework Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.RedTeam.Thm54NodeEncodingRegression

noncomputable section

set_option maxRecDepth 200000

/-! ## 1. Exact segmented certificate: every field is projected -/

/-- The S8 claim projects all six RAP widths and all six exact constraint counts. -/
theorem exact_claim_projects_widths_and_constraints
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (claim : ExactSegmentedCostVerification F K)
    (R : PlusIOSegmentedFamily F K) :
    (∀ kind, finalSegmentedCost (K := K).computeTable.localWidth = (R.computeTableRAP kind).w) ∧
      (∀ kind, finalSegmentedCost (K := K).computeWalk.localWidth = (R.computeWalkRAP kind).w) ∧
      (∀ kind, finalSegmentedCost (K := K).computeIO.localWidth = (R.computeIORAP kind).w) ∧
      (∀ kind, finalSegmentedCost (K := K).memoryTable.localWidth = (R.memoryTableRAP kind).w) ∧
      (∀ kind, finalSegmentedCost (K := K).memoryWalk.localWidth = (R.memoryWalkRAP kind).w) ∧
      (∀ kind, finalSegmentedCost (K := K).memoryIO.localWidth = (R.memoryIORAP kind).w) ∧
      finalSegmentedCost (K := K).computeTable.constraints =
        Nock.Reified.Trans.computeAIRchained.constraints.length ∧
      finalSegmentedCost (K := K).computeWalk.constraints =
        Nock.Reified.Trans.walkAIR.constraints.length ∧
      finalSegmentedCost (K := K).computeIO.constraints =
        Nock.Reified.Trans.ioProgAIR.constraints.length ∧
      finalSegmentedCost (K := K).memoryTable.constraints =
        Nock.Reified.Trans.memoryAIRchained (K := K).constraints.length ∧
      finalSegmentedCost (K := K).memoryWalk.constraints =
        Nock.Reified.Trans.walkAIR.constraints.length ∧
      finalSegmentedCost (K := K).memoryIO.constraints =
        Nock.Reified.Trans.ioMemAIR.constraints.length := by
  let h := claim R
  exact ⟨h.computeTable_width, h.computeWalk_width, h.computeIO_width,
    h.memoryTable_width, h.memoryWalk_width, h.memoryIO_width,
    h.computeTable_constraints, h.computeWalk_constraints, h.computeIO_constraints,
    h.memoryTable_constraints, h.memoryWalk_constraints, h.memoryIO_constraints⟩

/-- The same claim projects degree-four counts, exact AIR maxima, and complete histograms for all
six production AIRs. -/
theorem exact_claim_projects_degrees_and_histograms
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (claim : ExactSegmentedCostVerification F K)
    (R : PlusIOSegmentedFamily F K) :
    finalSegmentedCost (K := K).computeTable.degree4Gates =
        Nock.Reified.Trans.computeAIRchained.constraints.countP (fun x => x.degree == 4) ∧
      finalSegmentedCost (K := K).computeWalk.degree4Gates =
        Nock.Reified.Trans.walkAIR.constraints.countP (fun x => x.degree == 4) ∧
      finalSegmentedCost (K := K).computeIO.degree4Gates =
        Nock.Reified.Trans.ioProgAIR.constraints.countP (fun x => x.degree == 4) ∧
      finalSegmentedCost (K := K).memoryTable.degree4Gates =
        Nock.Reified.Trans.memoryAIRchained (K := K).constraints.countP (fun x => x.degree == 4) ∧
      finalSegmentedCost (K := K).memoryWalk.degree4Gates =
        Nock.Reified.Trans.walkAIR.constraints.countP (fun x => x.degree == 4) ∧
      finalSegmentedCost (K := K).memoryIO.degree4Gates =
        Nock.Reified.Trans.ioMemAIR.constraints.countP (fun x => x.degree == 4) ∧
      finalSegmentedCost (K := K).computeTable.airMaxDegree =
        Nock.Reified.Trans.computeAIRchained.maxDegree ∧
      finalSegmentedCost (K := K).computeWalk.airMaxDegree = Nock.Reified.Trans.walkAIR.maxDegree ∧
      finalSegmentedCost (K := K).computeIO.airMaxDegree = Nock.Reified.Trans.ioProgAIR.maxDegree ∧
      finalSegmentedCost (K := K).memoryTable.airMaxDegree =
        Nock.Reified.Trans.memoryAIRchained (K := K).maxDegree ∧
      finalSegmentedCost (K := K).memoryWalk.airMaxDegree = Nock.Reified.Trans.walkAIR.maxDegree ∧
      finalSegmentedCost (K := K).memoryIO.airMaxDegree = Nock.Reified.Trans.ioMemAIR.maxDegree ∧
      finalSegmentedCost (K := K).computeTable.histogram =
        degreeHistogram Nock.Reified.Trans.computeAIRchained ∧
      finalSegmentedCost (K := K).computeWalk.histogram =
        degreeHistogram Nock.Reified.Trans.walkAIR ∧
      finalSegmentedCost (K := K).computeIO.histogram =
        degreeHistogram Nock.Reified.Trans.ioProgAIR ∧
      finalSegmentedCost (K := K).memoryTable.histogram =
        degreeHistogram (Nock.Reified.Trans.memoryAIRchained (K := K)) ∧
      finalSegmentedCost (K := K).memoryWalk.histogram =
        degreeHistogram Nock.Reified.Trans.walkAIR ∧
      finalSegmentedCost (K := K).memoryIO.histogram =
        degreeHistogram Nock.Reified.Trans.ioMemAIR := by
  let h := claim R
  exact ⟨h.computeTable_deg4, h.computeWalk_deg4, h.computeIO_deg4,
    h.memoryTable_deg4, h.memoryWalk_deg4, h.memoryIO_deg4,
    h.computeTable_max, h.computeWalk_max, h.computeIO_max,
    h.memoryTable_max, h.memoryWalk_max, h.memoryIO_max,
    h.computeTable_hist, h.computeWalk_hist, h.computeIO_hist,
    h.memoryTable_hist, h.memoryWalk_hist, h.memoryIO_hist⟩

/-- Totals, extension metadata, every RAP's extension degree and degree bound, and the separate IO
accumulator-field layer are all load-bearing fields of the certificate. -/
theorem exact_claim_projects_global_metadata
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (claim : ExactSegmentedCostVerification F K)
    (R : PlusIOSegmentedFamily F K) :
    finalSegmentedCost (K := K).computeDisjointWidth = Fintype.card ComputePlusIOColumn ∧
      finalSegmentedCost (K := K).memoryDisjointWidth = Fintype.card MemoryPlusIOColumn ∧
      (finalSegmentedCost (K := K).eDeg = R.problem.cfg.eDeg ∧ R.problem.cfg.eDeg = 1) ∧
      (∀ kind,
        (R.computeTableRAP kind).e = finalSegmentedCost (K := K).eDeg ∧
        (R.computeWalkRAP kind).e = finalSegmentedCost (K := K).eDeg ∧
        (R.computeIORAP kind).e = finalSegmentedCost (K := K).eDeg ∧
        (R.memoryTableRAP kind).e = finalSegmentedCost (K := K).eDeg ∧
        (R.memoryWalkRAP kind).e = finalSegmentedCost (K := K).eDeg ∧
        (R.memoryIORAP kind).e = finalSegmentedCost (K := K).eDeg) ∧
      finalSegmentedCost (K := K).rapDegreeBound = 4 ∧
      (∀ kind,
        (R.computeTableRAP kind).d ≤ finalSegmentedCost (K := K).rapDegreeBound ∧
        (R.computeWalkRAP kind).d ≤ finalSegmentedCost (K := K).rapDegreeBound ∧
        (R.computeIORAP kind).d ≤ finalSegmentedCost (K := K).rapDegreeBound ∧
        (R.memoryTableRAP kind).d ≤ finalSegmentedCost (K := K).rapDegreeBound ∧
        (R.memoryWalkRAP kind).d ≤ finalSegmentedCost (K := K).rapDegreeBound ∧
        (R.memoryIORAP kind).d ≤ finalSegmentedCost (K := K).rapDegreeBound) ∧
      finalSegmentedCost (K := K).ioLayer = .separateRatFuncAccumulatorField := by
  let h := claim R
  exact ⟨h.computeTotal, h.memoryTotal, h.e_metadata, h.rap_e_metadata,
    h.rap_bound_value, h.rap_d_upper, h.io_layer⟩

/-- Independent anti-phantom projection: a certifiable record is definitionally the unique final
record, so no unmentioned nested or top-level cost field survives. -/
theorem exact_claim_has_unique_cost_record
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (R : PlusIOSegmentedFamily F K) (c : ReifiedFinalCost)
    (h : ExactCostCertificate R c) :
    c = finalSegmentedCost (K := K) :=
  certified_cost_unique h

def wrongWidthCost {K : Type} [Field K] : ReifiedFinalCost :=
  { finalSegmentedCost (K := K) with
      computeTable := { (finalSegmentedCost (K := K)).computeTable with localWidth := 95 } }

def wrongHistogramCost {K : Type} [Field K] : ReifiedFinalCost :=
  { finalSegmentedCost (K := K) with
      computeTable :=
        { (finalSegmentedCost (K := K)).computeTable with
            histogram := { (finalSegmentedCost (K := K)).computeTable.histogram with deg0 := 1 } } }

/-- Concrete malformed width and histogram records cannot carry an exact certificate. -/
theorem wrong_width_and_histogram_certificates_fail
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (R : PlusIOSegmentedFamily F K) :
    ¬ ExactCostCertificate R (wrongWidthCost (K := K)) ∧
      ¬ ExactCostCertificate R (wrongHistogramCost (K := K)) := by
  constructor
  · apply no_certificate_of_compute_width_ne
    change (95 ≠ 94)
    decide
  · apply no_certificate_of_compute_hist_ne
    intro h
    have h0 := congrArg DegreeHistogram.deg0 h
    have hleft : (wrongHistogramCost (K := K)).computeTable.histogram.deg0 = 1 := rfl
    rw [hleft] at h0
    -- Measured histogram: `computeAIR_deg0` is 0, and `lnChainExpr` is degree 1,
    -- so chained `deg0` stays 0. The decoy perturbs that bucket to 1.
    have hright : (degreeHistogram Nock.Reified.Trans.computeAIRchained).deg0 = 0 := by
      simp only [degreeHistogram, Nock.Reified.Trans.computeAIRchained]
      rw [List.countP_append, Nock.Reified.computeAIR_deg0, zero_add]
      simp [List.countP_cons, List.countP_nil, Nock.Reified.Constraint.degree,
        Nock.Reified.Trans.lnChainExpr, Nock.Reified.Expr.degree,
        Nock.Reified.tc, Nock.Reified.Trans.tn, Nat.max_self]
    rw [hright] at h0
    exact absurd h0 (by decide)

/-! ## 2. Concrete `ZMod 17` non-vacuity -/

abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17

/-- The real production family over `ZMod 17` carries the exact certificate, exposing all six
local widths together with the `102/44`, `e = 1` final metadata. -/
theorem zmod17_production_family_exact_cost_nonvacuous :
    ExactCostCertificate productionFamily (finalSegmentedCost (K := K17)) ∧
      (finalSegmentedCost (K := K17)).computeTable.localWidth = 94 ∧
      (finalSegmentedCost (K := K17)).computeWalk.localWidth = 6 ∧
      (finalSegmentedCost (K := K17)).computeIO.localWidth = 2 ∧
      (finalSegmentedCost (K := K17)).memoryTable.localWidth = 36 ∧
      (finalSegmentedCost (K := K17)).memoryWalk.localWidth = 6 ∧
      (finalSegmentedCost (K := K17)).memoryIO.localWidth = 3 ∧
      (finalSegmentedCost (K := K17)).computeDisjointWidth = 102 ∧
      (finalSegmentedCost (K := K17)).memoryDisjointWidth = 45 ∧
      (finalSegmentedCost (K := K17)).eDeg = 1 := by
  exact ⟨exactSegmentedCostVerification K17 K17 productionFamily,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. -/

instance batch44_prime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
abbrev Z7 := ZMod 7
abbrev T7 := Tag Z7 Z7 0 1 1

local instance : CharP Z7 (ringChar Z7) := ringChar.charP Z7

/-- A deliberately fake cost proposition: true, but unrelated to any family or certificate. -/
def FakeCostClaim : Prop := (finalSegmentedCost (K := ZMod 17)).computeDisjointWidth = 102

theorem fakeCostClaim_inhabited : FakeCostClaim := rfl

/-- This remains a positive G9 control, not a property of the current S8 slot. -/
@[reducible] def transportLegacyCost
    {ι₁ ι₂ : Type} [VMSystem ι₁] [VMSystem ι₂] (c : CostModel)
    (h : HasCostModel ι₁ c) : HasCostModel ι₂ c where
  compMaxDegree_eq_four := h.compMaxDegree_eq_four
  memMaxDegree_eq_four := h.memMaxDegree_eq_four
  memory_fewer_constraints := h.memory_fewer_constraints
  memory_fewer_deg4 := h.memory_fewer_deg4

@[reducible] def decoyAffineSplitCosted : HasParamCostModel T7 b13_decoyParamCost where
  compMaxDeg_le := by decide
  memMaxDeg_le := by decide
  mem_deg4_lt_comp := by
    intro e he
    simp only [b13_decoyParamCost, AffineE.eval]
    omega

theorem legacy_cost_attacks_remain_positive_controls :
    HasCostModel T7 reifiedNockCost ∧
      HasCostModel B12RejectVM reifiedNockCost ∧
      HasCostModel T7 RTNew.absurdCost ∧
      HasParamCostModel T7 RTNew.absurdParamCost ∧
      HasParamCostModel T7 b13_decoyParamCost ∧
      HasCostModel T7 reifiedNockCost := by
  exact ⟨nock_hasCostModel Z7 Z7 0 1 1,
    b12_s8_reject_vm_costed,
    RTNew.n2_absurd_columns_costed Z7 Z7 0 1 1,
    RTNew.n3_absurd_IO_param_costed Z7 Z7 0 1 1,
    decoyAffineSplitCosted,
    transportLegacyCost reifiedNockCost b12_s8_reject_vm_costed⟩

/-- Change only S8 while keeping all seven other genuine Layer-1 objects fixed. -/
@[reducible] noncomputable def alternateLayerS8 (C : Prop) (c : C) :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness Z7 Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness Z7 Z7)
      C c
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

/-- `True`, both retired cost classes, absurd columns, reject-VM cost, phantom IO, the affine
split decoy, a transported generic cost proof, raw cost data, and a fake proposition all fail in
the real S8 slot.  The genuine Layer-1 capstone compiles. -/
theorem layer1_rejects_all_legacy_and_fake_S8_substitutions :
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
  fail_if_success exact alternateLayerS8 True trivial
  fail_if_success exact alternateLayerS8 FakeCostClaim fakeCostClaim_inhabited
  fail_if_success
    exact alternateLayerS8 (HasCostModel T7 reifiedNockCost)
      (nock_hasCostModel Z7 Z7 0 1 1)
  fail_if_success
    exact alternateLayerS8 (HasCostModel B12RejectVM reifiedNockCost)
      b12_s8_reject_vm_costed
  fail_if_success
    exact alternateLayerS8 (HasCostModel T7 RTNew.absurdCost)
      (RTNew.n2_absurd_columns_costed Z7 Z7 0 1 1)
  fail_if_success
    exact alternateLayerS8 (HasParamCostModel T7 RTNew.absurdParamCost)
      (RTNew.n3_absurd_IO_param_costed Z7 Z7 0 1 1)
  fail_if_success
    exact alternateLayerS8 (HasParamCostModel T7 b13_decoyParamCost)
      decoyAffineSplitCosted
  fail_if_success
    exact alternateLayerS8 (HasCostModel T7 reifiedNockCost)
      (transportLegacyCost reifiedNockCost b12_s8_reject_vm_costed)
  fail_if_success exact reifiedNockCost
  exact NockVMROM_Thm54_structural Z7 Z7 0 1 1

/-! ## 4. Empty-bundle hygiene -/

/-- The class has no projections at all: every S1--S8 proposition/proof and the language witness
is selected in the type, and the sole constructor has no `True` or dummy field. -/
theorem verifiable_bundle_has_no_fields_or_legacy_cost_projection : True := by
  fail_if_success
    have _soundness := VerifiableVMCompilation.soundness
  fail_if_success
    have _cost := VerifiableVMCompilation.costVerified
  fail_if_success
    have _completeness := VerifiableVMCompilation.completeness
  fail_if_success
    have _twoRAP := VerifiableVMCompilation.twoRAPVerified
  fail_if_success
    have _mes := VerifiableVMCompilation.uniqueMES
  fail_if_success
    have _canonical := VerifiableVMCompilation.canonicalRAP
  fail_if_success
    have _oneHot := VerifiableVMCompilation.oneHot
  fail_if_success
    have _traversable := VerifiableVMCompilation.traversable
  fail_if_success
    have _language := VerifiableVMCompilation.languageInhabited
  fail_if_success
    have _legacy := VerifiableVMCompilation.hasCostModel
  trivial

/-- The fake claim constructs a bundle only at its own explicit type; it cannot be returned at the
genuine capstone type checked above. -/
theorem fake_cost_claim_has_distinct_bundle_type :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness Z7 Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness Z7 Z7)
      FakeCostClaim fakeCostClaim_inhabited
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

/-! ## 5. Strict package threading and substitution attacks -/

section Strict

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb q Λ : ℕ}

abbrev StrictS8StructuralType (P : StrictNockVMROMPackage F K hOrb q Λ) : Prop :=
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
    ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩

/-- Every strict S8 field projects at the same package `P`: fingerprint, shape, actual transition
gate lists with paper ties, and the exact shared-execution row budgets. -/
theorem strict_cost_projects_every_field (P : StrictNockVMROMPackage F K hOrb q Λ) :
    (P.compRAP.w, P.memRAP.w, P.compRAP.e) =
        CompleteProductionCost.strictPaperG10Fingerprint ∧
      (P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧
        P.compRAP.e = 3 ∧ P.memRAP.e = 3 ∧
        P.compRAP.d = 4 ∧ P.memRAP.d = 4 ∧
        P.compRAP.k = 2 ∧ P.memRAP.k = 1) ∧
      (((compTemplate F).transitionGates P.basis).length = 87 ∧
        ((compTemplate F).transitionGates P.basis).length =
          Nock.NockVM.comp_io_deg4_gates 3) ∧
      (((memTemplate F).transitionGates P.basis).length = 88 ∧
        ((memTemplate F).transitionGates P.basis).length =
          Nock.NockVM.mem_io_deg4_gates 3) ∧
      P.compRAP.H.card = P.objects.cfg.compRows ∧
      P.memRAP.H.card =
        RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec := by
  let h : StrictCostRealization P := P.strictCostRealization
  exact ⟨h.fingerprint, h.chip_shape, h.compute_transition_gates,
    h.memory_transition_gates, h.compute_row_budget, h.memory_row_budget⟩

abbrev FingerprintOnly (P : StrictNockVMROMPackage F K hOrb q Λ) : Prop :=
  (P.compRAP.w, P.memRAP.w, P.compRAP.e) =
    CompleteProductionCost.strictPaperG10Fingerprint

abbrev TransitionGatesOnly (P : StrictNockVMROMPackage F K hOrb q Λ) : Prop :=
  ((compTemplate F).transitionGates P.basis).length = 87 ∧
    ((memTemplate F).transitionGates P.basis).length = 88

abbrev RowBudgetsOnly (P : StrictNockVMROMPackage F K hOrb q Λ) : Prop :=
  P.compRAP.H.card = P.objects.cfg.compRows ∧
    P.memRAP.H.card =
      RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec

@[reducible] noncomputable def alternateStrictS8
    (P : StrictNockVMROMPackage F K hOrb q Λ) (C : Prop) (c : C) :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, ProductionP8Containment.FixedFieldSoundnessClaim P.strategy q Λ lmb)
      P.fixedField_falseAcceptance_le
      C c
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

/-- A sibling package and each independently weakened fingerprint/gate/row claim elaborate at their
own types but cannot fill `P`'s strict S8 slot. -/
theorem strict_consumer_rejects_wrong_package_and_weakened_costs
    (P _QP : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictS8StructuralType P := by
  fail_if_success exact _QP.structural
  fail_if_success
    exact alternateStrictS8 P (StrictCostRealization _QP) _QP.strictCostRealization
  fail_if_success
    exact alternateStrictS8 P (FingerprintOnly P) P.strictCostRealization.fingerprint
  fail_if_success
    exact alternateStrictS8 P (TransitionGatesOnly P)
      ⟨P.strictCostRealization.compute_transition_gates.1,
        P.strictCostRealization.memory_transition_gates.1⟩
  fail_if_success
    exact alternateStrictS8 P (RowBudgetsOnly P)
      ⟨P.strictCostRealization.compute_row_budget,
        P.strictCostRealization.memory_row_budget⟩
  exact P.structural

/-- Numerically wrong chip, transition-gate, and row claims are contradicted by the package's own
strict realization, not merely absent from an API. -/
theorem strict_wrong_chip_gate_and_row_values_fail
    (P : StrictNockVMROMPackage F K hOrb q Λ) :
    P.compRAP.w ≠ 198 ∧ P.memRAP.w ≠ 195 ∧
      ((compTemplate F).transitionGates P.basis).length ≠ 86 ∧
      ((memTemplate F).transitionGates P.basis).length ≠ 89 ∧
      P.compRAP.H.card ≠ P.objects.cfg.compRows + 1 ∧
      P.memRAP.H.card ≠
        RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbad
    have hgood := P.strictCostRealization.chip_shape.1
    omega
  · intro hbad
    have hgood := P.strictCostRealization.chip_shape.2.1
    omega
  · intro hbad
    have hgood := P.strictCostRealization.compute_transition_gates.1
    omega
  · intro hbad
    have hgood := P.strictCostRealization.memory_transition_gates.1
    omega
  · intro hbad
    have hgood := P.strictCostRealization.compute_row_budget
    omega
  · intro hbad
    have hgood := P.strictCostRealization.memory_row_budget
    omega

/-- `StrictThm54Statement`'s S8 siblings and its structural slot all read the same `P`; transition
gate ties remain available through the exact cost proposition consumed by `structural`. -/
theorem strict_statement_s8_fields_are_consistent
    {P : StrictNockVMROMPackage F K hOrb q Λ} (S : StrictThm54Statement P) :
    StrictS8StructuralType P ∧
      StrictCostRealization P ∧
      (P.compRAP.w, P.memRAP.w, P.compRAP.e) =
        CompleteProductionCost.strictPaperG10Fingerprint ∧
      (P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧
        P.compRAP.e = 3 ∧ P.memRAP.e = 3 ∧
        P.compRAP.d = 4 ∧ P.memRAP.d = 4 ∧
        P.compRAP.k = 2 ∧ P.memRAP.k = 1) ∧
      (((compTemplate F).transitionGates P.basis).length = 87 ∧
        ((compTemplate F).transitionGates P.basis).length =
          Nock.NockVM.comp_io_deg4_gates 3) ∧
      (((memTemplate F).transitionGates P.basis).length = 88 ∧
        ((memTemplate F).transitionGates P.basis).length =
          Nock.NockVM.mem_io_deg4_gates 3) ∧
      (P.compRAP.H.card = P.objects.cfg.compRows ∧
        P.memRAP.H.card =
          RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec) := by
  exact ⟨S.structural, P.strictCostRealization, S.fingerprint, S.chip_shape,
    P.strictCostRealization.compute_transition_gates,
    P.strictCostRealization.memory_transition_gates, S.row_budgets⟩

/-! ## 6. Wrong-layer and R6/G10 boundary -/

/-- The segmented certificate and strict package remain visibly distinct layers, while the paper
census arithmetic retains the nonzero residual summands.  This is not an identification theorem. -/
theorem segmented_strict_and_paper_census_remain_distinct
    (P : StrictNockVMROMPackage F K hOrb q Λ) :
    finalSegmentedCost (K := K).computeDisjointWidth = 102 ∧
      finalSegmentedCost (K := K).memoryDisjointWidth = 45 ∧
      finalSegmentedCost (K := K).eDeg = 1 ∧
      P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧
      P.compRAP.e = 3 ∧ P.memRAP.e = 3 ∧
      finalSegmentedCost (K := K).computeDisjointWidth ≠ P.compRAP.w ∧
      finalSegmentedCost (K := K).memoryDisjointWidth ≠ P.memRAP.w ∧
      PaperCensusArithmetic.compAfterGenericIOColumns 3 = 187 ∧
      PaperCensusArithmetic.compAfterGenericIOTransitions 3 = 76 ∧
      PaperCensusArithmetic.memAfterGenericIOColumns 3 = 171 ∧
      PaperCensusArithmetic.memAfterGenericIOTransitions 3 = 77 ∧
      Nock.NockVM.comp_io_columns 3 = 199 ∧
      Nock.NockVM.comp_io_deg4_gates 3 = 87 ∧
      Nock.NockVM.mem_io_columns 3 = 196 ∧
      Nock.NockVM.mem_io_deg4_gates 3 = 88 ∧
      PaperCensusArithmetic.compAfterGenericIOColumns 3 + 4 * 3 =
        Nock.NockVM.comp_io_columns 3 ∧
      PaperCensusArithmetic.compAfterGenericIOTransitions 3 + (3 * 3 + 2) =
        Nock.NockVM.comp_io_deg4_gates 3 ∧
      PaperCensusArithmetic.memAfterGenericIOColumns 3 + (6 * 3 + 7) =
        Nock.NockVM.mem_io_columns 3 ∧
      PaperCensusArithmetic.memAfterGenericIOTransitions 3 + (3 * 3 + 2) =
        Nock.NockVM.mem_io_deg4_gates 3 := by
  have hs := P.chip_shape
  have hc := PaperCensusArithmetic.cubic_snapshot
  refine ⟨rfl, rfl, rfl, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_,
    hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
    hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2,
    PaperCensusArithmetic.comp_columns_residual 3,
    PaperCensusArithmetic.comp_transitions_residual 3,
    PaperCensusArithmetic.mem_columns_residual 3,
    PaperCensusArithmetic.mem_transitions_residual 3⟩
  · intro hbad
    change 102 = P.compRAP.w at hbad
    omega
  · intro hbad
    change 45 = P.memRAP.w at hbad
    omega

end Strict

/-- Narrow verdict guard: Wave-T S8 does not repoint the paper theorem alias. -/
theorem paper_alias_remains_operational_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end

end Nock.RedTeam.Batch44

#print axioms Nock.NockVMROM.Thm54.exactSegmentedCostVerification
#print axioms Nock.NockVMROM.Thm54.certified_cost_unique
#print axioms Nock.NockVMROM.NockVMROM_Thm54_structural
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.strictCostRealization
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.structural
#print axioms Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package

#print axioms Nock.RedTeam.Batch44.exact_claim_projects_widths_and_constraints
#print axioms Nock.RedTeam.Batch44.exact_claim_projects_degrees_and_histograms
#print axioms Nock.RedTeam.Batch44.exact_claim_projects_global_metadata
#print axioms Nock.RedTeam.Batch44.exact_claim_has_unique_cost_record
#print axioms Nock.RedTeam.Batch44.wrong_width_and_histogram_certificates_fail
#print axioms Nock.RedTeam.Batch44.zmod17_production_family_exact_cost_nonvacuous
#print axioms Nock.RedTeam.Batch44.legacy_cost_attacks_remain_positive_controls
#print axioms Nock.RedTeam.Batch44.layer1_rejects_all_legacy_and_fake_S8_substitutions
#print axioms Nock.RedTeam.Batch44.verifiable_bundle_has_no_fields_or_legacy_cost_projection
#print axioms Nock.RedTeam.Batch44.fake_cost_claim_has_distinct_bundle_type
#print axioms Nock.RedTeam.Batch44.strict_cost_projects_every_field
#print axioms Nock.RedTeam.Batch44.strict_consumer_rejects_wrong_package_and_weakened_costs
#print axioms Nock.RedTeam.Batch44.strict_wrong_chip_gate_and_row_values_fail
#print axioms Nock.RedTeam.Batch44.strict_statement_s8_fields_are_consistent
#print axioms Nock.RedTeam.Batch44.segmented_strict_and_paper_census_remain_distinct
#print axioms Nock.RedTeam.Batch44.paper_alias_remains_operational_forest
