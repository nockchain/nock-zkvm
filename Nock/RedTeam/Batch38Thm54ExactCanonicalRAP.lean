import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.Thm54P3Nonvacuity

/-!
# Exact canonical RAP at consumed capstones

Paper frame:
* `Def:Canonical_RAP`, the paper: common parameters and the two exact
  sub-verifier-acceptance iff RAP-satisfaction clauses.
* Nock application, the paper; consumed theorem, the paper.

Its scope is the 94/36-column minus-IO families.
-/

namespace Nock.RedTeam.Batch38

open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictPackage
open scoped Classical Polynomial

noncomputable section

instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

abbrev Z7 := ZMod 7
abbrev T7 := Tag Z7 Z7 0 1 1

local instance : CharP Z7 (ringChar Z7) := ringChar.charP Z7

/-- Keeping it local avoids
depending on Wave-S-d's concurrently changing S3 regression artifact. -/
@[reducible] def fakeLegacyCRAP : HasCanonicalRAP T7 (nmrMEF Z7 Z7) Z7 where
  Rprog := (nock_hasCanonicalRAP Z7 Z7 0 1 1).Rprog
  Rmem := (nock_hasCanonicalRAP Z7 Z7 0 1 1).Rmem
  ProgProblem := Unit
  MemProblem := Unit
  progAccepts := fun _ => True
  progSatisfiable := fun _ => True
  memAccepts := fun _ => True
  memSatisfiable := fun _ => True
  compute_iff := fun _ => Iff.rfl
  memory_iff := fun _ => Iff.rfl

/-! ## 1. Attacks at the exact real consumed capstone type -/

/-- The exact concrete target used for all S2-only substitution attacks. -/
abbrev ExactRealCapstoneZ7 : Prop :=
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
    (nock_languageInhabited Z7 Z7 0 1 1)

/-- Negative control: change only S2 to the old `True`/`trivial` claim and proof. -/
@[reducible] def trueS2Bundle :
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
      True trivial
      (ExactChainedOneHot Z7 Z7)
      (exactChainedOneHot Z7 Z7)
      (ExactDefTraversable Z7 Z7)
      (exactDefTraversable Z7 Z7)
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

@[reducible] def fakeCRAPS2Bundle :
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
      (Nonempty (HasCanonicalRAP T7 (nmrMEF Z7 Z7) Z7)) ⟨fakeLegacyCRAP⟩
      (ExactChainedOneHot Z7 Z7)
      (exactChainedOneHot Z7 Z7)
      (ExactDefTraversable Z7 Z7)
      (exactDefTraversable Z7 Z7)
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

@[reducible] def legacyNockS2Bundle :
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
      (Nonempty (HasCanonicalRAP T7 (nmrMEF Z7 Z7) Z7))
      ⟨nock_hasCanonicalRAP Z7 Z7 0 1 1⟩
      (ExactChainedOneHot Z7 Z7)
      (exactChainedOneHot Z7 Z7)
      (ExactDefTraversable Z7 Z7)
      (exactDefTraversable Z7 Z7)
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

/-- All other exact parameters are held fixed. -/
theorem exact_real_capstone_rejects_all_legacy_S2_substitutions :
    ExactRealCapstoneZ7 := by
  fail_if_success
    let _ : Prop := HasCanonicalRAP T7 (nmrMEF Z7 Z7) Z7
  fail_if_success
    exact trueS2Bundle
  fail_if_success
    exact fakeCRAPS2Bundle
  fail_if_success
    exact legacyNockS2Bundle
  exact NockVMROM_Thm54_structural Z7 Z7 0 1 1

/-! ## 2. Full exact type indices and literal `RAP.Satisfies` RHS -/

/-- The official proposition exposes the shared problem type, fixed acceptance predicates, both
chained AIRs, dependent auxiliaries, exact parameter families, and canonical encoders. -/
theorem exact_type_exposes_every_identity_bearing_index (F K : Type)
    [Field F] [Field K] [Algebra F K] :
    ExactChainedHasCanonicalRAP2 F K =
      HasCanonicalRAP2 K
        (ExactCanonicalRAPProblem F K) (ExactCanonicalRAPProblem F K)
        (exactComputeChainedAccepts (F := F) (K := K))
        (exactMemoryChainedAccepts (F := F) (K := K))
        Trans.computeAIRchained (Trans.memoryAIRchained (K := K))
        (ExactCanonicalProgAux (F := F) (K := K))
        (ExactCanonicalMemAux (F := F) (K := K))
        (exactCanonicalProgParams (F := F) (K := K))
        (exactCanonicalMemParams (F := F) (K := K))
        (exactCanonicalEncodeProg (F := F) (K := K))
        (exactCanonicalEncodeMem (F := F) (K := K)) :=
  exactChainedHasCanonicalRAP2_type_indices F K

/-- Both parameter families are projections of the same exact configuration, so the extension
degree, orbit exponent, generator, and coset shift are shared rather than independently chosen.
The paper's separate `w_prog,w_mem ⊆ w_RAP` containment remains a disclosed representation delta. -/
theorem exact_parameter_families_share_common_RAP_core
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (p : ExactCanonicalRAPProblem F K) :
    ((exactCanonicalProgParams p).eDeg, (exactCanonicalProgParams p).hExp,
        (exactCanonicalProgParams p).ω, (exactCanonicalProgParams p).βcoset) =
      ((exactCanonicalMemParams p).eDeg, (exactCanonicalMemParams p).hExp,
        (exactCanonicalMemParams p).ω, (exactCanonicalMemParams p).βcoset) :=
  rfl

/-- Compute acceptance is iff actual satisfaction of every fixed chained segment RAP. -/
theorem exact_compute_RHS_is_RAP_Satisfies
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (p : ExactCanonicalRAPProblem F K) :
    exactComputeChainedAccepts p ↔
      ∃ ex : ExactCanonicalProgAux p, ∀ kind,
        ((exactCanonicalProgParams p).rap Trans.computeAIRchained kind).Satisfies
          (exactCanonicalEncodeProg p ex) :=
  (exactChainedHasCanonicalRAP2 F K).compute_iff p

/-- Memory acceptance is iff actual satisfaction of every fixed chained segment RAP. -/
theorem exact_memory_RHS_is_RAP_Satisfies
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (p : ExactCanonicalRAPProblem F K) :
    exactMemoryChainedAccepts p ↔
      ∃ g : ExactCanonicalMemAux p, ∀ kind,
        ((exactCanonicalMemParams p).rap (Trans.memoryAIRchained (K := K)) kind).Satisfies
          (exactCanonicalEncodeMem p g) :=
  (exactChainedHasCanonicalRAP2 F K).memory_iff p

/-! ## 3. -/

/-- Generic quantification is strongest: every inhabitable exact problem has nonempty row domains
on both sides, because `ExactConfig` carries positive compute and memory row counts. -/
theorem every_exact_problem_has_nonempty_official_row_domains
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (p : ExactCanonicalRAPProblem F K) :
    (exactCanonicalProgParams p).domain .row ≠ ∅ ∧
      (exactCanonicalMemParams p).domain .row ≠ ∅ :=
  ⟨exactCanonicalProgRowDomain_nonempty p, exactCanonicalMemRowDomain_nonempty p⟩

def concreteExactProblem :
    ExactCanonicalRAPProblem
      Nock.RedTeam.Thm54P2Nonvacuity.K17 Nock.RedTeam.Thm54P2Nonvacuity.K17 :=
  ExactCanonicalRAPProblem.ofChained
    Nock.RedTeam.Thm54P3Nonvacuity.production_chained

theorem concrete_exact_problem_domains_nonempty :
    (exactCanonicalProgParams concreteExactProblem).domain .row ≠ ∅ ∧
      (exactCanonicalMemParams concreteExactProblem).domain .row ≠ ∅ :=
  every_exact_problem_has_nonempty_official_row_domains concreteExactProblem

theorem legacy_empty_H_RAPs_are_not_official
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (p : ExactCanonicalRAPProblem F K) (α β : K) (Ksz : ℕ) :
    (exactCanonicalProgParams p).rap Trans.computeAIRchained .row ≠
        (nock_hasCanonicalRAP F K α β Ksz).Rprog ∧
      (exactCanonicalMemParams p).rap (Trans.memoryAIRchained (K := K)) .row ≠
        (nock_hasCanonicalRAP F K α β Ksz).Rmem :=
  ⟨legacyEmptyRprog_ne_exactCanonicalProgRowRAP p α β Ksz,
    exactCanonicalMemRowRAP_ne_emptyDomain p _ rfl⟩

/-! ## 4. Same-execution and consumed StrictPackage receipts -/

/-- `ofChained` preserves one cfg/exec definitionally and its paired certificate uses that one
problem value for both compute and memory satisfaction families. -/
theorem exact_same_execution_not_independently_quantified
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    let p := ExactCanonicalRAPProblem.ofChained h
    p.cfg = cfg ∧ p.exec = exec ∧ ExactCanonicalRAPSameExecutionCertificate p :=
  ⟨rfl, rfl, h.exactCanonicalRAP_sameExecution⟩

/-- Exact structural proposition selected by both strict consumers for their one package. -/
abbrev StrictExactStructuralType
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) : Prop :=
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

/-- The package projection and final conditional statement pin the same exact S2 claim/proof.
The package's own chained execution simultaneously supplies the paired exact certificate. -/
theorem strict_consumers_pin_exact_S2_and_same_execution
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictExactStructuralType P ∧
      StrictExactStructuralType P ∧
      ExactCanonicalRAPSameExecutionCertificate
        (ExactCanonicalRAPProblem.ofChained P.chained) :=
  ⟨P.structural, (strictNockVMROM_of_package P).structural,
    P.chained.exactCanonicalRAP_sameExecution⟩

/-! ## 5. Honest scope guards and still-open neighboring obligations -/

/-- The consumed exact S2 is 94/36 and cannot be confused with final G10's 199/196 chips. -/
theorem exact_S2_is_94_36_minus_IO_not_G10 {K : Type} [Field K] :
    Trans.computeAIRchained.numTraceCols = 94 ∧
      (Trans.memoryAIRchained (K := K)).numTraceCols = 36 ∧
      Trans.computeAIRchained.numTraceCols ≠ 199 ∧
      (Trans.memoryAIRchained (K := K)).numTraceCols ≠ 196 :=
  exactChainedCanonicalRAP_minusIO_scope

theorem S6_remains_legacy_row_local
    (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    (nockCompletenessModel F K α β Ksz).Problem = ComputeProblem K :=
  rfl

structure OtherVM : Type

instance : VMSystem OtherVM where
  Statement := Unit
  Witness := Unit
  accepts := fun _ _ => False

/-- The S7 model body transports field-for-field across VM indices. -/
def transportSoundnessModel {ι₁ ι₂ : Type} [VMSystem ι₁] [VMSystem ι₂]
    (m : ConcreteSoundnessModel ι₁) : ConcreteSoundnessModel ι₂ :=
  ⟨m.Trial, m.badProbability, m.bound⟩

/-- G9 remains reproducible: the Nock S7 model and proof transport to an unrelated reject VM. -/
theorem G9_transport_remains_open :
    HasConcreteSoundness OtherVM
      (transportSoundnessModel
        (nockConcreteSoundness (ZMod 7) (ZMod 7) 0 1 1)) where
  sound := (nock_hasConcreteSoundness (ZMod 7) (ZMod 7) 0 1 1).sound

theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end

end Nock.RedTeam.Batch38

#print axioms Nock.RedTeam.Batch38.exact_real_capstone_rejects_all_legacy_S2_substitutions
#print axioms Nock.RedTeam.Batch38.exact_type_exposes_every_identity_bearing_index
#print axioms Nock.RedTeam.Batch38.exact_parameter_families_share_common_RAP_core
#print axioms Nock.RedTeam.Batch38.exact_compute_RHS_is_RAP_Satisfies
#print axioms Nock.RedTeam.Batch38.exact_memory_RHS_is_RAP_Satisfies
#print axioms Nock.RedTeam.Batch38.every_exact_problem_has_nonempty_official_row_domains
#print axioms Nock.RedTeam.Batch38.concrete_exact_problem_domains_nonempty
#print axioms Nock.RedTeam.Batch38.legacy_empty_H_RAPs_are_not_official
#print axioms Nock.RedTeam.Batch38.exact_same_execution_not_independently_quantified
#print axioms Nock.RedTeam.Batch38.strict_consumers_pin_exact_S2_and_same_execution
#print axioms Nock.RedTeam.Batch38.exact_S2_is_94_36_minus_IO_not_G10
#print axioms Nock.RedTeam.Batch38.S6_remains_legacy_row_local
#print axioms Nock.RedTeam.Batch38.G9_transport_remains_open
#print axioms Nock.RedTeam.Batch38.paper_alias_remains_forest
