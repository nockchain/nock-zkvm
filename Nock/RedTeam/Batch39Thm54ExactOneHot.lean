/-
Exact execution-dependent `Def:one-hot`.

Paper frame:
* `Def:one-hot`: the paper.
* Nock specialization: the paper-1895.
* Consumed structural sentence: the paper.

Scope:
* This batch checks all five exact one-hot clauses, the top-level S3 type pin, and the strict
  package's same-configuration/same-execution specialization.
* Ten numeric opcodes and the separately typed structural `cons` action are preserved.
* Condition 4b's zero-OP_IO antecedent remains explicitly impossible; the padding half is checked
  separately.
* No conclusion is made here about S-e, G9, package residuals, R6, or alias closure.
-/

import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.SecondWave.RtAlias
import Nock.RedTeam.SecondWave.RtEasy
import Nock.RedTeam.Thm54P5Regression

namespace Nock.RedTeam.Batch39

open scoped BigOperators Classical

open Nock Nock.Framework Nock.NockVMROM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

local instance : CharP RTAlias.Z7 (ringChar RTAlias.Z7) := ringChar.charP RTAlias.Z7

/-! ## 1. The five paper conditions are fields of one exact realization -/

/-- Condition 1 receipt: active compute capacity, ten numeric boolean selectors, the separately
typed structural selector, and exactly one selected action on every exact compute row. -/
theorem b39_condition1_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    cfg.compRows ≤ 2 ^ cfg.orbit.h ∧
      (∀ (i : ExactComputeRow cfg) (op : Fin 10),
        numericSelector exec i op * (1 - numericSelector exec i op) = 0) ∧
      (∀ i : ExactComputeRow cfg,
        structuralConsSelector exec i * (1 - structuralConsSelector exec i) = 0) ∧
      (∀ i : ExactComputeRow cfg,
        (∑ op : Fin 10, numericSelector exec i op) +
          structuralConsSelector exec i = 1) := by
  let R := h.oneHotRealization
  exact ⟨R.condition1.h1_capacity, R.condition1.numeric_boolean,
    R.condition1.structural_boolean, R.condition1.exactly_one_action⟩

/-- Condition 2 receipt: active memory capacity, `Vmem` acceptance of every exact memory row,
its one exact eight-coordinate `pub.mem` representation, and one list element per active row.
This intentionally does not identify represented rows with the filtered external response list. -/
theorem b39_condition2_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    cfg.memRows ≤ 2 ^ cfg.orbit.h ∧
      (∀ i : ExactMemoryRow cfg,
        MemoryTable.Vmem cfg.challenges.memoryInputs (exactMemoryPubAt exec i)) ∧
      (∀ i : ExactMemoryRow cfg,
        memoryRecordAt exec i =
          NockVM.encRecC (exactMemoryPubAt exec i).mem
            (exactMemoryPubAt exec i).cprime) ∧
      (actualMemoryRecords exec).length = cfg.memRows ∧
      (actualEncodedMemoryRecords exec).length = cfg.memRows := by
  let R := h.oneHotRealization
  refine ⟨R.condition2.h2_capacity, R.condition2.row_verified,
    R.condition2.exact_record_representation, ?_, ?_⟩
  · simp [actualMemoryRecords]
  · simp [actualEncodedMemoryRecords]

/-- Condition 3 receipt: the IO vector is indexed by exactly three slots, the public request list
is the canonical nonzero-filtered extractor from those slots, and structural `recordCount` lies in
`[1,3]`.  No equality between `recordCount` and filtered-list length is asserted. -/
theorem b39_condition3_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    (∀ i : ExactComputeRow cfg,
      List.ofFn (computeRawIO exec i) = computeRawIOSlots exec i) ∧
      (∀ i : ExactComputeRow cfg, (computeRawIOSlots exec i).length = 3) ∧
      (∀ i : ExactComputeRow cfg,
        ComputeTable.requestRecords (exactComputePubAt exec i) =
          (computeRawIOSlots exec i).filter
            (fun r => decide
              (r ≠ (ComputeTable.MemRec.zero : ComputeTable.MemRec K)))) ∧
      (∀ i : ExactComputeRow cfg,
        1 ≤ recordCount (exactComputePubAt exec i).state) ∧
      (∀ i : ExactComputeRow cfg,
        recordCount (exactComputePubAt exec i).state ≤ 3) := by
  let R := h.oneHotRealization
  refine ⟨R.condition3.exact_slot_vector, ?_,
    R.condition3.canonical_request_extractor,
    R.condition3.recordCount_pos, R.condition3.recordCount_le_three⟩
  intro i
  simp [computeRawIOSlots]

/-- Condition 4 receipt: `OP_IO` is all eleven actions (ten numeric plus structural `cons`),
`regs` is the exact structural count, the zero-selector antecedent is impossible, and every raw
and encoded slot beyond that count is zero. -/
theorem b39_condition4_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    exactOPIO = Finset.univ ∧
      (∀ action : Fin 11, exactRegs action = recordCount (sfin action)) ∧
      (∀ i : ExactComputeRow cfg,
        ¬ (∑ action ∈ exactOPIO, actionSelector exec i action) = 0) ∧
      (∀ (i : ExactComputeRow cfg) (slot : Fin 3),
        recordCount (exactComputePubAt exec i).state ≤ (slot : ℕ) →
          computeRawIO exec i slot = ComputeTable.MemRec.zero) ∧
      (∀ (i : ExactComputeRow cfg) (slot : Fin 3),
        recordCount (exactComputePubAt exec i).state ≤ (slot : ℕ) →
          ∀ c : Fin 9, computeIO exec i slot c = 0) := by
  let R := h.oneHotRealization
  exact ⟨R.condition4.opIO_all, R.condition4.regs_exact,
    R.condition4.no_zero_opIO_antecedent,
    R.condition4.extra_raw_slots_zero, R.condition4.extra_encoded_slots_zero⟩

/-- Condition 5 receipt: emitted responses fit the memory-row capacity and each raw/encoded
response has an exact `ver = true` row witness.  The final conjunct records the
derived encoded subset of all actual memory-row representations. -/
theorem b39_condition5_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    exec.rawResponses.length ≤ cfg.memRows ∧
      (∀ r ∈ exec.rawResponses,
        ∃ i : ExactMemoryRow cfg,
          (exactMemoryPubAt exec i).ver = true ∧
            r = (exactMemoryPubAt exec i).mem ∧
            r ∈ actualMemoryRecords exec) ∧
      (∀ r ∈ exec.derivedResponseIO,
        ∃ i : ExactMemoryRow cfg,
          (exactMemoryPubAt exec i).ver = true ∧
            r = memoryRecordAt exec i ∧
            (exactMemoryPubAt exec i).mem ∈ actualMemoryRecords exec) ∧
      exec.derivedResponseIO ⊆ actualEncodedMemoryRecords exec := by
  let R := h.oneHotRealization
  exact ⟨R.condition5.response_capacity, R.condition5.raw_responses_in_place,
    R.condition5.encoded_responses_in_place,
    R.derivedResponseIO_subset_actualEncodedMemoryRecords⟩

/-! ## 2. Non-vacuity: inhabited row domains and a concrete exact execution -/

/-- Positivity fields in every `ExactConfig` make both separately tagged row domains inhabited. -/
theorem b39_exact_row_domains_are_nonempty
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) :
    Nonempty (ExactComputeRow cfg) ∧ Nonempty (ExactMemoryRow cfg) :=
  exactRowDomains_nonempty cfg

/-- This
separates "the theorem ranges over all exact executions" from "there exists a real antecedent." -/
theorem b39_universal_claim_fires_on_concrete_execution :
    ChainedSemanticExactLanguage
        Nock.RedTeam.Thm54P5Regression.p3Cfg
        Nock.RedTeam.Thm54P5Regression.p3Exec ∧
      OneHotRealization
        Nock.RedTeam.Thm54P5Regression.p3Cfg
        Nock.RedTeam.Thm54P5Regression.p3Exec :=
  ⟨Nock.RedTeam.Thm54P3Nonvacuity.production_chained,
    exactChainedOneHot
      Nock.RedTeam.Thm54P5Regression.K17
      Nock.RedTeam.Thm54P5Regression.K17
      Nock.RedTeam.Thm54P5Regression.p3Cfg
      Nock.RedTeam.Thm54P5Regression.p3Exec
      Nock.RedTeam.Thm54P3Nonvacuity.production_chained⟩

theorem b39_concrete_execution_receipt :
    (Nonempty
        (ExactComputeRow Nock.RedTeam.Thm54P5Regression.p3Cfg) ∧
      Nonempty
        (ExactMemoryRow Nock.RedTeam.Thm54P5Regression.p3Cfg)) ∧
      OneHotRealization
        Nock.RedTeam.Thm54P5Regression.p3Cfg
        Nock.RedTeam.Thm54P5Regression.p3Exec ∧
      Nock.RedTeam.Thm54P5Regression.p3Exec.rawResponses =
        [Nock.RedTeam.Thm54P2Nonvacuity.rowRecord] :=
  ⟨Nock.RedTeam.Thm54P5Regression.production_row_domains_nonempty,
    Nock.RedTeam.Thm54P5Regression.productionRealization,
    Nock.RedTeam.Thm54P5Regression.production_raw_response_singleton⟩

/-! ## 3. -/

/-- The old empty-row witness transported onto the genuine Nock S1 index. -/
@[reducible] noncomputable def b39_transported_legacy_oneHot :
    @OpcodeMemoryOneHot RTAlias.T7 _ (nmrMEF RTAlias.Z7 RTAlias.Z7) RTAlias.Z7 _
      10 3 (nock_uniqueMES RTAlias.Z7 RTAlias.Z7 0 1 1) :=
  RTNew.n5_oneHot_transport
    (S₁ := RTAlias.fakeMES)
    (S₂ := nock_uniqueMES RTAlias.Z7 RTAlias.Z7 0 1 1)
    RTAlias.fakeOneHot

theorem b39_legacy_empty_row_controls_remain :
    RTAlias.fakeOneHot.Row = Empty ∧
      b39_transported_legacy_oneHot.Row = Empty :=
  ⟨rfl, rfl⟩

abbrev B39LegacyClaim : Prop :=
  Nonempty
    (@OpcodeMemoryOneHot RTAlias.T7 _ (nmrMEF RTAlias.Z7 RTAlias.Z7) RTAlias.Z7 _
      10 3 (nock_uniqueMES RTAlias.Z7 RTAlias.Z7 0 1 1))

/-- A bundle whose explicit S3 claim is arbitrary `True`.  It remains constructible at that
different proposition and is used below as a negative type-boundary control. -/
@[reducible] noncomputable def b39_true_S3_bundle :
    VerifiableVMCompilation RTAlias.T7 (nmrMEF RTAlias.Z7 RTAlias.Z7) RTAlias.Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
      (ExactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
      (exactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
      (ExactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
      (exactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
      (ExactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
      (exactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
      (nock_uniqueMES RTAlias.Z7 RTAlias.Z7 0 1 1)
      (ExactChainedHasCanonicalRAP2 RTAlias.Z7 RTAlias.Z7)
      (exactChainedHasCanonicalRAP2 RTAlias.Z7 RTAlias.Z7)
      True trivial
      (ExactDefTraversable RTAlias.Z7 RTAlias.Z7)
      (exactDefTraversable RTAlias.Z7 RTAlias.Z7)
      (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) :=
  ⟨⟩

@[reducible] noncomputable def b39_legacy_S3_bundle :
    VerifiableVMCompilation RTAlias.T7 (nmrMEF RTAlias.Z7 RTAlias.Z7) RTAlias.Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
      (ExactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
      (exactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
      (ExactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
      (exactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
      (ExactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
      (exactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
      (nock_uniqueMES RTAlias.Z7 RTAlias.Z7 0 1 1)
      (ExactChainedHasCanonicalRAP2 RTAlias.Z7 RTAlias.Z7)
      (exactChainedHasCanonicalRAP2 RTAlias.Z7 RTAlias.Z7)
      B39LegacyClaim ⟨b39_transported_legacy_oneHot⟩
      (ExactDefTraversable RTAlias.Z7 RTAlias.Z7)
      (exactDefTraversable RTAlias.Z7 RTAlias.Z7)
      (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) :=
  ⟨⟩

/-- Exact consumed-capstone attack. -/
theorem b39_real_capstone_rejects_weak_S3_substitutions :
    VerifiableVMCompilation RTAlias.T7 (nmrMEF RTAlias.Z7 RTAlias.Z7) RTAlias.Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
      (ExactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
      (exactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
      (ExactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
      (exactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
      (ExactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
      (exactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
      (nock_uniqueMES RTAlias.Z7 RTAlias.Z7 0 1 1)
      (ExactChainedHasCanonicalRAP2 RTAlias.Z7 RTAlias.Z7)
      (exactChainedHasCanonicalRAP2 RTAlias.Z7 RTAlias.Z7)
      (ExactChainedOneHot RTAlias.Z7 RTAlias.Z7)
      (exactChainedOneHot RTAlias.Z7 RTAlias.Z7)
      (ExactDefTraversable RTAlias.Z7 RTAlias.Z7)
      (exactDefTraversable RTAlias.Z7 RTAlias.Z7)
      (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) := by
  fail_if_success
    exact b39_true_S3_bundle
  fail_if_success
    exact b39_legacy_S3_bundle
  fail_if_success
    exact RTAlias.fakeThm54
  exact NockVMROM_Thm54_structural RTAlias.Z7 RTAlias.Z7 0 1 1

/-! ## 4. Strict consumers pin one configuration, one dependent execution, and one proof -/

/-- Both strict structural consumers elaborate only with
`OneHotRealization P.objects.cfg P.objects.exec` and the proof
`P.chained.oneHotRealization`.  This is the execution-specialized S3, not the detached universal
implication used by the top-level field-generic capstone. -/
theorem b39_strict_consumers_pin_same_exact_S3
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : StrictNockVMROMPackage F K hOrb q Λ) :
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
        ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩) :=
  ⟨P.structural, (strictNockVMROM_of_package P).structural⟩

/-- Direct attacks on the strict S3 proposition.  An arbitrary `True` proof, a realization at a
different configuration, and a realization at a different dependent execution cannot be supplied
where the package requires its exact `cfg` and `exec`. -/
theorem b39_strict_S3_rejects_true_wrong_cfg_wrong_exec
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : StrictNockVMROMPackage F K hOrb q Λ)
    {cfg' : ExactConfig F K} (exec' : ExactExecution cfg')
    (_wrongCfg : OneHotRealization cfg' exec')
    (exec'' : ExactExecution P.objects.cfg)
    (_wrongExec : OneHotRealization P.objects.cfg exec'') : True := by
  fail_if_success
    have _bad : OneHotRealization P.objects.cfg P.objects.exec := trivial
  fail_if_success
    have _bad : OneHotRealization P.objects.cfg P.objects.exec := _wrongCfg
  fail_if_success
    have _bad : OneHotRealization P.objects.cfg P.objects.exec := _wrongExec
  exact True.intro

/-- The strict package's actual chained witness directly supplies the exact S3 proposition, proving
that the preceding expected failures are type discrimination rather than target emptiness. -/
theorem b39_strict_exact_S3_positive
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : StrictNockVMROMPackage F K hOrb q Λ) :
    OneHotRealization P.objects.cfg P.objects.exec :=
  P.chained.oneHotRealization

end

end Nock.RedTeam.Batch39

#print axioms Nock.NockVMROM.Thm54.ChainedSemanticExactLanguage.oneHotRealization
#print axioms Nock.NockVMROM.Thm54.exactChainedOneHot
#print axioms Nock.NockVMROM.NockVMROM_Thm54_structural
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.structural
#print axioms Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package
#print axioms Nock.RedTeam.Batch39.b39_condition1_fields
#print axioms Nock.RedTeam.Batch39.b39_condition2_fields
#print axioms Nock.RedTeam.Batch39.b39_condition3_fields
#print axioms Nock.RedTeam.Batch39.b39_condition4_fields
#print axioms Nock.RedTeam.Batch39.b39_condition5_fields
#print axioms Nock.RedTeam.Batch39.b39_exact_row_domains_are_nonempty
#print axioms Nock.RedTeam.Batch39.b39_universal_claim_fires_on_concrete_execution
#print axioms Nock.RedTeam.Batch39.b39_concrete_execution_receipt
#print axioms Nock.RedTeam.Batch39.b39_transported_legacy_oneHot
#print axioms Nock.RedTeam.Batch39.b39_legacy_empty_row_controls_remain
#print axioms Nock.RedTeam.Batch39.b39_true_S3_bundle
#print axioms Nock.RedTeam.Batch39.b39_legacy_S3_bundle
#print axioms Nock.RedTeam.Batch39.b39_real_capstone_rejects_weak_S3_substitutions
#print axioms Nock.RedTeam.Batch39.b39_strict_consumers_pin_same_exact_S3
#print axioms Nock.RedTeam.Batch39.b39_strict_S3_rejects_true_wrong_cfg_wrong_exec
#print axioms Nock.RedTeam.Batch39.b39_strict_exact_S3_positive
