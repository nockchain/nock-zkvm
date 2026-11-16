import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.Batch12Thm54Independent
import Nock.RedTeam.SecondWave.RtAlias
import Nock.RedTeam.Thm54P6Regression

/-!
# Exact `Def:traversable`

Paper frame:
* `Def:traversable`, the paper, requires bijections from the complete accepted compute
  and memory sublanguages to products of RVT languages.
* The Nock specialization uses that definition at the paper, `1358`, and `1497`.
* Theorem 5.4 consumes traversability at the paper.

It makes no overall Theorem 5.4 or
paper-alias claim.
-/

namespace Nock.RedTeam.Batch40

open scoped Classical

open Nock Nock.Framework Nock.Walk Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

/-! ## 1. Exact accepted-language sources carry fixed production semantics -/

/-- The source subtypes are the complete accepted public row languages.  Compute acceptance
existentially carries aligned `Dec` rows and a one-root structural witness; memory acceptance
carries the configured nonempty forest and checks every public row. -/
theorem b40_exact_accepted_source_types
    (F K : Type) [Field F] [Field K] [Algebra F K] (cfg : ExactConfig F K) :
    ComputePublicAcceptedLanguage K =
        {rows : List (ComputePublicLabel K) //
          Nonempty (ComputePublicRowsAcceptedWitness rows)} ∧
      MemoryPublicAcceptedLanguage cfg =
        {rows : List (MemoryTable.MState × MemoryTable.DTmem K) //
          Nonempty (MemoryPublicRowsForestWitness cfg rows) ∧
            rows.Forall MemoryPublicRowAccepted} :=
  ⟨rfl, rfl⟩

/-- Acceptance is not mere tree structure: its nodewise compute predicate contains the fixed
production verifier `Vcomp`, and its memory predicate contains the fixed production verifier
`Vmem`. -/
theorem b40_row_acceptance_is_fixed_Vcomp_Vmem
    {K : Type} [Field K]
    (crow : ComputePublicLabel K) (dec : ComputeTable.Dec K)
    (mrow : MemoryTable.MState × MemoryTable.DTmem K) :
    (ComputePublicRowAccepted crow dec ↔
        crow.1 = crow.2.2.state ∧ ComputeTable.Vcomp crow.2.1 crow.2.2 dec) ∧
      (MemoryPublicRowAccepted mrow ↔
        mrow.1 = mrow.2.2.st ∧ MemoryTable.Vmem mrow.2.1 mrow.2.2) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- `Dec` is proof-side existential data.  The public statement is exactly the list of
`State × (Inputs × Pub)` rows; acceptance chooses the aligned `Dec` list and structural tree. -/
theorem b40_Dec_is_existential_witness_not_statement
    {K : Type} [Field K] (x : ComputePublicAcceptedLanguage K) :
    ∃ decs : List (ComputeTable.Dec K),
      decs.length = x.1.length ∧
        List.Forall₂ ComputePublicRowAccepted x.1 decs ∧
        Nonempty (ComputePublicRowsTreeWitness x.1 decs) := by
  let w := x.acceptedWitness
  exact ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩

/-- Different private `Dec`/tree witnesses cannot change public statement identity. -/
theorem b40_Dec_witnesses_do_not_change_statement
    {K : Type} [Field K] (rows : List (ComputePublicLabel K))
    (w₁ w₂ : ComputePublicRowsAcceptedWitness rows) :
    (⟨rows, ⟨w₁⟩⟩ : ComputePublicAcceptedLanguage K) =
      (⟨rows, ⟨w₂⟩⟩ : ComputePublicAcceptedLanguage K) :=
  computePublicAccepted_eq_of_private_witnesses rows w₁ w₂

/-! ## 2. Exact product factors, arities, and all inverse laws -/

/-- The compute target has exactly one factor and exact arity three; the memory target has exactly
`cfg.kMem` factors and exact arity two. -/
theorem b40_exact_product_factors_and_arities
    (F K : Type) [Field F] [Field K] [Algebra F K] (cfg : ExactConfig F K) :
    ComputePublicExactRVTProduct K =
        (Π _ : Fin 1,
          {t : NTree (ComputePublicLabel K) //
            ∃ witnessTree : NTree (ComputeTable.State × ComputeTable.DTcomp K),
              ComputeTreeWitnessAligned t witnessTree ∧
                (RVT (ComputeTable.Fcomp (K := K)) witnessTree ∧
                  ProperArity 3 witnessTree)}) ∧
      MemoryExactRVTProduct cfg =
        (Π _ : Fin cfg.kMem,
          {t : NTree (MemoryTable.MState × MemoryTable.DTmem K) //
            RVT (MemoryTable.Fmem (K := K)) t ∧ ProperArity 2 t}) :=
  ⟨rfl, rfl⟩

/-- Projecting all three realization fields exposes genuine `Equiv`s and both inverse laws at
their exact source and target types. -/
theorem b40_all_realization_fields_have_both_inverse_laws
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (R : DefTraversableRealization cfg) :
    (∃ e : ComputePublicAcceptedLanguage K ≃ ComputePublicExactRVTProduct K,
        (∀ x, e.symm (e x) = x) ∧ (∀ y, e (e.symm y) = y)) ∧
      (∃ e : MemoryPublicAcceptedLanguage cfg ≃ MemoryExactRVTProduct cfg,
        (∀ x, e.symm (e x) = x) ∧ (∀ y, e (e.symm y) = y)) ∧
      (∃ e : PacketLocalPublicAcceptedLanguage cfg ≃ PacketLocalExactRVTProducts cfg,
        (∀ x, e.symm (e x) = x) ∧ (∀ y, e (e.symm y) = y)) := by
  rcases R.compute with ⟨ec⟩
  rcases R.memory with ⟨em⟩
  rcases R.paired with ⟨ep⟩
  exact
    ⟨⟨ec, ec.left_inv, ec.right_inv⟩,
      ⟨em, em.left_inv, em.right_inv⟩,
      ⟨ep, ep.left_inv, ep.right_inv⟩⟩

/-- The paired field does not overstrengthen the paper's two existential bijections: it is
derivable from the compute and memory fields by the product equivalence. -/
theorem b40_realization_iff_two_component_bijections
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) :
    DefTraversableRealization cfg ↔
      Nonempty (ComputePublicAcceptedLanguage K ≃ ComputePublicExactRVTProduct K) ∧
        Nonempty (MemoryPublicAcceptedLanguage cfg ≃ MemoryExactRVTProduct cfg) := by
  constructor
  · intro R
    exact ⟨R.compute, R.memory⟩
  · rintro ⟨⟨ec⟩, ⟨em⟩⟩
    exact ⟨⟨ec⟩, ⟨em⟩, ⟨Equiv.prodCongr ec em⟩⟩

/-- At zero memory roots the accepted memory source is empty while the raw `Fin 0` target product
is inhabited, so no equivalence—and hence no exact realization—can exist. -/
theorem b40_zero_kMem_rejects_exact_realization
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) (hk : cfg.kMem = 0) :
    ¬ DefTraversableRealization cfg := by
  intro R
  exact no_memoryPublicTraversalEquiv_of_kMem_eq_zero cfg hk R.memory

/-! ## 3. Concrete ZMod-17 nonvacuity and bad-structure controls -/

namespace P6

open Nock.RedTeam.Thm54P6Regression

abbrev cfg := Nock.RedTeam.Thm54P3Nonvacuity.cfg
abbrev exec := Nock.RedTeam.Thm54P3Nonvacuity.exec
abbrev K17 := Nock.RedTeam.Thm54P6Regression.K17

theorem b40_concrete_sources_products_and_realization_nonempty :
    Nonempty (ComputePublicAcceptedLanguage K17) ∧
      Nonempty (MemoryPublicAcceptedLanguage cfg) ∧
      Nonempty (ComputePublicExactRVTProduct K17) ∧
      Nonempty (MemoryExactRVTProduct cfg) ∧
      DefTraversableRealization cfg :=
  ⟨⟨productionComputePublicAccepted⟩, ⟨productionMemoryPublicAccepted⟩,
    ⟨productionComputePublicRVTProduct⟩, ⟨productionMemoryRVTProduct⟩,
    defTraversableRealization cfg exec.memoryRootCount_pos⟩

/-- The concrete compute, memory, and paired maps all satisfy their exact round trips. -/
theorem b40_concrete_exact_roundtrips :
    (computePublicTraversalEquiv K17).symm productionComputePublicRVTProduct =
        productionComputePublicAccepted ∧
      (memoryPublicTraversalEquiv cfg exec.memoryRootCount_pos).symm
          productionMemoryRVTProduct = productionMemoryPublicAccepted ∧
      (packetLocalDefTraversableEquiv cfg exec.memoryRootCount_pos).symm
          productionPacketLocalRVTProducts = productionPublicAcceptedComponents :=
  ⟨production_inverse_roundtrips.1, production_inverse_roundtrips.2,
    production_packet_local_roundtrip⟩

/-- Verifier-free leaf structure is insufficient on both sides: the concrete bad rows possess
valid structural witnesses but fail the fixed `Vcomp`/`Vmem` acceptance predicates. -/
theorem b40_bad_structure_is_not_accepted :
    Nonempty (ComputePublicRowsTreeWitness badComputeRows
        [Nock.RedTeam.Thm54P2Nonvacuity.cDec]) ∧
      ¬ ComputePublicRowsAccepted badComputeRows ∧
      Nonempty (MemoryPublicRowsForestWitness cfg badMemoryRows) ∧
      ¬ MemoryPublicRowsAccepted cfg badMemoryRows :=
  ⟨badComputeStructuralWitness, badComputeRows_not_accepted,
    badMemoryStructuralWitness, badMemoryRows_not_accepted⟩

end P6

/-! ## 4. -/

abbrev Z7 := RTAlias.Z7
abbrev T7 := RTAlias.T7

local instance : CharP Z7 (ringChar Z7) := ringChar.charP Z7

/-- The exact concrete Layer-1 type used for all S4 substitution attacks. -/
abbrev B40ExactCapstoneZ7 : Prop :=
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

/-- The all-`True` S4 claim still builds at its own explicit proposition type. -/
@[reducible] def b40_true_S4_bundle :
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
      True trivial
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

abbrev B40FakeLegacyTraversalClaim : Prop :=
  Nonempty
    (@IsTraversable T7 (inferInstance : VMSystem T7) (nmrMEF Z7 Z7)
      RTAlias.fakeTM RTAlias.fakeMES)

@[reducible] def b40_fake_legacy_S4_bundle :
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
      B40FakeLegacyTraversalClaim ⟨RTAlias.fakeTraversable⟩
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

abbrev B40SingletonLegacyTraversalClaim : Prop :=
  Nonempty
    (@IsTraversable T7 (inferInstance : VMSystem T7) (nmrMEF Z7 Z7)
      (nock_traversalModel Z7 Z7 0 1 1) (nock_uniqueMES Z7 Z7 0 1 1))

@[reducible] def b40_singleton_legacy_S4_bundle :
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
      B40SingletonLegacyTraversalClaim ⟨nock_isTraversable Z7 Z7 0 1 1⟩
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

theorem b40_singleton_readout_control_remains :
    ∃ (ps : (nock_uniqueMES ℚ ℚ 0 1 1).ProgStatement)
      (pw : (nock_uniqueMES ℚ ℚ 0 1 1).ProgWitness)
      (io : (nock_uniqueMES ℚ ℚ 0 1 1).ProgIO),
      (nock_uniqueMES ℚ ℚ 0 1 1).computeAccepts ps pw io ∧
        ∀ lbl : (nock_traversalModel ℚ ℚ 0 1 1).ComputeLabel,
          ((nock_isTraversable ℚ ℚ 0 1 1).computeReadout lbl).1 ≠ ps :=
  Nock.RedTeam.b12_s4_accepted_not_in_readout

theorem b40_real_capstone_rejects_weak_S4_substitutions :
    B40ExactCapstoneZ7 := by
  fail_if_success
    exact b40_true_S4_bundle
  fail_if_success
    exact b40_fake_legacy_S4_bundle
  fail_if_success
    exact b40_singleton_legacy_S4_bundle
  exact NockVMROM_Thm54_structural Z7 Z7 0 1 1

/-! ## 5. Strict cfg-only scope: correct language-level strength, with root-count pinning -/

/-- A concrete wrong configuration for S4 changes the paper-relevant memory-product factor count. -/
def cfgWithExtraMemoryRoot
    {F K : Type} [Field F] [Field K] [Algebra F K] (cfg : ExactConfig F K) :
    ExactConfig F K :=
  { cfg with kMem := cfg.kMem + 1 }

/-- The wrong configuration is itself positive-root and therefore has its own exact realization. -/
def extraRootRealization
    {F K : Type} [Field F] [Field K] [Algebra F K] (cfg : ExactConfig F K) :
    DefTraversableRealization (cfgWithExtraMemoryRoot cfg) :=
  defTraversableRealization _ (by simp [cfgWithExtraMemoryRoot])

/-- A realization whose memory product has one extra factor cannot directly inhabit the strict
claim at `P.objects.cfg`.  `True` is rejected there as well. -/
theorem b40_strict_S4_rejects_true_and_wrong_cfg
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    DefTraversableRealization P.objects.cfg := by
  fail_if_success
    have _bad : DefTraversableRealization P.objects.cfg := trivial
  fail_if_success
    have _bad : DefTraversableRealization P.objects.cfg :=
      extraRootRealization P.objects.cfg
  exact defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos

/-- Both strict consumers pin the same cfg-only exact S4 proposition and canonical proof. -/
theorem b40_strict_consumers_pin_same_cfg_only_S4
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
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

/-- `Def:traversable` is a language/configuration property, not a property of
one selected execution.  Any exact execution at the same cfg contributes only the proof that the
memory-root count is positive; no wrong-exec rejection is demanded or encoded. -/
theorem b40_any_same_cfg_execution_contributes_only_memoryRootCount_pos
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec₁ exec₂ : ExactExecution cfg) :
    (0 < cfg.kMem ∧ DefTraversableRealization cfg) ∧
      (0 < cfg.kMem ∧ DefTraversableRealization cfg) :=
  ⟨⟨exec₁.memoryRootCount_pos,
      defTraversableRealization cfg exec₁.memoryRootCount_pos⟩,
    ⟨exec₂.memoryRootCount_pos,
      defTraversableRealization cfg exec₂.memoryRootCount_pos⟩⟩

end

end Nock.RedTeam.Batch40

#print axioms Nock.RedTeam.Batch40.b40_exact_accepted_source_types
#print axioms Nock.RedTeam.Batch40.b40_row_acceptance_is_fixed_Vcomp_Vmem
#print axioms Nock.RedTeam.Batch40.b40_Dec_is_existential_witness_not_statement
#print axioms Nock.RedTeam.Batch40.b40_Dec_witnesses_do_not_change_statement
#print axioms Nock.RedTeam.Batch40.b40_exact_product_factors_and_arities
#print axioms Nock.RedTeam.Batch40.b40_all_realization_fields_have_both_inverse_laws
#print axioms Nock.RedTeam.Batch40.b40_realization_iff_two_component_bijections
#print axioms Nock.RedTeam.Batch40.b40_zero_kMem_rejects_exact_realization
#print axioms Nock.RedTeam.Batch40.P6.b40_concrete_sources_products_and_realization_nonempty
#print axioms Nock.RedTeam.Batch40.P6.b40_concrete_exact_roundtrips
#print axioms Nock.RedTeam.Batch40.P6.b40_bad_structure_is_not_accepted
#print axioms Nock.RedTeam.Batch40.b40_singleton_readout_control_remains
#print axioms Nock.RedTeam.Batch40.b40_real_capstone_rejects_weak_S4_substitutions
#print axioms Nock.RedTeam.Batch40.b40_strict_S4_rejects_true_and_wrong_cfg
#print axioms Nock.RedTeam.Batch40.b40_strict_consumers_pin_same_cfg_only_S4
#print axioms Nock.RedTeam.Batch40.b40_any_same_cfg_execution_contributes_only_memoryRootCount_pos
