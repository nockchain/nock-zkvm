/-
  Theorem 5.4 structural parameters.

  Paper frame:
  * Def:MES: the paper.
  * Def:Canonical_RAP: the paper.
  * Def:one-hot: the paper.
  * Def:traversable: the paper.
  * Consumed theorem: the paper especially 1450-1451.

  The later S-b hygiene parameter
  excludes G2's empty-language countermodel; semantic S-c/S-d/S-e remain separate.
-/

import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.SecondWave.RtAlias
import Nock.RedTeam.SecondWave.RtEasy
import Nock.RedTeam.SecondWave.RtMore
import Nock.RedTeam.SecondWave.AtkPackage

namespace Nock.RedTeam.Batch36

open Nock Nock.Framework Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

local instance : CharP RTAlias.Z7 (ringChar RTAlias.Z7) := ringChar.charP RTAlias.Z7

/-! ## 1. Exact consumed-capstone attacks

`b36_real_capstone_rejects_fake_substitutions` has the exact type of
`NockVMROM_Thm54_structural (ZMod 7) (ZMod 7) 0 1 1`.  Each `fail_if_success` is an expected
elaboration mismatch, followed by a positive inhabitant of the exact real target.

The attacks include:
* all five fake S1--S4 values together;
* only fake S2, with genuine S1/S3/S4;
* fake S3 transported onto the genuine S1 index (so the test does not rely merely on S3's original
  dependency on `fakeMES`);
* the coherent fake dependent group S1/S3/S4 while retaining genuine S2.
-/
theorem b36_real_capstone_rejects_fake_substitutions :
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
  -- Full G1 witness: all five fake values no longer have the exact real capstone type.
  fail_if_success
    exact RTAlias.fakeThm54
  -- Partial substitution: fake S2 alone.
  fail_if_success
    exact
      (show
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
          True trivial
          (ExactChainedOneHot RTAlias.Z7 RTAlias.Z7)
          (exactChainedOneHot RTAlias.Z7 RTAlias.Z7)
          (ExactDefTraversable RTAlias.Z7 RTAlias.Z7)
          (exactDefTraversable RTAlias.Z7 RTAlias.Z7)
          (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) from
        ⟨⟩)
  -- Partial substitution: S3 can still be transported to the genuine S1 type, but the transported
  -- value is a distinct explicit index and therefore does not preserve the real capstone type.
  fail_if_success
    exact
      (show
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
          (RTNew.n5_oneHot_transport
            (S₁ := RTAlias.fakeMES)
            (S₂ := nock_uniqueMES RTAlias.Z7 RTAlias.Z7 0 1 1)
            RTAlias.fakeOneHot)
          trivial
          (ExactDefTraversable RTAlias.Z7 RTAlias.Z7)
          (exactDefTraversable RTAlias.Z7 RTAlias.Z7)
          (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) from
        ⟨⟩)
  -- Partial coherent dependent substitution: fake S1/S3/traversal data/traversability, real S2.
  fail_if_success
    exact
      (show
        VerifiableVMCompilation RTAlias.T7 (nmrMEF RTAlias.Z7 RTAlias.Z7) RTAlias.Z7 10 3
          (ProductionP8Containment.ExactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
          (ProductionP8Containment.exactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
          (ExactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
          (exactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
          (ExactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
          (exactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
          (ExactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
          (exactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
          RTAlias.fakeMES
          (ExactChainedHasCanonicalRAP2 RTAlias.Z7 RTAlias.Z7)
          (exactChainedHasCanonicalRAP2 RTAlias.Z7 RTAlias.Z7)
          True trivial True trivial
          (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) from
        ⟨⟩)
  exact NockVMROM_Thm54_structural RTAlias.Z7 RTAlias.Z7 0 1 1

/-! ## 2. Prop/value-boundary receipt

The `theorem` declaration above can only target a proposition, so it machine-checks that this
instantiation of `VerifiableVMCompilation` is `Prop`.  The checks below additionally ensure the old
S1--S4 field projections are absent.  S1--S4 can only be selected as constructor/type parameters.
-/
theorem b36_old_structural_field_projections_are_absent : True := by
  fail_if_success
    have _oldUniqueMES := VerifiableVMCompilation.uniqueMES
  fail_if_success
    have _oldCanonicalRAP := VerifiableVMCompilation.canonicalRAP
  fail_if_success
    have _oldOneHot := VerifiableVMCompilation.oneHot
  fail_if_success
    have _oldTraversalModel := VerifiableVMCompilation.traversalModel
  fail_if_success
    have _oldTraversable := VerifiableVMCompilation.traversable
  fail_if_success
    have _oldTwoRAP := VerifiableVMCompilation.twoRAP
  trivial

/-! ## 3. Exact StrictPackage threading

Both the package projection and the final conditional consumer have exactly the same five Nock
objects, all read from the one shared package configuration.  No independently quantified S1--S4
objects occur in either result type.
-/
theorem b36_strict_consumers_pin_same_structural_objects
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
        ⟨⟨Nock.NockVMROM.Thm54.stmtOfExact P.objects.cfg P.objects.exec,
          P.perfect_completeness⟩⟩) ∧
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
        ⟨⟨Nock.NockVMROM.Thm54.stmtOfExact P.objects.cfg P.objects.exec,
          P.perfect_completeness⟩⟩) :=
  ⟨P.structural, (strictNockVMROM_of_package P).structural⟩

/-! ## 4. G9 transport attack

The old component-level VM/MEF/field-agnostic transport still exists; S-a does not pretend
otherwise.  But a transported/empty-language bundle has a different dependent proposition and
cannot inhabit the exact real Nock capstone type.
-/
theorem b36_g9_component_transport_still_exists :
    HasConcreteSoundness RTBundle.RejVM
      (RTMore.n11_sound_transport (ι₂ := RTBundle.RejVM)
        (nockConcreteSoundness (ZMod 7) (ZMod 7) 0 1 1)) :=
  RTMore.n11_nock_sound_model_on_other_vm RTBundle.RejVM

/-- The former walk-only S7 proposition remains a compiled diagnostic API. -/
abbrev LegacyWalkOnlyS7Claim : Prop :=
  HasConcreteSoundness RTAlias.T7
    (nockConcreteSoundness.{0, 1, 0, 0} RTAlias.Z7 RTAlias.Z7 0 1 1)

abbrev TransportedLegacyS7Claim : Prop :=
  HasConcreteSoundness RTAlias.T7
    (RTMore.n11_sound_transport (ι₂ := RTAlias.T7)
      (nockConcreteSoundness.{0, 1, 0, 0} RTAlias.Z7 RTAlias.Z7 0 1 1))

/-- Change only S7 while fixing every other parameter to the real capstone objects. -/
@[reducible] noncomputable def b36_alternateS7Bundle (C : Prop) (c : C) :
    VerifiableVMCompilation RTAlias.T7 (nmrMEF RTAlias.Z7 RTAlias.Z7) RTAlias.Z7 10 3
      C c
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
      (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) :=
  ⟨⟩

theorem b36_g9_transport_does_not_preserve_exact_real_capstone :
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
    exact b36_alternateS7Bundle LegacyWalkOnlyS7Claim
      (nock_hasConcreteSoundness RTAlias.Z7 RTAlias.Z7 0 1 1)
  fail_if_success
    exact b36_alternateS7Bundle TransportedLegacyS7Claim
      (RTMore.n11_nock_sound_model_on_other_vm RTAlias.T7)
  fail_if_success
    exact RTAlias.fakeThm54
  exact NockVMROM_Thm54_structural RTAlias.Z7 RTAlias.Z7 0 1 1

/-! ## 5. Vacuity scope

S-a itself added no substantive premise whose satisfiability could be witnessed: it changed the
indices of an already-inhabited proposition.  S-b subsequently added the explicit
`LanguageInhabited` hygiene parameter.  The exact Nock witness is positive above, while `RejVM`
cannot supply the parameter.
-/
theorem b36_g2_empty_language_residual_is_excluded :
    ¬ LanguageInhabited RTBundle.RejVM :=
  RTBundle.rej_languageInhabited_false

end

end Nock.RedTeam.Batch36

#print axioms Nock.RedTeam.Batch36.b36_real_capstone_rejects_fake_substitutions
#print axioms Nock.RedTeam.Batch36.b36_old_structural_field_projections_are_absent
#print axioms Nock.RedTeam.Batch36.b36_strict_consumers_pin_same_structural_objects
#print axioms Nock.RedTeam.Batch36.b36_g9_component_transport_still_exists
#print axioms Nock.RedTeam.Batch36.b36_g9_transport_does_not_preserve_exact_real_capstone
#print axioms Nock.RedTeam.Batch36.b36_g2_empty_language_residual_is_excluded
