/-
  Top-level language inhabitation hygiene.

  Paper/frame scope:
  * `Def:MES` defines a language by existence of a trace but does not require
    that language to be nonempty.
  * The NockVMROM recognizer is the conjunction at the paper.
  * The consumed structural sentence is Theorem 5.4 at the paper.

  This file makes no claim that it is a clause of `Def:MES`, and does
  not close S-c/S-d/S-e, G9, the strict-package residuals, or the paper alias.
-/

import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.Batch36Thm54StructuralParameters
import Nock.RedTeam.SecondWave.AtkPackage

namespace Nock.RedTeam.Batch37

open Nock Nock.Framework Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

local instance : CharP RTAlias.Z7 (ringChar RTAlias.Z7) := ringChar.charP RTAlias.Z7

/-! ## 1. Positive top-level recognizer witnesses -/

/-- At every positive bound, the witness inhabits the top-level `Language (Tag...)`, not merely
one of the compute or memory sub-verifiers. -/
theorem b37_generic_positive_top_level
    (F K : Type) [Field F] [Field K] (α β : K) {Ksz : ℕ} (hKsz : 1 ≤ Ksz) :
    LanguageInhabited (Tag F K α β Ksz) := by
  refine ⟨⟨⟨[], []⟩, ?_⟩⟩
  exact language_nonempty F K α β hKsz
    (0, ((0, 0, 0), (0, 0, 0)), 0)

/-- Concrete real-field receipt at `ZMod 7`: the empty-table statement is a member of the exact
top-level NockVMROM language at `Ksz = 1`. -/
theorem b37_z7_top_level_member :
    Language RTAlias.T7 (⟨[], []⟩ : Stmt RTAlias.Z7 RTAlias.Z7) :=
  language_nonempty RTAlias.Z7 RTAlias.Z7 0 1 (le_refl 1) RTAlias.r0

/-- Unfolding the preceding top-level member yields one witness satisfying all three conjuncts of
the named recognizer: compute, memory, and shared `L_mIO`. -/
theorem b37_z7_concrete_recognizer_witness :
    ∃ w : Wit RTAlias.Z7 RTAlias.Z7,
      ComputeTableAccepts ([] : List
        (ComputeTable.Inputs RTAlias.Z7 × ComputeTable.Pub RTAlias.Z7)) w.computeDec ∧
      MemoryTableAccepts ([] : List
        (MemoryTable.Inputs RTAlias.Z7 × MemoryTable.Pub RTAlias.Z7)) ∧
      IO.LmIO 1 w.progIO w.memIO :=
  (language_unfold RTAlias.Z7 RTAlias.Z7 0 1 1
    (⟨[], []⟩ : Stmt RTAlias.Z7 RTAlias.Z7)).mp b37_z7_top_level_member

/-- The exported Nock hygiene theorem itself exposes an existential member of the same top-level
language. -/
theorem b37_exported_witness_is_top_level :
    ∃ x : Stmt RTAlias.Z7 RTAlias.Z7, Language RTAlias.T7 x :=
  (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1).mem

/-! ## 2. The zero-boundary attack -/

/-- At `Ksz = 0` no top-level NockVMROM language witness exists, for any fields or challenges. -/
theorem b37_Ksz_zero_languageInhabited_false
    (F K : Type) [Field F] [Field K] (α β : K) :
    ¬ LanguageInhabited (Tag F K α β 0) := by
  rintro ⟨⟨x, hx⟩⟩
  exact not_language_Ksz_zero F K α β x hx

/-- Regression: the exported positive witness cannot be called at `Ksz = 0`; its `[NeZero Ksz]`
premise is load-bearing rather than inferred from an unrelated bundle field. -/
theorem b37_NeZero_is_load_bearing : True := by
  fail_if_success
    have _bad := nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 0
  exact True.intro

/-! ## 3. Reconstructing the old empty-language bundle -/

/-- The same degenerate S8 proof used by the pre-S-b negative control. -/
@[reducible] def b37_rejCosted : HasCostModel RTBundle.RejVM reifiedNockCost where
  compMaxDegree_eq_four := rfl
  memMaxDegree_eq_four := rfl
  memory_fewer_constraints := by decide
  memory_fewer_deg4 := by decide

/-- Even with every old S1--S8 object supplied, the current applied proposition cannot exist for
`RejVM`: its final explicit argument would be a refuted `LanguageInhabited RejVM`. -/
theorem b37_rej_current_bundle_impossible :
    ¬ ∃ h : LanguageInhabited RTBundle.RejVM,
      VerifiableVMCompilation RTBundle.RejVM (nmrMEF ℚ ℚ) ℚ 10 3
        True trivial
        (HasCostModel RTBundle.RejVM reifiedNockCost) b37_rejCosted
        (ExactChainedHasPerfectCompleteness ℚ ℚ)
        (exactChainedHasPerfectCompleteness ℚ ℚ)
        True trivial RTBundle.rejMES True trivial True trivial
        True trivial h := by
  rintro ⟨h, _⟩
  exact RTBundle.rej_languageInhabited_false h

/-- Elaboration attack: all former bundle fields do not suffice when the final explicit parameter
is left unsolved.  The second check confirms that the witness was not added merely as a stored
wrapper field. -/
theorem b37_required_parameter_is_not_implicit_or_wrapper_only : True := by
  fail_if_success
    have _bad :
        VerifiableVMCompilation RTBundle.RejVM (nmrMEF ℚ ℚ) ℚ 10 3
          True trivial
          (HasCostModel RTBundle.RejVM reifiedNockCost) b37_rejCosted
          (ExactChainedHasPerfectCompleteness ℚ ℚ)
          (exactChainedHasPerfectCompleteness ℚ ℚ)
          True trivial RTBundle.rejMES True trivial True trivial
          True trivial _ :=
      ⟨⟩
  fail_if_success
    have _oldField := VerifiableVMCompilation.languageInhabited
  exact True.intro

/-- Universe/tag drift does not turn the real Nock witness into a witness for the rejecting VM. -/
theorem b37_no_language_witness_type_drift : True := by
  fail_if_success
    have _bad : LanguageInhabited RTBundle.RejVM :=
      nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1
  exact True.intro

/-- Negative control retained: parameterizing S1--S4 alone still admits the rejecting VM in the
pre-S-b custom package. -/
theorem b37_pre_Sb_negative_control :
    Nonempty
        (Atk.ParamPkg RTBundle.RejVM (nmrMEF ℚ ℚ) ℚ 10 3 RTBundle.rejSoundModel
          reifiedNockCost RTBundle.rejCompModel RTBundle.rejTwoRAPModel RTBundle.rejMES
          RTBundle.rejCRAP RTBundle.rejOneHot RTBundle.rejTM RTBundle.rejTraversable) ∧
      (∀ x : VMSystem.Statement RTBundle.RejVM, ¬ Language RTBundle.RejVM x) :=
  Atk.parameterization_does_not_exclude_empty_languages

/-! ## 4. Exact consumed capstone pins -/

/-- The exact concrete Layer-1 consumer includes the real top-level witness as its final parameter. -/
theorem b37_exact_Z7_consumed_capstone :
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
      (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) :=
  NockVMROM_Thm54_structural RTAlias.Z7 RTAlias.Z7 0 1 1

/-- Scope receipt: a nonempty Nock tag does not make fake S1--S4 objects impossible at their own
explicit type.  S-b excludes empty top-level languages; it does not claim semantic S-c/S-d/S-e. -/
theorem b37_fake_S1_S4_still_possible_at_nonempty_tag :
    VerifiableVMCompilation RTAlias.T7 (nmrMEF RTAlias.Z7 RTAlias.Z7) RTAlias.Z7 10 3
      (ProductionP8Containment.ExactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
      (ProductionP8Containment.exactProductionFixedFieldSoundness RTAlias.Z7 RTAlias.Z7)
      (ExactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
      (exactSegmentedCostVerification RTAlias.Z7 RTAlias.Z7)
      (ExactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
      (exactChainedHasPerfectCompleteness RTAlias.Z7 RTAlias.Z7)
      (ExactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
      (exactTwoRAPVerification RTAlias.Z7 RTAlias.Z7)
      RTAlias.fakeMES True trivial True trivial True trivial
      (nock_languageInhabited RTAlias.Z7 RTAlias.Z7 0 1 1) :=
  RTAlias.fakeThm54

/-! ## 5. StrictPackage same-object threading -/

/-- The one package-threaded language witness. -/
def b37_strictWitness
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    LanguageInhabited
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz) :=
  ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩

/-- Definitional receipt for the package-threaded existential member. -/
theorem b37_strictWitness_mem_exact
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    (b37_strictWitness P).mem =
      ⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩ :=
  rfl

/-- Both `P.structural` and `StrictThm54Statement.structural` consume the same package-derived
statement/proof pair, with no detached generic language witness and no independently quantified
configuration or execution. -/
theorem b37_strict_consumers_use_same_exact_witness
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
        (b37_strictWitness P)) ∧
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
        (b37_strictWitness P)) ∧
      Language
        (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
        (stmtOfExact P.objects.cfg P.objects.exec) :=
  ⟨P.structural, (strictNockVMROM_of_package P).structural, P.perfect_completeness⟩

end

end Nock.RedTeam.Batch37

#print axioms Nock.RedTeam.Batch37.b37_generic_positive_top_level
#print axioms Nock.RedTeam.Batch37.b37_z7_top_level_member
#print axioms Nock.RedTeam.Batch37.b37_z7_concrete_recognizer_witness
#print axioms Nock.RedTeam.Batch37.b37_exported_witness_is_top_level
#print axioms Nock.RedTeam.Batch37.b37_Ksz_zero_languageInhabited_false
#print axioms Nock.RedTeam.Batch37.b37_NeZero_is_load_bearing
#print axioms Nock.RedTeam.Batch37.b37_rejCosted
#print axioms Nock.RedTeam.Batch37.b37_rej_current_bundle_impossible
#print axioms Nock.RedTeam.Batch37.b37_required_parameter_is_not_implicit_or_wrapper_only
#print axioms Nock.RedTeam.Batch37.b37_no_language_witness_type_drift
#print axioms Nock.RedTeam.Batch37.b37_pre_Sb_negative_control
#print axioms Nock.RedTeam.Batch37.b37_exact_Z7_consumed_capstone
#print axioms Nock.RedTeam.Batch37.b37_fake_S1_S4_still_possible_at_nonempty_tag
#print axioms Nock.RedTeam.Batch37.b37_strictWitness
#print axioms Nock.RedTeam.Batch37.b37_strictWitness_mem_exact
#print axioms Nock.RedTeam.Batch37.b37_strict_consumers_use_same_exact_witness
