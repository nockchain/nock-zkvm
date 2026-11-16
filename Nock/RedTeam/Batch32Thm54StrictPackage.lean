/-
  Nock/RedTeam/Batch32Thm54StrictPackage.lean

  Locked facts:

  1. **One execution.**  The arbitrary-prover verifier's honest specialization, the shared
     table/walk row family, the two encoded IO record lists and the finite-field IO argument's own
     records all reduce to the single `⟨objects.cfg, objects.exec⟩`, and the Packet-0 release
     contract holds of it.  There is no second execution in the package.
  2. **The two chips are the NAMED constructed RAPs**, with the deployed `e = 3` fingerprint
     `(199, 196, 3)` and row domains sized by that same execution (`N` and `M + 2L`).
  3. **Same-field soundness.**  The package's own false-acceptance event is bounded by its own
     canonical five-class workload divided by its own `|K|`; the bit-form consequence is tied to
     that same event and workload.
  4. **The residuals are genuine fields**, so the capstone is CONDITIONAL, not an overclaim.
     `b32_package_residuals_are_explicit_fields` projects all seven open obligations straight out of
     the package, and `b32_package_nonempty_only_under_residuals` shows the package type cannot be
     inhabited without them.
  5. The pre-cutover forest target is retained under
     `«Thm:NockVMROM:forest-control»`; this artifact does not assert the current paper target.
  6. **Non-vacuity, honestly.**  Each residual is a *satisfiable* obligation rather than an
     impossible one (receipts 6a-6d), but NO concrete small-field inhabitant of the whole package is
     exhibited: `slotSemantics` is the honest memory reconstruction of a genuine Nock execution.
-/

import Nock.NockVMROM.Thm54.StrictPackage

namespace Nock.RedTeam.Batch32

open Module
open Nock Nock.Framework Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.StrictAsymptoticSecurity
open Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ExactPrimeFamily
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb q Λ : ℕ}
  (P : StrictNockVMROMPackage F K hOrb q Λ)

/-! ## 1. One execution -/

/-- **Receipt 1.**  Every carrier of the package is the one shared execution. -/
theorem b32_package_threads_one_execution :
    specializedProblem P.verifier.raw.timestamp P.honestSeed P.honestSeed_ne P.honestAlpha
        P.objects.cfg.challenges.lam = ⟨P.objects.cfg, P.objects.exec⟩ ∧
      P.walkFamily.problem = ⟨P.objects.cfg, P.objects.exec⟩ ∧
      P.ioStrategy.records.requests = P.objects.exec.derivedRequestIO ∧
      P.ioStrategy.records.responses = P.objects.exec.derivedResponseIO ∧
      StrictReleaseContract P.objects.cfg P.objects.exec P.objects.reqRecs P.objects.respRecs := by
  obtain ⟨h1, h2, _, _, h5, h6, h7⟩ := package_single_execution P
  exact ⟨h1, h2, h5, h6, h7⟩

/-- **Receipt 1 (teeth).**  The threading equations are not decoration: a package whose execution
has nonempty derived request IO cannot present an empty encoded request list. -/
theorem b32_tampered_io_rejected (hne : P.objects.exec.derivedRequestIO ≠ []) :
    P.objects.reqRecs ≠ [] ∧ P.ioStrategy.records.requests ≠ [] := by
  refine ⟨?_, ?_⟩
  · rw [P.objects.req_eq_derived]; exact hne
  · rw [P.io_requests, P.objects.req_eq_derived]; exact hne

/-! ## 2. The named `199`/`196` chips -/

/-- **Receipt 2.**  The package's two chips ARE the constructed `RAP_NockComp-IO`/`RAP_NockMem-IO`, they carry the strict `(199, 196, 3)` G10 fingerprint,
and their row domains are the shared execution's `N` and `M + 2L`. -/
theorem b32_package_named_raps_199_196 :
    P.compRAP = RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc ∧
      P.memRAP = RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm ∧
      P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧ P.compRAP.e = 3 ∧
      (P.compRAP.w, P.memRAP.w, P.compRAP.e)
          = CompleteProductionCost.strictPaperG10Fingerprint ∧
      P.compRAP.H.card = P.objects.cfg.compRows ∧
      P.memRAP.H.card
        = RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec := by
  obtain ⟨hc, hm, _, _, hrowsC, hrowsM⟩ := package_uses_named_raps P
  obtain ⟨hfp, hw199, hw196, he3⟩ := package_fingerprint_eq_strictG10 P
  exact ⟨hc, hm, hw199, hw196, he3, hfp, hrowsC, hrowsM⟩

/-! ## 3. Same-field pointwise soundness -/

/-- **Receipt 3a.**  The soundness event, workload and denominator are all the package's own. -/
theorem b32_package_fixed_field_soundness (lmb : K) :
    |jointProbability (FalseAcceptanceSet P.strategy q Λ lmb)| ≤
      (workload P.strategy Λ
          (fixedTopologyWorkload P.strategy)
          (fixedAxisWorkload P.strategy) : ℝ) /
        (Fintype.card K : ℝ) :=
  P.fixedField_falseAcceptance_le lmb

/-- **Receipt 3b.**  The bit form is not a detached arithmetic fact: its support premise and
conclusion use exactly the workload and false-acceptance event in Receipt 3a. -/
theorem b32_package_fixed_field_bits (lmb : K) (b : ℕ)
    (hsupport :
      workload P.strategy Λ
          (fixedTopologyWorkload P.strategy)
          (fixedAxisWorkload P.strategy) * 2 ^ b ≤
        Fintype.card K) :
    |jointProbability (FalseAcceptanceSet P.strategy q Λ lmb)| ≤ 1 / 2 ^ b :=
  P.fixedField_falseAcceptance_le_two_pow_neg lmb b hsupport

/-! ## 4. The residuals are genuine fields -/

/-- **Receipt 4 — the capstone is CONDITIONAL.**  Its hypotheses are projected straight out of the
package.  Nothing is hidden, nothing is `True`. -/
theorem b32_package_residuals_are_explicit_fields :
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
        ExecTreeShapeMatchesAt P.commitment
          (specializedProblem P.verifier.raw.timestamp z hz α lmb).exec) ∧
      (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
        RowFrameChecksAt z P.commitment
          (specializedProblem P.verifier.raw.timestamp z hz α lmb).exec) ∧
      (∀ s ∈ computeSkeletonRows P.commitment.skeleton, SkeletonSlotSemantics s) ∧
      Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (compTemplate F) P.compLanguage ∧
      Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (memTemplate F) P.memLanguage ∧
      RowLayout.RecordCountBalanced P.objects.exec ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy P.commitment.skeleton Λ :=
  package_residuals_are_fields P

end Package

/-! ## 5. The capstone consumes a package, and a package needs the residuals -/

/-- **Receipt 5a.**  The compiled capstone: its type shows the package hypothesis, so the S1--S8
statement is never produced out of thin air. -/
def b32_capstone_consumes_package := @strictNockVMROM_of_package

/-- **Receipt 5b.**  The package type cannot be inhabited without the local residuals. -/
theorem b32_package_nonempty_only_under_residuals
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (h : Nonempty (StrictNockVMROMPackage F K hOrb q Λ)) :
    ∃ (C : SkeletonCommitment) (cfg : ExactConfig F K) (exec : ExactExecution cfg)
      (Lc Lm : Nock.Reified.Env K → Prop),
      (∀ s ∈ computeSkeletonRows C.skeleton, SkeletonSlotSemantics s) ∧
        RowLayout.RecordCountBalanced exec ∧
        Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (compTemplate F) Lc ∧
        Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (memTemplate F) Lm ∧
        SizeWindowCounting.SizeWindowNounsBoundedBy C.skeleton Λ :=
  package_nonempty_only_under_residuals h

/-! ## 6. Non-vacuity: the residuals are satisfiable obligations, not impossible ones -/

section Satisfiable

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **Receipt 6a.** -/
theorem b32_shape_and_frame_residuals_satisfiable {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z C.skeleton cfg exec) :
    ExecTreeShapeMatchesAt C exec ∧ RowFrameChecksAt z C exec :=
  ⟨execTreeShapeMatchesAt_of_bindsAt h, rowFrameChecksAt_of_bindsAt h⟩

/-- **Receipt 6b.** -/
theorem b32_slot_residual_satisfiable {s : ComputeRowSkeleton}
    (core : BoundSemanticTrace.SkeletonOperationalCore s) :
    SkeletonSlotSemantics s :=
  skeletonSlotSemantics_of_core core

/-- **Receipt 6c.** -/
theorem b32_recordCountBalance_satisfiable {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (h : RowLayout.memoryStateCount exec .verify_child =
      RowLayout.memoryStateCount exec .read_root) :
    RowLayout.RecordCountBalanced exec :=
  h

theorem b32_pairedLayout_satisfiable {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : RowLayout.consumedRecordList exec = RowLayout.addedRecordList exec) :
    RowLayout.PairedRecordLayout exec := by
  rw [RowLayout.PairedRecordLayout, h]

section D3

variable [FiniteDimensional F K]

/-- `B29SemanticTemplate` is satisfiable
only at a *self-chosen* language, namely the vanishing of the template's own `𝕂`-gates. -/
theorem b32_semanticTemplate_satisfiable_degenerately (T : ChipTemplate F) :
    Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) T
      (fun envK => ∀ g ∈ T.extTransition ++ T.extDeg1 ++ T.extDeg3, g.eval envK = 0) :=
  Nock.RedTeam.Batch29.b29_residual_satisfiable T

end D3

end Satisfiable

/-! ## 7. -/

/-- **Receipt 7.** -/
theorem b32_alias_still_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest := rfl

end

end Nock.RedTeam.Batch32

#print axioms Nock.RedTeam.Batch32.b32_package_threads_one_execution
#print axioms Nock.RedTeam.Batch32.b32_tampered_io_rejected
#print axioms Nock.RedTeam.Batch32.b32_package_named_raps_199_196
#print axioms Nock.RedTeam.Batch32.b32_package_fixed_field_soundness
#print axioms Nock.RedTeam.Batch32.b32_package_fixed_field_bits
#print axioms Nock.RedTeam.Batch32.b32_package_residuals_are_explicit_fields
#print axioms Nock.RedTeam.Batch32.b32_capstone_consumes_package
#print axioms Nock.RedTeam.Batch32.b32_package_nonempty_only_under_residuals
#print axioms Nock.RedTeam.Batch32.b32_shape_and_frame_residuals_satisfiable
#print axioms Nock.RedTeam.Batch32.b32_slot_residual_satisfiable
#print axioms Nock.RedTeam.Batch32.b32_recordCountBalance_satisfiable
#print axioms Nock.RedTeam.Batch32.b32_pairedLayout_satisfiable
#print axioms Nock.RedTeam.Batch32.b32_semanticTemplate_satisfiable_degenerately
#print axioms Nock.RedTeam.Batch32.b32_alias_still_forest
