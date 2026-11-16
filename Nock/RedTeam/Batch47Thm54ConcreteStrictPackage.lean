import Nock.NockVMROM.Thm54.ConcreteStrictPackage

/-!
# repaired concrete strict-package independent regression

Paper frame: `Def:MES`, the complete compute/memory construction
, and Theorem 5.4.

The first concrete production commitment used zero response multiplicity and was rejected by the
raw verifier. The production object now projects its tables, walks, IO accumulators, and
multiplicity from one `JointAssignment` over the same exact execution.

Both pointwise-containment premises are independently discharged at the same `honestCoins`, exact
package strategy/census, `q = 73`, and `Λ = 2`; the resulting `GenuineTargetAt` is obtained through
the package's consumed containment field.  A zero-seed substitution enters the exact union.  The
attempted collision/low-order substitutions instead establish a stronger specialization fact:
the concrete collision and size-window components are empty for every coin.  The package still
carries the documented AO/R6/D1 boundary: its two named monolithic semantic-template fields are
the existing Batch-29 satisfiable language witnesses.
-/

namespace Nock.RedTeam.Batch47

open scoped Classical

open Nock Nock.NockVMROM
open Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrictPackage
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

noncomputable section

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

noncomputable local instance concrete_fintype : Fintype K73cubic :=
  Fintype.ofFinite K73cubic

local instance concrete_charRing : CharP K73cubic (ringChar K73cubic) :=
  ConcreteStrictPackage.concrete_charRing

/-! ## 1. -/

theorem field_cubic_and_orbits_exact :
    Fintype.card F73 = 73 ∧
      Fintype.card K73cubic = 73 ^ 3 ∧
      Module.finrank F73 K73cubic = 3 ∧
      orderOf (10 : K73cubic) = 8 ∧
      orderOf strictOrbit.ω = 3 * 2 ^ 2 := by
  refine ⟨by simp [F73], ?_, ?_, omega10_order, strictOrbit.order_ω⟩
  · rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 73 3 (by norm_num)
  · exact GaloisField.finrank 73 (by norm_num)


theorem field_substitution_controls :
    Fintype.card K73cubic ≠ Fintype.card F73 ∧
      Fintype.card (ZMod 17) ≠ Fintype.card F73 := by
  rw [field_cubic_and_orbits_exact.2.1, field_cubic_and_orbits_exact.1]
  norm_num


theorem g13cubic_order_eight_arithmetic_obstruction :
    Nat.card (GaloisField 13 3) = 2197 ∧ ¬ 8 ∣ (2197 - 1 : ℕ) := by
  constructor
  · rw [GaloisField.card 13 3 (by norm_num)]
    norm_num
  · norm_num

theorem exact_execution_and_io_nonvacuous :
    (exec honestSeed honestAlpha).computeRows = [computeRow honestSeed honestAlpha] ∧
      (exec honestSeed honestAlpha).memoryRows =
        [dummyHaltRow honestSeed, readRow honestSeed honestAlpha,
          decomposeRow honestSeed honestAlpha, headRow honestSeed,
          verifyRow honestSeed honestAlpha, tailRow honestSeed] ∧
      (exec honestSeed honestAlpha).ComputeRowsAccepted ∧
      (exec honestSeed honestAlpha).MemoryRowsAccepted ∧
      ChainedSemanticExactLanguage (cfg honestSeed honestAlpha)
        (exec honestSeed honestAlpha) ∧
      (exec honestSeed honestAlpha).derivedRequestIO =
        [encRecFormR (requestRecord honestSeed honestAlpha) formRDefault] ∧
      (exec honestSeed honestAlpha).derivedResponseIO =
        [encRecFormR (requestRecord honestSeed honestAlpha) formRDefault] := by
  exact ⟨(execution_rows _ _).1, (execution_rows _ _).2,
    honest_computeRowsAccepted, honest_memoryRowsAccepted, honest_chained,
    derived_request_singleton, derived_response_singleton⟩

theorem request_is_genuine_and_io_accepts :
    requestRecord honestSeed honestAlpha ≠ (MemRec.zero : MemRec K73cubic) ∧
      IO.LIO 4 (exec honestSeed honestAlpha).derivedRequestIO
        (exec honestSeed honestAlpha).derivedResponseIO :=
  ⟨honest_request_ne_zero, io_lio⟩

/-! ## 2. Universal R3/R4, concrete R5/R7/R2a, and the R6 boundary -/

theorem universal_all_z_all_alpha_binding :
    ∀ (z : K73cubic) (hz : z ≠ 0) (α : K73cubic),
      specializedProblem verifier.raw.timestamp z hz α MemoryTable.formRDefault = ⟨cfg z α, exec z α⟩ ∧
        BindsAt z semanticSkeleton (cfg z α) (exec z α) ∧
        ActiveFingerprintChecksAt z commitment (exec z α) ∧
        ExecTreeShapeMatchesAt commitment (exec z α) ∧
        RowFrameChecksAt z commitment (exec z α) := by
  intro z hz α
  exact ⟨verifier_specializedProblem z hz α, bindsAt z α, scanAt z α,
    shapeMatchAt z α, rowFrameAt z α⟩

theorem concrete_R5_R7_R2a :
    (∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonSlotSemantics s) ∧
      (∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonRecordEquations s) ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy semanticSkeleton 2 ∧
      RowLayout.RecordCountBalanced (exec honestSeed honestAlpha) :=
  ⟨slotSemantics, recordEquations, sizeWindowBound, recordCountBalance⟩

/-- R5 is exercised by the actual OP1 row; no OP0/OP9 row is hidden in the singleton skeleton. -/
theorem concrete_skeleton_is_exactly_nonempty_op1 :
    computeSkeletonRows semanticSkeleton = [computeSkeletonRow] ∧
      computeSkeletonRow.state = .s1 ∧
      (∀ s ∈ computeSkeletonRows semanticSkeleton, s.state ≠ .s0 ∧ s.state ≠ .s9) := by
  have hrows : computeSkeletonRows semanticSkeleton = [computeSkeletonRow] := by
    norm_num [computeSkeletonRows, semanticSkeleton, bfsForest, NTree.size, totalSize]
  refine ⟨hrows, rfl, ?_⟩
  intro s hs
  rw [hrows] at hs
  simp only [List.mem_singleton] at hs
  subst s
  simp [computeSkeletonRow]

/-- R7's specialization is exact: the current skeleton has no OP3/OP4/OP6 size-window noun.
Any attempted OP4 insertion is therefore not a row of this package's committed skeleton. -/
theorem concrete_size_window_is_empty_and_rejects_op4_insertion :
    SizeWindowCounting.skeletonSizeWindowNouns semanticSkeleton = [] ∧
      ∀ s ∈ computeSkeletonRows semanticSkeleton, s.state ≠ .s4 := by
  constructor
  · simp [SizeWindowCounting.skeletonSizeWindowNouns,
      SizeWindowCounting.requiredSizeWindowNouns, semanticSkeleton,
      computeSkeletonRows, computeSkeletonRow, bfsForest]
  · intro s hs
    have hrows : computeSkeletonRows semanticSkeleton = [computeSkeletonRow] := by
      norm_num [computeSkeletonRows, semanticSkeleton, bfsForest, NTree.size, totalSize]
    rw [hrows] at hs
    simp only [List.mem_singleton] at hs
    subst s
    simp [computeSkeletonRow]

/-- Exact boundary: the two monolithic semantic-template fields still use the documented
Batch-29 satisfiable factory, so the repair does not close AO/R6/D1. -/
theorem R6_boundary_is_unchanged :
    Nock.RedTeam.Batch29.B29SemanticTemplate
        (K := K73cubic) (MonolithicRAP.compTemplate F73) compLanguage ∧
      Nock.RedTeam.Batch29.B29SemanticTemplate
        (K := K73cubic) (MonolithicRAP.memTemplate F73) memLanguage :=
  ⟨compSemanticTemplate, memSemanticTemplate⟩

/-! ## 3. Retracted finding preserved as a negative regression -/

/-- The local bad commitment is exactly the old implementation: every response multiplicity is
zero.  It is not the repaired production `alphaMCommitment`. -/
theorem bad_committed_multiplicity_is_zero
    (z : K73cubic) (hz : z ≠ 0) (α : K73cubic)
    (j : Fin ((zeroAlphaMCommitment z hz α MemoryTable.formRDefault).familyData.base.exec.derivedResponseIO.length)) :
    (zeroAlphaMCommitment z hz α MemoryTable.formRDefault).io.multiplicity j = 0 :=
  rfl

theorem every_specialization_has_one_response
    (z : K73cubic) (hz : z ≠ 0) (α : K73cubic) :
    (specializedProblem timestampStrategy z hz α MemoryTable.formRDefault).exec.derivedResponseIO.length = 1 := by
  rw [specializedProblem_eq, derivedResponseIO_singleton]
  rfl

/-- The old zero-multiplicity strategy still rejects every coin, proving the original attack remains
a live regression rather than disappearing after the repair. -/
theorem bad_zeroRawStrategy_acceptance_empty (ω : JointCoins K73cubic) :
    ¬ zeroRawStrategy.Accepts ω MemoryTable.formRDefault := by
  intro hacc
  by_cases hz : nprSeed ω ≠ 0
  · have hraw := (zeroRawStrategy.accepts_iff_raw ω MemoryTable.formRDefault hz).1 hacc
    rcases hraw.1 with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hmult, _, _, _, _⟩
    have hlen :
        (zeroRawStrategy.familyAt ω MemoryTable.formRDefault hz).exec.derivedResponseIO.length = 1 := by
      change
        (specializedProblem timestampStrategy (nprSeed ω) hz
          (alphaM ω) MemoryTable.formRDefault).exec.derivedResponseIO.length = 1
      exact every_specialization_has_one_response (nprSeed ω) hz (alphaM ω)
    let j : Fin (zeroRawStrategy.familyAt ω MemoryTable.formRDefault hz).exec.derivedResponseIO.length :=
      ⟨0, by omega⟩
    have hj := hmult j
    change (0 : ZMod (ringChar K73cubic)) ≠ 0 at hj
    exact hj rfl
  · simp [TemplateRawJointSoundness.Strategy.Accepts, hz] at hacc

/-! ## 4. Same-object index checks, seventeen gates, and six families -/

theorem repaired_same_object_threading :
    rawStrategy.familyAt honestCoins MemoryTable.formRDefault honestSeed_ne =
        RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily ∧
      rawStrategy.messageAt honestCoins MemoryTable.formRDefault honestSeed_ne =
        RawMessage.ofLegacy honestAssignment ∧
      (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).problem =
        ⟨cfg honestSeed honestAlpha, exec honestSeed honestAlpha⟩ ∧
      concreteStrictPackage.objects = objects ∧
      concreteStrictPackage.verifier = verifier ∧
      concreteStrictPackage.strategy.verifier = verifier := by
  exact ⟨rawStrategy_familyAt_honest, rawStrategy_messageAt_honest,
    honestRawLegacy_problem, rfl, rfl, rfl⟩

/-- The package-facing skeleton, IO lists, table row domains, and final containment strategy all
retain the exact same cfg/exec carrier checked above. -/
theorem package_skeleton_io_and_row_domains_are_identical :
    concreteStrictPackage.commitment.skeleton = semanticSkeleton ∧
      concreteStrictPackage.objects.reqRecs =
        (exec honestSeed honestAlpha).derivedRequestIO ∧
      concreteStrictPackage.objects.respRecs =
        (exec honestSeed honestAlpha).derivedResponseIO ∧
      (concreteStrictPackage.strategy.verifier.raw.familyAt
        honestCoins MemoryTable.formRDefault honestSeed_ne).problem =
          ⟨cfg honestSeed honestAlpha, exec honestSeed honestAlpha⟩ ∧
      concreteStrictPackage.Hc.card =
        (exec honestSeed honestAlpha).computeRows.length ∧
      concreteStrictPackage.Hm.card =
        (exec honestSeed honestAlpha).memoryRows.length := by
  refine ⟨rfl, rfl, rfl, ?_, Hc_card, Hm_card⟩
  change (rawStrategy.familyAt honestCoins MemoryTable.formRDefault honestSeed_ne).problem =
    ⟨cfg honestSeed honestAlpha, exec honestSeed honestAlpha⟩
  rw [rawStrategy_familyAt_honest]
  exact honestRawLegacy_problem

/-- The topology adapter wraps the exact raw message above; it does not change the family/message
index before the production topology checks are added. -/
theorem adapter_wraps_the_exact_raw_message :
    (verifier.messageAt honestCoins MemoryTable.formRDefault honestSeed_ne).raw =
      RawMessage.ofLegacy honestAssignment := by
  change rawStrategy.messageAt honestCoins MemoryTable.formRDefault honestSeed_ne =
    RawMessage.ofLegacy honestAssignment
  exact rawStrategy_messageAt_honest

/-- The complete gate tuple, projected at the exact honest message and public claim.  The seventeen
conjuncts are: seed, four challenge pins, row alignment, canonical encoders, three root claims,
requests=responses, outMem=0, nonzero multiplicity, two range gates, and two nodup gates. -/
theorem all_seventeen_verifier_gates :
    let R := RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily
    let M := RawMessage.ofLegacy honestAssignment
    nprSeed honestCoins ≠ 0 ∧
      R.cfg.challenges.z = nprSeed honestCoins ∧
      R.computeWalkAlpha = alphaC honestCoins ∧
      R.walkGamma = gamma honestCoins ∧
      R.memoryWalkAlpha = alphaM honestCoins ∧
      RawMessage.RowAlignmentGates (R := R) ∧
      R.CanonicalNodeEncoderGates ∧
      (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).s =
        GlobalCarryRecognizer.enc (nprSeed honestCoins) semanticSkeleton.publicClaim.subject ∧
      (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).f =
        GlobalCarryRecognizer.enc (nprSeed honestCoins) semanticSkeleton.publicClaim.formula ∧
      (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).e =
        GlobalCarryRecognizer.enc (nprSeed honestCoins) semanticSkeleton.publicClaim.result ∧
      R.requests = R.responses ∧
      R.outMem = 0 ∧
      (∀ j, M.io.multiplicity j ≠ 0) ∧
      IO.InRange R.cfg.Ksz R.exec.derivedRequestIO.length ∧
      R.exec.derivedRequestIO.Nodup ∧
      R.exec.derivedResponseIO.length ≤ R.cfg.Ksz ∧
      R.exec.derivedResponseIO.Nodup := by
  exact honestVerifierGates

/-- On the concrete singleton request/response execution, the repaired exact-IO multiplicity is
not merely nonzero: the two symbolic accumulator endpoints force its prime-field value to be one. -/
theorem repaired_honest_multiplicity_is_one
    (j : Fin honestLegacyFamily.problem.exec.derivedResponseIO.length) :
    honestAssignment.exactIO.multiplicity j = 1 := by
  let r := encRecFormR (requestRecord honestSeed honestAlpha) formRDefault
  have hreqList :
      honestLegacyFamily.problem.exec.derivedRequestIO = [r] := by
    change
      (specializedProblem timestampStrategy honestSeed honestSeed_ne
        honestAlpha MemoryTable.formRDefault).exec.derivedRequestIO = [r]
    rw [specializedProblem_eq]
    exact derived_request_singleton
  have hrespList :
      honestLegacyFamily.problem.exec.derivedResponseIO = [r] := by
    change
      (specializedProblem timestampStrategy honestSeed honestSeed_ne
        honestAlpha MemoryTable.formRDefault).exec.derivedResponseIO = [r]
    rw [specializedProblem_eq]
    exact derived_response_singleton
  let j0 : Fin honestLegacyFamily.problem.exec.derivedResponseIO.length :=
    ⟨0, by rw [hrespList]; norm_num⟩
  have hj : j = j0 := by
    apply Fin.ext
    have hji := j.isLt
    have hlen := congrArg List.length hrespList
    simp only [List.length_singleton] at hlen
    omega
  subst j
  have hreqLen :
      honestLegacyFamily.problem.exec.derivedRequestIO.length = 1 := by
    simpa using congrArg List.length hreqList
  have hrespLen :
      honestLegacyFamily.problem.exec.derivedResponseIO.length = 1 := by
    simpa using congrArg List.length hrespList
  have hreq0 :
      IO.listExt honestLegacyFamily.problem.exec.derivedRequestIO 0 = r := by
    rw [hreqList]
    rfl
  have hresp0 :
      IO.listExt honestLegacyFamily.problem.exec.derivedResponseIO 0 = r := by
    rw [hrespList]
    rfl
  have hpStep := honestAssignment.exactIO.progSat.step 0 (by omega)
  rw [hreq0] at hpStep
  have hpTerm := honestAssignment.exactIO.progSat.term
  rw [hreqLen] at hpTerm
  have hp :
      honestLegacyFamily.requests = SetEq.frac (SetEq.RLC r) := by
    rw [hpTerm, hpStep, honestAssignment.exactIO.progSat.init, zero_add]
  have hcast := IO.castμ_fin (𝔽 := K73cubic)
    honestAssignment.exactIO.multiplicity j0
  change
    IO.castμ (𝔽 := K73cubic) honestAssignment.exactIO.multiplicity 0 =
      SetEq.castZ (ringChar K73cubic)
        (honestAssignment.exactIO.multiplicity j0) at hcast
  have hmStep := honestAssignment.exactIO.memSat.step 0 (by omega)
  rw [hresp0, hcast] at hmStep
  rw [Algebra.smul_def] at hmStep
  have hmTerm := honestAssignment.exactIO.memSat.term
  rw [hrespLen, honestAssignment.exactIO.memory_closes] at hmTerm
  have hmAcc :
      honestAssignment.exactIO.memAcc 0 =
        (SetEq.castZ (ringChar K73cubic)
          (honestAssignment.exactIO.multiplicity j0) : RatFunc K73cubic) •
            SetEq.frac (SetEq.RLC r) := by
    rw [Algebra.smul_def]
    linear_combination -hmStep - hmTerm
  have hm :
      honestLegacyFamily.responses =
        (SetEq.castZ (ringChar K73cubic)
          (honestAssignment.exactIO.multiplicity j0) : RatFunc K73cubic) •
            SetEq.frac (SetEq.RLC r) := by
    rw [← honestAssignment.exactIO.memSat.init, hmAcc]
  have hfrac :
      SetEq.frac (SetEq.RLC r) =
        algebraMap (RatFunc K73cubic) (IOField K73cubic)
          (SetEq.castZ (ringChar K73cubic)
            (honestAssignment.exactIO.multiplicity j0)) *
            SetEq.frac (SetEq.RLC r) := by
    calc
      SetEq.frac (SetEq.RLC r) = honestLegacyFamily.requests := by
        exact hp.symm
      _ = honestLegacyFamily.responses :=
        honestAssignment.exactIO.endpoints_agree
      _ = algebraMap (RatFunc K73cubic) (IOField K73cubic)
          (SetEq.castZ (ringChar K73cubic)
            (honestAssignment.exactIO.multiplicity j0)) *
            SetEq.frac (SetEq.RLC r) := by simpa [Algebra.smul_def] using hm
  have hfrac_ne : SetEq.frac (SetEq.RLC r) ≠ 0 := by
    unfold SetEq.frac
    exact inv_ne_zero (SetEq.algebraMap_poleP_ne_zero _)
  have hcoeff_outer :
      algebraMap (RatFunc K73cubic) (IOField K73cubic)
          (SetEq.castZ (ringChar K73cubic)
            (honestAssignment.exactIO.multiplicity j0)) = 1 := by
    apply mul_right_cancel₀ hfrac_ne
    simpa using hfrac.symm
  have hcoeff :
      (SetEq.castZ (ringChar K73cubic)
          (honestAssignment.exactIO.multiplicity j0) : RatFunc K73cubic) = 1 :=
    by
      rw [RatFunc.algebraMap_eq_C] at hcoeff_outer
      exact RatFunc.C_injective (K := RatFunc K73cubic) (by
        simpa only [map_one] using hcoeff_outer)
  exact (SetEq.castZ_injective (L := RatFunc K73cubic)
    (ringChar K73cubic)) (by simpa using hcoeff)

/-- The repaired production commitment transports the same nonzero multiplicity to every
all-`z`/all-`alphaM` specialization. -/
theorem repaired_multiplicity_nonzero_universal
    (z : K73cubic) (hz : z ≠ 0) (α : K73cubic)
    (j : Fin ((alphaMCommitment z hz α MemoryTable.formRDefault).familyData.base.exec.derivedResponseIO.length)) :
    (alphaMCommitment z hz α MemoryTable.formRDefault).io.multiplicity j ≠ 0 := by
  let j' : Fin honestLegacyFamily.problem.exec.derivedResponseIO.length :=
    ⟨j, by
      rw [honestAssignment_response_length]
      have hj := j.isLt
      change j.val <
        (acceptedFamilyData z hz α MemoryTable.formRDefault).base.exec.derivedResponseIO.length at hj
      rw [acceptedFamily_response_length z hz α] at hj
      exact hj⟩
  change honestAssignment.exactIO.multiplicity _ ≠ 0
  convert honestAssignment.exactIO.multiplicity_ne_zero j' using 1

/-- One concrete row-kind trace from each of the six table/walk/IO families.  All six types retain
the single `honestLegacyFamily.problem`, hence the same cfg/exec and row domains. -/
theorem six_concrete_row_trace_facts :
    let R := RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily
    let M := RawMessage.ofLegacy honestAssignment
    (R.computeTableRAP .row).Satisfies M.computeTableTrace ∧
      (R.memoryTableRAP .row).Satisfies M.memoryTableTrace ∧
      (R.computeWalkRAP .row).Satisfies M.computeWalkTrace ∧
      (R.memoryWalkRAP .row).Satisfies M.memoryWalkTrace ∧
      (R.computeIORAP .row).Satisfies M.computeIOTrace ∧
      (R.memoryIORAP .row).Satisfies M.memoryIOTrace := by
  have h := honestCompletion.assignment.six_family_satisfaction
  exact ⟨h.1 .row, h.2.1 .row, h.2.2.1 .row, h.2.2.2.1 .row,
    h.2.2.2.2.1 .row, h.2.2.2.2.2 .row⟩

theorem all_six_RAP_families :
    (RawMessage.ofLegacy honestAssignment).SixRAPSatisfy :=
  RawMessage.sixRAPSatisfy_of_legacy honestAssignment
    honestCompletion.assignment.sixFamilies

/-! ## 5. Independent acceptance reconstruction -/

/-- Raw acceptance rebuilt directly from the expanded gates and six-family witness.  This does not
invoke `ConcreteStrictPackage.rawStrategy_accepts_honestCoins`. -/
theorem reconstructed_raw_message_accepts :
    (RawMessage.ofLegacy honestAssignment).Accepts
      semanticSkeleton.publicClaim honestCoins :=
  ⟨honestVerifierGates, all_six_RAP_families⟩

theorem independently_reconstructed_rawStrategy_accepts :
    rawStrategy.Accepts honestCoins MemoryTable.formRDefault := by
  apply (rawStrategy.accepts_iff_raw honestCoins MemoryTable.formRDefault honestSeed_ne).2
  rw [rawStrategy_messageAt_honest]
  exact reconstructed_raw_message_accepts

/-- The adapter acceptance is reconstructed from the independently rebuilt raw acceptance and the
two exact topology witnesses. -/
theorem independently_reconstructed_verifier_accepts :
    verifier.Accepts honestCoins MemoryTable.formRDefault := by
  exact ProductionRawVerifier.TemplateAdapter.Strategy.honest_accepts
    rawStrategy honestCoins MemoryTable.formRDefault honestSeed_ne independently_reconstructed_rawStrategy_accepts
    honest_exactTopology

/-- Final acceptance is rebuilt from adapter acceptance, the two deterministic structural checks,
and the root-axis boundary.  It does not invoke
`ConcreteStrictPackage.production_accepts_honestCoins`. -/
theorem independently_reconstructed_production_accepts :
    concreteStrictPackage.strategy.Accepts honestCoins MemoryTable.formRDefault := by
  apply (concreteStrictPackage.strategy.accepts_iff honestCoins MemoryTable.formRDefault honestSeed_ne).2
  constructor
  · apply (ProductionAxisStructureVerifier.accepts_iff verifier honestCoins MemoryTable.formRDefault
      honestSeed_ne).2
    exact ⟨(verifier.accepts_iff_production honestCoins MemoryTable.formRDefault honestSeed_ne).1
      independently_reconstructed_verifier_accepts, honest_structuralChecks⟩
  · exact honest_rootAxisBoundary

/-! ## 6. Five exact FailureUnion exclusions -/

theorem independently_not_zeroSeedFailureEvent :
    honestCoins ∉ (zeroSeedFailureEvent : Finset (JointCoins K73cubic)) := by
  rw [mem_zeroSeedFailureEvent_iff]
  change honestSeed ≠ 0
  exact honestSeed_ne

theorem independently_not_collisionFailureEvent :
    honestCoins ∉
      collisionFailureEvent concreteStrictPackage.census.census := by
  rw [mem_collisionFailureEvent_iff]
  rintro ⟨i, hi⟩
  apply hi
  have hmem :
      concreteStrictPackage.census.census.pair i ∈
        EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton := by
    change
      (ComparisonCensus.ofPairList
        (EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton) _).pair i ∈
          EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton
    erw [ComparisonCensus.ofPairList_pair]
    exact List.get_mem _ _
  simp [EdgeComparisonCensus.combinedSkeletonPairs,
      BoundSemanticTrace.skeletonPairs, EdgeComparisonCensus.edgePairs,
      EdgeComparisonCensus.rowEdgePairs, P8Census.skeletonComparisonCensus,
      P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
      semanticSkeleton, computeSkeletonRow, NTree.childOpt,
      subjectNoun, formulaNoun, headNoun, resultNoun, requestSkeleton,
      SemanticStrategy.SemanticSkeleton.publicClaim,
      SemanticTrace.ComparisonUse.pair, decActive, computeSkeletonRows, bfsForest] at hmem
  rcases hmem with hmem | hmem | hmem | hmem | hmem | hmem <;> rw [hmem]
  all_goals
    change GlobalCarryRecognizer.SepSeed honestSeed _ _
  all_goals
    simp [GlobalCarryRecognizer.SepSeed]

theorem independently_not_specializedTopologyFailureEvent :
    honestCoins ∉
      specializedTopologyFailureEvent concreteStrictPackage.strategy.verifier.raw MemoryTable.formRDefault := by
  rw [mem_specializedTopologyFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change honestGamma ∈ topologyBadGammas walkFamily at hbad
  have hcomputeTree :
      walkFamily.exec.computeTree = (exec honestSeed honestAlpha).computeTree :=
    congrArg (fun P : RawProblem F73 K73cubic => P.exec.computeTree)
      walkFamily_problem
  have hmemoryForest :
      walkFamily.exec.memoryForest = (exec honestSeed honestAlpha).memoryForest :=
    congrArg (fun P : RawProblem F73 K73cubic => P.exec.memoryForest)
      walkFamily_problem
  rw [topologyBadGammas, computeTopologyBadGammas, memoryTopologyBadGammas,
    RawPlusIOSegmentedFamily.computeWalkRows,
    RawPlusIOSegmentedFamily.memoryWalkRows, hcomputeTree] at hbad
  simp only [hmemoryForest] at hbad
  simp [honestGamma,
    computeTopologyBadGammas, memoryTopologyBadGammas,
    computeSlotBadGammas, memorySlotBadGammas,
    computeActualPayload, computeExpectedPayload,
    memoryActualPayload, memoryExpectedPayload,
    exec, dummyHaltTree, dummyHaltRow, dummyHaltPub, readTree, decomposeTree, headTree,
      verifyTree, tailTree, bfsForest,
    computeRow, readRow, decomposeRow, headRow, verifyRow, tailRow,
    computePub, readPub, decomposePub, headPub, verifyPub, tailPub,
    ComputeTable.fanoutComp, MemoryTable.fanoutMem,
    ComputeTable.sfTriple, MemoryTable.memCell, NTree.childLabel, NTree.childOpt] at hbad
  obtain ⟨a, ha, hbad⟩ := hbad
  interval_cases a <;>
    simp [memorySlotBadGammas, memoryActualPayload, memoryExpectedPayload,
      MemoryTable.fanoutMem, MemoryTable.memCell, NTree.childLabel, NTree.childOpt,
      dummyHaltRow, dummyHaltPub, readRow, decomposeRow, headRow, verifyRow, tailRow,
      readPub, decomposePub, headPub, verifyPub, tailPub] at hbad

theorem independently_not_guardedAxisFailureEvent :
    honestCoins ∉ guardedAxisFailureEvent concreteStrictPackage.strategy MemoryTable.formRDefault :=
  ConcreteStrictPackage.honestCoins_not_guardedAxisFailureEvent

theorem independently_not_sizeWindowFailure :
    honestCoins ∉ SizeWindowCounting.SizeWindowFailure
      concreteStrictPackage.strategy.skeleton := by
  change honestCoins ∉ SizeWindowCounting.SizeWindowFailure semanticSkeleton
  rw [SizeWindowCounting.mem_SizeWindowFailure_iff]
  simp [honestCoins, SizeWindowCounting.skeletonSizeWindowNouns,
    SizeWindowCounting.requiredSizeWindowNouns, semanticSkeleton,
    computeSkeletonRows, computeSkeletonRow, bfsForest]

/-- All five exclusions are projected at exactly the package's strategy, census and `Λ = 2`
carrier.  No separately constructed lookalike strategy or census occurs in this statement. -/
theorem all_five_exact_failure_exclusions :
    honestCoins ∉ (zeroSeedFailureEvent : Finset (JointCoins K73cubic)) ∧
      honestCoins ∉ collisionFailureEvent concreteStrictPackage.census.census ∧
      honestCoins ∉ specializedTopologyFailureEvent
        concreteStrictPackage.strategy.verifier.raw MemoryTable.formRDefault ∧
      honestCoins ∉ guardedAxisFailureEvent concreteStrictPackage.strategy MemoryTable.formRDefault ∧
      honestCoins ∉ SizeWindowCounting.SizeWindowFailure
        concreteStrictPackage.strategy.skeleton :=
  ⟨independently_not_zeroSeedFailureEvent,
    independently_not_collisionFailureEvent,
    independently_not_specializedTopologyFailureEvent,
    independently_not_guardedAxisFailureEvent,
    independently_not_sizeWindowFailure⟩

theorem independently_honestCoins_not_failureUnion :
    honestCoins ∉ ProductionP8Containment.FailureUnion
      concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault := by
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact independently_not_zeroSeedFailureEvent hbad
        · exact independently_not_collisionFailureEvent hbad
      · exact independently_not_specializedTopologyFailureEvent hbad
    · exact independently_not_guardedAxisFailureEvent hbad
  · exact independently_not_sizeWindowFailure hbad

/-! ## 7. Wrong-coin controls -/

def zeroSeedCoins : JointCoins K73cubic :=
  ((honestAlphaC, honestGamma), (honestAlpha, 0))

theorem wrong_zeroSeedCoins_lands_in_exact_failureUnion :
    zeroSeedCoins ∈
      (zeroSeedFailureEvent : Finset (JointCoins K73cubic)) ∧
    zeroSeedCoins ∈ ProductionP8Containment.FailureUnion
      concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault := by
  constructor
  · rw [mem_zeroSeedFailureEvent_iff]
    rfl
  · have hz :
        zeroSeedCoins ∈
          (zeroSeedFailureEvent : Finset (JointCoins K73cubic)) := by
      rw [mem_zeroSeedFailureEvent_iff]
      rfl
    change zeroSeedCoins ∈
      ((((zeroSeedFailureEvent ∪
          collisionFailureEvent concreteStrictPackage.census.census) ∪
          specializedTopologyFailureEvent concreteStrictPackage.strategy.verifier.raw MemoryTable.formRDefault) ∪
          guardedAxisFailureEvent concreteStrictPackage.strategy MemoryTable.formRDefault) ∪
          SizeWindowCounting.SizeWindowFailure concreteStrictPackage.strategy.skeleton)
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl hz)))

/-- The attempted collision substitution cannot succeed for this concrete census: every occurrence
compares a noun with itself, so the exact package collision event is empty for every coin. -/
theorem exact_collision_event_is_empty :
    collisionFailureEvent concreteStrictPackage.census.census =
      (∅ : Finset (JointCoins K73cubic)) := by
  apply Finset.ext
  intro ω
  constructor
  · rw [mem_collisionFailureEvent_iff]
    rintro ⟨i, hi⟩
    exfalso
    apply hi
    have hmem :
        concreteStrictPackage.census.census.pair i ∈
          EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton
        := by
      change
        (ComparisonCensus.ofPairList
          (EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton) _).pair i ∈
            EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton
      erw [ComparisonCensus.ofPairList_pair]
      exact List.get_mem _ _
    simp [EdgeComparisonCensus.combinedSkeletonPairs,
        BoundSemanticTrace.skeletonPairs, EdgeComparisonCensus.edgePairs,
        EdgeComparisonCensus.rowEdgePairs, P8Census.skeletonComparisonCensus,
        P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
        semanticSkeleton, computeSkeletonRow, NTree.childOpt,
        subjectNoun, formulaNoun, headNoun, resultNoun, requestSkeleton,
        SemanticStrategy.SemanticSkeleton.publicClaim,
        SemanticTrace.ComparisonUse.pair, decActive, computeSkeletonRows, bfsForest] at hmem
    rcases hmem with hmem | hmem | hmem | hmem | hmem | hmem <;> rw [hmem]
    all_goals
      change GlobalCarryRecognizer.SepSeed (nprSeed ω) _ _
    all_goals
      simp [GlobalCarryRecognizer.SepSeed]
  · intro h
    simp at h

/-- A low-order substitution cannot enter the size-window component either: the exact package's
R7 specialization has no size-window nouns. -/
theorem exact_sizeWindow_event_is_empty :
    SizeWindowCounting.SizeWindowFailure concreteStrictPackage.strategy.skeleton =
      (∅ : Finset (JointCoins K73cubic)) := by
  ext ω
  change
    (ω ∈ SizeWindowCounting.SizeWindowFailure semanticSkeleton) ↔
      ω ∈ (∅ : Finset (JointCoins K73cubic))
  rw [SizeWindowCounting.mem_SizeWindowFailure_iff]
  simp [SizeWindowCounting.skeletonSizeWindowNouns,
    SizeWindowCounting.requiredSizeWindowNouns, semanticSkeleton,
    computeSkeletonRows, computeSkeletonRow, bfsForest]

/-! ## 8. Exact containment and capstone scope -/

theorem package_and_capstone_nonvacuous :
    Nonempty (StrictNockVMROMPackage F73 K73cubic 2 73 2) ∧
      Nonempty (StrictThm54Statement concreteStrictPackage) ∧
      ∃ ω : JointCoins K73cubic, concreteStrictPackage.strategy.Accepts ω MemoryTable.formRDefault :=
  ⟨⟨concreteStrictPackage⟩, ⟨strictNockVMROM_of_concretePackage⟩,
    ⟨honestCoins, independently_reconstructed_production_accepts⟩⟩

/-- Both consumed antecedents hold on the same coin and exact package strategy/census. -/
theorem containment_antecedents_are_one_conjunction :
    concreteStrictPackage.strategy.Accepts honestCoins MemoryTable.formRDefault ∧
      honestCoins ∉ ProductionP8Containment.FailureUnion
        concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault :=
  ⟨independently_reconstructed_production_accepts,
    independently_honestCoins_not_failureUnion⟩

/-- Genuine target evidence comes through the consumed package containment field, with exactly
`strategy`, `q = 73`, `Λ = 2`, `census`, and `honestCoins`. -/
theorem independently_honest_genuineTarget :
    GenuineTargetAt concreteStrictPackage.strategy 73 2 honestCoins MemoryTable.formRDefault :=
  concreteStrictPackage.containment honestCoins MemoryTable.formRDefault
    independently_reconstructed_production_accepts
    independently_honestCoins_not_failureUnion

/-- Existential non-vacuity retains one witness outside both quantifiers; acceptance and failure
avoidance are conjuncts about that same `ω`. -/
theorem independently_containment_antecedents_jointly_satisfiable :
    ∃ ω : JointCoins K73cubic,
      concreteStrictPackage.strategy.Accepts ω MemoryTable.formRDefault ∧
        ω ∉ ProductionP8Containment.FailureUnion
          concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault :=
  ⟨honestCoins, independently_reconstructed_production_accepts,
    independently_honestCoins_not_failureUnion⟩


theorem production_containment_receipts_thread_exact_objects :
    concreteStrictPackage.strategy.Accepts honestCoins MemoryTable.formRDefault ∧
      honestCoins ∉ ProductionP8Containment.FailureUnion
        concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault ∧
      GenuineTargetAt concreteStrictPackage.strategy 73 2 honestCoins MemoryTable.formRDefault :=
  ⟨production_accepts_honestCoins, honestCoins_not_failureUnion,
    honest_genuineTarget⟩


theorem production_honest_genuineTarget_is_consumed_containment :
    honest_genuineTarget =
      concreteStrictPackage.containment honestCoins MemoryTable.formRDefault
        production_accepts_honestCoins honestCoins_not_failureUnion :=
  rfl


theorem production_joint_satisfiability_has_one_witness :
    ∃ ω : JointCoins K73cubic,
      concreteStrictPackage.strategy.Accepts ω MemoryTable.formRDefault ∧
        ω ∉ ProductionP8Containment.FailureUnion
          concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault :=
  containment_antecedents_jointly_satisfiable


theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

#print axioms Nock.RedTeam.Batch47.field_cubic_and_orbits_exact
#print axioms Nock.RedTeam.Batch47.universal_all_z_all_alpha_binding
#print axioms Nock.RedTeam.Batch47.concrete_R5_R7_R2a
#print axioms Nock.RedTeam.Batch47.R6_boundary_is_unchanged
#print axioms Nock.RedTeam.Batch47.bad_committed_multiplicity_is_zero
#print axioms Nock.RedTeam.Batch47.every_specialization_has_one_response
#print axioms Nock.RedTeam.Batch47.bad_zeroRawStrategy_acceptance_empty
#print axioms Nock.RedTeam.Batch47.package_skeleton_io_and_row_domains_are_identical
#print axioms Nock.RedTeam.Batch47.adapter_wraps_the_exact_raw_message
#print axioms Nock.RedTeam.Batch47.all_seventeen_verifier_gates
#print axioms Nock.RedTeam.Batch47.repaired_honest_multiplicity_is_one
#print axioms Nock.RedTeam.Batch47.six_concrete_row_trace_facts
#print axioms Nock.RedTeam.Batch47.independently_reconstructed_rawStrategy_accepts
#print axioms Nock.RedTeam.Batch47.independently_reconstructed_verifier_accepts
#print axioms Nock.RedTeam.Batch47.independently_reconstructed_production_accepts
#print axioms Nock.RedTeam.Batch47.all_five_exact_failure_exclusions
#print axioms Nock.RedTeam.Batch47.wrong_zeroSeedCoins_lands_in_exact_failureUnion
#print axioms Nock.RedTeam.Batch47.exact_collision_event_is_empty
#print axioms Nock.RedTeam.Batch47.exact_sizeWindow_event_is_empty
#print axioms Nock.RedTeam.Batch47.independently_honestCoins_not_failureUnion
#print axioms Nock.RedTeam.Batch47.containment_antecedents_are_one_conjunction
#print axioms Nock.RedTeam.Batch47.independently_honest_genuineTarget
#print axioms Nock.RedTeam.Batch47.independently_containment_antecedents_jointly_satisfiable
#print axioms Nock.RedTeam.Batch47.production_containment_receipts_thread_exact_objects
#print axioms Nock.RedTeam.Batch47.production_honest_genuineTarget_is_consumed_containment
#print axioms Nock.RedTeam.Batch47.production_joint_satisfiability_has_one_witness
#print axioms Nock.RedTeam.Batch47.package_and_capstone_nonvacuous
#print axioms Nock.RedTeam.Batch47.paper_alias_remains_forest

end

end Nock.RedTeam.Batch47
