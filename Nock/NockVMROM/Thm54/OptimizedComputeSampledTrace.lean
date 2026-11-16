import Nock.NockVMROM.Thm54.OptimizedComputeOverlay
import Nock.NockVMROM.Thm54.ComputeSampledIOCoResidence
import Nock.NockVMROM.Thm54.ConcreteStrictPackage

/-!
# Optimized compute rows with sampled finite-field IO

The fixed nine-slot overlay carries five compute-walk values, the co-resident sampled request
accumulator, and three inactive-safe row-local request denominators. No `IOField K` value is stored
in the optimized row.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeSampledTrace

open Nock
open Nock.ComputeTable
open ComputeSampledIO

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- Host-level copy of the semantic second-slot request mask. -/
def secondRequestMask (st : State) : K :=
  match st with
  | .s0 | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 => 1
  | _ => 0

/-- Host-level copy of the semantic third-slot request mask. -/
def thirdRequestMask (st : State) : K :=
  match st with
  | .s6 | .s9 => 1
  | _ => 0

/-- The co-resident row contribution is exactly the three fixed slots weighted by the opcode
activity masks.  This is the bridge from state-indexed request arity to the degree-four safe gate. -/
theorem rowTerm_eq_fixed_slots
    (coins : FiniteIO.IOCoins K) (lam : K)
    (row : ComputeTable.State × ComputeTable.DTcomp K) :
    ComputeSampledIO.rowTerm coins lam row =
      ComputeSampledIO.requestInv coins (NockVM.encRecFormR row.2.2.1.mr1 lam) +
      secondRequestMask row.2.2.1.state *
        ComputeSampledIO.requestInv coins (NockVM.encRecFormR row.2.2.1.mr2 lam) +
      thirdRequestMask row.2.2.1.state *
        ComputeSampledIO.requestInv coins (NockVM.encRecFormR row.2.2.1.mr3 lam) := by
  cases hs : row.2.2.1.state <;>
    simp [ComputeSampledIO.rowTerm, ComputeSampledIO.rowRequests,
      NockVM.activeRequestRecords, ComputeSampledIO.requestInv,
      secondRequestMask, thirdRequestMask, hs] <;> ring

theorem rowTermC_eq_fixed_slots
    (comp : (Fin 9 → K) → K) (lam : K)
    (row : ComputeTable.State × ComputeTable.DTcomp K) :
    ComputeSampledIO.rowTermC comp lam row =
      (comp (NockVM.encRecFormR row.2.2.1.mr1 lam))⁻¹ +
      secondRequestMask row.2.2.1.state *
        (comp (NockVM.encRecFormR row.2.2.1.mr2 lam))⁻¹ +
      thirdRequestMask row.2.2.1.state *
        (comp (NockVM.encRecFormR row.2.2.1.mr3 lam))⁻¹ := by
  cases hs : row.2.2.1.state <;>
    simp [ComputeSampledIO.rowTermC, ComputeSampledIO.rowRequests,
      NockVM.activeRequestRecords, secondRequestMask, thirdRequestMask, hs] <;> ring

/-- Normalize an inactive raw denominator to one. -/
def inactiveSafe (active denom : K) : K :=
  active * denom + (1 - active)

/-- The nine live values physically shared into one optimized compute row. -/
def overlayAt (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) : OptimizedComputeOverlay.SampledOverlayValues K where
  toOverlayValues :=
    { walkCount := A.exact.computeWalk.count (i + 1)
      walkAcc := A.exact.computeWalk.acc (i + 1)
      sf1_st := ComputeTable.childStateTagCol R.computeWalkRows (i + 1) 0
      sf2_st := ComputeTable.childStateTagCol R.computeWalkRows (i + 1) 1
      sf3_st := ComputeTable.childStateTagCol R.computeWalkRows (i + 1) 2
      ioAcc :=
        coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows i }
  denom0 :=
    A.compress10
      (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr1 R.problem.cfg.challenges.lam)
  denom1 :=
    inactiveSafe (secondRequestMask (R.problem.exec.computePubAt i).state)
      (A.compress10
        (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr2 R.problem.cfg.challenges.lam))
  denom2 :=
    inactiveSafe (thirdRequestMask (R.problem.exec.computePubAt i).state)
      (A.compress10
        (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr3 R.problem.cfg.challenges.lam))

/-- One physical 13/58 optimized row from the exact execution, its canonical table auxiliary,
the existing walk assignment, and sampled finite-field IO assignment. -/
def encodedRowAt (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    OptimizedComputeCodec.Row F K :=
  OptimizedComputeOverlay.sampledEncode
    (R.problem.exec.computePubAt i)
    (R.problem.exec.computeDecAt i)
    (A.exact.computeTableAux i)
    (overlayAt A i)

/-- The sampled accumulator occupies the sixth overlay coordinate exactly. -/
@[simp] theorem overlayAt_ioAcc
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    (overlayAt A i).ioAcc =
      coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows i :=
  rfl

/-- All-trace compute-table satisfaction recovers the exact `Vcomp` row required by the codec. -/
theorem vcompAt_of_compute_obligations
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) :
    Vcomp R.problem.cfg.challenges.computeInputs
      (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i) := by
  have haccept : exactComputeChainedAccepts R.problem :=
    (exactChainedHasCanonicalRAP2 F K).compute_iff R.problem |>.2
      ⟨A.exact.computeTableAux, h.1⟩
  exact haccept.1 i

/-- Exact decode/encode roundtrip on every accepting table/walk/sampled-IO row. -/
theorem decode_encodedRowAt
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) :
    OptimizedComputeOverlay.sampledDecode (F := F)
        R.problem.cfg.challenges.computeInputs (encodedRowAt A i) =
      (OptimizedComputeOverlay.withOverlayTags
        { R.problem.exec.computePubAt i with
            sf1_st := none, sf2_st := none, sf3_st := none, certC? := none }
        (overlayAt A i).toOverlayValues,
        R.problem.exec.computeDecAt i,
        A.exact.computeTableAux i, overlayAt A i) :=
  OptimizedComputeOverlay.sampledDecode_encode_of_vcomp (F := F)
    (vcompAt_of_compute_obligations A h i)

/-- The accepted sampled strategy and exact compute capacity produce a genuine co-resident
program-IO phase with no appended rows. -/
theorem no_appended_phase
    (A : SampledIOSameExecutionAssignment R p)
    (hcap : R.problem.cfg.compRows ≤ 2 ^ R.problem.cfg.orbit.h) :
    ComputeSampledIO.NoAppendedComputeIOPhase A :=
  ComputeSampledIO.noAppendedComputeIOPhase A hcap

namespace Concrete

open ConcreteStrictPackage

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- The concrete in-table pole `2` misses the nine-slot in-table hit event at `γ = 0`. -/
theorem honest_interPoleHitGood :
    (2 : K73cubic) ∉
      FiniteIO.IOPoleHitEvent
        { requests := (RowLayout.consumedRecordList honestLegacyFamily.problem.exec).map
            (fun r => NockVM.encRecC r (honestLegacyFamily.problem.exec.cprimeOf r))
          responses := honestLegacyFamily.problem.exec.derivedResponseIO }
        (ioStrategy : FiniteIO.FiniteIOStrategy K73cubic 9 4 (ringChar K73cubic)).coins.gamma := by
    intro h
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨v, hv, hz⟩ := h
    have hcons :
        RowLayout.consumedRecordList honestLegacyFamily.problem.exec
          = [rowRecord honestSeed honestAlpha] := by
      change RowLayout.consumedRecordList
          (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
            honestSeed_ne honestAlpha MemoryTable.formRDefault).exec = _
      rw [specializedProblem_eq]
      show (exec honestSeed honestAlpha).memoryRows.flatMap
          (fun row => RowLayout.consumedRecords row.2.2) = _
      rw [(execution_rows honestSeed honestAlpha).2]
      simp [RowLayout.consumedRecords, dummyHaltRow, readRow, decomposeRow, headRow,
        verifyRow, tailRow, dummyHaltPub, readPub, decomposePub, headPub, verifyPub, tailPub]
    have hresp :
        honestLegacyFamily.problem.exec.derivedResponseIO =
          [NockVM.encRecFormR (requestRecord honestSeed honestAlpha)
            MemoryTable.formRDefault] := by
      change (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
          honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.derivedResponseIO = _
      rw [specializedProblem_eq, derived_response_singleton]
    -- Row-level memory: the consumed record is `rowRecord` (axis `T`), the response its Form R
    -- encode; both keep slot 0 = `root.size`, which is all `rlc` reads at `gamma = 0`.
    have hv0 : v 0 = (requestRecord honestSeed honestAlpha).root.size := by
      rw [hcons, hresp] at hv
      simp only [List.map_cons, List.map_nil, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · simp [NockVM.encRecC, rowRecord_root]
      · simp [NockVM.encRecFormR, NockVM.encRecC]
    change (2 : K73cubic) + Walk.rlc (0 : K73cubic) v = 0 at hz
    simp only [Walk.rlc, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ,
      zero_pow (Nat.succ_ne_zero _), zero_mul, add_zero, Finset.univ_eq_empty,
      Finset.sum_empty] at hz
    rw [hv0] at hz
    simp [requestRecord, formula_fp] at hz
    have hne : (2 : K73cubic) + 1 ≠ 0 := by
      have h3 : (2 : K73cubic) + 1 = 3 := by norm_num
      rw [h3]
      intro hk
      have hbase : (3 : F73) ≠ 0 := by decide
      exact hbase ((algebraMap F73 K73cubic).injective
        (by simpa only [map_ofNat, map_zero] using hk))
    exact hne hz

theorem honest_derivedRequestIO :
    honestLegacyFamily.problem.exec.derivedRequestIO =
      [NockVM.encRecFormR (requestRecord honestSeed honestAlpha) MemoryTable.formRDefault] := by
  change (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
      honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.derivedRequestIO = _
  rw [specializedProblem_eq, derived_request_singleton]

theorem honest_derivedResponseIO :
    honestLegacyFamily.problem.exec.derivedResponseIO =
      [NockVM.encRecFormR (requestRecord honestSeed honestAlpha) MemoryTable.formRDefault] := by
  change (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
      honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.derivedResponseIO = _
  rw [specializedProblem_eq, derived_response_singleton]

theorem honest_ioGood10 :
    ((ioStrategy : FiniteIO.FiniteIOStrategy K73cubic 9 4 (ringChar K73cubic)).coins.gamma,
        (ioStrategy : FiniteIO.FiniteIOStrategy K73cubic 9 4 (ringChar K73cubic)).coins.pole) ∉
      FiniteIO.IOFailureEvent (honestRecords10 honestLegacyFamily) := by
  unfold honestRecords10
  rw [honest_derivedResponseIO, honest_derivedRequestIO]
  apply RecordCarrier.notMem_IOFailureEvent_extRecords_single
  · rfl
  · intro h
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨v, hv, hz⟩ := h
    refine io_compress_ne_zero v ?_ hz
    change v ∈ (exec honestSeed honestAlpha).derivedRequestIO ++
      (exec honestSeed honestAlpha).derivedResponseIO
    rw [derived_request_singleton, derived_response_singleton]
    exact hv

theorem honest_interPoleHitGood10 :
    (2 : K73cubic) ∉
      FiniteIO.IOPoleHitEvent (honestInterRecords10 honestLegacyFamily)
        (ioStrategy : FiniteIO.FiniteIOStrategy K73cubic 9 4 (ringChar K73cubic)).coins.gamma := by
  have hγ : (ioStrategy : FiniteIO.FiniteIOStrategy K73cubic 9 4
      (ringChar K73cubic)).coins.gamma = 0 := rfl
  have h := honest_interPoleHitGood
  rw [hγ] at h ⊢
  unfold honestInterRecords10
  rw [RecordCarrier.IOPoleHitEvent_extRecords_zero]
  exact h

/-- Concrete cubic sampled same-execution assignment. -/
noncomputable def honestSampled :
    SampledIOSameExecutionAssignment honestLegacyFamily (ringChar K73cubic) where
  exact := honestAssignment
  sampled := ioStrategy
  requests_eq := by
    change (exec honestSeed honestAlpha).derivedRequestIO =
      (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
        honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.derivedRequestIO
    rw [specializedProblem_eq]
  responses_eq := by
    change (exec honestSeed honestAlpha).derivedResponseIO =
      (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
        honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.derivedResponseIO
    rw [specializedProblem_eq]
  poleHitGood := by
    intro h
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨v, hv, hz⟩ := h
    exact io_compress_ne_zero v hv hz
  interPole := 2
  interPoleHitGood := honest_interPoleHitGood
  honestVer := by
    change ∀ row ∈
        (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
          honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
    rw [specializedProblem_eq]
    simp [(execution_rows honestSeed honestAlpha).2, dummyHaltRow, readRow, decomposeRow, headRow,
      verifyRow, tailRow, dummyHaltPub, readPub, decomposePub, headPub, verifyPub, tailPub]
  ioGood10 := honest_ioGood10
  interPoleHitGood10 := honest_interPoleHitGood10

/-- The encoder is the `LT_comp`
projection by construction, and the single `OP_1` row has no children. -/
theorem honest_walkLabelObligations : honestSampled.WalkLabelObligations := by
  refine ⟨fun t => rfl, ?_⟩
  intro t ht
  have hex : honestLegacyFamily.problem.exec.computeTree =
      (exec honestSeed honestAlpha).computeTree := by
    change (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
      honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.computeTree = _
    rw [specializedProblem_eq]
  rw [PlusIOSegmentedFamily.computeWalkRows, hex] at ht
  simp [exec, Walk.bfsForest] at ht
  subst ht
  simp [computeRow, computePub, ComputeTable.fanoutComp, ComputeTable.childLinkComp]

theorem honest_obligations :
    honestSampled.ComputeSampledObligations :=
  by
    apply honestSampled.computeSampledObligations_of_six
    · change honestAssignment.SixConcreteObligations
      exact (honestAssignment.satisfies_iff_six_concrete_obligations).1
        honestCompletion.assignment.sixFamilies
    · exact honest_walkLabelObligations

/-- The unique active compute-row index of the concrete execution. -/
def honestRowIndex : Fin honestLegacyFamily.problem.cfg.compRows :=
  ⟨0, by
    change 0 < (cfg honestSeed honestAlpha).compRows
    norm_num [cfg]⟩

theorem honest_computePubAt :
    honestLegacyFamily.problem.exec.computePubAt honestRowIndex =
      computePub honestSeed honestAlpha := by
  have h := honestRawLegacy_computePubAt_zero
  change honestLegacyFamily.problem.exec.computePubAt _ =
    computePub honestSeed honestAlpha at h
  let j : Fin honestLegacyFamily.problem.cfg.compRows :=
    ⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩
  have hij : honestRowIndex = j := by
    apply Fin.ext
    rfl
  rw [hij]
  exact h

/-- The concrete OP1 row stores `(1,1,1)`: the active denominator is one and both inactive raw
zero denominators are normalized to one. -/
theorem honest_safe_denominators :
    (overlayAt honestSampled honestRowIndex).denom0 = 1 ∧
      (overlayAt honestSampled honestRowIndex).denom1 = 1 ∧
      (overlayAt honestSampled honestRowIndex).denom2 = 1 := by
  change
    honestSampled.compress10
          (NockVM.encRecFormR (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).mr1
              MemoryTable.formRDefault) = 1 ∧
      inactiveSafe
        (secondRequestMask
          (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).state)
        (honestSampled.compress10
          (NockVM.encRecFormR (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).mr2
              MemoryTable.formRDefault)) = 1 ∧
      inactiveSafe
        (thirdRequestMask
          (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).state)
        (honestSampled.compress10
          (NockVM.encRecFormR (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).mr3
              MemoryTable.formRDefault)) = 1
  simp only [SampledIOSameExecutionAssignment.compress10, RecordCarrier.extRec]
  rw [show honestSampled.sampled.coins = ioCoins by rfl, honest_computePubAt]
  simp only [FiniteIO.compress, RecordCarrier.rlc_withExp]
  simp [computePub, requestRecord, formula_fp, NockVM.encRecFormR, NockVM.encRecC,
      FiniteIO.compress, ioCoins,
    Walk.rlc, Fin.sum_univ_succ, inactiveSafe, secondRequestMask, thirdRequestMask]

/-- Concrete non-vacuity: the unique cubic compute row decodes to the exact honest table row
(with `sf*_st` recovered from overlay hosts), canonical auxiliary, walk/IO overlay. -/
theorem honest_row_roundtrip :
    OptimizedComputeOverlay.sampledDecode (F := F73)
        honestLegacyFamily.problem.cfg.challenges.computeInputs
        (encodedRowAt honestSampled honestRowIndex) =
      (OptimizedComputeOverlay.withOverlayTags
        { honestLegacyFamily.problem.exec.computePubAt honestRowIndex with
            sf1_st := none, sf2_st := none, sf3_st := none, certC? := none }
        (overlayAt honestSampled honestRowIndex).toOverlayValues,
        honestLegacyFamily.problem.exec.computeDecAt honestRowIndex,
        honestAssignment.computeTableAux honestRowIndex,
        overlayAt honestSampled honestRowIndex) :=
  by simpa [honestSampled] using
    (decode_encodedRowAt honestSampled honest_obligations honestRowIndex)

/-- Concrete cubic co-residence reaches the sampled request terminal on the compute table itself. -/
theorem honest_terminal_on_compute :
    coResidentAcc honestSampled.sampled.coins honestLegacyFamily.problem.cfg.challenges.lam
        honestLegacyFamily.problem.exec.computeRows
        honestLegacyFamily.problem.exec.computeRows.length =
      honestSampled.sampled.witness.requestAcc (Fin.last _) :=
  coResidentAcc_terminal_eq_witness honestSampled

end Concrete

#print axioms decode_encodedRowAt
#print axioms no_appended_phase
#print axioms Concrete.honest_obligations
#print axioms Concrete.honest_safe_denominators
#print axioms Concrete.honest_row_roundtrip
#print axioms Concrete.honest_terminal_on_compute

end
end OptimizedComputeSampledTrace
end Nock.NockVMROM.Thm54
