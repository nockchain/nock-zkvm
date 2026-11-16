import Nock.NockVMROM.Thm54.OptimizedComputeFormRSlots

/-!
# Honest Form R request denominators

On an honest typed compute row whose certificate columns hold the leftover certificate of the
row's natural axis (`axisNatK`) at the row's `λ` coin `lam` (challenge slot `9`; honestly the
configuration's `cfg.challenges.lam`), the deployed sampled denominator of every *active* request
slot is the compressed Form R encode `encRecFormR mr lam` of that request record — the record the
derived compute IO (`NockVM.reqRecs`) and the memory rows (`BindMemRow`) carry.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeFormRDenoms

open Nock
open Nock.ComputeTable
open Nock.Reified
open OptimizedComputeCodec
open OptimizedComputeSampledTrace
open OptimizedComputeSubstitution
open OptimizedComputeCorrectedFinal
open OptimizedComputeRangeCertificate
open OptimizedComputeFinalTrace
open OptimizedComputeFormRSlots
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- Every row's natural axis is below the chip width `2^64` (from `FormRAxisBound`). -/
def FormRAxisSmall (A : SampledIOSameExecutionAssignment R p) : Prop :=
  ∀ i : Fin R.problem.cfg.compRows, axisNatK A i < 2 ^ 64

theorem formRAxisSmall_of_bound (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (hax : FormRAxisBound A b) : FormRAxisSmall A := by
  intro i
  rw [← axisNat_axisLeafCoord_eq A b hax i]
  cases h : axisLeafCoord A b i with
  | none => simp [axisNat_none]
  | some L =>
      obtain ⟨a, ha0, -, h64, haL, -⟩ := hax i L h
      exact axisNat_lt_64 L ha0 h64 haL

/-- Honest certificate base columns `202.. 295` of row `i`. -/
noncomputable def exactFinalCertBase (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) : Fin 94 → F :=
  fun j => formROffNat (F := F) (axisNatK A i) j

/-- Honest certificate `𝕂` helpers `H`, `T` of row `i` at the `𝕂` coin `λ`. -/
noncomputable def exactFinalCertExt (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (lam : K) : Fin 2 → K :=
  fun j =>
    if (j : ℕ) = 0 then formRLamHNat (F := F) (axisNatK A i) lam
    else formRLamTNat (F := F) (axisNatK A i) lam

/-- The three request records of row `i` (`mr₁`, `mr₂`, `mr₃`). -/
def slotRecord (R : PlusIOSegmentedFamily F K) (i : Fin R.problem.cfg.compRows) :
    Fin 3 → ComputeTable.MemRec K
  | 0 => (R.problem.exec.computePubAt i).mr1
  | 1 => (R.problem.exec.computePubAt i).mr2
  | 2 => (R.problem.exec.computePubAt i).mr3

/-- Activity of the three request slots of row `i` (`1`, the second and third masks). -/
def slotActive (R : PlusIOSegmentedFamily F K) (i : Fin R.problem.cfg.compRows) :
    Fin 3 → K
  | 0 => 1
  | 1 => secondRequestMask (R.problem.exec.computePubAt i).state
  | 2 => thirdRequestMask (R.problem.exec.computePubAt i).state

/-- An active request slot holds the `j`-th opcode-active request record. -/
theorem slotRecord_active (R : PlusIOSegmentedFamily F K) (i : Fin R.problem.cfg.compRows)
    (j : Fin 3) (hact : slotActive R i j = 1) :
    ∃ hj : (j : ℕ) < (NockVM.activeRequestRecords (R.problem.exec.computePubAt i)).length,
      slotRecord R i j = (NockVM.activeRequestRecords (R.problem.exec.computePubAt i))[(j : ℕ)] := by
  fin_cases j <;> cases hs : (R.problem.exec.computePubAt i).state <;>
    simp_all [slotActive, secondRequestMask, thirdRequestMask, NockVM.activeRequestRecords,
      slotRecord]

theorem withExp_honestS_eq_extRec (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : Fin 3) (hact : slotActive R i j = 1) :
    RecordCarrier.withExp (NockVM.encRecFormR (slotRecord R i j) R.problem.cfg.challenges.lam)
        (((honestS R i + (j : ℕ) + 1 : ℕ)) : K) =
      RecordCarrier.extRec R.problem.exec.derivedRequestIO
        (NockVM.encRecFormR (slotRecord R i j) R.problem.cfg.challenges.lam) := by
  obtain ⟨hj, hrec⟩ := slotRecord_active R i j hact
  rw [RecordCarrier.extRec, hrec, honestExp_activeRequest A i j hj]

theorem decodeState_encodedRowAt (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    decodeState (encodedRowAt A i).base = (R.problem.exec.computePubAt i).state := by
  simp [encodedRowAt, OptimizedComputeOverlay.sampledEncode, decodeState_encodeBase]

theorem finalSampledNamespace_traceCur (i : ℕ) :
    finalSampledNamespace .traceCur i = .Var .traceCur i := rfl

theorem finalSampledNamespace_challenge (i : ℕ) (h6 : i ≠ 6) (h7 : i ≠ 7) :
    finalSampledNamespace .challenge i = .Var .challenge i := by
  unfold finalSampledNamespace
  split <;> simp_all

theorem sampledRecordRLC_eval (E : Env K) (base : ℕ) :
    (sampledRecordRLC .traceCur base).eval E =
      Walk.rlc (E.chal 6) (RecordCarrier.withExp (fun c : Fin 9 =>
        if (c : ℕ) = 6 then (sampledSlotT .traceCur base).eval E
        else if (c : ℕ) = 8 then (sampledSlotC .traceCur base).eval E
        else (computeTraceSubst .traceCur (base + c)).eval E)
        ((sampledSlotE .traceCur base).eval E)) := by
  rw [RecordCarrier.rlc_withExp]
  simp only [sampledRecordRLC, sampledGamma, List.range, List.range.loop, List.foldr,
    Expr.eval, Walk.rlc, Fin.sum_univ_succ]
  simp
  ring

/-- The nine-slot sampled record of request slot `j` on a source environment: slot `6` the
Form R `T_slot`, slot `8` the Form R `C_slot`, the rest the decoded record columns. -/
def sampledSlotRecord (E : Env K) (j : Fin 3) : Fin 9 → K :=
  fun c =>
    if (c : ℕ) = 6 then (sampledSlotT .traceCur (67 + 8 * (j : ℕ))).eval E
    else if (c : ℕ) = 8 then (sampledSlotC .traceCur (67 + 8 * (j : ℕ))).eval E
    else (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + c)).eval E

/-- **Honest active request records are Form R encodes** (slot level). -/
theorem sampledSlotRecord_eq_formR
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F)
    (env : CorrectedFinalTypedEnv F K)
    (j : Fin 3) (lam : K)
    (hsel : ∀ s : State, env.toSourceEnv.trace (Nock.Reified.opCol s) =
      if s = (R.problem.exec.computePubAt i).state then 1 else 0)
    (hcol : ∀ c : Fin 8,
      (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).eval
          (Env.ofSubst finalSampledNamespace env.toSourceEnv) =
        NockVM.encRecC
          (slotRecord R i j) 1 c.castSucc)
    (h9 : env.chal 9 = lam)
    (hcb : env.certBase = exactFinalCertBase A i)
    (hce : env.certExt = exactFinalCertExt A i lam)
    (h41 : env.toSourceEnv.trace 54 = coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩)
    (h44 : env.toSourceEnv.trace 57 = coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩)
    (hact : slotActive R i j = 1) :
    sampledSlotRecord (Env.ofSubst finalSampledNamespace env.toSourceEnv) j =
      NockVM.encRecFormR (slotRecord R i j) lam := by
  set st := (R.problem.exec.computePubAt i).state with hst
  set E := env.toSourceEnv with hE
  set E' := Env.ofSubst finalSampledNamespace E with hE'
  -- environment readings on the substituted environment
  have htr : ∀ k, E'.trace k = E.trace k := fun k => by
    simp only [hE', Env.ofSubst, finalSampledNamespace_traceCur, Expr.eval]
  have hsel' : ∀ s : State, E'.trace (Nock.Reified.opCol s) = if s = st then 1 else 0 :=
    fun s => by rw [htr]; exact hsel s
  have h9' : E'.chal 9 = lam := by
    simp only [hE', Env.ofSubst, finalSampledNamespace_challenge 9 (by decide) (by decide),
      Expr.eval]
    rw [hE, toSource_chal9, h9]
  have hlp : ∀ d, d < 64 → E'.chal (100 + d) = lamPowVal lam d := by
    intro d hd
    simp only [hE', Env.ofSubst,
      finalSampledNamespace_challenge (100 + d) (by omega) (by omega), Expr.eval]
    rw [hE, toSource_lamPow env d hd, h9]
  have hcb' : ∀ k, k < 63 →
      E'.trace (202 + k) = algebraMap F K (formROffNat (F := F) (axisNatK A i) k) := by
    intro k hk
    rw [htr, hE, toSource_certBase env k (by omega), hcb]
    rfl
  have hT' : E'.trace 299 = formRLamTNat (F := F) (axisNatK A i) lam := by
    rw [htr, hE, toSource_certT, hce]
    simp [exactFinalCertExt]
  have hs := formR_slots (F := F) E' lam st hsel' (axisNatK A i) (hsmall i)
    (one_le_pwScaleExp hwidth) (pwScaleExp_le_63 hwidth) h9' hlp hcb' hT'
  -- state facts
  have hdec : decodeState (encodedRowAt A i).base = st := decodeState_encodedRowAt A i
  have hsel0 := hsel' .s0
  have hsel2 := hsel' .s2
  have hsel5 := hsel' .s5
  have hsel6 := hsel' .s6
  have hsel7 := hsel' .s7
  have hsel8 := hsel' .s8
  have hsel9 := hsel' .s9
  simp only [Nock.Reified.opCol] at hsel0 hsel2 hsel5 hsel6 hsel7 hsel8 hsel9
  -- the record slots
  have hslot :
      (sampledSlotT .traceCur (67 + 8 * (j : ℕ))).eval E' =
          MemoryTable.formRT lam (MemoryTable.nockAxisOf
            (slotRecord R i j).axis) ∧
        (sampledSlotC .traceCur (67 + 8 * (j : ℕ))).eval E' =
          MemoryTable.formRC lam (MemoryTable.nockAxisOf
            (slotRecord R i j).axis) := by
    have hc6 := hcol 6
    obtain ⟨h1, hs0, hsG, hs6, hs9⟩ := hs
    fin_cases j
    · have hax : (R.problem.exec.computePubAt i).mr1.axis = 3 := by
        simp [computeTraceSubst, Expr.eval, NockVM.encRecC, slotRecord] at hc6
        exact hc6.symm
      simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, mul_zero, add_zero, slotRecord]
      rw [hax, nockAxisOf_three hwidth]
      exact h1
    · simp only [Fin.mk_one, Fin.isValue, Fin.val_one, mul_one, slotRecord, slotActive]
        at hact hc6 ⊢
      cases hs : st with
      | s0 =>
          have hax : (R.problem.exec.computePubAt i).mr2.axis =
              coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩ := by
            simp [computeTraceSubst, mr2Field, mr2Group, decFP, ext0, Expr.eval,
              NockVM.encRecC, hsel0, hsel2, hsel5, hsel6, hsel7, hsel8, hsel9, hs,
              htr, h41] at hc6
            exact hc6.symm
          have hK : MemoryTable.nockAxisOf (R.problem.exec.computePubAt i).mr2.axis =
              axisNatK A i := by
            rw [hax]
            simp [axisNatK, axisLeafK, hdec, hs]
          rw [hK]
          exact hs0 hs
      | s2 | s5 | s6 | s7 | s8 | s9 =>
          have hax : (R.problem.exec.computePubAt i).mr2.axis = 2 := by
            simp [computeTraceSubst, mr2Field, mr2Group, decFP, ext0, Expr.eval,
              NockVM.encRecC, hsel0, hsel2, hsel5, hsel6, hsel7, hsel8, hsel9, hs] at hc6
            norm_num at hc6
            exact hc6.symm
          rw [hax, nockAxisOf_two hwidth]
          exact hsG (by simp [hs])
      | s1 | s3 | s4 | cons =>
          rw [← hst, hs] at hact
          simp [secondRequestMask] at hact
    · simp only [Fin.reduceFinMk, Fin.isValue, Fin.val_two, slotRecord, slotActive]
        at hact hc6 ⊢
      cases hs : st with
      | s6 =>
          have hax : (R.problem.exec.computePubAt i).mr3.axis = 2 := by
            simp [computeTraceSubst, mr3Field, mr3Group, decFP, ext0, Expr.eval,
              NockVM.encRecC, hsel6, hsel9, hs] at hc6
            norm_num at hc6
            exact hc6.symm
          rw [hax, nockAxisOf_two hwidth]
          exact hs6 hs
      | s9 =>
          have hax : (R.problem.exec.computePubAt i).mr3.axis =
              coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩ := by
            simp [computeTraceSubst, mr3Field, mr3Group, decFP, ext0, Expr.eval,
              NockVM.encRecC, hsel6, hsel9, hs, htr, h44] at hc6
            exact hc6.symm
          have hK : MemoryTable.nockAxisOf (R.problem.exec.computePubAt i).mr3.axis =
              axisNatK A i := by
            rw [hax]
            simp [axisNatK, axisLeafK, hdec, hs]
          rw [hK]
          exact hs9 hs
      | s0 | s1 | s2 | s3 | s4 | s5 | s7 | s8 | cons =>
          rw [← hst, hs] at hact
          simp [thirdRequestMask] at hact
  -- assemble
  funext c
  unfold sampledSlotRecord
  by_cases h6 : (c : ℕ) = 6
  · have hc : c = 6 := Fin.ext h6
    subst hc
    simp only [show ((6 : Fin 9) : ℕ) = 6 from rfl, if_true]
    rw [hslot.1]
    simp [NockVM.encRecFormR, NockVM.encRecC]
  by_cases h8 : (c : ℕ) = 8
  · have hc : c = 8 := Fin.ext h8
    subst hc
    simp only [show ((8 : Fin 9) : ℕ) = 8 from rfl, if_true, show (8 : ℕ) ≠ 6 by decide,
      if_false]
    rw [hslot.2]
    simp [NockVM.encRecFormR, NockVM.encRecC]
  · simp only [h6, h8, if_false]
    have hc8 : (c : ℕ) < 8 := by omega
    have hcc := hcol ⟨c, hc8⟩
    rw [show 67 + 8 * (j : ℕ) + (c : ℕ) = 67 + 8 * (j : ℕ) + ((⟨c, hc8⟩ : Fin 8) : ℕ) from rfl,
      hcc]
    have hcast : (⟨(c : ℕ), hc8⟩ : Fin 8).castSucc = c := Fin.ext rfl
    rw [hcast]
    fin_cases c <;> (fin_cases j <;> simp_all [NockVM.encRecFormR, NockVM.encRecC, slotRecord])

/-- **Honest active request denominators are Form R encodes.** -/
theorem sampledDenom_eq_formR
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F)
    (env : CorrectedFinalTypedEnv F K)
    (j : Fin 3) (lam : K)
    (hsel : ∀ s : State, env.toSourceEnv.trace (Nock.Reified.opCol s) =
      if s = (R.problem.exec.computePubAt i).state then 1 else 0)
    (hcol : ∀ c : Fin 8,
      (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).eval
          (Env.ofSubst finalSampledNamespace env.toSourceEnv) =
        NockVM.encRecC
          (slotRecord R i j) 1 c.castSucc)
    (hγ : env.toSourceEnv.chal 7 = A.sampled.coins.gamma)
    (hpole : env.toSourceEnv.chal 8 = A.sampled.coins.pole)
    (h9 : env.chal 9 = lam)
    (hcb : env.certBase = exactFinalCertBase A i)
    (hce : env.certExt = exactFinalCertExt A i lam)
    (h41 : env.toSourceEnv.trace 54 = coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩)
    (h44 : env.toSourceEnv.trace 57 = coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩)
    (hact : slotActive R i j = 1) (x : K)
    (hx : (sampledSlotE .traceCur (67 + 8 * (j : ℕ))).eval
      (Env.ofSubst finalSampledNamespace env.toSourceEnv) = x) :
    ((sampledDenom .traceCur j).subst finalSampledNamespace).eval env.toSourceEnv =
      FiniteIO.compress A.sampled.coins
        (RecordCarrier.withExp (NockVM.encRecFormR
          (slotRecord R i j) lam) x) := by
  have hrec := sampledSlotRecord_eq_formR A i hsmall hwidth env j lam hsel hcol h9 hcb hce h41
    h44 hact
  set E' := Env.ofSubst finalSampledNamespace env.toSourceEnv with hE'
  have hγ' : E'.chal 6 = A.sampled.coins.gamma := by
    simp only [hE', Env.ofSubst, finalSampledNamespace, finalSampledGamma, sampledChallenge,
      sampledChallengeBase, Expr.eval]
    exact hγ
  have hpole' : E'.chal 7 = A.sampled.coins.pole := by
    simp only [hE', Env.ofSubst, finalSampledNamespace, finalSampledPole, sampledChallenge,
      sampledChallengeBase, Expr.eval]
    exact hpole
  rw [Expr.eval_subst, ← hrec]
  have hbase : (sampledDenom .traceCur j).eval E' =
      E'.chal 7 + (sampledRecordRLC .traceCur (67 + 8 * (j : ℕ))).eval E' := by
    fin_cases j <;> simp [sampledDenom, sampledPole, Expr.eval]
  rw [hbase, sampledRecordRLC_eval, hγ', hpole', FiniteIO.compress, hx]
  rfl
end

end OptimizedComputeFormRDenoms
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedComputeFormRDenoms.sampledDenom_eq_formR
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeFormRDenoms.sampledSlotRecord_eq_formR
