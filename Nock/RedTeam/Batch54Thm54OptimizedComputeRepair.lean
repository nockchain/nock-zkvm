import Nock.RedTeam.Batch53Thm54OptimizedComputeSubstitution
import Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates

/-!
Production now pins inactive-safe denominators instead. This artifact keeps
the former raw-pin gate locally, proves the old witness still attacks that retired definition, and
records the repaired production rejection. It is a regression control, not a current finding.
-/

namespace Nock.RedTeam.Batch54

set_option maxRecDepth 200000
set_option maxHeartbeats 16000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates

noncomputable local instance : Fintype ConcreteStrictPackage.K73cubic :=
  Fintype.ofFinite ConcreteStrictPackage.K73cubic
noncomputable local instance : DecidableEq ConcreteStrictPackage.K73cubic :=
  Classical.decEq ConcreteStrictPackage.K73cubic
local instance : CharP ConcreteStrictPackage.K73cubic 73 := inferInstance
local instance : CharP ConcreteStrictPackage.K73cubic
    (ringChar ConcreteStrictPackage.K73cubic) :=
  ringChar.charP ConcreteStrictPackage.K73cubic

/-! ## Repaired role allocation -/

/-- Every current-row source role is structurally distinct within its phase. -/
theorem current_role_allocation_nodup :
    [walkSubst .traceCur 0, walkSubst .traceCur 1, walkSubst .traceCur 2,
      walkSubst .traceCur 3, walkSubst .traceCur 4, walkSubst .traceCur 5,
      sampledIOSubst .traceCur 0, sampledIOSubst .traceCur 1,
      sampledIOSubst .traceCur 2, sampledIOSubst .traceCur 3,
      sampledIOSubst .traceCur 4, sampledIOSubst .traceCur 5,
      sampledIOSubst .traceCur 6].Nodup := by
  classical
  simp [walkSubst, sampledIOSubst, sampledDenomWitness, sampledActive, overlayCoord,
    lnCur, pubFP, ext0, Nock.Reified.allStates, overlayANat, overlayBNat,
    Nock.Reified.opCol]

/-- Every next-row source role is structurally distinct within its phase. -/
theorem next_role_allocation_nodup :
    [walkSubst .traceNext 0, walkSubst .traceNext 1, walkSubst .traceNext 2,
      walkSubst .traceNext 3, walkSubst .traceNext 4, walkSubst .traceNext 5,
      sampledIOSubst .traceNext 0, sampledIOSubst .traceNext 1,
      sampledIOSubst .traceNext 2, sampledIOSubst .traceNext 3,
      sampledIOSubst .traceNext 4, sampledIOSubst .traceNext 5,
      sampledIOSubst .traceNext 6].Nodup := by
  classical
  simp [walkSubst, sampledIOSubst, sampledDenomWitness, sampledActive, overlayCoord,
    lnCur, pubFP, ext0, Nock.Reified.allStates, overlayANat, overlayBNat,
    Nock.Reified.opCol]

theorem repaired_walk_map_and_collision :
    walkSubst .traceCur 1 = overlayCoord .traceCur 0 ∧
      walkSubst .traceNext 1 = overlayCoord .traceNext 0 ∧
      walkSubst .traceCur 5 ≠ sampledIOSubst .traceCur 0 ∧
      walkSubst .traceNext 5 ≠ sampledIOSubst .traceNext 0 :=
  ⟨rfl, rfl, walkMultiplier_ne_sampledAcc.1, walkMultiplier_ne_sampledAcc.2⟩

theorem wrong_coin_replay_rejected :
    ¬ FiniteIO.FiniteIOAccepts
      Batch26.honestRecords Batch26.shiftedCoins
      (Batch26.honestWitness.transport (c₂ := Batch26.shiftedCoins)) :=
  Batch52.wrong_coin_substitution_rejected

theorem malformed_denominator_and_active_rejected {K : Type*} [Field K]
    (env : Env K) (kind : VarKind) (hkind : kind = .traceCur ∨ kind = .traceNext)
    (hpins : ∀ j : Fin 3, (sampledDenomPin kind j).eval env = 0)
    (j : Fin 3) (badDenom badActive : K)
    (hdenom : badDenom ≠ (sampledSafeDenom kind j).eval env)
    (hactive : badActive ≠ (sampledActive kind j).eval env) :
    envValue (Env.ofSubst sampledIOSubst env) kind (1 + j) ≠ badDenom ∧
      envValue (Env.ofSubst sampledIOSubst env) kind (4 + j) ≠ badActive :=
  ⟨malformed_sampledDenom_rejected env kind hkind hpins j badDenom hdenom,
    malformed_sampledActive_rejected env kind hkind j badActive hactive⟩

/-! ## Semantic active indicators and nine-value carrier -/

def selectorEnv (st : State) : Env ℚ where
  trace i := if i = Nock.Reified.opCol st then 1 else 0
  traceNext i := if i = Nock.Reified.opCol st then 1 else 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- The three indicators are exactly the current row's one/two/three request-slot masks. -/
theorem active_masks_all_states (st : State) :
    [(sampledActive .traceCur 0).eval (selectorEnv st),
      (sampledActive .traceCur 1).eval (selectorEnv st),
      (sampledActive .traceCur 2).eval (selectorEnv st)] =
      match st with
      | .s0 | .s2 | .s5 | .s7 | .s8 => [1, 1, 0]
      | .s6 | .s9 => [1, 1, 1]
      | _ => [1, 0, 0] := by
  cases st <;>
    norm_num [sampledActive, selectorEnv, Nock.Reified.opCol, Expr.eval]

/-- The fingerprint codec does not carry the `sf*_st` tags — they are hosted in
overlay `2..4` and stamped back by `withOverlayTags` — so the round trip recovers `pub` up to the
three `Option` tags, which it reads off the overlay values. -/
theorem nine_value_roundtrip {F K : Type*} [Field F] [Field K]
    {inp : Inputs K} {pub : Pub K} {dec : Dec K} {ex : Extra K}
    {v : OptimizedComputeOverlay.SampledOverlayValues K}
    (h : Vcomp inp pub dec) :
    OptimizedComputeOverlay.sampledDecode inp
        (OptimizedComputeOverlay.sampledEncode (F := F) pub dec ex v) =
      (OptimizedComputeOverlay.withOverlayTags
        { pub with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none }
          v.toOverlayValues,
        dec, ex, v) :=
  OptimizedComputeOverlay.sampledDecode_encode_of_vcomp h

theorem concrete_F73_K73cubic_roundtrip :
    OptimizedComputeOverlay.sampledDecode (F := ConcreteStrictPackage.F73)
        ConcreteStrictPackage.honestLegacyFamily.problem.cfg.challenges.computeInputs
        (OptimizedComputeSampledTrace.encodedRowAt
          OptimizedComputeSampledTrace.Concrete.honestSampled
          OptimizedComputeSampledTrace.Concrete.honestRowIndex) =
      (OptimizedComputeOverlay.withOverlayTags
        { ConcreteStrictPackage.honestLegacyFamily.problem.exec.computePubAt
            OptimizedComputeSampledTrace.Concrete.honestRowIndex with
            sf1_st := none, sf2_st := none, sf3_st := none, certC? := none }
        (OptimizedComputeSampledTrace.overlayAt
          OptimizedComputeSampledTrace.Concrete.honestSampled
          OptimizedComputeSampledTrace.Concrete.honestRowIndex).toOverlayValues,
        ConcreteStrictPackage.honestLegacyFamily.problem.exec.computeDecAt
          OptimizedComputeSampledTrace.Concrete.honestRowIndex,
        ConcreteStrictPackage.honestAssignment.computeTableAux
          OptimizedComputeSampledTrace.Concrete.honestRowIndex,
        OptimizedComputeSampledTrace.overlayAt
          OptimizedComputeSampledTrace.Concrete.honestSampled
          OptimizedComputeSampledTrace.Concrete.honestRowIndex) :=
  OptimizedComputeSampledTrace.Concrete.honest_row_roundtrip

theorem overlay_denominators_are_same_assignment
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    (OptimizedComputeSampledTrace.overlayAt A i).denom0 =
        A.compress10
          (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr1
            R.problem.cfg.challenges.lam) ∧
      (OptimizedComputeSampledTrace.overlayAt A i).denom1 =
        OptimizedComputeSampledTrace.inactiveSafe
          (OptimizedComputeSampledTrace.secondRequestMask
            (R.problem.exec.computePubAt i).state)
          (A.compress10
            (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr2
            R.problem.cfg.challenges.lam)) ∧
      (OptimizedComputeSampledTrace.overlayAt A i).denom2 =
        OptimizedComputeSampledTrace.inactiveSafe
          (OptimizedComputeSampledTrace.thirdRequestMask
            (R.problem.exec.computePubAt i).state)
          (A.compress10
            (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr3
            R.problem.cfg.challenges.lam)) :=
  ⟨rfl, rfl, rfl⟩

/-- The raw inactive OP1 records still compress to zero under exact `(gamma,pole)=(0,0)` coins.
This is harmless after normalization: the committed safe denominators are one. -/
theorem concrete_honest_raw_inactive_denominators_zero :
    FiniteIO.compress
        OptimizedComputeSampledTrace.Concrete.honestSampled.sampled.coins
        (NockVM.encRec
          (ConcreteStrictPackage.honestLegacyFamily.problem.exec.computePubAt
            OptimizedComputeSampledTrace.Concrete.honestRowIndex).mr2) = 0 ∧
      FiniteIO.compress
        OptimizedComputeSampledTrace.Concrete.honestSampled.sampled.coins
        (NockVM.encRec
          (ConcreteStrictPackage.honestLegacyFamily.problem.exec.computePubAt
            OptimizedComputeSampledTrace.Concrete.honestRowIndex).mr3) = 0 := by
  rw [show OptimizedComputeSampledTrace.Concrete.honestSampled.sampled.coins =
    ConcreteStrictPackage.ioCoins by rfl]
  have hpub :
      ConcreteStrictPackage.honestLegacyFamily.problem.exec.computePubAt
          OptimizedComputeSampledTrace.Concrete.honestRowIndex =
        ConcreteStrictPackage.computePub ConcreteStrictPackage.honestSeed
          ConcreteStrictPackage.honestAlpha := by
    have h := ConcreteStrictPackage.honestRawLegacy_computePubAt_zero
    change
      ConcreteStrictPackage.honestLegacyFamily.problem.exec.computePubAt _ =
        ConcreteStrictPackage.computePub ConcreteStrictPackage.honestSeed
          ConcreteStrictPackage.honestAlpha at h
    let j : Fin ConcreteStrictPackage.honestLegacyFamily.problem.cfg.compRows :=
      ⟨0, ConcreteStrictPackage.honestLegacyFamily.problem.cfg.compRows_pos⟩
    have hij : OptimizedComputeSampledTrace.Concrete.honestRowIndex = j := by
      apply Fin.ext
      rfl
    rw [hij]
    exact h
  rw [hpub]
  change
    FiniteIO.compress ConcreteStrictPackage.ioCoins (NockVM.encRec MemRec.zero) = 0 ∧
      FiniteIO.compress ConcreteStrictPackage.ioCoins (NockVM.encRec MemRec.zero) = 0
  have hzero :
      NockVM.encRec (MemRec.zero : MemRec ConcreteStrictPackage.K73cubic) =
        fun _ => 0 := by
    funext i
    fin_cases i <;> rfl
  rw [hzero]
  simp [ConcreteStrictPackage.ioCoins, FiniteIO.compress, Walk.rlc]

theorem concrete_honest_safe_denominators_one :
    (OptimizedComputeSampledTrace.overlayAt
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom0 = 1 ∧
      (OptimizedComputeSampledTrace.overlayAt
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom1 = 1 ∧
      (OptimizedComputeSampledTrace.overlayAt
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom2 = 1 :=
  OptimizedComputeSampledTrace.Concrete.honest_safe_denominators

/-! ## Refold degree census -/

theorem repaired_degree_census :
    (refoldedPerStateGates.map Expr.degree).foldr Nat.max 0 = 4 ∧
      (∀ g ∈ optimizedSampledIOTransitionGates, g.degree ≤ 4) ∧
      ((List.range refoldedPerStateGates.length).zip
        (refoldedPerStateGates.map Expr.degree)).filter (fun x => 4 < x.2) = [] := by
  refine ⟨refoldedPerStateGates_max_degree,
    optimizedSampledIOTransitionGates_degree, ?_⟩
  decide

theorem op3_op5_refolds_are_exact_on_oneHot {K : Type*} [Field K]
    (env : Env K) (active : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = active then 1 else 0) :
    (op3ELeafBool.subst computeSubst).eval env = op3ELeafBoolRefold.eval env ∧
      (op5ELeafBool.subst computeSubst).eval env = op5ELeafBoolRefold.eval env :=
  ⟨op3ELeafBool_refold_eval_oneHot env active hsel,
    op5ELeafBool_refold_eval_oneHot env active hsel⟩


/-- The retired raw-denominator pin. Production uses `sampledDenomPin`, whose right side is
`sampledSafeDenom`. -/
def historicalRawDenomPin (kind : VarKind) (j : ℕ) : Expr :=
  .Sub (sampledDenomWitness kind j) (sampledDenom kind j)

def historicalRawDenomPinGates : List Expr :=
  [historicalRawDenomPin .traceCur 0, historicalRawDenomPin .traceCur 1,
    historicalRawDenomPin .traceCur 2]

def historicalRawSampledIOTransitionGates : List Expr :=
  historicalRawDenomPinGates ++ [optimizedFoldedProgStep3]

theorem historicalRawSampledIOTransitionGates_eval {K : Type*} [Field K] (env : Env K) :
    (∀ g ∈ historicalRawSampledIOTransitionGates, g.eval env = 0) ↔
      (∀ j : Fin 3,
        (sampledDenomWitness .traceCur j).eval env =
          (sampledDenom .traceCur j).eval env) ∧
      FoldedProgStep3
        ((sampledIOSubst .traceCur 0).eval env)
        ((sampledIOSubst .traceNext 0).eval env)
        ((sampledIOSubst .traceCur 1).eval env)
        ((sampledIOSubst .traceCur 2).eval env)
        ((sampledIOSubst .traceCur 3).eval env)
        ((sampledIOSubst .traceCur 4).eval env)
        ((sampledIOSubst .traceCur 5).eval env)
        ((sampledIOSubst .traceCur 6).eval env) := by
  rw [show
    (∀ g ∈ historicalRawSampledIOTransitionGates, g.eval env = 0) ↔
      ((historicalRawDenomPin .traceCur 0).eval env = 0 ∧
      (historicalRawDenomPin .traceCur 1).eval env = 0 ∧
      (historicalRawDenomPin .traceCur 2).eval env = 0 ∧
      optimizedFoldedProgStep3.eval env = 0) by
        simp [historicalRawSampledIOTransitionGates, historicalRawDenomPinGates]]
  rw [optimizedFoldedProgStep3_eval]
  constructor
  · rintro ⟨h0, h1, h2, hfold⟩
    refine ⟨fun j => ?_, hfold⟩
    fin_cases j
    · simpa [historicalRawDenomPin, Expr.eval] using sub_eq_zero.mp h0
    · simpa [historicalRawDenomPin, Expr.eval] using sub_eq_zero.mp h1
    · simpa [historicalRawDenomPin, Expr.eval] using sub_eq_zero.mp h2
  · rintro ⟨hpins, hfold⟩
    exact ⟨sub_eq_zero.mpr (hpins 0), sub_eq_zero.mpr (hpins 1),
      sub_eq_zero.mpr (hpins 2), hfold⟩

/-- An OP1-shaped normalized environment. The active record has denominator one; both inactive
zero records have denominator zero because `gamma = pole = 0`. The next accumulator is maliciously
set to two instead of the required one. -/
def cancellationEnv : Env ℚ where
  trace i :=
    if i = 1 then 1
    else if i = 16 then 1
    else if i = 46 then 1
    else 0
  traceNext i := if i = 45 then 2 else 0
  chal := fun _ => 0
  pub := fun _ => 0

theorem cancellation_values :
    (sampledIOSubst .traceCur 0).eval cancellationEnv = 0 ∧
      (sampledIOSubst .traceNext 0).eval cancellationEnv = 2 ∧
      (sampledIOSubst .traceCur 1).eval cancellationEnv = 1 ∧
      (sampledIOSubst .traceCur 2).eval cancellationEnv = 0 ∧
      (sampledIOSubst .traceCur 3).eval cancellationEnv = 0 ∧
      (sampledIOSubst .traceCur 4).eval cancellationEnv = 1 ∧
      (sampledIOSubst .traceCur 5).eval cancellationEnv = 0 ∧
      (sampledIOSubst .traceCur 6).eval cancellationEnv = 0 := by
  norm_num [sampledIOSubst, sampledDenomWitness, sampledActive, overlayCoord,
    cancellationEnv, pubFP, ext0, Nock.Reified.allStates, overlayANat, overlayBNat,
    Nock.Reified.opCol, Expr.eval]

theorem range_eight : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide

theorem cancellation_denominator_pins :
    ∀ j : Fin 3,
      (sampledDenomWitness .traceCur j).eval cancellationEnv =
        (sampledDenom .traceCur j).eval cancellationEnv := by
  intro j
  fin_cases j <;>
    norm_num [sampledDenomWitness, sampledDenom, sampledRecordRLC, range_eight,
      sampledGamma, sampledPole, computeTraceSubst, semanticPub, restoredPub,
      sourcePubAt, restoredAField, restoredBField, restoredIOHostField,
      restoredDenomHostField, mr2Field, mr2Group, mr3Field, mr3Group,
      cancellationEnv, Nock.Reified.allStates, overlayANat, overlayBNat,
      pubFP, decFP, lnPrev, lnCur, consInv, invGen, ext0, Nock.Reified.opCol,
      Expr.eval]
  all_goals
    norm_num [overlayCoord, pubFP, ext0, cancellationEnv, Expr.eval]

/-- **Retracted B54-F1 control.** All four gates of the retired raw-pin block vanish despite the
false active-slot step. -/
theorem historical_raw_gate_accepts_bad_active_step :
    (∀ g ∈ historicalRawSampledIOTransitionGates, g.eval cancellationEnv = 0) ∧
      (sampledIOSubst .traceNext 0).eval cancellationEnv ≠
        (sampledIOSubst .traceCur 0).eval cancellationEnv +
          (sampledIOSubst .traceCur 4).eval cancellationEnv *
            ((sampledIOSubst .traceCur 1).eval cancellationEnv)⁻¹ +
          (sampledIOSubst .traceCur 5).eval cancellationEnv *
            ((sampledIOSubst .traceCur 2).eval cancellationEnv)⁻¹ +
          (sampledIOSubst .traceCur 6).eval cancellationEnv *
            ((sampledIOSubst .traceCur 3).eval cancellationEnv)⁻¹ := by
  constructor
  · rw [historicalRawSampledIOTransitionGates_eval]
    refine ⟨cancellation_denominator_pins, ?_⟩
    rcases cancellation_values with ⟨hacc, hnext, hd0, hd1, hd2, ha0, ha1, ha2⟩
    rw [hacc, hnext, hd0, hd1, hd2, ha0, ha1, ha2]
    norm_num [FoldedProgStep3]
  · rcases cancellation_values with ⟨hacc, hnext, hd0, hd1, hd2, ha0, ha1, ha2⟩
    rw [hnext, hacc, ha0, hd0, ha1, hd1, ha2, hd2]
    norm_num

/-- The retired gate also fails to imply its inverse-witness conjunction. -/
theorem historical_raw_gate_does_not_imply_original_conjunction :
    (∀ g ∈ historicalRawSampledIOTransitionGates, g.eval cancellationEnv = 0) ∧
      ¬ ∃ inv0 inv1 inv2 : ℚ,
        (sampledIOSubst .traceCur 1).eval cancellationEnv * inv0 = 1 ∧
        (sampledIOSubst .traceCur 2).eval cancellationEnv * inv1 = 1 ∧
        (sampledIOSubst .traceCur 3).eval cancellationEnv * inv2 = 1 ∧
        (sampledIOSubst .traceNext 0).eval cancellationEnv =
          (sampledIOSubst .traceCur 0).eval cancellationEnv +
            (sampledIOSubst .traceCur 4).eval cancellationEnv * inv0 +
            (sampledIOSubst .traceCur 5).eval cancellationEnv * inv1 +
            (sampledIOSubst .traceCur 6).eval cancellationEnv * inv2 := by
  refine ⟨historical_raw_gate_accepts_bad_active_step.1, ?_⟩
  rintro ⟨inv0, inv1, inv2, h0, h1, h2, hstep⟩
  have hz := cancellation_values.2.2.2.1
  rw [hz] at h1
  norm_num at h1

theorem repaired_gate_rejects_historical_witness :
    ∃ g ∈ optimizedSampledIOTransitionGates, g.eval cancellationEnv ≠ 0 := by
  refine ⟨sampledDenomPin .traceCur 1, ?_, ?_⟩
  · simp [optimizedSampledIOTransitionGates, optimizedDenomPinGates]
  · norm_num [sampledDenomPin, sampledDenomWitness, sampledSafeDenom, sampledDenom,
      sampledRecordRLC, sampledActive, sampledGamma, sampledPole, overlayCoord,
      computeTraceSubst, semanticPub, restoredPub, sourcePubAt, restoredAField,
      restoredBField, restoredIOHostField, restoredDenomHostField, mr2Field, mr2Group,
      Nock.Reified.allStates, overlayANat, overlayBNat, pubFP, decFP, lnPrev, lnCur,
      consInv, invGen, ext0, Nock.Reified.opCol, cancellationEnv, Expr.eval]


theorem scope_guard_alias :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch53.scope_guard_alias

end Nock.RedTeam.Batch54

#print axioms Nock.RedTeam.Batch54.current_role_allocation_nodup
#print axioms Nock.RedTeam.Batch54.wrong_coin_replay_rejected
#print axioms Nock.RedTeam.Batch54.malformed_denominator_and_active_rejected
#print axioms Nock.RedTeam.Batch54.active_masks_all_states
#print axioms Nock.RedTeam.Batch54.nine_value_roundtrip
#print axioms Nock.RedTeam.Batch54.concrete_F73_K73cubic_roundtrip
#print axioms Nock.RedTeam.Batch54.repaired_degree_census
#print axioms Nock.RedTeam.Batch54.op3_op5_refolds_are_exact_on_oneHot
#print axioms Nock.RedTeam.Batch54.historical_raw_gate_accepts_bad_active_step
#print axioms Nock.RedTeam.Batch54.historical_raw_gate_does_not_imply_original_conjunction
#print axioms Nock.RedTeam.Batch54.repaired_gate_rejects_historical_witness
#print axioms Nock.RedTeam.Batch54.scope_guard_alias
