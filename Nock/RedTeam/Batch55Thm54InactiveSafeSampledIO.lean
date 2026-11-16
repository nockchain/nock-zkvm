import Nock.RedTeam.Batch54Thm54OptimizedComputeRepair

/-!
The inactive-safe sampled I/O gate block: safe-denominator inverse pins are trivially satisfiable on inactive slots and force the raw value to be nonzero on active slots, the production gate is equivalent to three safe inverse pins, and no cross-slot cancellation is possible. It also gives concrete cubic-field acceptance and mutation-rejection controls, an exact degree and variable census, and records that the four-gate block is not the full 21-gate basis.
-/


namespace Nock.RedTeam.Batch55

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

noncomputable local instance : Fintype ConcreteStrictPackage.K73cubic :=
  Fintype.ofFinite ConcreteStrictPackage.K73cubic
noncomputable local instance : DecidableEq ConcreteStrictPackage.K73cubic :=
  Classical.decEq ConcreteStrictPackage.K73cubic
local instance : CharP ConcreteStrictPackage.K73cubic 73 := inferInstance
local instance : CharP ConcreteStrictPackage.K73cubic
    (ringChar ConcreteStrictPackage.K73cubic) :=
  ringChar.charP ConcreteStrictPackage.K73cubic

/-! ## 1. Independent inactive-safe unfolding -/

theorem inactive_safe_is_one {K : Type*} [Field K] (raw : K) :
    SafeDenom 0 raw = 1 := by
  simp [SafeDenom]

theorem inactive_contribution_is_zero {K : Type*} [Field K] (inv : K) :
    (0 : K) * inv = 0 := by
  simp

theorem active_safe_is_raw {K : Type*} [Field K] (raw : K) :
    SafeDenom 1 raw = raw := by
  simp [SafeDenom]

theorem active_inverse_pin_forces_raw_nonzero {K : Type*} [Field K]
    (raw inv : K) (hpin : SafeDenom 1 raw * inv = 1) :
    raw ≠ 0 := by
  rw [active_safe_is_raw] at hpin
  intro hzero
  rw [hzero, zero_mul] at hpin
  exact zero_ne_one hpin

theorem inactive_inverse_pin_is_satisfiable_for_every_raw {K : Type*} [Field K] (raw : K) :
    ∃ inv : K, SafeDenom 0 raw * inv = 1 :=
  ⟨1, by simp [SafeDenom]⟩

/-! ## 2. Exact three-slot gate shape under one-hot-derived booleanity -/

theorem production_gate_iff_three_safe_inverse_pins
    {K : Type*} [Field K] (env : Env K) (activeState : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) =
      if st = activeState then 1 else 0)
    (hd0 : (sampledDenom .traceCur 0).eval env ≠ 0)
    (hd1 : (sampledActive .traceCur 1).eval env = 1 →
      (sampledDenom .traceCur 1).eval env ≠ 0)
    (hd2 : (sampledActive .traceCur 2).eval env = 1 →
      (sampledDenom .traceCur 2).eval env ≠ 0) :
    (∀ g ∈ optimizedSampledIOTransitionGates, g.eval env = 0) ↔
      (∀ j : Fin 3,
        (sampledDenomWitness .traceCur j).eval env =
          (sampledSafeDenom .traceCur j).eval env) ∧
      ∃ inv0 inv1 inv2 : K,
        (sampledDenomWitness .traceCur 0).eval env * inv0 = 1 ∧
        (sampledDenomWitness .traceCur 1).eval env * inv1 = 1 ∧
        (sampledDenomWitness .traceCur 2).eval env * inv2 = 1 ∧
        (sampledIOSubst .traceNext 0).eval env =
          (sampledIOSubst .traceCur 0).eval env +
            (sampledActive .traceCur 0).eval env * inv0 +
            (sampledActive .traceCur 1).eval env * inv1 +
            (sampledActive .traceCur 2).eval env * inv2 := by
  have hb0 := sampledActive_boolean_of_oneHot env .traceCur (Or.inl rfl)
    activeState hsel (0 : Fin 3)
  have hb1 := sampledActive_boolean_of_oneHot env .traceCur (Or.inl rfl)
    activeState hsel (1 : Fin 3)
  have hb2 := sampledActive_boolean_of_oneHot env .traceCur (Or.inl rfl)
    activeState hsel (2 : Fin 3)
  have hs0 :
      (sampledSafeDenom .traceCur 0).eval env =
        SafeDenom ((sampledActive .traceCur 0).eval env)
          ((sampledDenom .traceCur 0).eval env) := by
    simp [sampledSafeDenom, SafeDenom, Expr.eval]
  have hs1 :
      (sampledSafeDenom .traceCur 1).eval env =
        SafeDenom ((sampledActive .traceCur 1).eval env)
          ((sampledDenom .traceCur 1).eval env) := by
    simp [sampledSafeDenom, SafeDenom, Expr.eval]
  have hs2 :
      (sampledSafeDenom .traceCur 2).eval env =
        SafeDenom ((sampledActive .traceCur 2).eval env)
          ((sampledDenom .traceCur 2).eval env) := by
    simp [sampledSafeDenom, SafeDenom, Expr.eval]
  have hn0 :
      (sampledSafeDenom .traceCur 0).eval env ≠ 0 := by
    rw [hs0]
    exact safeDenom_ne_zero _ _ hb0 (fun _ => hd0)
  have hn1 :
      (sampledSafeDenom .traceCur 1).eval env ≠ 0 := by
    rw [hs1]
    exact safeDenom_ne_zero _ _ hb1 hd1
  have hn2 :
      (sampledSafeDenom .traceCur 2).eval env ≠ 0 := by
    rw [hs2]
    exact safeDenom_ne_zero _ _ hb2 hd2
  rw [optimizedSampledIOTransitionGates_eval]
  constructor
  · rintro ⟨hpins, hfold⟩
    have hpin0 := hpins (0 : Fin 3)
    have hpin1 := hpins (1 : Fin 3)
    have hpin2 := hpins (2 : Fin 3)
    have hw0 : (sampledDenomWitness .traceCur 0).eval env ≠ 0 := by
      rw [show (sampledDenomWitness .traceCur 0).eval env =
        (sampledSafeDenom .traceCur 0).eval env by simpa using hpin0]
      exact hn0
    have hw1 : (sampledDenomWitness .traceCur 1).eval env ≠ 0 := by
      rw [show (sampledDenomWitness .traceCur 1).eval env =
        (sampledSafeDenom .traceCur 1).eval env by simpa using hpin1]
      exact hn1
    have hw2 : (sampledDenomWitness .traceCur 2).eval env ≠ 0 := by
      rw [show (sampledDenomWitness .traceCur 2).eval env =
        (sampledSafeDenom .traceCur 2).eval env by simpa using hpin2]
      exact hn2
    exact ⟨hpins,
      (foldedProgStep3_iff_inverse_witnesses
        ((sampledIOSubst .traceCur 0).eval env)
        ((sampledIOSubst .traceNext 0).eval env)
        ((sampledIOSubst .traceCur 1).eval env)
        ((sampledIOSubst .traceCur 2).eval env)
        ((sampledIOSubst .traceCur 3).eval env)
        ((sampledIOSubst .traceCur 4).eval env)
        ((sampledIOSubst .traceCur 5).eval env)
        ((sampledIOSubst .traceCur 6).eval env) hw0 hw1 hw2).1 hfold⟩
  · rintro ⟨hpins, hinv⟩
    rcases hinv with ⟨inv0, inv1, inv2, hi0, hi1, hi2, hstep⟩
    have hw0 : (sampledDenomWitness .traceCur 0).eval env ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hi0
      exact zero_ne_one hi0
    have hw1 : (sampledDenomWitness .traceCur 1).eval env ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hi1
      exact zero_ne_one hi1
    have hw2 : (sampledDenomWitness .traceCur 2).eval env ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hi2
      exact zero_ne_one hi2
    refine ⟨hpins, (foldedProgStep3_iff_inverse_witnesses
      ((sampledIOSubst .traceCur 0).eval env)
      ((sampledIOSubst .traceNext 0).eval env)
      ((sampledIOSubst .traceCur 1).eval env)
      ((sampledIOSubst .traceCur 2).eval env)
      ((sampledIOSubst .traceCur 3).eval env)
      ((sampledIOSubst .traceCur 4).eval env)
      ((sampledIOSubst .traceCur 5).eval env)
      ((sampledIOSubst .traceCur 6).eval env) hw0 hw1 hw2).2 ?_⟩
    exact ⟨inv0, inv1, inv2, hi0, hi1, hi2, hstep⟩

theorem no_cross_slot_cancellation
    {K : Type*} [Field K] (env : Env K) (activeState : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) =
      if st = activeState then 1 else 0)
    (hd0 : (sampledDenom .traceCur 0).eval env ≠ 0)
    (hd1 : (sampledActive .traceCur 1).eval env = 1 →
      (sampledDenom .traceCur 1).eval env ≠ 0)
    (hd2 : (sampledActive .traceCur 2).eval env = 1 →
      (sampledDenom .traceCur 2).eval env ≠ 0)
    (hgates : ∀ g ∈ optimizedSampledIOTransitionGates, g.eval env = 0) :
    ∃ inv0 inv1 inv2 : K,
      (sampledDenomWitness .traceCur 0).eval env * inv0 = 1 ∧
      (sampledDenomWitness .traceCur 1).eval env * inv1 = 1 ∧
      (sampledDenomWitness .traceCur 2).eval env * inv2 = 1 ∧
      (sampledIOSubst .traceNext 0).eval env =
        (sampledIOSubst .traceCur 0).eval env +
          (sampledActive .traceCur 0).eval env * inv0 +
          (sampledActive .traceCur 1).eval env * inv1 +
          (sampledActive .traceCur 2).eval env * inv2 :=
  ((production_gate_iff_three_safe_inverse_pins env activeState hsel hd0 hd1 hd2).1
    hgates).2

theorem safe_denominator_product_nonzero {K : Type*} [Field K]
    (a0 a1 a2 d0 d1 d2 : K)
    (hb0 : a0 = 0 ∨ a0 = 1) (hb1 : a1 = 0 ∨ a1 = 1)
    (hb2 : a2 = 0 ∨ a2 = 1)
    (hd0 : a0 = 1 → d0 ≠ 0) (hd1 : a1 = 1 → d1 ≠ 0)
    (hd2 : a2 = 1 → d2 ≠ 0) :
    SafeDenom a0 d0 * SafeDenom a1 d1 * SafeDenom a2 d2 ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (safeDenom_ne_zero _ _ hb0 hd0) (safeDenom_ne_zero _ _ hb1 hd1))
    (safeDenom_ne_zero _ _ hb2 hd2)

theorem wrong_inverse_pin_rejected {K : Type*} [Field K]
    (d inv bad : K) (hpin : d * inv = 1) (hbad : bad ≠ inv) :
    d * bad ≠ 1 := by
  intro hbadPin
  have hinv : inv = d⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hpin)
  have hbadInv : bad = d⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hbadPin)
  exact hbad (hbadInv.trans hinv.symm)

theorem nonboolean_active_incompatible_with_oneHot
    {K : Type*} [Field K] (env : Env K) (activeState : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) =
      if st = activeState then 1 else 0)
    (j : Fin 3)
    (hbad : (sampledActive .traceCur j).eval env ≠ 0 ∧
      (sampledActive .traceCur j).eval env ≠ 1) :
    False := by
  rcases sampledActive_boolean_of_oneHot env .traceCur (Or.inl rfl)
      activeState hsel j with h0 | h1
  · exact hbad.1 h0
  · exact hbad.2 h1

/-! ## 3. The earlier gate block is rejected by the repaired block -/

def oldBatch54Env : Env ℚ where
  trace i :=
    if i = 1 then 1
    else if i = 16 then 1
    else if i = 46 then 1
    else 0
  traceNext i := if i = 45 then 2 else 0
  chal := fun _ => 0
  pub := fun _ => 0

theorem oldBatch54Env_eq : oldBatch54Env = Batch54.cancellationEnv := rfl

theorem repaired_specific_gate_fails :
    (sampledDenomPin .traceCur 1).eval oldBatch54Env ≠ 0 := by
  rw [oldBatch54Env_eq]
  norm_num [sampledDenomPin, sampledDenomWitness, sampledSafeDenom, sampledDenom,
    sampledRecordRLC, sampledActive, sampledGamma, sampledPole, overlayCoord,
    computeTraceSubst, semanticPub, restoredPub, sourcePubAt, restoredAField,
    restoredBField, restoredIOHostField, restoredDenomHostField, mr2Field, mr2Group,
    Nock.Reified.allStates, overlayANat, overlayBNat, pubFP, decFP, lnPrev, lnCur,
    consInv, invGen, ext0, Nock.Reified.opCol, Batch54.cancellationEnv, Expr.eval]

theorem repaired_block_rejects_oldBatch54 :
    ∃ g ∈ optimizedSampledIOTransitionGates, g.eval oldBatch54Env ≠ 0 := by
  rw [oldBatch54Env_eq]
  exact Batch54.repaired_gate_rejects_historical_witness

/-! ## 4. Concrete cubic non-vacuity and mutation controls -/

theorem concrete_op1_safe_denominators_and_acceptance :
    (OptimizedComputeSampledTrace.overlayAt
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom0 = 1 ∧
      (OptimizedComputeSampledTrace.overlayAt
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom1 = 1 ∧
      (OptimizedComputeSampledTrace.overlayAt
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom2 = 1 ∧
      FoldedProgStep3 (0 : ConcreteStrictPackage.K73cubic) 1 1 1 1 1 0 0 ∧
      FiniteIO.FiniteIOAccepts
        OptimizedComputeSampledTrace.Concrete.honestSampled.sampled.records
        OptimizedComputeSampledTrace.Concrete.honestSampled.sampled.coins
        OptimizedComputeSampledTrace.Concrete.honestSampled.sampled.witness := by
  rcases OptimizedComputeSampledTrace.Concrete.honest_safe_denominators with
    ⟨h0, h1, h2⟩
  exact ⟨h0, h1, h2, by norm_num [FoldedProgStep3],
    OptimizedComputeSampledTrace.Concrete.honestSampled.sampled.accepts⟩

theorem concrete_op1_forces_accNext_one
    (accNext : ConcreteStrictPackage.K73cubic)
    (h : FoldedProgStep3 0 accNext 1 1 1 1 0 0) :
    accNext = 1 := by
  simpa [FoldedProgStep3] using h

theorem concrete_wrong_coin_rejected :
    ¬ FiniteIO.FiniteIOAccepts
      Batch26.honestRecords Batch26.shiftedCoins
      (Batch26.honestWitness.transport (c₂ := Batch26.shiftedCoins)) :=
  Batch52.wrong_coin_substitution_rejected

theorem active_raw_denominator_mutation_rejected {K : Type*} [Field K]
    (env : Env K) (kind : VarKind) (hkind : kind = .traceCur ∨ kind = .traceNext)
    (hpins : ∀ j : Fin 3, (sampledDenomPin kind j).eval env = 0)
    (j : Fin 3) (hactive : (sampledActive kind j).eval env = 1)
    (bad : K) (hbad : bad ≠ (sampledDenom kind j).eval env) :
    envValue (Env.ofSubst sampledIOSubst env) kind (1 + j) ≠ bad := by
  apply malformed_sampledDenom_rejected env kind hkind hpins j bad
  simpa [sampledSafeDenom, Expr.eval, hactive] using hbad

theorem wrong_active_rejected {K : Type*} [Field K]
    (env : Env K) (kind : VarKind) (hkind : kind = .traceCur ∨ kind = .traceNext)
    (j : Fin 3) (bad : K)
    (hbad : bad ≠ (sampledActive kind j).eval env) :
    envValue (Env.ofSubst sampledIOSubst env) kind (4 + j) ≠ bad :=
  malformed_sampledActive_rejected env kind hkind j bad hbad

theorem wrong_terminal_rejected :
    ¬ FiniteIO.FiniteIOAccepts Batch26.honestRecords Batch26.honestCoins
      Batch26.wrongEndpointWitness :=
  Batch26.b26_wrong_endpoint_rejected

/-! ## 5. Degree, variable, and field-boundary census -/

theorem exact_repaired_gate_census :
    optimizedSampledIOTransitionGates.length = 4 ∧
      (optimizedSampledIOTransitionGates.map Expr.degree).foldr Nat.max 0 = 4 ∧
      ∀ g ∈ optimizedSampledIOTransitionGates, g.degree ≤ 4 :=
  ⟨optimizedSampledIOTransitionGates_length,
    optimizedSampledIOTransitionGates_max_degree,
    optimizedSampledIOTransitionGates_degree⟩

theorem exact_repaired_gate_bodies :
    optimizedSampledIOTransitionGates =
      [sampledDenomPin .traceCur 0, sampledDenomPin .traceCur 1,
        sampledDenomPin .traceCur 2, optimizedFoldedProgStep3] :=
  rfl

theorem compute_decoder_variable_boundary
    (kind : VarKind) (i : Fin 94)
    (hkind : kind = .traceCur ∨ kind = .traceNext) :
    ∀ x ∈ (computeTraceSubst kind i).vars,
      match x.1 with
      | .traceCur | .traceNext => x.2 < 71
      | .challenge => x.2 < 6
      | .publicVal => True :=
  Batch53.all_94_source_columns_have_physical_decoders kind i hkind

theorem sampled_coin_variable_boundary :
    sampledGamma = .Var .challenge 6 ∧ sampledPole = .Var .challenge 7 :=
  ⟨rfl, rfl⟩

def evaluatedRepairedGateBlock {K : Type*} [Field K] (env : Env K) : List K :=
  optimizedSampledIOTransitionGates.map fun g => g.eval env

theorem evaluatedRepairedGateBlock_length {K : Type*} [Field K] (env : Env K) :
    (evaluatedRepairedGateBlock env).length = 4 := by
  simp [evaluatedRepairedGateBlock, optimizedSampledIOTransitionGates_length]

/-! ## 6. Scope: the sampled block is not the full 21-gate basis -/

theorem sampled_block_is_not_complete_21_basis :
    optimizedSampledIOTransitionGates.length = 4 ∧
      optimizedSampledIOTransitionGates.length < 21 :=
  ⟨optimizedSampledIOTransitionGates_length, by decide⟩

def strict_package_still_requires_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :=
  Batch53.strict_package_still_requires_B29 P

theorem paper_alias_is_still_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Batch54.scope_guard_alias

end
end Nock.RedTeam.Batch55

#print axioms Nock.RedTeam.Batch55.inactive_safe_is_one
#print axioms Nock.RedTeam.Batch55.production_gate_iff_three_safe_inverse_pins
#print axioms Nock.RedTeam.Batch55.no_cross_slot_cancellation
#print axioms Nock.RedTeam.Batch55.safe_denominator_product_nonzero
#print axioms Nock.RedTeam.Batch55.wrong_inverse_pin_rejected
#print axioms Nock.RedTeam.Batch55.nonboolean_active_incompatible_with_oneHot
#print axioms Nock.RedTeam.Batch55.repaired_specific_gate_fails
#print axioms Nock.RedTeam.Batch55.repaired_block_rejects_oldBatch54
#print axioms Nock.RedTeam.Batch55.concrete_op1_safe_denominators_and_acceptance
#print axioms Nock.RedTeam.Batch55.concrete_op1_forces_accNext_one
#print axioms Nock.RedTeam.Batch55.concrete_wrong_coin_rejected
#print axioms Nock.RedTeam.Batch55.active_raw_denominator_mutation_rejected
#print axioms Nock.RedTeam.Batch55.wrong_active_rejected
#print axioms Nock.RedTeam.Batch55.wrong_terminal_rejected
#print axioms Nock.RedTeam.Batch55.exact_repaired_gate_census
#print axioms Nock.RedTeam.Batch55.exact_repaired_gate_bodies
#print axioms Nock.RedTeam.Batch55.compute_decoder_variable_boundary
#print axioms Nock.RedTeam.Batch55.sampled_block_is_not_complete_21_basis
#print axioms Nock.RedTeam.Batch55.strict_package_still_requires_B29
#print axioms Nock.RedTeam.Batch55.paper_alias_is_still_forest
