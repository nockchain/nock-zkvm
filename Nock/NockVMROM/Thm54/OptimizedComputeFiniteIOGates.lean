import Nock.NockVMROM.Thm54.FiniteFieldIOAIR
import Nock.NockVMROM.Thm54.ComputeSampledIOCoResidence
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution

/-!
# Degree-four folded sampled-IO gate for compute rows

A compute row emits at most three requests.  Rather than storing three inverse columns, one
degree-four gate clears three inactive-safe sampled denominators at once:

`(acc' - acc)d₀d₁d₂ = a₀d₁d₂ + a₁d₀d₂ + a₂d₀d₁`.

Here `aⱼ ∈ {0,1}` marks whether slot `j` is emitted.  The committed input is
`safeDⱼ = aⱼ·dⱼ + (1-aⱼ)`, where `dⱼ = pole + RLC^gamma(record_j)`.  Thus an inactive slot is one,
not its potentially-zero raw record compression. Under bad-pole exclusion for active records this
is equivalent to the emitted-request inverse equations followed by the request accumulator step.
Its trace degree is exactly four.

This module supplies the sampled-IO member of the authorized folded extension basis.  It does not
claim that the remaining compute/walk folds have already been assembled into the complete
twenty-one-element list.
-/

namespace Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates

open Nock
open Nock.Reified
open OptimizedComputeSubstitution

noncomputable section

variable {K : Type*} [Field K]

/-- Physical local layout for the folded request gate:
`0=acc`, `1..3=denominators`, `4..6=active-slot indicators`; next `0=acc'`. -/
def foldedProgStep3 : Expr :=
  .Sub
    (.Mul (.Mul (.Mul (.Sub (Trans.tn 0) (tc 0)) (tc 1)) (tc 2)) (tc 3))
    (.Add
      (.Add
        (.Mul (.Mul (tc 4) (tc 2)) (tc 3))
        (.Mul (.Mul (tc 5) (tc 1)) (tc 3)))
      (.Mul (.Mul (tc 6) (tc 1)) (tc 2)))

/-- The sampled-IO folded transition is load-bearing and has the required degree bound. -/
theorem foldedProgStep3_degree : foldedProgStep3.degree = 4 := by
  decide

/-- Semantic polynomial represented by `foldedProgStep3`. -/
def FoldedProgStep3 (acc accNext d0 d1 d2 a0 a1 a2 : K) : Prop :=
  (accNext - acc) * d0 * d1 * d2 =
    a0 * d1 * d2 + a1 * d0 * d2 + a2 * d0 * d1

/-- Scalar inactive-safe denominator used by the symbolic decoder and the honest encoder. -/
def SafeDenom (active denom : K) : K :=
  active * denom + (1 - active)

theorem safeDenom_ne_zero (active denom : K)
    (hbool : active = 0 ∨ active = 1)
    (hactive : active = 1 → denom ≠ 0) :
    SafeDenom active denom ≠ 0 := by
  rcases hbool with rfl | rfl
  · simp [SafeDenom]
  · simpa [SafeDenom] using hactive rfl

theorem active_mul_safeDenom_inv (active denom : K)
    (hbool : active = 0 ∨ active = 1) :
    active * (SafeDenom active denom)⁻¹ = active * denom⁻¹ := by
  rcases hbool with rfl | rfl <;> simp [SafeDenom]

/-- Exact evaluation theorem for the reified degree-four gate. -/
theorem foldedProgStep3_eval
    (env : Env K) :
    foldedProgStep3.eval env = 0 ↔
      FoldedProgStep3
        (env.trace 0) (env.traceNext 0)
        (env.trace 1) (env.trace 2) (env.trace 3)
        (env.trace 4) (env.trace 5) (env.trace 6) := by
  simp only [foldedProgStep3, Expr.eval, FoldedProgStep3]
  constructor <;> intro h
  · exact sub_eq_zero.mp h
  · exact sub_eq_zero.mpr h

/-- Clearing the three nonzero denominators is equivalent to the unfurled finite-field request
accumulator update. -/
theorem foldedProgStep3_iff
    (acc accNext d0 d1 d2 a0 a1 a2 : K)
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) :
    FoldedProgStep3 acc accNext d0 d1 d2 a0 a1 a2 ↔
      accNext =
        acc + a0 * d0⁻¹ + a1 * d1⁻¹ + a2 * d2⁻¹ := by
  change
    (accNext - acc) * d0 * d1 * d2 =
        a0 * d1 * d2 + a1 * d0 * d2 + a2 * d0 * d1 ↔ _
  constructor
  · intro h
    field_simp [hd0, hd1, hd2]
    linear_combination h
  · intro h
    field_simp [hd0, hd1, hd2] at h
    linear_combination h

/-- The folded gate is equivalent to three inverse pins plus one unfurled accumulator step,
matching the semantics of `FiniteFieldIOAIR.ioInvPin` and `ioProgAccStep`. -/
theorem foldedProgStep3_iff_inverse_witnesses
    (acc accNext d0 d1 d2 a0 a1 a2 : K)
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) :
    FoldedProgStep3 acc accNext d0 d1 d2 a0 a1 a2 ↔
      ∃ inv0 inv1 inv2 : K,
        d0 * inv0 = 1 ∧ d1 * inv1 = 1 ∧ d2 * inv2 = 1 ∧
        accNext = acc + a0 * inv0 + a1 * inv1 + a2 * inv2 := by
  rw [foldedProgStep3_iff acc accNext d0 d1 d2 a0 a1 a2 hd0 hd1 hd2]
  constructor
  · intro h
    exact ⟨d0⁻¹, d1⁻¹, d2⁻¹, mul_inv_cancel₀ hd0, mul_inv_cancel₀ hd1,
      mul_inv_cancel₀ hd2, h⟩
  · rintro ⟨inv0, inv1, inv2, h0, h1, h2, hstep⟩
    have hi0 : inv0 = d0⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h0)
    have hi1 : inv1 = d1⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h1)
    have hi2 : inv2 = d2⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h2)
    simpa [hi0, hi1, hi2] using hstep

/-- Inactive-safe exactness. Raw inactive denominators need no nonzero premise and contribute
zero; only active slots require a nonzero compressed record. -/
theorem foldedProgStep3_safe_iff
    (acc accNext d0 d1 d2 a0 a1 a2 : K)
    (ha0 : a0 = 0 ∨ a0 = 1) (ha1 : a1 = 0 ∨ a1 = 1) (ha2 : a2 = 0 ∨ a2 = 1)
    (hd0 : a0 = 1 → d0 ≠ 0) (hd1 : a1 = 1 → d1 ≠ 0)
    (hd2 : a2 = 1 → d2 ≠ 0) :
    FoldedProgStep3 acc accNext
        (SafeDenom a0 d0) (SafeDenom a1 d1) (SafeDenom a2 d2) a0 a1 a2 ↔
      accNext = acc + a0 * d0⁻¹ + a1 * d1⁻¹ + a2 * d2⁻¹ := by
  rw [foldedProgStep3_iff acc accNext
    (SafeDenom a0 d0) (SafeDenom a1 d1) (SafeDenom a2 d2) a0 a1 a2
    (safeDenom_ne_zero a0 d0 ha0 hd0)
    (safeDenom_ne_zero a1 d1 ha1 hd1)
    (safeDenom_ne_zero a2 d2 ha2 hd2)]
  rw [active_mul_safeDenom_inv a0 d0 ha0,
    active_mul_safeDenom_inv a1 d1 ha1,
    active_mul_safeDenom_inv a2 d2 ha2]

theorem foldedProgStep3_safe_iff_inverse_witnesses
    (acc accNext d0 d1 d2 a0 a1 a2 : K)
    (ha0 : a0 = 0 ∨ a0 = 1) (ha1 : a1 = 0 ∨ a1 = 1) (ha2 : a2 = 0 ∨ a2 = 1)
    (hd0 : a0 = 1 → d0 ≠ 0) (hd1 : a1 = 1 → d1 ≠ 0)
    (hd2 : a2 = 1 → d2 ≠ 0) :
    FoldedProgStep3 acc accNext
        (SafeDenom a0 d0) (SafeDenom a1 d1) (SafeDenom a2 d2) a0 a1 a2 ↔
      ∃ inv0 inv1 inv2 : K,
        SafeDenom a0 d0 * inv0 = 1 ∧
        SafeDenom a1 d1 * inv1 = 1 ∧
        SafeDenom a2 d2 * inv2 = 1 ∧
        accNext = acc + a0 * inv0 + a1 * inv1 + a2 * inv2 :=
  foldedProgStep3_iff_inverse_witnesses acc accNext
    (SafeDenom a0 d0) (SafeDenom a1 d1) (SafeDenom a2 d2) a0 a1 a2
    (safeDenom_ne_zero a0 d0 ha0 hd0)
    (safeDenom_ne_zero a1 d1 ha1 hd1)
    (safeDenom_ne_zero a2 d2 ha2 hd2)

/-- The finite-IO contribution to the future extension transition list is a real expression, not a
dummy or zero gate. -/
def sampledIOTransitionGates : List Expr := [foldedProgStep3]

@[simp] theorem sampledIOTransitionGates_length :
    sampledIOTransitionGates.length = 1 := rfl

theorem sampledIOTransitionGate_nonzero :
    foldedProgStep3 ≠ (.Const 0 : Expr) := by
  intro h
  cases h

/-! ## Production fixed-overlay gate block -/

def optimizedDenomPinGates : List Expr :=
  [sampledDenomPin .traceCur 0, sampledDenomPin .traceCur 1,
    sampledDenomPin .traceCur 2]

def optimizedFoldedProgStep3 : Expr :=
  foldedProgStep3.subst sampledIOSubst

def optimizedSampledIOTransitionGates : List Expr :=
  optimizedDenomPinGates ++ [optimizedFoldedProgStep3]

def legacyDenomPinGates : List Expr :=
  [legacySampledDenomPin .traceCur 0, legacySampledDenomPin .traceCur 1,
    legacySampledDenomPin .traceCur 2]

def legacySampledIOTransitionGates : List Expr :=
  legacyDenomPinGates ++ [optimizedFoldedProgStep3]

@[simp] theorem legacySampledIOTransitionGates_length :
    legacySampledIOTransitionGates.length = 4 := rfl

theorem legacySampledIOTransitionGates_degree :
    ∀ g ∈ legacySampledIOTransitionGates, g.degree ≤ 4 := by
  intro g hg
  simp only [legacySampledIOTransitionGates, legacyDenomPinGates, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl) | rfl <;> decide

@[simp] theorem optimizedSampledIOTransitionGates_length :
    optimizedSampledIOTransitionGates.length = 4 := rfl

theorem optimizedFoldedProgStep3_degree :
    optimizedFoldedProgStep3.degree = 4 := by
  decide

set_option maxRecDepth 100000 in
theorem optimizedDenomPinGates_degree :
    ∀ g ∈ optimizedDenomPinGates, g.degree ≤ 4 := by
  intro g hg
  simp only [optimizedDenomPinGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> decide

theorem optimizedSampledIOTransitionGates_degree :
    ∀ g ∈ optimizedSampledIOTransitionGates, g.degree ≤ 4 := by
  intro g hg
  simp only [optimizedSampledIOTransitionGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact (optimizedDenomPinGates_degree g hg).trans (by decide)
  · rw [optimizedFoldedProgStep3_degree]

set_option maxRecDepth 100000 in
/-- Exact post-substitution degree census for the repaired sampled-IO block. -/
theorem optimizedSampledIOTransitionGates_max_degree :
    (optimizedSampledIOTransitionGates.map Expr.degree).foldr Nat.max 0 = 4 := by
  decide

theorem optimizedFoldedProgStep3_eval (env : Env K) :
    optimizedFoldedProgStep3.eval env = 0 ↔
      FoldedProgStep3
        ((sampledIOSubst .traceCur 0).eval env)
        ((sampledIOSubst .traceNext 0).eval env)
        ((sampledIOSubst .traceCur 1).eval env)
        ((sampledIOSubst .traceCur 2).eval env)
        ((sampledIOSubst .traceCur 3).eval env)
        ((sampledIOSubst .traceCur 4).eval env)
        ((sampledIOSubst .traceCur 5).eval env)
        ((sampledIOSubst .traceCur 6).eval env) := by
  rw [optimizedFoldedProgStep3, Expr.eval_subst, foldedProgStep3_eval]
  rfl

theorem optimizedSampledIOTransitionGates_eval (env : Env K) :
    (∀ g ∈ optimizedSampledIOTransitionGates, g.eval env = 0) ↔
      (∀ j : Fin 3,
        (sampledDenomWitness .traceCur j).eval env =
          (sampledSafeDenom .traceCur j).eval env) ∧
      FoldedProgStep3
        ((sampledIOSubst .traceCur 0).eval env)
        ((sampledIOSubst .traceNext 0).eval env)
        ((sampledIOSubst .traceCur 1).eval env)
        ((sampledIOSubst .traceCur 2).eval env)
        ((sampledIOSubst .traceCur 3).eval env)
        ((sampledIOSubst .traceCur 4).eval env)
        ((sampledIOSubst .traceCur 5).eval env)
        ((sampledIOSubst .traceCur 6).eval env) := by
  have hlist :
      (∀ g ∈ optimizedSampledIOTransitionGates, g.eval env = 0) ↔
      ((sampledDenomPin .traceCur 0).eval env = 0 ∧
      (sampledDenomPin .traceCur 1).eval env = 0 ∧
      (sampledDenomPin .traceCur 2).eval env = 0 ∧
      optimizedFoldedProgStep3.eval env = 0) := by
    simp [optimizedSampledIOTransitionGates, optimizedDenomPinGates]
  rw [hlist]
  constructor
  · rintro ⟨h0, h1, h2, hfold⟩
    refine ⟨?_, (optimizedFoldedProgStep3_eval env).1 hfold⟩
    exact (sampledDenomPins_eval_iff env .traceCur).1 fun j => by
      fin_cases j <;> assumption
  · rintro ⟨hpins, hfold⟩
    have hp := (sampledDenomPins_eval_iff env .traceCur).2 hpins
    exact ⟨hp 0, hp 1, hp 2, (optimizedFoldedProgStep3_eval env).2 hfold⟩

/-! ## The anchored step: `acc_after` in witness role `60`

The
paper's `acc_prog(i)` is one column read at `i-1` and `i`; its terminal value
is the RAP output `requests = acc_prog(h₁)`.  At the last
row the step now *defines* `acc_after(h₁)`, which the terminal gate compares with `requests`. -/

/-- Raw index of the `acc_after` witness: extension role `60` of the `13/62` layout. -/
def accAfterIndex : ℕ := 73

/-- `sampledIOSubst` with the next-row accumulator replaced by the current row's `acc_after`. -/
def accAfterIOSubst : VarKind → ℕ → Expr
  | .traceNext, 0 => .Var .traceCur accAfterIndex
  | kind, i => sampledIOSubst kind i

/-- The unmasked accumulator step against `acc_after` (the paper, with `acc_prog(i)`
read from role `60` of the same row). -/
def optimizedAccAfterStep : Expr :=
  foldedProgStep3.subst accAfterIOSubst

theorem optimizedAccAfterStep_degree :
    optimizedAccAfterStep.degree = 4 := by
  decide

theorem optimizedAccAfterStep_eval (env : Env K) :
    optimizedAccAfterStep.eval env = 0 ↔
      FoldedProgStep3
        ((sampledIOSubst .traceCur 0).eval env)
        (env.trace accAfterIndex)
        ((sampledIOSubst .traceCur 1).eval env)
        ((sampledIOSubst .traceCur 2).eval env)
        ((sampledIOSubst .traceCur 3).eval env)
        ((sampledIOSubst .traceCur 4).eval env)
        ((sampledIOSubst .traceCur 5).eval env)
        ((sampledIOSubst .traceCur 6).eval env) := by
  rw [optimizedAccAfterStep, Expr.eval_subst, foldedProgStep3_eval]
  rfl

/-- The anchored step reads the accumulator only at the current row: on any environment whose
`acc_after` equals the next row's accumulator it is the old masked fold's body. -/
theorem optimizedAccAfterStep_eval_eq_fold (env : Env K)
    (h : env.trace accAfterIndex = (sampledIOSubst .traceNext 0).eval env) :
    optimizedAccAfterStep.eval env = optimizedFoldedProgStep3.eval env := by
  rw [optimizedAccAfterStep, optimizedFoldedProgStep3, Expr.eval_subst, Expr.eval_subst]
  have hc : ∀ i, (Env.ofSubst accAfterIOSubst env).trace i =
      (Env.ofSubst sampledIOSubst env).trace i := fun _ => rfl
  have hn : (Env.ofSubst accAfterIOSubst env).traceNext 0 =
      (Env.ofSubst sampledIOSubst env).traceNext 0 := by
    change (Expr.Var .traceCur accAfterIndex).eval env =
      (sampledIOSubst .traceNext 0).eval env
    exact h
  simp only [foldedProgStep3, Expr.eval, Trans.tn, tc, hc, hn]

/-- The unfurled source conjunction is exactly the existing reified
`FiniteFieldIOAIR` request-gate biconditional. The degree-four fold above changes only how up to
three consecutive inverse contributions are combined on one compute row. -/
theorem finiteIOAIR_program_source_sound
    {m : ℕ} (records : FiniteIO.PreChallengeRecords K m)
    (coins : FiniteIO.IOCoins K)
    (w : FiniteIO.PostChallengeIOWitness records coins) :
    (FiniteIO.ioAccInit.eval (FiniteIO.progEnvAt records coins w 0) = 0
      ∧ (∀ i, i < records.requests.length →
          (FiniteIO.ioInvPin m 4).eval (FiniteIO.progEnvAt records coins w i) = 0)
      ∧ (∀ i, i < records.requests.length →
          FiniteIO.ioProgAccStep.eval
            (Nock.Reified.Trans.twoRow (FiniteIO.progEnvAt records coins w i)
              (FiniteIO.progEnvAt records coins w (i + 1))) = 0)
      ∧ FiniteIO.ioTerm.eval
          (FiniteIO.progEnvAt records coins w records.requests.length) = 0)
    ↔ (w.requestAcc 0 = 0
        ∧ (∀ i, FiniteIO.compress coins (records.requests.get i) * w.requestInv i = 1)
        ∧ (∀ i : Fin records.requests.length,
            w.requestAcc i.succ = w.requestAcc i.castSucc + w.requestInv i)
        ∧ w.requestAcc (Fin.last _) = w.terminal) :=
  FiniteIO.reified_finiteIOProg_sound records coins w

/-! ## Concrete cubic and cancellation regression -/

namespace Concrete

open ConcreteStrictPackage
open OptimizedComputeSampledTrace

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- On the accepted concrete OP1 row, the repaired fold accepts exactly the update `0 ↦ 1`. -/
theorem honest_op1_fold :
    FoldedProgStep3 (0 : K73cubic) 1
      (OptimizedComputeSampledTrace.overlayAt
        (F := F73)
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom0
      (OptimizedComputeSampledTrace.overlayAt
        (F := F73)
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom1
      (OptimizedComputeSampledTrace.overlayAt
        (F := F73)
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom2 1 0 0 := by
  rcases OptimizedComputeSampledTrace.Concrete.honest_safe_denominators with
    ⟨h0, h1, h2⟩
  rw [h0, h1, h2]
  norm_num [FoldedProgStep3]

/-- Conversely, the concrete OP1 fold forces the expected next accumulator to be one. -/
theorem honest_op1_accNext_eq_one (accNext : K73cubic)
    (h : FoldedProgStep3 0 accNext
      (OptimizedComputeSampledTrace.overlayAt
        (F := F73)
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom0
      (OptimizedComputeSampledTrace.overlayAt
        (F := F73)
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom1
      (OptimizedComputeSampledTrace.overlayAt
        (F := F73)
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedComputeSampledTrace.Concrete.honestRowIndex).denom2 1 0 0) :
    accNext = 1 := by
  rcases OptimizedComputeSampledTrace.Concrete.honest_safe_denominators with
    ⟨h0, h1, h2⟩
  rw [h0, h1, h2] at h
  simpa [FoldedProgStep3] using h

end Concrete

def cancellationRegressionEnv : Env ℚ where
  trace i :=
    if i = 1 then 1
    else if i = 16 then 1
    else if i = 46 then 1
    else 0
  traceNext i := if i = 45 then 2 else 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- The repaired production gate list rejects the old cancellation witness at the second
inactive-safe denominator pin: the supplied zero must instead be one. -/
theorem cancellation_regression_rejected :
    ∃ g ∈ optimizedSampledIOTransitionGates,
      g.eval cancellationRegressionEnv ≠ 0 := by
  refine ⟨sampledDenomPin .traceCur 1, ?_, ?_⟩
  · simp [optimizedSampledIOTransitionGates, optimizedDenomPinGates]
  · norm_num [sampledDenomPin, sampledDenomWitness, sampledSafeDenom, sampledDenom,
      sampledRecordRLC, sampledActive, sampledGamma, sampledPole, overlayCoord,
      sampledSlotT, sampledSlotC, sampledCprime, sampledGSel, sampledLam, lamPowVar, certCVar,
      certTVar,
      computeTraceSubst, semanticPub, restoredPub, sourcePubAt, restoredAField,
      restoredBField, restoredIOHostField, restoredDenomHostField, mr2Field, mr2Group,
      Nock.Reified.allStates, overlayANat, overlayBNat, pubFP, decFP, lnPrev, lnCur,
      consInv, invGen, ext0, Nock.Reified.opCol, cancellationRegressionEnv, Expr.eval]

#print axioms foldedProgStep3_eval
#print axioms foldedProgStep3_iff
#print axioms foldedProgStep3_iff_inverse_witnesses
#print axioms foldedProgStep3_safe_iff
#print axioms foldedProgStep3_safe_iff_inverse_witnesses
#print axioms sampledIOTransitionGate_nonzero
#print axioms optimizedFoldedProgStep3_eval
#print axioms optimizedSampledIOTransitionGates_eval
#print axioms optimizedSampledIOTransitionGates_max_degree
#print axioms finiteIOAIR_program_source_sound
#print axioms Concrete.honest_op1_fold
#print axioms Concrete.honest_op1_accNext_eq_one
#print axioms cancellation_regression_rejected

end
end Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
