import Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity
import Nock.RedTeam.Batch16Thm54SecurityGap

/-!
# Fixed-Goldilocks concrete security bit-margin

This batch does instantiate it and computes the maximal integer bit-margin mechanically.

The result is **120**, not the `121` of the paper.

The one-bit difference is not a defect of the construction, and it is not hidden by a rounding
convention here:

* `b31_121_holds_at_rounded_cap` — against the paper's own rounded cap `|𝕂| ≈ 2^192` the exponent
  `121` does hold, with equality `2^71 · 2^121 = 2^192`;
* `b31_p3_brackets` — the true Goldilocks cubic cardinality satisfies `2^191 < p³ < 2^192`, so the
  equality case is lost and `121` fails at the exact cardinality;
* `b31_paper_general_formula_gives_120` — the paper's own general formula on the same line,
  `log₂|𝕂| − 2log₂k − log₂Λ − 1`, evaluates to `120` at `Λ = 2^9`, `k = 2^31`, `log₂|𝕂| = 192`.
  So the paper's prose figure also disagrees with the paper's own formula by one.

`NockVM.security_bits = 121` is a transcription `def`.  `b31_security_bits_is_transcription_only`
records that it is closed by `rfl`, i.e. it carries no arithmetic content and is never evidence for
a bit count; it is only the comparison target of `b31_paper_121_vs_actual_120`.

1. **vacuity** — `b31_falseAcceptance_hypothesis_nonvacuous` exhibits a real inhabitant of the
   joint-event cardinality premise over the concrete Goldilocks field, and
   `b31_supported_bits_nonempty` shows the bit-margin set is inhabited;
3. **weakening/bundling** — the maximum is stated as `IsGreatest`, not as a pair of independent
   inequalities, and `b31_supported_bits_iff` gives the full characterization;
4. **wrong layer** — `b31_production_margin_le_120` reproduces the ceiling at the *production*
   numerator rather than only at the collision numerator, as a hypothesis-taking lemma since the
   concrete `ProductionStrategy` inhabitant is Packet F.
-/

namespace Nock.RedTeam.Batch31

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity


theorem b31_prime_agrees_with_b16 :
    GoldilocksConcreteSecurity.goldilocksPrime = Batch16.goldilocksPrime := rfl

theorem b31_workload_agrees_with_b16 :
    collisionWorkload = Batch16.numeratorScale := rfl

theorem b31_roundedCard_agrees_with_b16 :
    roundedCard = Batch16.cubicFieldCap := by
  unfold roundedCard Batch16.cubicFieldCap Batch16.baseFieldCap Nock.NockVM.extOrder
  norm_num

theorem b31_workload_eq_two_pow_71 : collisionWorkload = 2 ^ 71 :=
  collisionWorkload_eq

/-! ## Exact bracketing of the true cardinality -/

/-- **`2^191 < p³ < 2^192`.**  The true Goldilocks cubic cardinality sits strictly between the two
consecutive powers of two, so it is strictly below the paper's rounded cap. -/
theorem b31_p3_brackets :
    2 ^ 191 < GoldilocksConcreteSecurity.goldilocksPrime ^ 3 ∧
      GoldilocksConcreteSecurity.goldilocksPrime ^ 3 < 2 ^ 192 :=
  ⟨two_pow_191_lt_goldilocksPrime_cube, goldilocksPrime_cube_lt_two_pow_192⟩

theorem b31_prime_below_base_cap :
    GoldilocksConcreteSecurity.goldilocksPrime < Batch16.baseFieldCap :=
  Batch16.b16_goldilocks_below_base_cap

/-! ## The mechanical bit-margin -/

/-- `120` bits are supported at the exact Goldilocks cubic cardinality. -/
theorem b31_supports_120 : SupportsSecurityBits 120 := supports_120

/-- `121` bits are NOT supported at the exact Goldilocks cubic cardinality. -/
theorem b31_not_supports_121 : ¬ SupportsSecurityBits 121 := not_supports_121

/-- The complete characterization: `b` bits are supported exactly when `b ≤ 120`.  There is no
rounding convention in the predicate that could turn `120` into `121`. -/
theorem b31_supported_bits_iff (b : ℕ) : SupportsSecurityBits b ↔ b ≤ 120 :=
  supportsSecurityBits_iff b

/-- **The maximum is `120`.**  Stated as `IsGreatest`, so membership and the upper bound are
threaded through the same set, not asserted independently. -/
theorem b31_max_bits_120 : IsGreatest {b : ℕ | SupportsSecurityBits b} 120 :=
  goldilocks_max_security_bits

/-- Non-vacuity of the bit-margin set. -/
theorem b31_supported_bits_nonempty : {b : ℕ | SupportsSecurityBits b}.Nonempty :=
  ⟨120, supports_120⟩

/-! ## The paper's `121`, and where it comes from -/

/-- `NockVM.security_bits` is a transcription `def` of the paper's prose: the equation is closed by
`rfl` and therefore carries no arithmetic content about the field. -/
theorem b31_security_bits_is_transcription_only : Nock.NockVM.security_bits = 121 := rfl

/-- **The honest mismatch receipt**.  The transcribed figure is `121`; the exact
Goldilocks cubic cardinality supports `120` and refutes `121`. -/
theorem b31_paper_121_vs_actual_120 :
    Nock.NockVM.security_bits = 121 ∧ ¬ SupportsSecurityBits 121 ∧
      SupportsSecurityBits 120 :=
  paper_states_121_actual_is_120

/-- **The source of the off-by-one.**  Against the paper's rounded cap `2^192`, the exponent `121`
holds — with equality — so the paper's figure is exactly the rounded-cap answer. -/
theorem b31_121_holds_at_rounded_cap : SupportsSecurityBitsAtRoundedCard 121 :=
  supports_121_at_roundedCard

/-- At the rounded cap the maximum is exactly `121`, so the `121` versus `120` difference is
entirely the `p³ ↦ 2^192` rounding and nothing else. -/
theorem b31_rounded_cap_max_bits_121 :
    IsGreatest {b : ℕ | SupportsSecurityBitsAtRoundedCard b} 121 :=
  roundedCard_max_security_bits

/-- The two caps differ, which is the whole content of the discrepancy. -/
theorem b31_rounding_is_strict : goldilocksCard < roundedCard :=
  goldilocksCard_lt_roundedCard

/-- **The paper's own general formula also gives `120`.**  the paper states the security level
as `log₂|𝕂| − 2log₂k − log₂Λ − 1`; at `log₂|𝕂| = 192`, `log₂k = 31`, `log₂Λ = 9` this is
`192 − 62 − 9 − 1 = 120`, agreeing with the mechanical answer and disagreeing with the same line's
prose figure `121`. -/
theorem b31_paper_general_formula_gives_120 : 192 - 2 * 31 - 9 - 1 = 120 := by norm_num

/-! ## The production layer: the real margin can only be smaller

This batch constructs no `ProductionStrategy`; that inhabitant is Packet F.  The ceiling is
therefore reproduced at the production numerator as a hypothesis-taking lemma, with the dominance
premise named explicitly. -/

/-- **Ceiling at the production layer.**  The production failure-union workload contains the
collision class, so it dominates the paper's collision numerator.  Under that named dominance
premise, every bit count it supports over the fixed Goldilocks cubic field is at most `120`: the
real margin can only be smaller than the collision-only margin, never larger. -/
theorem b31_production_margin_le_120
    (productionWorkload b : ℕ)
    (hdominates : collisionWorkload ≤ productionWorkload)
    (hsupports : productionWorkload * 2 ^ b ≤ goldilocksCard) :
    b ≤ 120 :=
  goldilocks_production_margin_le_120 productionWorkload b hdominates hsupports

/-- The dominance premise of `b31_production_margin_le_120` is satisfiable (it holds trivially at
the collision numerator itself), so the lemma is not vacuous. -/
theorem b31_production_dominance_nonvacuous :
    collisionWorkload ≤ collisionWorkload := le_rfl

/-- Instantiating the ceiling at the collision numerator itself recovers `b ≤ 120` unconditionally,
confirming that the hypothesis-taking form is not hiding a weaker statement. -/
theorem b31_production_margin_at_collision_numerator (b : ℕ)
    (hsupports : collisionWorkload * 2 ^ b ≤ goldilocksCard) :
    b ≤ 120 :=
  b31_production_margin_le_120 collisionWorkload b le_rfl hsupports

/-! ## The concrete field and the concrete false-acceptance premise -/

/-- The concrete field's cardinality really is the bracketed `p³`, and the `120`/`121` verdict
transports to it verbatim.  This declaration is in the cone of the blessed
`Nock.Field.goldilocks_prime` axiom. -/
theorem b31_concrete_field_verdict :
    Fintype.card Nock.Field.K = goldilocksCard ∧
      collisionWorkload * 2 ^ 120 ≤ Fintype.card Nock.Field.K ∧
      ¬ collisionWorkload * 2 ^ 121 ≤ Fintype.card Nock.Field.K :=
  ⟨goldilocksField_card_eq, goldilocksField_supports_120,
    goldilocksField_not_supports_121⟩

/-- **Non-vacuity of the false-acceptance premise.**  The empty joint event satisfies the
cardinality hypothesis of `goldilocks_concrete_falseAcceptance_le` over the real Goldilocks cubic
field, so the hypothesis-taking bound has an actual instance. -/
theorem b31_falseAcceptance_hypothesis_nonvacuous :
    (∅ : Finset (JointCoins Nock.Field.K)).card ≤
      collisionWorkload * Fintype.card Nock.Field.K ^ 3 := by
  simp

/-- The concrete false-acceptance bound, instantiated at the witness above: the probability of the
empty joint event is at most `2⁻¹²⁰`.  This is a real instance of the conditional bound, not a
claim about the full production failure union. -/
theorem b31_falseAcceptance_instance :
    |jointProbability (∅ : Finset (JointCoins Nock.Field.K))| ≤ 1 / 2 ^ 120 :=
  goldilocks_concrete_falseAcceptance_le_two_pow_neg_120 ∅
    b31_falseAcceptance_hypothesis_nonvacuous

end Nock.RedTeam.Batch31

#print axioms Nock.RedTeam.Batch31.b31_prime_agrees_with_b16
#print axioms Nock.RedTeam.Batch31.b31_workload_agrees_with_b16
#print axioms Nock.RedTeam.Batch31.b31_roundedCard_agrees_with_b16
#print axioms Nock.RedTeam.Batch31.b31_workload_eq_two_pow_71
#print axioms Nock.RedTeam.Batch31.b31_p3_brackets
#print axioms Nock.RedTeam.Batch31.b31_prime_below_base_cap
#print axioms Nock.RedTeam.Batch31.b31_supports_120
#print axioms Nock.RedTeam.Batch31.b31_not_supports_121
#print axioms Nock.RedTeam.Batch31.b31_supported_bits_iff
#print axioms Nock.RedTeam.Batch31.b31_max_bits_120
#print axioms Nock.RedTeam.Batch31.b31_supported_bits_nonempty
#print axioms Nock.RedTeam.Batch31.b31_security_bits_is_transcription_only
#print axioms Nock.RedTeam.Batch31.b31_paper_121_vs_actual_120
#print axioms Nock.RedTeam.Batch31.b31_121_holds_at_rounded_cap
#print axioms Nock.RedTeam.Batch31.b31_rounded_cap_max_bits_121
#print axioms Nock.RedTeam.Batch31.b31_rounding_is_strict
#print axioms Nock.RedTeam.Batch31.b31_paper_general_formula_gives_120
#print axioms Nock.RedTeam.Batch31.b31_production_margin_le_120
#print axioms Nock.RedTeam.Batch31.b31_production_dominance_nonvacuous
#print axioms Nock.RedTeam.Batch31.b31_production_margin_at_collision_numerator
#print axioms Nock.RedTeam.Batch31.b31_concrete_field_verdict
#print axioms Nock.RedTeam.Batch31.b31_falseAcceptance_hypothesis_nonvacuous
#print axioms Nock.RedTeam.Batch31.b31_falseAcceptance_instance
