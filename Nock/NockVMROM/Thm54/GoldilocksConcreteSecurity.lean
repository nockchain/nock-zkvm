/-
  Nock/NockVMROM/Thm54/GoldilocksConcreteSecurity.lean

  This module is the complementary fixed-parameter statement: it pins the
  one Goldilocks prime `p = 2^64 - 2^32 + 1`, its cubic extension `|𝕂| = p³`, and the paper's own collision numerator `k²·Λ` at `k = 2^31`, `Λ = 2^9`, and then computes the *maximal* integer bit-margin mechanically.

  ## The honest result: 120, not 121

  the paper states "121 bits of security" for `Λ = 2^9`, `k = 2^31`, `|𝕂| ≈ 2^192`.  The
  maximal `b` with `k²·Λ·2^b ≤ p³` is **120**, proved below as `goldilocks_max_security_bits`.
  The single-bit difference is fully explained and localized here:

  * `supports_121_at_roundedCard` — against the paper's *rounded* cap `2^192`, `b = 121` does hold
    (with equality `2^71 · 2^121 = 2^192`);
  * `goldilocksCard_lt_two_pow_192` — the actual Goldilocks cubic cardinality is strictly below
    that rounded cap, so the equality case is lost and `b = 121` fails at the true `p³`.

  So the paper's `121` is exactly the value obtained by rounding `|𝕂|` up to `2^192`.  Note also
  that the paper's own general formula on the same line, `log₂|𝕂| − 2log₂k − log₂Λ − 1`, evaluates
  to `192 − 62 − 9 − 1 = 120` at these parameters, agreeing with the mechanical answer.

  `NockVM.security_bits = 121` is a transcription `def` of the paper's prose.  It is the *target*
  of the comparison, never evidence for it; `paper_states_121_actual_is_120` records the exact
  mismatch.

  ## Layering

  Everything in the first sections is pure `ℕ` arithmetic and is kernel-clean.  Only the clearly
  marked `Concrete field instance` section mentions `Nock.Field.K`, and therefore only that section
  depends on the blessed `Nock.Field.goldilocks_prime` axiom.  No generic lemma here touches it.

  This module constructs **no** `ProductionStrategy` inhabitant.  The concrete false-acceptance
  statement is therefore hypothesis-taking: it consumes a joint-event cardinality bound at the
  collision numerator.  The named coupling to the production failure-union workload is
  `goldilocks_production_margin_le_120`.
-/

import Nock.NockVMROM.Thm54.PointwiseBridge
import Nock.NockVM
import Nock.Field

namespace Nock.NockVMROM.Thm54
namespace GoldilocksConcreteSecurity

/-! ## The fixed Goldilocks parameters -/

/-- The Goldilocks prime `p = 2^64 − 2^32 + 1`. -/
def goldilocksPrime : ℕ := 2 ^ 64 - 2 ^ 32 + 1

/-- The cardinality of the degree-`3` extension `𝕂` over the Goldilocks field, `|𝕂| = p³`.  This is the exact value, not the paper's rounded `2^192`. -/
def goldilocksCard : ℕ := goldilocksPrime ^ 3

/-- The paper's rounded cardinality `|𝕂| ≈ 2^192` as used in the prose bit count. -/
def roundedCard : ℕ := 2 ^ 192

/-- The paper's collision numerator `k²·Λ` at its own parameters `k = 2^31`, `Λ = 2^9`
(the paper`ε(Λ,𝕂)·k(k−1)/2` with `ε(Λ,𝕂) = Λ/|𝕂|`). -/
def collisionWorkload : ℕ := Nock.NockVM.kbound ^ 2 * Nock.NockVM.Λ

/-- The collision numerator is exactly `2^71`. -/
theorem collisionWorkload_eq : collisionWorkload = 2 ^ 71 := by
  unfold collisionWorkload Nock.NockVM.kbound Nock.NockVM.Λ
  norm_num

/-- The decimal value of the Goldilocks prime. -/
theorem goldilocksPrime_eq : goldilocksPrime = 18446744069414584321 := by
  norm_num [goldilocksPrime]

/-! ## Exact bracketing of `p³`

`p` is just below `2^64`, so `p³` is just below `2^192` — but comfortably above `2^191`.  These two
strict inequalities are what decide the bit-margin, and they are what makes the answer `120` rather
than `121`. -/

/-- **Upper bracket.**  The true Goldilocks cubic cardinality is strictly below the paper's rounded
cap `2^192`. -/
theorem goldilocksPrime_cube_lt_two_pow_192 : goldilocksPrime ^ 3 < 2 ^ 192 := by
  norm_num [goldilocksPrime]

/-- **Lower bracket.**  The true Goldilocks cubic cardinality is strictly above `2^191`. -/
theorem two_pow_191_lt_goldilocksPrime_cube : 2 ^ 191 < goldilocksPrime ^ 3 := by
  norm_num [goldilocksPrime]

/-- The upper bracket in terms of `goldilocksCard`. -/
theorem goldilocksCard_lt_two_pow_192 : goldilocksCard < 2 ^ 192 :=
  goldilocksPrime_cube_lt_two_pow_192

/-- The lower bracket in terms of `goldilocksCard`. -/
theorem two_pow_191_lt_goldilocksCard : 2 ^ 191 < goldilocksCard :=
  two_pow_191_lt_goldilocksPrime_cube

/-- The two-sided bracket `2^191 < p³ < 2^192`. -/
theorem goldilocksCard_brackets :
    2 ^ 191 < goldilocksCard ∧ goldilocksCard < 2 ^ 192 :=
  ⟨two_pow_191_lt_goldilocksCard, goldilocksCard_lt_two_pow_192⟩

/-- The true cardinality is strictly below the paper's rounded cardinality. -/
theorem goldilocksCard_lt_roundedCard : goldilocksCard < roundedCard :=
  goldilocksCard_lt_two_pow_192

/-- The cubic cardinality is positive. -/
theorem goldilocksCard_pos : 0 < goldilocksCard :=
  lt_of_le_of_lt (Nat.zero_le _) two_pow_191_lt_goldilocksCard

/-! ## The security-bit predicate and its exact maximum -/

/-- `b` bits of security are supported when the paper's collision numerator, amplified by an
adversarial factor of `2^b`, still fits inside the field cardinality. -/
def SupportsSecurityBits (b : ℕ) : Prop :=
  collisionWorkload * 2 ^ b ≤ goldilocksCard

/-- The same predicate evaluated against the paper's *rounded* cap `2^192` instead of the true
cubic cardinality.  Comparing the two maxima isolates the rounding. -/
def SupportsSecurityBitsAtRoundedCard (b : ℕ) : Prop :=
  collisionWorkload * 2 ^ b ≤ roundedCard

/-- Supported bit counts are downward closed. -/
theorem supportsSecurityBits_antitone {a b : ℕ} (hab : a ≤ b)
    (hb : SupportsSecurityBits b) : SupportsSecurityBits a :=
  le_trans (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by norm_num) hab)) hb

/-- The collision numerator scaled by `2^120` is exactly `2^191`. -/
theorem collisionWorkload_mul_two_pow_120 :
    collisionWorkload * 2 ^ 120 = 2 ^ 191 := by
  rw [collisionWorkload_eq, ← pow_add]

/-- The collision numerator scaled by `2^121` is exactly `2^192`. -/
theorem collisionWorkload_mul_two_pow_121 :
    collisionWorkload * 2 ^ 121 = 2 ^ 192 := by
  rw [collisionWorkload_eq, ← pow_add]

/-- **120 bits are supported.**  `2^71 · 2^120 = 2^191 ≤ p³`, from the lower bracket. -/
theorem supports_120 : SupportsSecurityBits 120 := by
  show collisionWorkload * 2 ^ 120 ≤ goldilocksCard
  rw [collisionWorkload_mul_two_pow_120]
  exact le_of_lt two_pow_191_lt_goldilocksCard

/-- **121 bits are NOT supported.**  `2^71 · 2^121 = 2^192 > p³`, from the upper bracket.  This is
the mechanical refutation of the paper's prose figure at the exact Goldilocks cardinality. -/
theorem not_supports_121 : ¬ SupportsSecurityBits 121 := by
  show ¬ collisionWorkload * 2 ^ 121 ≤ goldilocksCard
  rw [collisionWorkload_mul_two_pow_121]
  exact Nat.not_le.mpr goldilocksCard_lt_two_pow_192

/-- **The exact characterization of the supported bit counts.** -/
theorem supportsSecurityBits_iff (b : ℕ) : SupportsSecurityBits b ↔ b ≤ 120 := by
  constructor
  · intro hb
    by_contra hgt
    exact not_supports_121
      (supportsSecurityBits_antitone (by omega : (121 : ℕ) ≤ b) hb)
  · intro hb
    exact supportsSecurityBits_antitone hb supports_120

/-- The maximal number of security bits supported by the paper's
own collision numerator over the *exact* fixed Goldilocks cubic field is `120`. -/
theorem goldilocks_max_security_bits :
    IsGreatest {b : ℕ | SupportsSecurityBits b} 120 :=
  ⟨supports_120, fun _ hb => (supportsSecurityBits_iff _).mp hb⟩

/-! ## Localizing the paper's off-by-one to the `2^192` rounding -/

/-- **121 bits DO hold against the rounded cap.**  `2^71 · 2^121 = 2^192 = roundedCard`, with
equality.  This is precisely the step the paper takes when it writes `|𝕂| ≈ 2^192`. -/
theorem supports_121_at_roundedCard : SupportsSecurityBitsAtRoundedCard 121 :=
  le_of_eq collisionWorkload_mul_two_pow_121

/-- 122 bits fail even against the rounded cap, so `121` is exactly the rounded-cap maximum. -/
theorem not_supports_122_at_roundedCard : ¬ SupportsSecurityBitsAtRoundedCard 122 := by
  show ¬ collisionWorkload * 2 ^ 122 ≤ roundedCard
  rw [collisionWorkload_eq, ← pow_add]
  unfold roundedCard
  exact Nat.not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by norm_num))

/-- **The rounded-cap maximum is exactly the paper's `121`.**  Together with
`goldilocks_max_security_bits` this pins the entire discrepancy on the `p³ ↦ 2^192` rounding: the
predicate, the numerator and the exponent arithmetic are shared, only the denominator differs. -/
theorem roundedCard_max_security_bits :
    IsGreatest {b : ℕ | SupportsSecurityBitsAtRoundedCard b} 121 := by
  refine ⟨supports_121_at_roundedCard, fun b hb => ?_⟩
  by_contra hgt
  refine not_supports_122_at_roundedCard ?_
  refine le_trans (Nat.mul_le_mul le_rfl
    (Nat.pow_le_pow_right (by norm_num) (by omega : (122 : ℕ) ≤ b))) hb

/-- **The honest receipt.**  The paper transcribes `121` bits, but at the exact
Goldilocks cubic cardinality `121` is unsupported and `120` is the true maximum.  Note that
`NockVM.security_bits` is a transcription of the paper's prose, recorded here as the comparison
target — it is never used as evidence for the bit count. -/
theorem paper_states_121_actual_is_120 :
    Nock.NockVM.security_bits = 121 ∧ ¬ SupportsSecurityBits 121 ∧
      SupportsSecurityBits 120 :=
  ⟨rfl, not_supports_121, supports_120⟩

/-- **The full source-of-discrepancy receipt.**  The same numerator and the same exponent `121`
succeed against the rounded `2^192` and fail against the exact `p³`, and the reason is exactly that
`p³ < 2^192`. -/
theorem paper_121_is_the_rounding :
    SupportsSecurityBitsAtRoundedCard 121 ∧ ¬ SupportsSecurityBits 121 ∧
      goldilocksCard < roundedCard :=
  ⟨supports_121_at_roundedCard, not_supports_121, goldilocksCard_lt_roundedCard⟩

/-! ## Coupling to the production workload (Packet F)

This module deliberately builds no `ProductionStrategy`.  The production failure-union workload is
a *superset* numerator: it contains the collision class among others.  The lemma below is the named
coupling, and it says the real margin can only be smaller: any bit count supported by a numerator
dominating the collision numerator is already at most `120`. -/

/-- **Named Packet-F coupling.**  If the production failure-union workload dominates the paper's
collision numerator, then every bit count it supports over the fixed Goldilocks cubic field is at
most `120`.  The dominance hypothesis is exactly what a concrete `ProductionStrategy` inhabitant
must supply; nothing about the maximum `120` depends on it. -/
theorem goldilocks_production_margin_le_120
    (productionWorkload b : ℕ)
    (hdominates : collisionWorkload ≤ productionWorkload)
    (hsupports : productionWorkload * 2 ^ b ≤ goldilocksCard) :
    b ≤ 120 :=
  (supportsSecurityBits_iff b).mp
    (le_trans (Nat.mul_le_mul hdominates le_rfl) hsupports)

/-! ## Concrete field instance

⚠ Everything below mentions the concrete `Nock.Field.K = GaloisField Nock.Field.p 3` and therefore
depends on the blessed `Nock.Field.goldilocks_prime` axiom.  No `ℕ`-arithmetic result above is in
its cone. -/

section ConcreteField

theorem goldilocksPrime_eq_fieldP : Nock.Field.p = goldilocksPrime := rfl

/-- **The field-side cardinality.**  `|GaloisField p 3| = p³`.  Depends on
`Nock.Field.goldilocks_prime`. -/
theorem goldilocksField_card :
    Fintype.card (GaloisField Nock.Field.p 3) = Nock.Field.p ^ 3 :=
  Nock.Field.card_K

theorem goldilocksField_card_eq : Fintype.card Nock.Field.K = goldilocksCard :=
  Nock.Field.card_K

/-- The bracket transported to the actual field cardinality. -/
theorem goldilocksField_card_brackets :
    2 ^ 191 < Fintype.card Nock.Field.K ∧ Fintype.card Nock.Field.K < 2 ^ 192 := by
  rw [goldilocksField_card_eq]
  exact goldilocksCard_brackets

/-- `120` bits are supported by the actual concrete field cardinality. -/
theorem goldilocksField_supports_120 :
    collisionWorkload * 2 ^ 120 ≤ Fintype.card Nock.Field.K := by
  rw [goldilocksField_card_eq]
  exact supports_120

/-- `121` bits are not supported by the actual concrete field cardinality. -/
theorem goldilocksField_not_supports_121 :
    ¬ collisionWorkload * 2 ^ 121 ≤ Fintype.card Nock.Field.K := by
  rw [goldilocksField_card_eq]
  exact not_supports_121

/-! ### The concrete false-acceptance inequality

`jointProbability_le_workload_div_card` is the existing generic NPR-collision/joint-event bound.
Specialized to the fixed Goldilocks cubic field it gives the paper's `≤ workload / |𝕂|` shape.  The
joint-event cardinality bound at the collision numerator is retained as an explicit hypothesis:
supplying it for the full production failure union needs a concrete `ProductionStrategy`, which is
Packet F.  `goldilocks_production_margin_le_120` is the named coupling. -/

/-- **Concrete false acceptance over the fixed Goldilocks cubic field.**  Any joint event whose
cardinality is bounded by the paper's collision numerator times `|𝕂|³` has probability at most
`k²·Λ / p³`.  The cardinality premise is the Packet-F obligation. -/
theorem goldilocks_concrete_falseAcceptance_le
    (E : Finset (JointCoins Nock.Field.K))
    (hcard : E.card ≤ collisionWorkload * Fintype.card Nock.Field.K ^ 3) :
    |jointProbability E| ≤ (collisionWorkload : ℝ) / (goldilocksCard : ℝ) := by
  haveI : Nonempty Nock.Field.K := ⟨0⟩
  have h := jointProbability_le_workload_div_card E collisionWorkload hcard
  rwa [goldilocksField_card_eq] at h

/-- **The concrete bound in bit form.**  The same premise gives false-acceptance probability at
most `2⁻¹²⁰`, the mechanically proved margin.  The `121`-bit figure of the paper is not
obtained. -/
theorem goldilocks_concrete_falseAcceptance_le_two_pow_neg_120
    (E : Finset (JointCoins Nock.Field.K))
    (hcard : E.card ≤ collisionWorkload * Fintype.card Nock.Field.K ^ 3) :
    |jointProbability E| ≤ 1 / 2 ^ 120 := by
  refine (goldilocks_concrete_falseAcceptance_le E hcard).trans ?_
  have hpos : (0 : ℝ) < (goldilocksCard : ℝ) := by
    exact_mod_cast goldilocksCard_pos
  have hreal : (collisionWorkload : ℝ) * 2 ^ 120 ≤ (goldilocksCard : ℝ) := by
    exact_mod_cast supports_120
  rw [div_le_div_iff₀ hpos (by positivity : (0 : ℝ) < 2 ^ 120)]
  linarith

end ConcreteField

end GoldilocksConcreteSecurity
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.collisionWorkload_eq
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksPrime_eq
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksPrime_cube_lt_two_pow_192
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.two_pow_191_lt_goldilocksPrime_cube
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksCard_brackets
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksCard_lt_roundedCard
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksCard_pos
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.supportsSecurityBits_antitone
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.collisionWorkload_mul_two_pow_120
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.collisionWorkload_mul_two_pow_121
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.supports_120
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.not_supports_121
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.supportsSecurityBits_iff
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocks_max_security_bits
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.supports_121_at_roundedCard
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.not_supports_122_at_roundedCard
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.roundedCard_max_security_bits
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.paper_states_121_actual_is_120
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.paper_121_is_the_rounding
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocks_production_margin_le_120
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksPrime_eq_fieldP
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksField_card
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksField_card_eq
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksField_card_brackets
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksField_supports_120
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocksField_not_supports_121
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocks_concrete_falseAcceptance_le
#print axioms Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity.goldilocks_concrete_falseAcceptance_le_two_pow_neg_120
