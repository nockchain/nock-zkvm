/-
  Nock/RedTeam/Batch1560PrimalityCerts.lean

  * §A the new theorems depend on `{propext, Classical.choice, Quot.sound}` only (no
    `Nock.Field.goldilocks_prime`, no `Lean.ofReduceBool`, no `sorryAx`);
    this includes `seven_not_square`, whose statement passes `ZMod.commRing` explicitly and so mentions no
    `Field` instance; `four_is_square` below is stated through the Field instance and DOES list the axiom;
  * §B the axiom and the theorem are the same proposition (`goldilocks_prime = goldilocks_prime_thm`
    by proof irrelevance; THIS receipt, unlike the theorem, does depend on the axiom);
  * §C negative controls: a wrong Lucas witness fails the checker, a Fermat pseudoprime fails, a
    certificate with a non-certified factor fails, and `τ(p³−1) ≠ 12671`.
-/
import Nock.Primality.Goldilocks
import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower

set_option autoImplicit false

namespace Nock.RedTeam.Batch1560

open Nock.Primality

/-- The axiom's statement and the proved theorem are one proposition; the axiom is untouched. -/
theorem axiom_eq_theorem :
    Nock.Field.goldilocks_prime = goldilocks_prime_thm := rfl

/-- NEGATIVE: the Goldilocks line with the wrong witness `2` (order `192`) is rejected. -/
def badWitnessCert : List Entry :=
  goldilocksCert.map (fun E => if E.n = 18446744069414584321 then { E with a := 2 } else E)

theorem wrong_witness_rejected : checkAll badWitnessCert [2] = false := by decide +kernel

/-- NEGATIVE: the small wrong witness `4` for `n = 5` (`4^2 = 1`, so `4` has order `2`). -/
theorem wrong_witness_five : checkEntry [2] ⟨5, 4, [(2, 2)]⟩ = false := by decide +kernel

/-- Positive control for the same line with the right witness `3`. -/
theorem right_witness_five : checkEntry [2] ⟨5, 3, [(2, 2)]⟩ = true := by decide +kernel

/-- NEGATIVE: `341 = 11 · 31` is a base-2 Fermat pseudoprime (`2^340 ≡ 1`), and is still rejected
by the order condition. -/
theorem pseudoprime_rejected : checkEntry [2, 5, 17] ⟨341, 2, [(2, 2), (5, 1), (17, 1)]⟩ = false := by
  decide +kernel

/-- NEGATIVE: a factor that is not certified (`7` missing from `known`) is rejected. -/
theorem uncertified_factor_rejected : checkEntry [2] ⟨29, 2, [(2, 2), (7, 1)]⟩ = false := by
  decide +kernel

/-- NEGATIVE: the divisor count is exact, not vacuous: `12671` is not `τ(p³ − 1)`. -/
theorem tau_p3_ne : ((Nock.Field.p) ^ 3 - 1).divisors.card ≠ 12671 := by
  rw [tau_p3_sub_one]; norm_num

/-- NEGATIVE: `7` is a non-square but `4` is a square, so the criterion is not vacuous. -/
theorem four_is_square : IsSquare (4 : ZMod Nock.Field.p) := ⟨2, by norm_num⟩

end Nock.RedTeam.Batch1560

/-! ## `δ = 7` is a non-square at the paper's cubic extension `K = GaloisField p 3`

`7` is a non-square in `ZMod p` (`seven_not_square`) and stays one in the cubic `K` (T0
`nonsquare_lift`).  This is the instance the quadratic tower `K[X]/(X² − 7)` needs.  The statement is
about `Nock.Field.K`, whose `Field` instance is built from `Nock.Field.instFactPrimeP`, so (unlike
`seven_not_square`) this instance DOES depend on `Nock.Field.goldilocks_prime`. -/

namespace Nock.RedTeam.Batch1560

section DeltaSeven

open Nock.NockVMROM.Thm54.T0Tower

theorem seven_not_square_K : ¬ IsSquare (7 : Nock.Field.K) := by
  have h : ¬ IsSquare (algebraMap (ZMod Nock.Field.p) Nock.Field.K 7) :=
    nonsquare_lift (F := ZMod Nock.Field.p) (K := Nock.Field.K)
      (by rw [ZMod.ringChar_zmod_n]; have := Nock.Field.p_eq; omega)
      (by
        haveI : Fact (Nat.Prime Nock.Field.p) := ⟨Nock.Field.goldilocks_prime⟩
        haveI : CharP Nock.Field.K Nock.Field.p :=
          charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) Nock.Field.K).injective _
        rw [ringChar.eq Nock.Field.K Nock.Field.p]; have := Nock.Field.p_eq; omega)
      (GaloisField.finrank Nock.Field.p (by norm_num)) 7
      (by
        haveI : Fact (Nat.Prime Nock.Field.p) := ⟨Nock.Field.goldilocks_prime⟩
        intro h0
        have : ((7 : ℕ) : ZMod Nock.Field.p) = ((0 : ℕ) : ZMod Nock.Field.p) := by simpa using h0
        rw [ZMod.natCast_eq_natCast_iff', Nock.Field.p_eq] at this; norm_num at this)
      (by
        haveI : Fact (Nat.Prime Nock.Field.p) := ⟨Nock.Field.goldilocks_prime⟩
        exact Nock.Primality.seven_not_square_of_fact)
  rwa [map_ofNat] at h

/-- The `Fact` instance the T0 tower (`Quad δ`, `FP2`) takes, at `δ = 7` over `Nock.Field.K`. -/
instance instFactNotSquareSevenK : Fact (¬ IsSquare (7 : Nock.Field.K)) := ⟨seven_not_square_K⟩

end DeltaSeven

end Nock.RedTeam.Batch1560

#print axioms Nock.Primality.powModAux_eq
#print axioms Nock.Primality.prime_of_cert
#print axioms Nock.Primality.card_divisors_prodPow
#print axioms Nock.Primality.card_divisors_le_two_mul_sqrt
#print axioms Nock.Primality.goldilocksCert_ok
#print axioms Nock.Primality.goldilocks_prime_thm
#print axioms Nock.Primality.tau_p3_sub_one
#print axioms Nock.Primality.tau_p6_sub_one_le
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLambdaK3_goldilocks_hΛK_proved
#print axioms Nock.NockVMROM.Thm54.TightWindow.hLambdaK6_goldilocks_hΛK_proved
#print axioms Nock.RedTeam.Batch1560.wrong_witness_rejected
#print axioms Nock.RedTeam.Batch1560.pseudoprime_rejected
#print axioms Nock.RedTeam.Batch1560.tau_p3_ne
#print axioms Nock.Primality.seven_not_square
#print axioms Nock.RedTeam.Batch1560.four_is_square
-- Expected to LIST the axiom (the receipt that ties the two statements together):
#print axioms Nock.RedTeam.Batch1560.axiom_eq_theorem
#print axioms Nock.RedTeam.Batch1560.seven_not_square_K
