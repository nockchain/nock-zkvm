import Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
import Nock.NockVMROM.Thm54.ConcreteStrictPackage

/-! Concrete non-vacuity of the corrected compute collision exclusion. -/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeCollisionConcrete

open Nock.Reified
open OptimizedComputeCollisionBound
open ConcreteStrictPackage

noncomputable section

local instance concrete_fintype : Fintype K73cubic :=
  Fintype.ofFinite K73cubic
local instance concrete_decidableEq : DecidableEq K73cubic := Classical.decEq _

theorem concrete_field_cards :
    Fintype.card F73 = 73 ∧ Fintype.card K73cubic = 73 ^ 3 := by
  constructor
  · simp [F73]
  · rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 73 3 (by norm_num)

theorem concrete_challenge_tuple_card :
    Fintype.card (FinalComputeChallengeTuple K73cubic) = Fintype.card K73cubic ^ 3 := by
  let e : FinalComputeChallengeTuple K73cubic ≃ (K73cubic × K73cubic × K73cubic) :=
    { toFun := fun c => (c.eqA, c.eqB, c.eqC)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro p; rfl }
  rw [Fintype.card_congr e]
  simp [pow_three]

theorem concrete_full_collision_bound_lt_coin_space
    (envK : Fin 1 → Env K73cubic) (walkEnv : Env K73cubic) :
    (extensionFinalComputeCollisionEvent envK walkEnv).card <
      Fintype.card (FinalComputeChallengeTuple K73cubic) := by
  simp [extensionFinalComputeCollisionEvent, concrete_challenge_tuple_card]
  exact pow_pos Fintype.card_pos 3

/-- The event is empty, so every tuple is good. -/
theorem concrete_exists_good_challenge_tuple
    (envK : Fin 1 → Env K73cubic) (walkEnv : Env K73cubic) :
    ∃ c : FinalComputeChallengeTuple K73cubic,
      c ∉ extensionFinalComputeCollisionEvent envK walkEnv :=
  ⟨default, by simp [extensionFinalComputeCollisionEvent]⟩

#print axioms concrete_exists_good_challenge_tuple

end
end OptimizedComputeCollisionConcrete
end Nock.NockVMROM.Thm54
