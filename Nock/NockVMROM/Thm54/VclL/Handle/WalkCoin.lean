/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkCoin.lean

  **The honest bad event of the walk coin `α`**, priced.  The
  queue non-emptiness gate needs `h ≤ orderOf α` (`WalkGatesH.walkGatesH_honest`); over a finite field at
  most `h²` coins violate it (the roots of `X · ∏_{k<h} (X^k − 1)`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.PoleFree

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Polynomial


theorem walk_coin_order_few {K : Type} [Field K] [Finite K] (h : ℕ) (hh : 1 ≤ h) :
    ∃ B : Finset K, B.card ≤ h * h ∧ ∀ α : K, α ∉ B → h ≤ orderOf α := by
  classical
  let P : K[X] := X * ∏ k ∈ Finset.Icc 1 (h - 1), (X ^ k - C (1 : K))
  have hmon : P.Monic := by
    refine monic_X.mul (monic_prod_of_monic _ _ fun k hk => ?_)
    exact monic_X_pow_sub_C 1 (by have := (Finset.mem_Icc.mp hk).1; omega)
  have hP0 : P ≠ 0 := hmon.ne_zero
  refine ⟨P.roots.toFinset, ?_, ?_⟩
  · calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
      _ ≤ 1 + ∑ k ∈ Finset.Icc 1 (h - 1), k := by
        refine (natDegree_mul_le).trans ?_
        rw [natDegree_X]
        refine Nat.add_le_add_left ((natDegree_prod_le _ _).trans ?_) 1
        refine Finset.sum_le_sum fun k hk => ?_
        rw [natDegree_X_pow_sub_C]
      _ ≤ 1 + (h - 1) * (h - 1) := by
        refine Nat.add_le_add_left ((Finset.sum_le_card_nsmul _ _ (h - 1) fun k hk => ?_).trans ?_) 1
        · exact (Finset.mem_Icc.mp hk).2
        · simp
      _ ≤ h * h := by
        obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        nlinarith
  · intro α hα
    rw [Multiset.mem_toFinset, mem_roots hP0] at hα
    simp only [IsRoot, P, eval_mul, eval_X, eval_prod, eval_sub, eval_pow, eval_C] at hα
    have hα0 : α ≠ 0 := fun h0 => hα (by simp [h0])
    have hk : ∀ k ∈ Finset.Icc 1 (h - 1), α ^ k ≠ 1 := by
      intro k hk h1
      exact hα (by rw [Finset.prod_eq_zero hk (by rw [h1]; simp)]; simp)
    by_contra hlt
    have hlt : orderOf α < h := not_le.mp hlt
    haveI : Fintype K := Fintype.ofFinite K
    have hfin : IsOfFinOrder α := by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨Fintype.card K - 1, by have := Fintype.one_lt_card (α := K); omega,
        FiniteField.pow_card_sub_one_eq_one α hα0⟩
    have hpos : 0 < orderOf α := hfin.orderOf_pos
    exact hk (orderOf α) (Finset.mem_Icc.mpr ⟨hpos, by omega⟩) (pow_orderOf_eq_one α)

end Nock.NockVMROM.Thm54.VclL.Handle
