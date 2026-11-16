/-
  Nock/RedTeam/Batch1210Thm54RepairIIFibNarrowing.lean

  At fib Goldilocks the memory forest has `1277` rows at EVERY `α` (`fib_mem_rows z α`), so
  `programFit α fibTree` is `α`-independent (`fib_fit_alpha_indep`) and §1's `hF` constrains
  `p − 1`, never `orderOf α`.  Since `1280 = 2^8 · 5 ∣ p − 1 ∣ p^3 − 1` and `Kˣ` is cyclic, some
  `α ∈ K` has order `1280` (`exists_order_1280`).  At that `α`:

  * the SIGNED weakest `hwin` holds: `programAcc + 3 ≤ 102 < 1280` and `1277 ≤ 1280`;
  * the fit form `programFit α t + 2 < orderOf α` (the pre-greenlight's recommendation, not
    signed) FAILS: `programFit ≥ 1278`, and `1280 < 1280` is false.

  So the fit form's four-order exclusion (`Batch1062.narrowing_window_sharp`) is reached at a
  configuration §1 admits, and the signed form does not pay it.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenFibGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Nock.RedTeam.Batch1210

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks

/-- `K` has an element of order 1280 (`Kˣ` cyclic of order `p^3 − 1`, and `1280 ∣ p^3 − 1`). -/
theorem exists_order_1280 : ∃ α : K, orderOf α = 1280 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = Fintype.card Kˣ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hcard : Fintype.card Kˣ = Nock.Field.p ^ 3 - 1 := by
    rw [Fintype.card_units, Nock.Field.card_K]
  have hd : 1280 ∣ orderOf g := by
    rw [hog, hcard, Nock.Field.p_eq]; norm_num
  obtain ⟨m, hm⟩ := hd
  have hm0 : m ≠ 0 := by
    rintro rfl; rw [mul_zero] at hm; exact (orderOf_pos g).ne' hm
  refine ⟨((g ^ m : Kˣ) : K), ?_⟩
  rw [orderOf_units, orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hm.symm), hm]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)

/-- `programFit α fibTree` does not depend on `α` (so neither does `hF`). -/
theorem fib_fit_alpha_indep (α β : K) :
    programFit α (fibTree (K := K)) = programFit β (fibTree (K := K)) := by
  have ha : programMemShape α (fibTree (K := K)) = 1277 := fib_mem_rows 0 α
  have hb : programMemShape β (fibTree (K := K)) = 1277 := fib_mem_rows 0 β
  unfold programFit
  rw [ha, hb]

/-- **The fit form would exclude this; the weakest form admits it.**  At any `α` of order 1280
the signed `hwin` holds and the fit form fails. -/
theorem fib_weakest_admits_fit_excludes (α : K) (hα : orderOf α = 1280) :
    (programAcc (fibTree (K := K)) + 3 < orderOf α
      ∧ programMemShape α (fibTree (K := K)) ≤ orderOf α)
    ∧ ¬ (programFit α (fibTree (K := K)) + 2 < orderOf α) := by
  have hm : programMemShape α (fibTree (K := K)) = 1277 := fib_mem_rows 0 α
  have hacc := fib_acc_le
  have hfit := programMemShape_succ_le_fit α (fibTree (K := K))
  refine ⟨⟨by omega, by omega⟩, by omega⟩

/-- Such an `α` exists at fib Goldilocks. -/
theorem fib_weakest_admits_fit_excludes_inhabited :
    ∃ α : K, (programAcc (fibTree (K := K)) + 3 < orderOf α
      ∧ programMemShape α (fibTree (K := K)) ≤ orderOf α)
    ∧ ¬ (programFit α (fibTree (K := K)) + 2 < orderOf α) := by
  obtain ⟨α, hα⟩ := exists_order_1280
  exact ⟨α, fib_weakest_admits_fit_excludes α hα⟩

end Nock.RedTeam.Batch1210

#print axioms Nock.RedTeam.Batch1210.exists_order_1280
#print axioms Nock.RedTeam.Batch1210.fib_fit_alpha_indep
#print axioms Nock.RedTeam.Batch1210.fib_weakest_admits_fit_excludes_inhabited
