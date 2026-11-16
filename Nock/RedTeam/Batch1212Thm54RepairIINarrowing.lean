/-
  Nock/RedTeam/Batch1212Thm54RepairIINarrowing.lean

  The new `hwin` (`programAcc t + 3 < orderOf α ∧ programMemShape α t ≤ orderOf α`) implies the old
  one (`Batch1063.old_hwin_of_weakest`), but the converse fails.  At fib Goldilocks the memory
  forest has `1277` rows at every `α` (`fib_mem_rows`), and `programAcc ≤ 99`.  Some `α` has order
  `128`: the OLD §1 (QM) admitted it (`99 + 3 < 128`), the signed §1 excludes it (`1277 > 128`).

  So §1 is STRICTLY narrowed by the memory conjunct.  This is the signed narrowing; at such an `α` QM's package was
  not honestly accepted anyway (`Batch994.honest_memory_acceptance_forces_walk_alpha`: the memory
  walk ran at a coin other than `α`, and the line numbers collide).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenFibGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Nock.RedTeam.Batch1212

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks

/-- `K` has an element of order 128 (`Kˣ` cyclic of order `p^3 − 1`, and `128 ∣ p^3 − 1`). -/
theorem exists_order_128 : ∃ α : K, orderOf α = 128 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = Fintype.card Kˣ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hcard : Fintype.card Kˣ = Nock.Field.p ^ 3 - 1 := by
    rw [Fintype.card_units, Nock.Field.card_K]
  have hd : 128 ∣ orderOf g := by
    rw [hog, hcard, Nock.Field.p_eq]; norm_num
  obtain ⟨m, hm⟩ := hd
  have hm0 : m ≠ 0 := by
    rintro rfl; rw [mul_zero] at hm; exact (orderOf_pos g).ne' hm
  refine ⟨((g ^ m : Kˣ) : K), ?_⟩
  rw [orderOf_units, orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hm.symm), hm]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)

/-- **§1 is STRICTLY narrowed by the memory conjunct.**  At fib Goldilocks there is an `α` the OLD
`hwin` admits and the signed one excludes (`hF` is `α`-independent there:
`Batch1210.fib_fit_alpha_indep`). -/
theorem fib_old_admits_new_excludes :
    ∃ α : K, programAcc (fibTree (K := K)) + 3 < orderOf α ∧
      ¬ (programAcc (fibTree (K := K)) + 3 < orderOf α ∧
          programMemShape α (fibTree (K := K)) ≤ orderOf α) := by
  obtain ⟨α, hα⟩ := exists_order_128
  have hm : programMemShape α (fibTree (K := K)) = 1277 := fib_mem_rows 0 α
  have hacc : programAcc (fibTree (K := K)) ≤ 99 := fib_acc_le
  refine ⟨α, by omega, fun h => by omega⟩

end Nock.RedTeam.Batch1212
