/-
  Nock/RedTeam/Batch206Thm54GoldilocksTimestampBase.lean

  **The Goldilocks timestamp base, measured.**

  `TraceGen/GoldilocksTimestampBase.lean` names a timestamp base `α` at `Nock.Field.K` and discharges the generic assembly's orbit conditions from
  it.  So this module measures the witness.

  Four measurements, and the third is the one that matters:

  1. **The order.**  `orderOf goldilocksTimestampBase = p^3 - 1 =`
     `6277101731002175853884774869567645561244584131361410908160`, which is `2^192` to within one
     part in `2^64`.  It is the full unit-group order of the cubic extension.
  2. **The choice is optimal, not merely large.**  `b206_no_longer_orbit`: every nonzero element of
     `Field.K` has order at most this one's, so the admissible-trace bound is a property of the
     Goldilocks cubic extension and not of which element the module happened to choose.
  3. **What it admits, in rows rather than records.**  The side condition is stated on
     `accAt (airReorder t) (bfsRows (airReorder t)).length` — the number of memory records the
     trace emits, not its row count.
  4. **What it excludes, exactly.**  `b206_window_iff` puts the boundary at
     `6277101731002175853884774869567645561244584131361410908157` records, and
     `b206_window_not_vacuous` exhibits a record count that fails — so the hypothesis has content
     and is not a disguised `True`, even though nothing it excludes is reachable.

  **Not claimed.**  This is a statement about *hypotheses being satisfiable*, nothing more.  It also says nothing about the **seed** family `hseed`/`hbad`/`hout`, which are counting
  arguments over `z` and a separate provisioning problem (`EA`, `ED`, `ES.2`).

  Nor is there a *concrete* Goldilocks trace here: `Field.K`'s `Fintype`/`DecidableEq` instances
  are noncomputable (`Field.lean:57-58`), so no `decide` can run at this carrier and Tier A's live
  fixture is at `GaloisField 769 3`.  The measurement is therefore `∀ t`, which is the stronger
  reading, but it is a bound and not an evaluation.
-/
import Nock.NockVMROM.Thm54.TraceGen.GoldilocksTimestampBase
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulNodup

set_option autoImplicit false

namespace Nock.RedTeam.Batch206Goldilocks

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.Framework.Thm54

noncomputable section

/-! ## 1. The order of the witness -/

/-- The witness's order, as a decimal.  `≈ 2^192`. -/
theorem b206_order :
    orderOf goldilocksTimestampBase
      = 6277101731002175853884774869567645561244584131361410908160 :=
  goldilocksTimestampBase_order_value

/-- The witness is nonzero — the `hα` every orbit premise subsumes. -/
theorem b206_ne_zero : goldilocksTimestampBase ≠ 0 :=
  goldilocksTimestampBase_ne_zero

/-! ## 2. The choice is optimal

`orderOf_le_card_sub_one` is field-generic, so this is not "our `α` is big" but "no `α` in this
field is bigger". -/

/-- **No timestamp base in `Field.K` admits a longer trace.** -/
theorem b206_no_longer_orbit {α : Nock.Field.K} (hα : α ≠ 0) :
    orderOf α ≤ 6277101731002175853884774869567645561244584131361410908160 := by
  rw [← b206_order]
  exact goldilocksTimestampBase_maximal hα

/-! ## 3. What the condition admits: every trace of at most `2^63` rows

The premise `genSemanticData` needs is on the record count `accAt … (bfsRows …).length`, which is a
prefix sum of `recordCount` and so at most three per row (`accAt_le_three_mul`).  Converting to rows
is what makes the bound legible: rows are what a deployment sizes. -/

/-- Record count is at most three per BFS row.  A restatement of the generic
`accAt_le_three_mul` at the index the assembly uses. -/
theorem b206_records_le_three_mul_rows (t : NTree (GenComputeRow Nock.Field.K)) :
    accAt (airReorder t) (bfsRows (airReorder t)).length
      ≤ 3 * (bfsRows (airReorder t)).length :=
  accAt_le_three_mul (airReorder t) _

/-- **The row-count form of the side condition.**  For every program-generated tree, a row count
below `(p^3 - 4)/3` suffices; no property of the program enters. -/
theorem b206_fit_of_rows {t : NTree (GenComputeRow Nock.Field.K)}
    (hrows : 3 * (bfsRows (airReorder t)).length + 3 < Nock.Field.p ^ 3 - 1) :
    accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < Nock.Field.p ^ 3 - 1 := by
  have := b206_records_le_three_mul_rows t
  omega

/-- **Every generated trace of at most `2^63` rows meets every orbit condition of the assembly.**

The conclusion is, in order: `genSemanticData`'s `hα`, its `hB` at
`B := orderOf goldilocksTimestampBase`, its `hwin`, and `genRoots`' `horbα`.  `t` is arbitrary, so
this holds for every program `genComputeSkeleton` accepts. -/
theorem b206_admits_two_pow_63 {t : NTree (GenComputeRow Nock.Field.K)}
    (hrows : (bfsRows (airReorder t)).length ≤ 2 ^ 63) :
    goldilocksTimestampBase ≠ 0 ∧
      orderOf goldilocksTimestampBase ≤ orderOf goldilocksTimestampBase ∧
      accAt (airReorder t) (bfsRows (airReorder t)).length + 3
        < orderOf goldilocksTimestampBase ∧
      accAt (airReorder t) (bfsRows (airReorder t)).length
        < orderOf goldilocksTimestampBase := by
  refine goldilocksTimestampBase_trace_orbit (b206_fit_of_rows ?_)
  have hp : Nock.Field.p ^ 3 - 1
      = 6277101731002175853884774869567645561244584131361410908160 := by
    rw [Nock.Field.p_eq]; norm_num
  rw [hp]
  omega

/-! ## 4. What the condition excludes, exactly -/

/-- The exclusion boundary: the side condition is exactly "fewer than `p^3 - 4` records". -/
theorem b206_window_iff (n : ℕ) :
    n + 3 < Nock.Field.p ^ 3 - 1
      ↔ n < 6277101731002175853884774869567645561244584131361410908157 := by
  have hp : Nock.Field.p ^ 3 - 1
      = 6277101731002175853884774869567645561244584131361410908160 := by
    rw [Nock.Field.p_eq]; norm_num
  rw [hp]
  omega

/-- **The hypothesis has content.**  A record count at the boundary fails it, so
`goldilocksTimestampBase_assembly_orbit`'s premise is not a disguised `True` — even though nothing
it excludes is reachable by any trace a machine could emit. -/
theorem b206_window_not_vacuous :
    ¬ (6277101731002175853884774869567645561244584131361410908157 + 3
        < Nock.Field.p ^ 3 - 1) := by
  rw [b206_window_iff]
  omega

/-! ## 5. The three obligations, named individually

Stated separately so a consumer can see that each of `genSemanticData`'s orbit arguments has a
witness, rather than only that some conjunction holds. -/

/-- `genSemanticData`'s `hB`, at `B := orderOf goldilocksTimestampBase`. -/
theorem b206_hB : orderOf goldilocksTimestampBase ≤ orderOf goldilocksTimestampBase := le_rfl

/-- `genSemanticData`'s `hwin`, for any trace of at most `2^63` rows. -/
theorem b206_hwin {t : NTree (GenComputeRow Nock.Field.K)}
    (hrows : (bfsRows (airReorder t)).length ≤ 2 ^ 63) :
    accAt (airReorder t) (bfsRows (airReorder t)).length + 3
      < orderOf goldilocksTimestampBase :=
  (b206_admits_two_pow_63 hrows).2.2.1

/-- `genRoots`' `horbα`, for any trace of at most `2^63` rows.  It is not an extra assumption:
`horb_of_window` derives it from `hwin`. -/
theorem b206_horb {t : NTree (GenComputeRow Nock.Field.K)}
    (hrows : (bfsRows (airReorder t)).length ≤ 2 ^ 63) :
    accAt (airReorder t) (bfsRows (airReorder t)).length
      < orderOf goldilocksTimestampBase :=
  (b206_admits_two_pow_63 hrows).2.2.2

end

end Nock.RedTeam.Batch206Goldilocks

#print axioms Nock.RedTeam.Batch206Goldilocks.b206_order
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_ne_zero
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_no_longer_orbit
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_records_le_three_mul_rows
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_fit_of_rows
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_admits_two_pow_63
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_window_iff
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_window_not_vacuous
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_hwin
#print axioms Nock.RedTeam.Batch206Goldilocks.b206_horb
