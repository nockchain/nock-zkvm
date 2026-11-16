/-
  Nock/NockVMROM/Thm54/TraceGen/GenLineAdvance.lean

  **The line-number recurrence has CONTENT at the generated carrier, for any program.**

  The supplier itself was already here.  `genComputeTimestamps` / `genMemoryTimestamps` /
  `genSpecializesAt` (`GenChainedLanguage.lean`) are quantified over an arbitrary
  `t : NTree (GenComputeRow K)` and an arbitrary accepted program, and their compute conclusion is
  the **relative** `ComputeTimestampSpecializesAt` — `ln = ln_prev · α^(lnExponent −
  lnPrevExponent)` with `ln_prev` unconstrained.

  What is added here is the answer to "is that conclusion vacuous?".  A relative recurrence whose
  exponent gap were `0` would read `ln = ln_prev · α^0 = ln_prev` and say nothing.  Three lemmas:

  * `bfsStamps_lineAdvance` — on any BFS-assigned tree the gap is exactly the row's own
    `recordCount`.  This is the paper's `ln` column identity
    `ln(i−1) · (α·Σ_{j∈{1,3,4}} op_j + α²·Σ_{j∈{0,2,5,7,8}} op_j + α³·Σ_{j∈{6,9}} op_j) = ln(i)`: a state-selected power of `α`, multiplying `ln(i−1)` — never an
    absolute pin.  `Nock.Framework.recordCount` reproduces that one-hot selection exactly
    (`1`/`2`/`3` over the same three state classes).
  * `ln_ne_ln_prev_of_specializes` — one row, `ln ≠ ln_prev`, from `recordCount ≥ 1` and
    `recordCount < orderOf α`.
  * `forall₂_ln_ne_ln_prev` / `genComputeLineAdvances` — the whole trace, for any program the
    generator accepts.

  `hα : α ≠ 0` is §1's `hα`; the orbit
  condition here is `Nock.NockVM.mem_record_arity < orderOf α`, i.e. `3 < orderOf α`, which is
  implied by §1's `horb` (`rowCount ≤ orderOf α`) at any trace of four or more rows.

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## The exponent gap is the row's record count -/

/-- Every stamp on a BFS-assigned tree advances the line exponent by its own state's
`recordCount` — the paper's one-hot `α^{1,2,3}` selection at the paper. -/
theorem bfsStamps_lineAdvance (t : NTree (GenComputeRow K)) :
    ∀ stamp ∈ bfsStamps (bfsAssign t),
      stamp.lnExponent =
        stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state := by
  intro stamp hst
  unfold bfsStamps at hst
  rw [show (fun n : NTree (GenComputeRow K) => n.label.stamp)
        = GenComputeRow.stamp ∘ NTree.label from rfl, ← List.map_map,
    bfsAssign_bfsForest_labels, List.map_map, List.mem_map] at hst
  obtain ⟨i, hi, rfl⟩ := hst
  simp only [Function.comp_apply]
  rw [bfsLabelAt_stamp t i (lt_bfsRows_of_mem_range' hi)]
  exact stampOfAcc_computeLineAdvance _ _

/-! ## One row: the recurrence moves the line number -/

/-- The relative recurrence is a genuine multiplication at a single row: the line number after
the row differs from the line number before it.  No hypothesis pins `ln_prev`; only that it is
nonzero, which the generated carrier's own origin supplies. -/
theorem ln_ne_ln_prev_of_specializes {α : K}
    {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row)
    (hadv : stamp.lnExponent =
      stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state)
    (hprev : row.2.2.1.ln_prev ≠ 0)
    (hord : Nock.Framework.recordCount stamp.state < orderOf α) :
    row.2.2.1.ln ≠ row.2.2.1.ln_prev := by
  have h4 := htime.2.2.2.1
  rw [hadv, Nat.add_sub_cancel_left] at h4
  intro heq
  rw [heq] at h4
  have h' : row.2.2.1.ln_prev * 1 =
      row.2.2.1.ln_prev * α ^ Nock.Framework.recordCount stamp.state := by
    rw [mul_one]; exact h4
  have hone : α ^ Nock.Framework.recordCount stamp.state = 1 :=
    (mul_left_cancel₀ hprev h').symm
  exact pow_ne_one_of_lt_orderOf
    (Nat.one_le_iff_ne_zero.mp (Nock.Framework.recordCount_pos stamp.state)) hord hone

/-- The whole trace, from the two `Forall₂`s the supplier returns. -/
theorem forall₂_ln_ne_ln_prev {α : K} (hα : α ≠ 0)
    (hord : Nock.NockVM.mem_record_arity < orderOf α)
    {stamps : List ComputeTimestampRow}
    {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    (hadv : ∀ stamp ∈ stamps, stamp.lnExponent =
      stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state)
    (htime : List.Forall₂ (ComputeTimestampSpecializesAt α) stamps rows)
    (horig : List.Forall₂
      (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent) stamps rows) :
    List.Forall₂ (fun _ row => row.2.2.1.ln ≠ row.2.2.1.ln_prev) stamps rows := by
  revert hadv horig
  induction htime with
  | nil => intro _ _; exact .nil
  | @cons s _r _ss _rs hh _ht ih =>
      intro hadv horig
      cases horig with
      | cons oh ot =>
          refine .cons ?_ (ih (fun st hst => hadv st (List.mem_cons_of_mem _ hst)) ot)
          exact ln_ne_ln_prev_of_specializes hh (hadv s (List.mem_cons_self ..))
            (by rw [oh]; exact pow_ne_zero _ hα)
            (lt_of_le_of_lt (Nock.Framework.recordCount_le _) hord)

/-! ## At the generated carrier, for any program -/

/-- **The line number genuinely moves at every compute row of any generated trace.**

`genComputeTimestamps` supplies the relative recurrence and `genComputeOrigins` the origin, both
over an arbitrary `t` and forest `mf`; `bfsStamps_lineAdvance` supplies the gap.  So the supplier's
conclusion is not the trivial `ln = ln_prev · α^0` on any row of any trace. -/
theorem genComputeLineAdvances
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (hα : α ≠ 0)
    (hord : Nock.NockVM.mem_record_arity < orderOf α)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    List.Forall₂ (fun _ row => row.2.2.1.ln ≠ row.2.2.1.ln_prev)
      (bfsStamps (bfsAssign (airReorder t)))
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computeRows :=
  forall₂_ln_ne_ln_prev hα hord (bfsStamps_lineAdvance _)
    (genComputeTimestamps (F := F) chal Ksz orbit horb z α a b c t mf hmempos hcomp hmem)
    (genComputeOrigins (F := F) chal Ksz orbit horb z α a b c t mf hmempos hcomp hmem)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsStamps_lineAdvance
#print axioms Nock.NockVMROM.Thm54.TraceGen.ln_ne_ln_prev_of_specializes
#print axioms Nock.NockVMROM.Thm54.TraceGen.forall₂_ln_ne_ln_prev
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeLineAdvances
