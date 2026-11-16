/-
  Nock/NockVMROM/Thm54/TraceGen/GenForestIndexRange.lean

  **`forestIndexRange`, reduced to a `Ksz` choice and one non-vacuous fact.**

  `ExactServedMemoryTrace.forestIndexRange` (`ServedMemoryTrace.lean:613`) is the `[K]` index range
  of `L_mIO` applied once to the aggregate service timestamp list of the whole
  supplied forest.  `IO.InRange K n` unfolds to `1 ≤ n ∧ n ≤ K` (`Nock/IO.lean:43`).

  The point of this module is that the field says **nothing about `roots`**.  `readPartition`
  already pins each root's service list to a permutation of that root's `read_root` exponents
  (`ServedMemoryTrace.lean:501`), so the aggregate length is forced:

      ‖⋃ᵢ (roots i).timestampPowers‖ = ‖forestReadTimestamps cfg exec‖
                                     = Σᵢ ‖readExps (exactAxisTree cfg exec i)‖

  — a number determined by the execution's own memory forest, whatever `roots` turns out to be.  So
  the obligation splits cleanly in two:

  * `n ≤ cfg.Ksz` is largely a **compiler choice** — `Ksz` is a free parameter of `genExactConfig`,
    picked by the generator as `q` is.
  * `1 ≤ n` is carried as a stated precondition, with `forestReadCount_pos` as the discharge from a
    single witnessing root.  That is true of
    an individual root and does **not** make `n = 0` reachable: `recordCount_pos`
    (`Framework/NockInstances.lean:65`) gives every one of the eleven states at least one memory
    record, so every accepted program emits at least one request and its forest at least one
    `read_root` row.  So this is a **composition obligation**, not a restriction — it is
    dischargeable for every accepted program and nobody has yet composed it.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedCoverage

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.AxisBridge

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Pointwise permutations lift through `flatMap`.  (`ServedMemoryTrace` has this privately;
restated here rather than de-privatised, since that file is on the capstone path.) -/
private theorem perm_flatMap_pointwise {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons b t ih =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact (h b (by simp)).append (ih fun a ha => h a (by simp [ha]))

/-- **The aggregate service timestamp list is a permutation of the forest read timestamps.**

Root-family-level restatement of `ExactServedMemoryTrace.forestReadTimestamps_perm`, which is a
method on the finished structure and so is unavailable while the structure is being built. -/
theorem forestTimestampPowers_perm {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (roots : ∀ i : Fin cfg.kMem, RootTrace cfg exec i) :
    (forestReadTimestamps cfg exec).Perm
      ((List.finRange cfg.kMem).flatMap (fun i => (roots i).timestampPowers)) :=
  perm_flatMap_pointwise fun i _ => (roots i).readTimestamps_perm

/-- **The aggregate length, in terms of the execution alone.**

No `roots` on the right-hand side: whatever root traces are eventually supplied, the list whose
length `forestIndexRange` constrains has exactly this many entries. -/
theorem forestTimestampPowers_length {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (roots : ∀ i : Fin cfg.kMem, RootTrace cfg exec i) :
    ((List.finRange cfg.kMem).flatMap (fun i => (roots i).timestampPowers)).length =
      ((List.finRange cfg.kMem).map
        (fun i => (readExps (exactAxisTree cfg exec i)).length)).sum := by
  rw [← (forestTimestampPowers_perm roots).length_eq]
  unfold forestReadTimestamps
  rw [List.length_flatMap]
  simp

/-- **`forestIndexRange` for any root family.**

The two halves are exactly as the module docstring describes them: `hle` is discharged by choosing
`Ksz`, `hpos` is the one genuine fact about the program's memory forest. -/
theorem forestIndexRange_of_readCount {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (roots : ∀ i : Fin cfg.kMem, RootTrace cfg exec i)
    (hpos : 1 ≤ ((List.finRange cfg.kMem).map
      (fun i => (readExps (exactAxisTree cfg exec i)).length)).sum)
    (hle : ((List.finRange cfg.kMem).map
      (fun i => (readExps (exactAxisTree cfg exec i)).length)).sum ≤ cfg.Ksz) :
    IO.InRange cfg.Ksz
      ((List.finRange cfg.kMem).flatMap (fun i => (roots i).timestampPowers)).length := by
  rw [IO.InRange, forestTimestampPowers_length roots]
  exact ⟨hpos, hle⟩

/-- **`1 ≤ n` from a single witnessing root.**

The usable form of the non-vacuous half: one root with at least one `read_root` row suffices, and
that is what a program containing any OP0 or OP9 row supplies. -/
theorem forestReadCount_pos {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (j : Fin cfg.kMem) (hj : 1 ≤ (readExps (exactAxisTree cfg exec j)).length) :
    1 ≤ ((List.finRange cfg.kMem).map
      (fun i => (readExps (exactAxisTree cfg exec i)).length)).sum := by
  refine le_trans hj (List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_)
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

/-! ## The services-length route

The `readExps` route above is not the shortest way to this
field.  `RootTrace.timestampPowers` is `services.map Service.exponent |>.map (α ^ ·)`, so its length
is just `services.length` — no read-back, no permutation, no `h1`/`h2`.  A `roots` family that
reports its `services.length` therefore bounds the aggregate directly.  This is the route
`genRoots` can use today; the one above waits on §D. -/

/-- A root's timestamp multiset is exactly as long as its service list. -/
@[simp] theorem timestampPowers_length {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {i : Fin cfg.kMem} (R : RootTrace cfg exec i) :
    R.timestampPowers.length = R.services.length := by
  simp [RootTrace.timestampPowers, RootTrace.exponents]

/-- The aggregate length is the sum of the per-root service counts. -/
theorem forestTimestampPowers_length_services {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (roots : ∀ i : Fin cfg.kMem, RootTrace cfg exec i) :
    ((List.finRange cfg.kMem).flatMap (fun i => (roots i).timestampPowers)).length =
      ((List.finRange cfg.kMem).map (fun i => (roots i).services.length)).sum := by
  rw [List.length_flatMap]
  simp

/-- **`forestIndexRange` from the per-root service counts.**

`hpos` needs one root to exist and to serve something; `hle` is the `Ksz` choice.  Neither half
touches the forest's read structure, which is why this does not wait on the read-back. -/
theorem forestIndexRange_of_services {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (roots : ∀ i : Fin cfg.kMem, RootTrace cfg exec i)
    (j : Fin cfg.kMem) (hj : 1 ≤ (roots j).services.length)
    (hle : ((List.finRange cfg.kMem).map
      (fun i => (roots i).services.length)).sum ≤ cfg.Ksz) :
    IO.InRange cfg.Ksz
      ((List.finRange cfg.kMem).flatMap (fun i => (roots i).timestampPowers)).length := by
  rw [IO.InRange, forestTimestampPowers_length_services roots]
  refine ⟨le_trans hj (List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_), hle⟩
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

/-- The sum is at most `2 * kMem` when every root serves at most two records — the shape both
`RootTrace` builders produce, so this is the bound a caller actually has. -/
theorem services_sum_le_two_mul {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (roots : ∀ i : Fin cfg.kMem, RootTrace cfg exec i)
    (hb : ∀ i, (roots i).services.length ≤ 2) :
    ((List.finRange cfg.kMem).map (fun i => (roots i).services.length)).sum
      ≤ 2 * cfg.kMem := by
  have h1 : ((List.finRange cfg.kMem).map (fun i => (roots i).services.length)).sum
      ≤ ((List.finRange cfg.kMem).map (fun _ : Fin cfg.kMem => 2)).sum :=
    List.sum_le_sum (fun i _ => hb i)
  refine h1.trans ?_
  rw [List.map_const', List.sum_replicate, List.length_finRange]
  simp [Nat.mul_comm]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.forestTimestampPowers_perm
#print axioms Nock.NockVMROM.Thm54.TraceGen.forestTimestampPowers_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.forestIndexRange_of_readCount
#print axioms Nock.NockVMROM.Thm54.TraceGen.forestReadCount_pos
#print axioms Nock.NockVMROM.Thm54.TraceGen.timestampPowers_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.forestTimestampPowers_length_services
#print axioms Nock.NockVMROM.Thm54.TraceGen.forestIndexRange_of_services
#print axioms Nock.NockVMROM.Thm54.TraceGen.services_sum_le_two_mul
