import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.NockGigaRAPFinite
import Nock.NockVMROM.Thm54.IOCoinReconciliation
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Where the two `RAP_prog-IO` coins sit in the giga-RAP, and the composition that follows

`NockGigaRAPFinite.lean` assembles the two combined AIRs with the prover-committed finite-field IO
chips substituted in, generic in the declared coin count `nc` and in the challenge renaming `fC`.
`IOCoinReconciliation.lean` identifies the two coins the `K`-valued IO chip consumes with the IO
coordinate of the production challenge tuple, and extends the staged chronology by the two slots
those coins need (`Chronology.nockChronologyWithIO`, `IOCoinReconciliation.lean:459`).

This module is the seam.  It carries the placement over the **ten**-coin chronology, proves that
the canonical placement is the only schedule-legal one that reads no coin the proof already uses,
rebuilds the two staged chips on that chronology, and composes
`GigaFinite`'s fold with `IOCoinReconciliation.io_lio_of_satisfies_at_production_coins`.

## The defect this fixes

`IOCoinReconciliation` put the two IO coins at **new** slots `8`, `9` of a ten-slot chronology and
proved `ioSlots_are_new` and `ioSlots_ne_memory_slots` (`IOCoinReconciliation.lean:482`, `:487`) —
in particular that neither is slot `6` (`β`) or slot `7` (`γ`).  `NockGigaRAPFinite` placed them
among the existing **eight**, with an `IOSlots` carrying `slot : Fin 2 → Fin 8` and an
`exampleIOSlots := ![gammaSlot, betaSlot]` using exactly the forbidden pair.  Neither theorem was
false, but they did not compose: `io_lio_of_giga_satisfies` needed a `ChipAgreement` asserting
`q.chalVal (S.slot i)` for `S.slot i : Fin 8`, and the coins
`io_lio_of_satisfies_at_production_coins` delivers are provably none of those eight.

The eight-slot reading was also wrong on its own terms.  Slots `6`/`7` are the memory table's
*internal* `intermediate` pole and record-RLC coin — the components of
`PairedRecordCountedEvent.interCoins` (`:210`), whose receipt
`interCoins_is_the_table_pole_not_the_io_sample` (`PairedRecordCountedEvent.lean:243`) says they
are not the `RAP_prog-IO` sample — and this tree pins `ChallengeVector.β := 0`, so a placement
onto slot `6` makes the "sampled" pole the constant `0`
(`memoryAlias_pole_is_the_table_beta`, §1.4).  The paper samples that pole: the paper
"Verifier responds with random elements `α, β ∈ 𝕂`", consumed by `RLC^α(IO_prog(i,k,·)) - β`, priced at the paper as "One round of interaction, providing two random
elements in `𝕂`", and *not* resampled on the memory side.

## What the round is, and why

the paper commits `Com(IO_prog)` and the paper builds `acc_prog`, with the two coins
between them.  So the coins are **not** usable by the columns that commit the records — this
tree's ext block, round `1` — and **are** usable by the accumulator columns, round `2`.  That is
one condition, `IOSlots.commit_then_sample`, and it is not vacuous: it excludes the four round-`0`
coins `z, a, b, c`.  Of the six slots it leaves, four are `nockChronology`'s own `α, α_C, β, γ`,
so slots `8` and `9` are the only fresh ones (`only_the_new_slots_are_fresh`) and the canonical
placement is unique up to transposing the pair (`canonical_is_the_only_fresh_placement`).

## Co-location with the timestamp column, and where it leaves a modelling hypothesis

the paper introduces `RAP_prog-IO` as "a new RAP … with an additional final round of
interaction", the paper sequences `IO_prog` → `Com(IO_prog)` → the coins `α, β` →
`acc_prog`, and the paper prices the round separately.  Read as a *sequence of messages* that
asks for a third verifier message after the block that commits `IO_prog`.
`nockChronologyWithIO` does not provide one: it keeps this tree's three column blocks and **two**
verifier messages, putting the two IO coins in the second message alongside the timestamp base
`α`.  Column `111` — `NockVM.encRec` coordinate `7`, the record timestamp `ts` with honest value
`ln(i−1)·α^k` — reads `α` and is therefore a round-`2` column, i.e. it
is committed in the *same* block as the accumulators and after the *same* message as the IO
coins.

So the timestamp column
and the multiset accumulators are committed after one and the same draw.

**What the LogUp argument needs is independence, not sequencing — and at column `111`/`52` this
module supplies that independence as an assumption, not as a consequence.**  What the paper's
commitment buys is that the prover cannot choose `IO_prog` *as a function of* the two coins of
the paper; the union bound over the pole then runs at each fixed record set.  Here that
independence is asserted of the columns rather than derived from the message order: §2's
`io_records_read_no_io_coin` says no record or multiplicity column of either IO block *declares*
either IO coin, the timestamp column included.

That is a fact about the **paper's** `V_comp`, a clause
over `W_comp`, and it has **no image in this tree's IO block**:
`FiniteIO.finiteIOProgAIR` (`FiniteFieldIOAIR.lean:153`) has four gates and none pins a record
coordinate, and `ComputeChip.computeAIRchained_varsBelow` together with
`GigaFinite.finiteIOProgAIR_varsBelow` (`NockGigaRAPFinite.lean:152`) make the compute and IO
blocks constraint-disjoint, so no gate of `computeCombinedFiniteAIR` mentions both a compute column
and an IO record column.  The sentence is withdrawn.

Scope, stated precisely.  The *ordering* difference between the paper and this
tree's two-message chronology is real and is recorded here, at
`record_timestamp_column_shares_the_message_with_the_io_coins`.  Where the difference bites is
exactly the two round-`2` IO data columns `111` and `52`: for compute `102 … 110` and memory
`43 … 51` the exclusion follows from `commit_then_sample` (`io_records_commit_before_the_io_coins`),
while at `111`/`52` it is the declaration alone, and a chip that declared the pair there would be
equally legal over the identical AIR, params and schedule.  `GigaRAPThirdMessage.lean` carries the
version in which the exclusion is *forced*: at a chronology giving the paper's "additional
final round of interaction" its own message,
`GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute` proves it for every chip.
-/

namespace Nock.NockVMROM.Thm54.GigaIOSlots

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GigaFinite
open Nock.NockVMROM.Thm54.IOCoinReconciliation
open Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology
open scoped Polynomial

/-! ## 1. The placement, over the ten-coin chronology -/

/-! ### 1.1 The schedule facts, transported to `Fin 10` -/

/-- Every coin of the ten-slot draw is delivered by one of the two verifier messages, so every one
of them is usable by a round-`2` column.  This is the analogue of
`GigaFinite.nockSampledAfter_lt_two` and the only new `decide` the widening needs. -/
theorem nockSampledAfterWithIO_lt_two : ∀ j : Fin 10, (nockSampledAfterWithIO j : ℕ) < 2 := by
  decide

/-- The round-`1`-usable coins of the compute chip, on the widened draw. -/
theorem withIO_computeRoundOne_coins : ∀ j : Fin 10, j ∈ ({1, 2, 3, 4} : Finset (Fin 10)) →
    (nockSampledAfterWithIO j : ℕ) < 1 := by decide

/-- The round-`1`-usable coin of the memory chip, on the widened draw. -/
theorem withIO_memoryRoundOne_coins : ∀ j : Fin 10, j ∈ ({1} : Finset (Fin 10)) →
    (nockSampledAfterWithIO j : ℕ) < 1 := by decide

/-- **The widened round-`1` coin set is the old one.** -/
theorem roundOne_coins_are_the_embedded_seeds :
    ({1, 2, 3, 4} : Finset (Fin 10)) = ({1, 2, 3, 4} : Finset (Fin 8)).image embed8 := by decide

/-- The compute chip's round-`2` coins, likewise. -/
theorem computeRoundTwo_coins_are_embedded :
    ({0, 1, 2, 3, 4, 5} : Finset (Fin 10))
      = ({0, 1, 2, 3, 4, 5} : Finset (Fin 8)).image embed8 := by decide

/-- The memory chip's round-`2` coins, likewise. -/
theorem memRoundTwo_coins_are_embedded :
    ({0, 1, 6, 7} : Finset (Fin 10)) = ({0, 1, 6, 7} : Finset (Fin 8)).image embed8 := by decide

/-! ### 1.2 `IOSlots`, widened -/

/-- **Where the two finite-IO coins live in the proof's coin space.**

`FiniteIO.ioRowEnv` reads `chal 0 = coins.gamma` and `chal 1 = coins.pole`
(`FiniteFieldIOAIR.lean:58`), so an IO block placed inside a combined AIR needs an injection of
`Fin 2` into the proof's slots.  The proof's slots are the **ten** of `nockChronologyWithIO`, not
the eight of `nockChronology`: none of those eight is the `RAP_prog-IO` pair (see the header).

`commit_then_sample` is the paper's own condition, and unlike the `early : … < 2` field this
structure carried before, it is **not** vacuous: the paper commits `Com(IO_prog)` before the
coins are sent, so a coin usable by a round-`1` column is too early, and the paper builds
`acc_prog` after them, so a round-`2` column must be able to read them. -/
structure IOSlots where
  /-- Slot `0` carries the record-RLC coin, slot `1` the LogUp pole. -/
  slot : Fin 2 → Fin 10
  /-- The two coins are distinct slots of the global draw. -/
  injective : Function.Injective slot
  /-- **Commit, then sample**: not usable by the block that commits
  `IO_prog`, usable by the block that accumulates. -/
  commit_then_sample : ∀ i, ¬ nockChronologyWithIO.usableByColumnOf 1 (slot i)
    ∧ nockChronologyWithIO.usableByColumnOf 2 (slot i)

namespace IOSlots

variable (S : IOSlots)

/-- Both coins are delivered before the accumulator round — the old `early` field, now derived. -/
theorem early : ∀ i, (nockSampledAfterWithIO (S.slot i) : ℕ) < 2 :=
  fun i => (S.commit_then_sample i).2

/-- **Both coins ride the final verifier message.**  `commit_then_sample` pins the round exactly:
`¬ (x < 1)` and `x < 2` force `x = 1`. -/
theorem final_round : ∀ i, nockSampledAfterWithIO (S.slot i) = 1 := by
  intro i
  have h1 := (S.commit_then_sample i).1
  have h2 := (S.commit_then_sample i).2
  simp only [ChallengeChronology.usableByColumnOf, nockChronologyWithIO, not_lt] at h1 h2
  exact Fin.ext (by omega)

/-- The two slots are different. -/
theorem slot_ne : S.slot 0 ≠ S.slot 1 := fun h => absurd (S.injective h) (by decide)

/-- The placement as a challenge renaming `ℕ → ℕ`, the form `Expr.remapBlock` consumes. -/
def map : ℕ → ℕ :=
  fun i => if h : i < 2 then ((S.slot ⟨i, h⟩ : Fin 10) : ℕ) else 0

@[simp] theorem map_zero : S.map 0 = (S.slot 0 : ℕ) := rfl
@[simp] theorem map_one : S.map 1 = (S.slot 1 : ℕ) := rfl

/-- Both placed slots are inside the proof's coin space. -/
theorem map_lt_ten : ∀ i, i < 2 → S.map i < 10 := by
  intro i hi
  interval_cases i
  · exact (S.slot 0).isLt
  · exact (S.slot 1).isLt

/-- **The two coins really are two coins.**  With `GigaFinite.collapsed_placement_identifies_coins`
this is what rules out the degenerate placement on which every valuation forces `gamma = pole`. -/
theorem map_ne : S.map 0 ≠ S.map 1 := by
  intro h
  exact absurd (S.injective (Fin.val_injective h)) (by decide)

end IOSlots

/-! ### 1.3 What the schedule permits, and the canonical placement -/

/-- **Exactly the final-message pairs are placements.**  Forward: `commit_then_sample` pins both
rounds to `1` and `injective` separates the slots.  Backward: any such pair is a placement.  So
the schedule excludes the four round-`0` coins `z, a, b, c` and nothing else. -/
theorem exists_placement_iff (s t : Fin 10) :
    (∃ S : IOSlots, S.slot 0 = s ∧ S.slot 1 = t)
      ↔ s ≠ t ∧ nockSampledAfterWithIO s = 1 ∧ nockSampledAfterWithIO t = 1 := by
  constructor
  · rintro ⟨S, hs, ht⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hs, ← ht]; exact S.slot_ne
    · rw [← hs]; exact S.final_round 0
    · rw [← ht]; exact S.final_round 1
  · rintro ⟨hst, hs, ht⟩
    refine ⟨{ slot := ![s, t], injective := ?_, commit_then_sample := ?_ }, rfl, rfl⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro i
      have h : nockSampledAfterWithIO (Matrix.vecCons s ![t] i) = 1 := by
        fin_cases i
        · simpa using hs
        · simpa using ht
      simp only [ChallengeChronology.usableByColumnOf, nockChronologyWithIO, h]
      exact ⟨by norm_num, by norm_num⟩

/-- The six schedule-legal slots: `α`, `α_C`, `β`, `γ` and the two new ones. -/
theorem placement_candidates :
    (Finset.univ.filter fun j : Fin 10 => nockSampledAfterWithIO j = 1)
      = {0, 5, 6, 7, 8, 9} := by decide

/-- **Only slots `8` and `9` are fresh.**  The complement of the eight coins `nockChronology`
already declares is exactly the two IO slots — so among the placements the schedule permits, the
canonical one is the only one that reads no coin the proof is already using for something else. -/
theorem only_the_new_slots_are_fresh :
    (Finset.univ : Finset (Fin 10)) \ (Finset.univ.image embed8)
      = {ioGammaSlot, ioPoleSlot} := by decide

/-- **The canonical placement**: the record-RLC coin `γ` of the paper's `RLC^α` on slot `8`,
the LogUp pole `-β` on slot `9` — the two slots `Chronology.nockChronologyWithIO` adds. -/
def canonicalIOSlots : IOSlots where
  slot := ![ioGammaSlot, ioPoleSlot]
  injective := by decide
  commit_then_sample := by decide

@[simp] theorem canonicalIOSlots_slot_zero : canonicalIOSlots.slot 0 = ioGammaSlot := rfl
@[simp] theorem canonicalIOSlots_slot_one : canonicalIOSlots.slot 1 = ioPoleSlot := rfl

/-- **The canonical placement reads two new coins.**  Neither slot is any of the eight
`nockChronology` declares — the projection of `Chronology.ioSlots_are_new`
(`IOCoinReconciliation.lean:482`) onto this placement. -/
theorem canonicalIOSlots_are_new (j : Fin 8) :
    embed8 j ≠ canonicalIOSlots.slot 0 ∧ embed8 j ≠ canonicalIOSlots.slot 1 :=
  Chronology.ioSlots_are_new j

/-- Stated at the two slots the retired `exampleIOSlots` used: the memory table's `γ` at `7` and
`β` at `6` are not the IO coins. -/
theorem canonicalIOSlots_ne_memory_slots :
    embed8 gammaSlot ≠ canonicalIOSlots.slot 0 ∧ embed8 betaSlot ≠ canonicalIOSlots.slot 1 :=
  Chronology.ioSlots_ne_memory_slots

/-- Both canonical coins ride the final verifier message. -/
theorem canonicalIOSlots_final_round :
    nockSampledAfterWithIO (canonicalIOSlots.slot 0) = 1
      ∧ nockSampledAfterWithIO (canonicalIOSlots.slot 1) = 1 :=
  ⟨canonicalIOSlots.final_round 0, canonicalIOSlots.final_round 1⟩

/-- **Uniqueness up to transposition.**  A placement that reads none of the eight declared coins
is the canonical one or its transpose.  Nothing else is available: this is
`only_the_new_slots_are_fresh` plus `injective`. -/
theorem canonical_is_the_only_fresh_placement (S : IOSlots)
    (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j) :
    (S.slot 0 = ioGammaSlot ∧ S.slot 1 = ioPoleSlot)
      ∨ (S.slot 0 = ioPoleSlot ∧ S.slot 1 = ioGammaSlot) := by
  have key : ∀ i, S.slot i = ioGammaSlot ∨ S.slot i = ioPoleSlot := by
    intro i
    have hmem : S.slot i ∈ (Finset.univ : Finset (Fin 10)) \ (Finset.univ.image embed8) := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image, not_exists]
      exact fun j hj => hfresh i j hj.symm
    rw [only_the_new_slots_are_fresh] at hmem
    simpa using hmem
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1
  · exact absurd (S.injective (h0.trans h1.symm)) (by decide)
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (S.injective (h0.trans h1.symm)) (by decide)

/-! ### 1.4 The retired example, kept as a labelled counterexample

`NockGigaRAPFinite.exampleIOSlots` was `![gammaSlot, betaSlot]`, i.e. the memory table's own
record-RLC coin and internal pole.  The schedule does **not** rule it out — both slots are
final-message coins — so the exclusion has to be semantic, and it is: the pair is the one
`Chronology.ioSlots_ne_memory_slots` forbids, and slot `6` carries a coin this tree pins to `0`. -/

/-- **A legal-by-schedule, semantically wrong placement** — the one the defective revision shipped
as `exampleIOSlots`.  Kept only as the subject of the two theorems below. -/
def memoryAliasIOSlots : IOSlots where
  slot := ![embed8 gammaSlot, embed8 betaSlot]
  injective := by decide
  commit_then_sample := by decide

/-- **What is wrong with it.**  Both its slots are coins `nockChronology` already declares, and
neither is an IO slot; the schedule is silent, `Chronology.ioSlots_ne_memory_slots` is not. -/
theorem memoryAliasIOSlots_reads_the_memory_table_coins :
    memoryAliasIOSlots.slot 0 = embed8 gammaSlot
      ∧ memoryAliasIOSlots.slot 1 = embed8 betaSlot
      ∧ memoryAliasIOSlots.slot 0 ≠ ioGammaSlot
      ∧ memoryAliasIOSlots.slot 1 ≠ ioPoleSlot :=
  ⟨rfl, rfl, Chronology.ioSlots_ne_memory_slots.1, Chronology.ioSlots_ne_memory_slots.2⟩

section AliasCost

variable {K : Type*} [Field K]

/-- **The cost of the wrong placement, priced.**  Under the alias placement the chip's
`ChipAgreement` asserts that the *pole* is whatever the proof's slot `6` carries.  That slot is
`ChallengeVector.β`, which this tree pins to `0` (`GenTierAConfig769.lean:89`,
`IOCoinReconciliation.interCoins_pole_eq_zero`), so the "sampled" pole would be the constant `0` —
and a soundness argument over a constant pole buys nothing, while the paper samples it and
the paper pays for it. -/
theorem memoryAlias_pole_is_the_table_beta {m : ℕ}
    (recs : List (Fin m → K)) (coins : IOCoins K) (terminal : K)
    (q : SegmentedRAPParams K) (x₀ : K) {w : ℕ} (Pt : Fin w → K[X])
    (hag : IOChip.ChipAgreement recs coins terminal
      (remapParams q memoryAliasIOSlots.map ComputeChip.ioPubOff) x₀ Pt)
    (hβ : q.chalVal ((embed8 betaSlot : Fin 10) : ℕ) = 0) :
    coins.pole = 0 := by
  have h := hag.pole_eq
  simp only [remapParams, IOSlots.map_one, memoryAliasIOSlots, Matrix.cons_val_one,
    Matrix.head_cons] at h
  exact h.symm.trans hβ

/-- The canonical placement has no such collapse available: its pole slot is `9`, which no other
column of either chip reads. -/
theorem canonical_pole_slot_is_fresh (j : Fin 8) :
    (canonicalIOSlots.map 1) ≠ ((embed8 j : Fin 10) : ℕ) := by
  intro h
  exact (canonicalIOSlots_are_new j).2 (Fin.ext h.symm)

end AliasCost

/-! ### 1.5 Shift or remap

`GigaFinite.shift_is_a_placement` says a constant challenge offset is a placement.  The canonical
placement **is** such an offset — the shift by `8` — so on the canonical wiring `remapBlock` could
have been `shiftBlock`.  `remapBlock` is still the right primitive, because the transposed
placement is legal by schedule and is not a shift. -/

/-- **The canonical placement is the shift by `8`.**  (The defective revision claimed of its
`exampleIOSlots` that no placement is a shift; that claim does not survive here, and this theorem
replaces it.) -/
theorem canonicalIOSlots_is_a_shift : ∀ i, i < 2 → canonicalIOSlots.map i = i + 8 := by
  intro i hi
  interval_cases i <;> rfl

/-- The transpose of the canonical placement: the pole on `8`, the record-RLC coin on `9`. -/
def transposedIOSlots : IOSlots where
  slot := ![ioPoleSlot, ioGammaSlot]
  injective := by decide
  commit_then_sample := by decide

/-- **But not every placement is a constant offset**, so the substituted AIRs are built with
`remapBlock`: the transposed placement is legal by the schedule (`exists_placement_iff`) and no
offset realizes it. -/
theorem transposedIOSlots_not_a_shift :
    ¬ ∃ offC : ℕ, ∀ i, i < 2 → transposedIOSlots.map i = i + offC := by
  rintro ⟨offC, h⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  simp only [IOSlots.map_zero, IOSlots.map_one, transposedIOSlots, ioGammaSlot, ioPoleSlot,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  omega

/-! ## 2. The chips' column challenges, with the placement threaded through -/

/-- The coins a substituted-compute column of round `r` may read **apart from the `RAP_prog-IO`
pair**: none at round `0`, `z, a, b, c` at round `1`, the compute chip's own six at round `2`.
The literals name the same coins as before the widening
(`roundOne_coins_are_the_embedded_seeds`, `computeRoundTwo_coins_are_embedded`). -/
def finComputeRoundChalOf (r : Fin 3) : Finset (Fin 10) :=
  if (r : ℕ) = 0 then ∅
  else if (r : ℕ) = 1 then {1, 2, 3, 4}
  else ({0, 1, 2, 3, 4, 5} : Finset (Fin 10))

/-- The memory analogue: `z` at round `1`, `α, z, β, γ` at round `2`. -/
def finMemRoundChalOf (r : Fin 3) : Finset (Fin 10) :=
  if (r : ℕ) = 0 then ∅
  else if (r : ℕ) = 1 then {1}
  else ({0, 1, 6, 7} : Finset (Fin 10))

/-- **The two compute columns that read the `RAP_prog-IO` coins**: the accumulator `acc_prog` and the committed reciprocal `1/(pole + RLC^γ(record))`.  No other column of the
chip does — that is `io_records_read_no_io_coin`, and it is why the declaration below is
per-column rather than per-round. -/
def finProgIoCoinCols : List ℕ := [100, 101]

/-- The memory twin. -/
def finMemIoCoinCols : List ℕ := [42, 43]

/-- **The declared per-column coin dependence.**  A round-`2` column reads the compute chip's own
six coins; the two IO-coin columns read the placement's two slots as well.

This is deliberately *finer* than a per-round declaration.  A per-round one would say that every
round-`2` column may read the IO pair — including the record timestamp `111`, which does not — and
the soundness argument of `GigaRAPIOFreshness.lean` needs the true dependence, not an upper
bound. -/
def finComputeColumnChallenges (S : IOSlots) (c : Fin 113) : Finset (Fin 10) :=
  if (c : ℕ) ∈ finProgIoCoinCols then
    insert (S.slot 0) (insert (S.slot 1) (finComputeRoundChalOf (finComputeRoundOf c)))
  else finComputeRoundChalOf (finComputeRoundOf c)

def finMemColumnChallenges (S : IOSlots) (c : Fin 55) : Finset (Fin 10) :=
  if (c : ℕ) ∈ finMemIoCoinCols then
    insert (S.slot 0) (insert (S.slot 1) (finMemRoundChalOf (finMemRoundOf c)))
  else finMemRoundChalOf (finMemRoundOf c)

/-- **Commit before sample** for the non-IO coins, at the level of rounds.  Round `2` closes by
`nockSampledAfterWithIO_lt_two`, which is why widening `Fin 8 → Fin 10` costs one `decide` and not
a per-column re-measurement. -/
theorem finComputeRoundChalOf_usable :
    ∀ r : Fin 3, ∀ j ∈ finComputeRoundChalOf r, (nockSampledAfterWithIO j : ℕ) < (r : ℕ) := by
  intro r j hj
  fin_cases r
  · simp [finComputeRoundChalOf] at hj
  · exact withIO_computeRoundOne_coins j (by simpa [finComputeRoundChalOf] using hj)
  · exact nockSampledAfterWithIO_lt_two j

theorem finMemRoundChalOf_usable :
    ∀ r : Fin 3, ∀ j ∈ finMemRoundChalOf r, (nockSampledAfterWithIO j : ℕ) < (r : ℕ) := by
  intro r j hj
  fin_cases r
  · simp [finMemRoundChalOf] at hj
  · exact withIO_memoryRoundOne_coins j (by simpa [finMemRoundChalOf] using hj)
  · exact nockSampledAfterWithIO_lt_two j

/-- The two IO-coin columns are round-`2` columns of their chips. -/
theorem finProgIoCoinCols_round_two (c : Fin 113) (hc : (c : ℕ) ∈ finProgIoCoinCols) :
    finComputeRoundOf c = 2 := by
  have h : (c : ℕ) = 100 ∨ (c : ℕ) = 101 := by simpa [finProgIoCoinCols] using hc
  rcases h with h | h <;> simp [finComputeRoundOf, finMegaExtCols, h]

theorem finMemIoCoinCols_round_two (c : Fin 55) (hc : (c : ℕ) ∈ finMemIoCoinCols) :
    finMemRoundOf c = 2 := by
  have h : (c : ℕ) = 42 ∨ (c : ℕ) = 43 := by simpa [finMemIoCoinCols] using hc
  rcases h with h | h <;> simp [finMemRoundOf, finMemBaseCols, finMemMegaExtCols, h]

/-- **Commit before sample**, per column.  For the two accumulator/reciprocal columns the IO pair
is declared and closes by `IOSlots.early` — the coins ride the second message and those columns
are committed in the third block, which is the paper before the paper. -/
theorem finComputeColumns_commit_before_sampling (S : IOSlots) :
    ∀ c : Fin 113, ∀ j ∈ finComputeColumnChallenges S c,
      (nockSampledAfterWithIO j : ℕ) < (finComputeRoundOf c : ℕ) := by
  intro c j hj
  by_cases hc : (c : ℕ) ∈ finProgIoCoinCols
  · rw [finProgIoCoinCols_round_two c hc]
    simp only [finComputeColumnChallenges, if_pos hc, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · simpa using S.early 0
    · simpa using S.early 1
    · simpa using nockSampledAfterWithIO_lt_two j
  · simp only [finComputeColumnChallenges, if_neg hc] at hj
    exact finComputeRoundChalOf_usable _ j hj

theorem finMemColumns_commit_before_sampling (S : IOSlots) :
    ∀ c : Fin 55, ∀ j ∈ finMemColumnChallenges S c,
      (nockSampledAfterWithIO j : ℕ) < (finMemRoundOf c : ℕ) := by
  intro c j hj
  by_cases hc : (c : ℕ) ∈ finMemIoCoinCols
  · rw [finMemIoCoinCols_round_two c hc]
    simp only [finMemColumnChallenges, if_pos hc, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · simpa using S.early 0
    · simpa using S.early 1
    · simpa using nockSampledAfterWithIO_lt_two j
  · simp only [finMemColumnChallenges, if_neg hc] at hj
    exact finMemRoundChalOf_usable _ j hj

/-! ### 2.1 The dependence statement the LogUp argument needs -/

/-- Every non-IO coin a column may read is one of the eight `nockChronology` declares. -/
theorem finComputeRoundChalOf_embedded (r : Fin 3) :
    finComputeRoundChalOf r ⊆ Finset.univ.image embed8 := by revert r; decide

theorem finMemRoundChalOf_embedded (r : Fin 3) :
    finMemRoundChalOf r ⊆ Finset.univ.image embed8 := by revert r; decide

/-- **No record or multiplicity column reads either `RAP_prog-IO` coin.**

Compute columns `102 … 111` and memory columns `43 … 52` — the two multiplicity columns and all
eight record coordinates of each block, the timestamp `111`/`52` included — declare only coins
that `GigaChips.nockChronology` already had.  So at a placement that reads *fresh* slots (the
canonical one and its transpose, by `canonical_is_the_only_fresh_placement`) neither IO coin is
among them.

**What this theorem is, exactly.**  It is a statement about `finComputeColumnChallenges` /
`finMemColumnChallenges`, i.e. about the *declaration* this module chose — not about the
constraint system.  For compute `102 … 110` and memory `43 … 51` the declaration is forced:
those are round-`1` columns and the IO coins ride message `1`, so `commit_then_sample` excludes
them (`io_records_commit_before_the_io_coins`).  For the timestamp `111`/`52` it is **not**
forced: those are round-`2` columns, committed after the same verifier message as the coins
(`record_timestamp_column_shares_the_message_with_the_io_coins`), and a chip declaring the pair
there satisfies `columns_commit_before_sampling` just as well.  So at those two columns this is a
modelling restriction on the prover class.

This docstring used to add that `ts` "is in any case forced from the
committed `ln_prev` chain by `ln = ln_prev·z^{1,2,3}`, so the prover does
not choose it at all".  That recurrence is a `V_comp` clause over `W_comp` and
has no image in `FiniteIO.finiteIOProgAIR` (`FiniteFieldIOAIR.lean:153`); the two blocks of
`computeCombinedFiniteAIR` are constraint-disjoint.  The sentence is withdrawn.  The enforced version of
this theorem is `GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute`
(`GigaRAPThirdMessage.lean`). -/
theorem io_records_read_no_io_coin (S : IOSlots)
    (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j) :
    (∀ c : Fin 113, 102 ≤ (c : ℕ) → (c : ℕ) ≤ 111 →
        ∀ i, S.slot i ∉ finComputeColumnChallenges S c)
      ∧ (∀ c : Fin 55, 44 ≤ (c : ℕ) → (c : ℕ) ≤ 53 →
        ∀ i, S.slot i ∉ finMemColumnChallenges S c) := by
  constructor
  · intro c h1 _ i hmem
    have hc : (c : ℕ) ∉ finProgIoCoinCols := by
      simp only [finProgIoCoinCols, List.mem_cons, List.not_mem_nil, or_false]
      omega
    rw [finComputeColumnChallenges, if_neg hc] at hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (finComputeRoundChalOf_embedded _ hmem)
    exact hfresh i j hj.symm
  · intro c h1 _ i hmem
    have hc : (c : ℕ) ∉ finMemIoCoinCols := by
      simp only [finMemIoCoinCols, List.mem_cons, List.not_mem_nil, or_false]
      omega
    rw [finMemColumnChallenges, if_neg hc] at hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (finMemRoundChalOf_embedded _ hmem)
    exact hfresh i j hj.symm

/-- At the canonical placement, where freshness is automatic. -/
theorem canonical_io_records_read_no_io_coin :
    (∀ c : Fin 113, 102 ≤ (c : ℕ) → (c : ℕ) ≤ 111 →
        ∀ i, canonicalIOSlots.slot i ∉ finComputeColumnChallenges canonicalIOSlots c)
      ∧ (∀ c : Fin 55, 44 ≤ (c : ℕ) → (c : ℕ) ≤ 53 →
        ∀ i, canonicalIOSlots.slot i ∉ finMemColumnChallenges canonicalIOSlots c) :=
  io_records_read_no_io_coin canonicalIOSlots (by
    intro i j h
    fin_cases i
    · exact (canonicalIOSlots_are_new j).1 h.symm
    · exact (canonicalIOSlots_are_new j).2 h.symm)

/-- The two accumulator/reciprocal columns **do** read both coins — the dependence is not vacuous,
and it is exactly where the paper puts it. -/
theorem accumulator_columns_read_both_io_coins (S : IOSlots) :
    (∀ i, S.slot i ∈ finComputeColumnChallenges S 100)
      ∧ (∀ i, S.slot i ∈ finComputeColumnChallenges S 101)
      ∧ (∀ i, S.slot i ∈ finMemColumnChallenges S 42)
      ∧ (∀ i, S.slot i ∈ finMemColumnChallenges S 43) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro i
      fin_cases i <;>
        simp [finComputeColumnChallenges, finMemColumnChallenges, finProgIoCoinCols,
          finMemIoCoinCols]

/-- **Seven of the eight record coordinates are committed before the IO coins are sent.**  Columns
`104 … 110` are ext (round-`1`) columns, so `commit_then_sample`'s first half says the IO coins are
not usable by them; the accumulator at `100` is round-`2`, so its second half says they are.  That
is the paper before the paper, at the columns it is about.

The eighth, `111`, is a round-`2` column and this theorem does not cover it; the statement that
covers all eight is `io_records_read_no_io_coin`, which is about *dependence* rather than about
message order.  See `record_timestamp_column_shares_the_message_with_the_io_coins`. -/
theorem io_records_commit_before_the_io_coins (S : IOSlots) :
    (∀ c : Fin 113, (c : ℕ) ∈ ({104, 105, 106, 107, 108, 109, 110} : Finset ℕ) →
        ∀ i, ¬ nockChronologyWithIO.usableByColumnOf (finComputeRoundOf c) (S.slot i))
      ∧ (∀ i, nockChronologyWithIO.usableByColumnOf (finComputeRoundOf 100) (S.slot i)) := by
  refine ⟨fun c hc i => ?_, fun i => ?_⟩
  · have hr : finComputeRoundOf c = 1 := by
      have : (c : ℕ) = 104 ∨ (c : ℕ) = 105 ∨ (c : ℕ) = 106 ∨ (c : ℕ) = 107 ∨ (c : ℕ) = 108 ∨
          (c : ℕ) = 109 ∨ (c : ℕ) = 110 := by
        simpa [Finset.mem_insert] using hc
      rcases this with h | h | h | h | h | h | h <;>
        simp [finComputeRoundOf, finMegaExtCols, h]
    rw [hr]; exact (S.commit_then_sample i).1
  · have hr : finComputeRoundOf 100 = 2 := by decide
    rw [hr]; exact (S.commit_then_sample i).2

/-- **The timestamp column shares a verifier message with the IO coins — and reads neither.**

`NockVM.encRec`'s coordinate `7` is the record timestamp `ts` (`rlc_encRec`,
`PairedRecordCountedEvent.lean:216`), whose honest value `ln(i-1)·α^k` reads the timestamp base `α` — a coin of this tree's **second** verifier message
(`GigaChips.nockSampledAfter alphaSlot = 1`).  So combined column `111` (memory `52`) is a
mega-ext, round-`2` column, committed in the same block as the accumulators and after the same
verifier message as the two `RAP_prog-IO` coins.  The first two conjuncts say exactly that, at
every placement.  The co-location is not a *soundness*
defect — the construction is presumed sound — but it is exactly what leaves the exclusion at
`111`/`52` a modelling hypothesis rather than a consequence, and a third verifier message is
precisely what removes it.  `GigaRAPThirdMessage.lean` builds that chronology and proves the
exclusion for every chip on it, at no cost in constraints
(`GigaIOThirdMessage.canonical3_satisfies_iff`, by `Iff.rfl`).

*What the paper says.*  the paper calls `RAP_prog-IO` "a new RAP … with an additional final
round of interaction"; the paper has `IO_prog` built by engaging "as per `RAP_prog`",
the paper commits it, the paper sends `α, β`, the paper builds `acc_prog`, and
the paper prices the round separately.  Read as a message *sequence* that is stricter than
this tree's two messages, and the difference is real and is recorded by the first two conjuncts.

*What the deployed client does.*

*What the last two conjuncts do and do not settle.*  The commitment of the paper exists so
that the prover cannot choose `IO_prog` as a function of the coins of the paper; the LogUp
union bound then runs at each fixed record set.  What the argument consumes is therefore
**independence**, not ordering — and the last two conjuncts assert that independence at the level
of the *declaration*: at a fresh placement no record or multiplicity column declares either IO
coin.  At this chronology that assertion is backed by the schedule at every IO data column except
`111` and `52`, where it is a modelling restriction on the prover class.

This docstring used to continue "and it is not freely chosen in any
case — `ln = ln_prev·z^{1,2,3}` forces it from the
committed `ln_prev` chain".  That is a `V_comp` clause over `W_comp` with no
image in `FiniteIO.finiteIOProgAIR`; the sentence is withdrawn.  `GigaRAPIOFreshness.lean` spends
the declaration as it stands; `GigaRAPThirdMessage.lean` spends the *forced* version, at a
chronology in which the paper's "additional final round of interaction" has its own
message. -/
theorem record_timestamp_column_shares_the_message_with_the_io_coins (S : IOSlots)
    (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j) :
    (finComputeRoundOf 111 = 2 ∧ finMemRoundOf 53 = 2)
      ∧ (∀ i, nockSampledAfterWithIO (S.slot i) = 1)
      ∧ (∀ i, S.slot i ∉ finComputeColumnChallenges S 111)
      ∧ (∀ i, S.slot i ∉ finMemColumnChallenges S 53) := by
  refine ⟨⟨by decide, by decide⟩, S.final_round, ?_, ?_⟩
  · exact fun i => (io_records_read_no_io_coin S hfresh).1 111 (by decide) (by decide) i
  · exact fun i => (io_records_read_no_io_coin S hfresh).2 53 (by decide) (by decide) i

/-! ## 3. The two substituted chips, on the ten-coin chronology -/

variable {L : Type*} [Field L]

/-- **The compute chip with the prover-committed prog-IO block**, on
`Chronology.nockChronologyWithIO` — ten coins, the last two of them the `RAP_prog-IO` pair. -/
noncomputable def finiteComputeChip (S : IOSlots) (q : SegmentedRAPParams L) :
    StagedChip L 3 nockChronologyWithIO where
  air := computeCombinedFiniteAIR 10 9 S.map
  params := q
  schedule := finComputeSchedule
  columnChallenges := finComputeColumnChallenges S
  columns_commit_before_sampling := finComputeColumns_commit_before_sampling S

/-- **The memory chip with the prover-committed mem-IO block.** -/
noncomputable def finiteMemoryChip (S : IOSlots) (q : SegmentedRAPParams L) :
    StagedChip L 3 nockChronologyWithIO where
  air := memoryCombinedFiniteAIR (K := L) 10 9 S.map
  params := q
  schedule := finMemorySchedule
  columnChallenges := finMemColumnChallenges S
  columns_commit_before_sampling := finMemColumns_commit_before_sampling S

@[simp] theorem finiteComputeChip_air (S : IOSlots) (q : SegmentedRAPParams L) :
    (finiteComputeChip S q).air = computeCombinedFiniteAIR 10 9 S.map := rfl

@[simp] theorem finiteMemoryChip_air (S : IOSlots) (q : SegmentedRAPParams L) :
    (finiteMemoryChip S q).air = memoryCombinedFiniteAIR (K := L) 10 9 S.map := rfl

/-- The AIRs now declare the proof's real coin count. -/
theorem finiteChips_numChallenges (S : IOSlots) (q : SegmentedRAPParams L) :
    (finiteComputeChip S q).air.numChallenges = 10
      ∧ (finiteMemoryChip S q).air.numChallenges = 10
      ∧ nockChronologyWithIO.numChallenges = 10 :=
  ⟨rfl, rfl, rfl⟩

/-- **The compute chip's census, re-measured at the ten-coin shape.**  Identical to the eight-coin
reading it replaces: `113` columns, `3` publics, `538` constraints as `526` row / `6` transition /
`4` boundary / `2` terminal, degree `4`.  Nothing here is a fresh kernel reduction — `GigaFinite`'s
census theorems are generic in the declared coin count, which is exactly the observation that made
the widening cheap. -/
theorem finiteComputeChip_census (S : IOSlots) (q : SegmentedRAPParams L) :
    (finiteComputeChip S q).air.numTraceCols = 113
      ∧ (finiteComputeChip S q).air.numChallenges = 10
      ∧ (finiteComputeChip S q).air.numPublic = 3
      ∧ (finiteComputeChip S q).air.constraints.length = 538
      ∧ (kindSeg (finiteComputeChip S q).air .row).constraints.length = 526
      ∧ (kindSeg (finiteComputeChip S q).air .transition).constraints.length = 6
      ∧ (kindSeg (finiteComputeChip S q).air .boundary).constraints.length = 4
      ∧ (kindSeg (finiteComputeChip S q).air .terminal).constraints.length = 2
      ∧ (finiteComputeChip S q).air.maxDegree = 4 := by
  obtain ⟨hr, ht, hb, hx⟩ := computeCombinedFiniteAIR_kindSeg_census 10 9 S.map
  exact ⟨rfl, rfl, rfl, computeCombinedFiniteAIR_num_constraints 10 9 S.map, hr, ht, hb, hx,
    computeCombinedFiniteAIR_maxDegree 10 9 S.map⟩

/-- **The memory chip's census, re-measured at the ten-coin shape.**  `55` columns, `3` publics,
`93` constraints as `75 / 8 / 7 / 3`, degree `4` — again unchanged. -/
theorem finiteMemoryChip_census (S : IOSlots) (q : SegmentedRAPParams L) :
    (finiteMemoryChip S q).air.numTraceCols = 55
      ∧ (finiteMemoryChip S q).air.numChallenges = 10
      ∧ (finiteMemoryChip S q).air.numPublic = 3
      ∧ (finiteMemoryChip S q).air.constraints.length = 93
      ∧ (kindSeg (finiteMemoryChip S q).air .row).constraints.length = 75
      ∧ (kindSeg (finiteMemoryChip S q).air .transition).constraints.length = 8
      ∧ (kindSeg (finiteMemoryChip S q).air .boundary).constraints.length = 7
      ∧ (kindSeg (finiteMemoryChip S q).air .terminal).constraints.length = 3
      ∧ (finiteMemoryChip S q).air.maxDegree = 4 := by
  obtain ⟨hr, ht, hb, hx⟩ := memoryCombinedFiniteAIR_kindSeg_census (K := L) 10 9 S.map
  exact ⟨rfl, rfl, rfl, memoryCombinedFiniteAIR_num_constraints (K := L) 10 9 S.map, hr, ht, hb, hx,
    memoryCombinedFiniteAIR_maxDegree (K := L) 10 9 S.map⟩

/-- The substituted compute chip's four derived RAPs: width `113`, `k = 3`, widths
`![11, 89, 13]`. -/
theorem finiteComputeChip_rap (S : IOSlots) (q : SegmentedRAPParams L)
    (kind : Reified.ConstraintKind) :
    ((finiteComputeChip S q).rap kind).w = 113 ∧ ((finiteComputeChip S q).rap kind).k = 3 ∧
      ((finiteComputeChip S q).rap kind).wRAP = ![11, 89, 13] := ⟨rfl, rfl, rfl⟩

/-- The substituted memory chip's four derived RAPs: width `53`, `k = 3`, widths
`![9, 26, 18]`. -/
theorem finiteMemoryChip_rap (S : IOSlots) (q : SegmentedRAPParams L)
    (kind : Reified.ConstraintKind) :
    ((finiteMemoryChip S q).rap kind).w = 55 ∧ ((finiteMemoryChip S q).rap kind).k = 3 ∧
      ((finiteMemoryChip S q).rap kind).wRAP = ![10, 27, 18] := ⟨rfl, rfl, rfl⟩

/-- **The substituted giga-RAP of one Nock proof**: two chips, one interaction schedule with the
two IO coins in it, both IO blocks prover-committed over the plain field. -/
noncomputable def nockGigaRAPFinite (S : IOSlots) (qC qM : SegmentedRAPParams L) : GigaRAP L where
  rounds := 3
  rounds_pos := by norm_num
  chronology := nockChronologyWithIO
  chips := [finiteComputeChip S qC, finiteMemoryChip S qM]

/-- Satisfaction of the substituted giga-RAP is satisfaction of both substituted chips. -/
theorem nockGigaRAPFinite_satisfies_iff (S : IOSlots) (qC qM : SegmentedRAPParams L)
    (Pt : (T : StagedChip L 3 nockChronologyWithIO) → Fin T.air.numTraceCols → L[X]) :
    (nockGigaRAPFinite S qC qM).Satisfies Pt
      ↔ (finiteComputeChip S qC).Satisfies (Pt (finiteComputeChip S qC))
        ∧ (finiteMemoryChip S qM).Satisfies (Pt (finiteMemoryChip S qM)) := by
  show ChipList.Satisfies [finiteComputeChip S qC, finiteMemoryChip S qM] Pt ↔ _
  rw [ChipList.satisfies_cons, ChipList.satisfies_cons]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ChipList.satisfies_nil Pt⟩⟩

theorem finiteComputeChip_satisfies_iff_kinded (S : IOSlots) (q : SegmentedRAPParams L)
    (Pt : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → L[X]) :
    (finiteComputeChip S q).Satisfies Pt
      ↔ ∀ c ∈ (computeCombinedFiniteAIR 10 9 S.map).constraints, ∀ x ∈ q.domain c.kind,
          c.expr.eval (envOfTrace Pt q.ω x q.chalVal q.pubVal) = 0 :=
  (finiteComputeChip S q).satisfies_iff_kinded Pt

theorem finiteMemoryChip_satisfies_iff_kinded (S : IOSlots) (q : SegmentedRAPParams L)
    (Pt : Fin (memoryCombinedFiniteAIR (K := L) 10 9 S.map).numTraceCols → L[X]) :
    (finiteMemoryChip S q).Satisfies Pt
      ↔ ∀ c ∈ (memoryCombinedFiniteAIR (K := L) 10 9 S.map).constraints, ∀ x ∈ q.domain c.kind,
          c.expr.eval (envOfTrace Pt q.ω x q.chalVal q.pubVal) = 0 :=
  (finiteMemoryChip S q).satisfies_iff_kinded Pt

/-- **Folding the substituted compute side loses nothing.**  Satisfying the single 112-column,
538-constraint chip yields the three separate per-kind `RAP.Satisfies` obligations — and the third
is now an obligation on `finiteIOProgAIR 9`, at the parameters `remapParams q S.map ioPubOff`
whose challenge slot `i` is the chip's slot `S.map i`. -/
theorem finiteComputeChip_fold_loses_nothing (S : IOSlots) (q : SegmentedRAPParams L)
    (Pt : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → L[X])
    (h : (finiteComputeChip S q).Satisfies Pt) :
    (∀ kind, (q.rap computeAIRchained kind).Satisfies (finComputeBlock Pt))
      ∧ (∀ kind, ((ComputeChip.shiftParams q ComputeChip.walkChalOff
          ComputeChip.walkPubOff).rap walkAIR kind).Satisfies (finWalkBlock Pt))
      ∧ (∀ kind, ((remapParams q S.map ComputeChip.ioPubOff).rap (finiteIOProgAIR 9)
          kind).Satisfies (finProgIoBlock Pt)) :=
  ⟨fold_gives_finCompute q q rfl (fun _ _ => rfl) (fun _ => rfl) Pt
     ((finiteComputeChip_satisfies_iff_kinded S q Pt).mp h),
   fold_gives_finWalk q (ComputeChip.shiftParams q ComputeChip.walkChalOff ComputeChip.walkPubOff)
     rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) Pt
     ((finiteComputeChip_satisfies_iff_kinded S q Pt).mp h),
   fold_gives_finProgIo q (remapParams q S.map ComputeChip.ioPubOff) rfl (fun _ _ => rfl)
     (fun _ _ => rfl) (fun _ => rfl) Pt ((finiteComputeChip_satisfies_iff_kinded S q Pt).mp h)⟩

/-- **Folding the substituted memory side loses nothing.** -/
theorem finiteMemoryChip_fold_loses_nothing (S : IOSlots) (q : SegmentedRAPParams L)
    (Pt : Fin (memoryCombinedFiniteAIR (K := L) 10 9 S.map).numTraceCols → L[X])
    (h : (finiteMemoryChip S q).Satisfies Pt) :
    (∀ kind, ((remapParams q memChalMap memPubOff).rap (memoryAIRchained (K := L)) kind).Satisfies
        (finMemBlock Pt))
      ∧ (∀ kind, ((remapParams q memWalkChalMap memWalkPubOff).rap walkAIR kind).Satisfies
          (finMemWalkBlock Pt))
      ∧ (∀ kind, ((remapParams q S.map memIoPubOff).rap (finiteIOMemAIR 9) kind).Satisfies
          (finMemIoBlock Pt)) :=
  ⟨fold_gives_finMem q (remapParams q memChalMap memPubOff) rfl (fun _ _ => rfl) (fun _ => rfl) Pt
     ((finiteMemoryChip_satisfies_iff_kinded S q Pt).mp h),
   fold_gives_finMemWalk q (remapParams q memWalkChalMap memWalkPubOff) rfl (fun _ _ => rfl)
     (fun _ _ => rfl) (fun _ => rfl) Pt ((finiteMemoryChip_satisfies_iff_kinded S q Pt).mp h),
   fold_gives_finMemIo q (remapParams q S.map memIoPubOff) rfl (fun _ _ => rfl) (fun _ _ => rfl)
     (fun _ => rfl) Pt ((finiteMemoryChip_satisfies_iff_kinded S q Pt).mp h)⟩

/-! ## 4. The payoff: the assembled object feeds `IOChipSoundness`

`IOChipSoundness.io_lio_of_satisfies` (`IOChipSoundness.lean:408`) consumes exactly
`∀ k, (qp.rap (finiteIOProgAIR m) k).Satisfies Pp` and its memory twin.  §3's fold theorems
produce precisely those two facts from satisfaction of the two **assembled** chips.

The two `ChipAgreement`s stay hypotheses, as they must: they say that *these* trace columns hold
*these* records and that *these* challenge slots carry `γ` and the pole.  With the placement `S`
threaded through `remapParams q S.map`, `ChipAgreement.gamma_eq` unfolds to
`q.chalVal (S.slot 0) = coins.gamma` and `pole_eq` to `q.chalVal (S.slot 1) = coins.pole`; at the
canonical placement those are slots `8` and `9`, which `canonicalIOSlots_are_new` proves are not
any of the eight coins the two tables read for anything else. -/

section Payoff

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

/-- **The record-level IO language from satisfaction of the assembled giga-RAP.**

`hC`/`hM` are satisfaction of the two substituted chips — the 112-column, 538-constraint compute
chip and the 53-column, 93-constraint memory chip, both staged over the ten-coin chronology.
Everything else is either a `ChipRows` row-domain condition, a `ChipAgreement` column/coin
identification, or one of `finiteIO_sound`'s own five non-event hypotheses and two counted-event
exclusions (`IOChipSoundness.lean:405`).  No execution, carrier or completeness theorem occurs. -/
theorem io_lio_of_giga_satisfies {Ksz : ℕ} (S : IOSlots)
    (records : PreChallengeRecords K 9) (coins : IOCoins K) (terminal : K)
    (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 S.map).numTraceCols → K[X])
    (hC : (finiteComputeChip S qC).Satisfies PC)
    (hM : (finiteMemoryChip S qM).Satisfies PM)
    (hrowsP : IOChip.ChipRows records.requests.length
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p)
    (hrowsM : IOChip.ChipRows records.responses.length
      (remapParams qM S.map memIoPubOff) x₀m)
    (hagP : IOChip.ChipAgreement records.requests coins terminal
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC))
    (hagM : IOChip.ChipAgreement records.responses coins terminal
      (remapParams qM S.map memIoPubOff) x₀m (finMemIoBlock PM))
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    IO.LIO Ksz records.requests records.responses :=
  IOChip.io_lio_of_satisfies (Ksz := Ksz) records coins terminal
    (remapParams qC S.map ComputeChip.ioPubOff) (remapParams qM S.map memIoPubOff) x₀p x₀m
    (finProgIoBlock PC) (finMemIoBlock PM)
    (finiteComputeChip_fold_loses_nothing S qC PC hC).2.2
    (finiteMemoryChip_fold_loses_nothing S qM PM hM).2.2
    hrowsP hrowsM hagP hagM hKp hKreq hKresp hreqnd hrespnd hγ hpole

/-- **The `Perm` conjunct alone** — the request records are a permutation of the response records
— read off satisfaction of the assembled giga-RAP. -/
theorem perm_of_giga_satisfies {Ksz : ℕ} (S : IOSlots)
    (records : PreChallengeRecords K 9) (coins : IOCoins K) (terminal : K)
    (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 S.map).numTraceCols → K[X])
    (hC : (finiteComputeChip S qC).Satisfies PC)
    (hM : (finiteMemoryChip S qM).Satisfies PM)
    (hrowsP : IOChip.ChipRows records.requests.length
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p)
    (hrowsM : IOChip.ChipRows records.responses.length
      (remapParams qM S.map memIoPubOff) x₀m)
    (hagP : IOChip.ChipAgreement records.requests coins terminal
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC))
    (hagM : IOChip.ChipAgreement records.responses coins terminal
      (remapParams qM S.map memIoPubOff) x₀m (finMemIoBlock PM))
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    records.requests.Perm records.responses :=
  (io_lio_of_giga_satisfies (Ksz := Ksz) S records coins terminal qC qM x₀p x₀m PC PM hC hM
    hrowsP hrowsM hagP hagM hKp hKreq hKresp hreqnd hrespnd hγ hpole).2.2

omit [Fintype K] [DecidableEq K] in
/-- **What the two `ChipAgreement`s say about the coins, unfolded.**  Under the placement `S` the
recovered challenge slots are the chip's slots `S.slot 0` and `S.slot 1`, so the agreement
hypotheses are literally "the proof's slot `S.slot 0` carries `γ`, and slot `S.slot 1` carries the
pole".  At `canonicalIOSlots` those are the two slots `nockChronologyWithIO` adds. -/
theorem chipAgreement_names_the_slots (S : IOSlots)
    (recs : List (Fin 9 → K)) (coins : IOCoins K) (terminal : K)
    (q : SegmentedRAPParams K) (x₀ : K) {w : ℕ} (Pt : Fin w → K[X])
    (hag : IOChip.ChipAgreement recs coins terminal
      (remapParams q S.map ComputeChip.ioPubOff) x₀ Pt) :
    q.chalVal (S.slot 0) = coins.gamma ∧ q.chalVal (S.slot 1) = coins.pole :=
  ⟨hag.gamma_eq, hag.pole_eq⟩

omit [Fintype K] [DecidableEq K] in
/-- The same, at the canonical placement: the two coins are read off slots `8` and `9`. -/
theorem chipAgreement_names_the_new_slots
    (recs : List (Fin 9 → K)) (coins : IOCoins K) (terminal : K)
    (q : SegmentedRAPParams K) (x₀ : K) {w : ℕ} (Pt : Fin w → K[X])
    (hag : IOChip.ChipAgreement recs coins terminal
      (remapParams q canonicalIOSlots.map ComputeChip.ioPubOff) x₀ Pt) :
    q.chalVal (ioGammaSlot : Fin 10) = coins.gamma
      ∧ q.chalVal (ioPoleSlot : Fin 10) = coins.pole :=
  ⟨hag.gamma_eq, hag.pole_eq⟩

end Payoff

/-! ## 5. The composition: acceptance plus assembled satisfaction gives `IO.LIO`

`IOCoinReconciliation.io_lio_of_satisfies_at_production_coins` (`:263`) discharges the two
counted-event hypotheses from *acceptance of the production tuple outside the production failure
event*, but wanted the two ordinary IO-chip RAP obligations as inputs; §3's
`finiteComputeChip_fold_loses_nothing` / `finiteMemoryChip_fold_loses_nothing` produce exactly
those from satisfaction of the two **assembled** chips.  The coins are not a parameter: they are
`ioCoinsOf c`, the IO coordinate of the accepted tuple, which
`IOCoinReconciliation.ioCoinsOf_eq_sampled` (`:177`) identifies with the package's sampled coins.

**Residual hypotheses, and why each is correct.**  What remains are exactly the `ChipRows` and
`ChipAgreement` data on both sides.  `ChipRows` says the boundary, record and terminal rows lie in
the evaluation domains their kinds are deployed on; `ChipAgreement` says the committed IO columns
of *these* traces hold *these* records, that public slot `0` is the shared terminal, and that the
challenge slots the placement names carry `γ` and the pole.  Those are the statements that tie a
hostile trace to the records the soundness argument is about, so they cannot be discharged from
acceptance — nothing else is assumed.  In particular the five range/uniqueness/characteristic side
conditions and both counted-event exclusions are **derived**, from the package's own sampled
strategy and from `hgood`. -/

section Composition

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **Headline.**  At an accepted production challenge tuple lying outside the production failure
event, satisfaction of the two *assembled* giga-RAP chips — 112 columns / 538 constraints and
53 columns / 93 constraints, staged over the ten-coin chronology with the two `RAP_prog-IO` coins
at the canonical slots `8`, `9` — implies the record-level IO language `IO.LIO` on the package's
own sampled records.

The two counted-event hypotheses of `IOChipSoundness.io_lio_of_satisfies` are **not** assumed:
they are read off `hgood` through `IOCoinReconciliation.sampled_coins_good`.  The coins are not a
parameter either: they are `ioCoinsOf c`. -/
theorem io_lio_of_giga_satisfies_at_production_coins
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (terminal : K) (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 canonicalIOSlots.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 canonicalIOSlots.map).numTraceCols → K[X])
    (hC : (finiteComputeChip canonicalIOSlots qC).Satisfies PC)
    (hM : (finiteMemoryChip canonicalIOSlots qM).Satisfies PM)
    (hrowsP : IOChip.ChipRows P.optimized.sampled.sampled.records.requests.length
      (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p)
    (hrowsM : IOChip.ChipRows P.optimized.sampled.sampled.records.responses.length
      (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m)
    (hagP : IOChip.ChipAgreement P.optimized.sampled.sampled.records.requests
      (ioCoinsOf c) terminal
      (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC))
    (hagM : IOChip.ChipAgreement P.optimized.sampled.sampled.records.responses
      (ioCoinsOf c) terminal
      (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m (finMemIoBlock PM)) :
    IO.LIO P.optimized.family.problem.cfg.Ksz
      P.optimized.sampled.sampled.records.requests
      P.optimized.sampled.sampled.records.responses :=
  io_lio_of_satisfies_at_production_coins P Qc Qm c hacc hgood terminal
    (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff)
    (remapParams qM canonicalIOSlots.map memIoPubOff) x₀p x₀m
    (finProgIoBlock PC) (finMemIoBlock PM)
    (finiteComputeChip_fold_loses_nothing canonicalIOSlots qC PC hC).2.2
    (finiteMemoryChip_fold_loses_nothing canonicalIOSlots qM PM hM).2.2
    hrowsP hrowsM hagP hagM

/-- **The `Perm` conjunct of the composition** — the memory requests the compute table issued are
a permutation of the responses the memory table served, from acceptance plus assembled
satisfaction. -/
theorem perm_of_giga_satisfies_at_production_coins
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (terminal : K) (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 canonicalIOSlots.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 canonicalIOSlots.map).numTraceCols → K[X])
    (hC : (finiteComputeChip canonicalIOSlots qC).Satisfies PC)
    (hM : (finiteMemoryChip canonicalIOSlots qM).Satisfies PM)
    (hrowsP : IOChip.ChipRows P.optimized.sampled.sampled.records.requests.length
      (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p)
    (hrowsM : IOChip.ChipRows P.optimized.sampled.sampled.records.responses.length
      (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m)
    (hagP : IOChip.ChipAgreement P.optimized.sampled.sampled.records.requests
      (ioCoinsOf c) terminal
      (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC))
    (hagM : IOChip.ChipAgreement P.optimized.sampled.sampled.records.responses
      (ioCoinsOf c) terminal
      (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m (finMemIoBlock PM)) :
    P.optimized.sampled.sampled.records.requests.Perm
      P.optimized.sampled.sampled.records.responses :=
  (io_lio_of_giga_satisfies_at_production_coins P Qc Qm c hacc hgood terminal qC qM x₀p x₀m
    PC PM hC hM hrowsP hrowsM hagP hagM).2.2

/-- **The coins the composition runs at are the sampled ones.**  Not a separate assumption: the
identification is `IOCoinReconciliation.ioCoinsOf_eq_sampled` at the same acceptance hypothesis,
recorded here so the headline's `ioCoinsOf c` is not read as an arbitrary pair. -/
theorem composition_coins_are_sampled
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    ioCoinsOf c = P.optimized.sampled.sampled.coins :=
  ioCoinsOf_eq_sampled P Qc Qm c hacc

end Composition

end Nock.NockVMROM.Thm54.GigaIOSlots

section Audit

open Nock.NockVMROM.Thm54.GigaIOSlots

#check @IOSlots
#check @canonicalIOSlots
#check @exists_placement_iff
#check @only_the_new_slots_are_fresh
#check @canonical_is_the_only_fresh_placement
#check @memoryAliasIOSlots
#check @io_records_read_no_io_coin
#check @record_timestamp_column_shares_the_message_with_the_io_coins
#check @memoryAlias_pole_is_the_table_beta
#check @finiteComputeChip_census
#check @finiteMemoryChip_census
#check @finiteComputeChip
#check @finiteMemoryChip
#check @nockGigaRAPFinite
#check @io_lio_of_giga_satisfies
#check @perm_of_giga_satisfies
#check @io_lio_of_giga_satisfies_at_production_coins
#check @perm_of_giga_satisfies_at_production_coins

#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.nockSampledAfterWithIO_lt_two
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.roundOne_coins_are_the_embedded_seeds
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.IOSlots.final_round
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.IOSlots.map_ne
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.exists_placement_iff
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.placement_candidates
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.only_the_new_slots_are_fresh
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.canonicalIOSlots_are_new
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.canonicalIOSlots_ne_memory_slots
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.canonicalIOSlots_final_round
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.canonical_is_the_only_fresh_placement
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.memoryAliasIOSlots_reads_the_memory_table_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.memoryAlias_pole_is_the_table_beta
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.canonicalIOSlots_is_a_shift
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.transposedIOSlots_not_a_shift
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finComputeColumns_commit_before_sampling
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finMemColumns_commit_before_sampling
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.io_records_commit_before_the_io_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.record_timestamp_column_shares_the_message_with_the_io_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.io_records_read_no_io_coin
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.canonical_io_records_read_no_io_coin
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.accumulator_columns_read_both_io_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finProgIoCoinCols_round_two
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finMemIoCoinCols_round_two
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finiteChips_numChallenges
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finiteComputeChip_census
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finiteMemoryChip_census
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finiteComputeChip_rap
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finiteMemoryChip_rap
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.nockGigaRAPFinite_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finiteComputeChip_fold_loses_nothing
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.finiteMemoryChip_fold_loses_nothing
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.io_lio_of_giga_satisfies
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.perm_of_giga_satisfies
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.chipAgreement_names_the_slots
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.chipAgreement_names_the_new_slots
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.io_lio_of_giga_satisfies_at_production_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.perm_of_giga_satisfies_at_production_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOSlots.composition_coins_are_sampled

end Audit
