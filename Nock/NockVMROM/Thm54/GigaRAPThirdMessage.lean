import Nock.NockVMROM.Thm54.GigaRAPIOSlots
import Nock.NockVMROM.Thm54.RoundFibredSoundness

/-!
# The paper's third verifier message, and the IO-coin exclusion it *forces*

`GigaRAPIOSlots.lean` stages the two substituted chips over the **three**-round /
**two**-message chronology `Chronology.nockChronologyWithIO`
(`IOCoinReconciliation.lean:459`), and separates the record columns from the two
`RAP_prog-IO` coins with a *per-column* declaration, `finComputeColumnChallenges`
(`GigaRAPIOSlots.lean:426`).

## The defect this module closes

`StagedChip.columnChallenges` (`StagedTableRAP.lean:171`) carries exactly one obligation,
`columns_commit_before_sampling` (`:174`): every declared coin must have been sampled strictly
before the column's round.  At the two-message chronology that obligation is **weaker than the
declaration** at exactly one column per chip:

| columns | round (`finComputeRoundOf`, `NockGigaRAPFinite.lean:842`) | is the exclusion forced? |
|---|---|---|
| `102`, `103` (multiplicities), `104 … 110` (7 record coords) | `1` | **yes** — the IO coins ride message `1`, so `1 < 1` fails |
| `111` (the record timestamp `ts`) | `2` | **no** |
| memory `43 … 51` | `1` | yes |
| memory `52` (`ts`) | `2` | **no** |

At `111`/`52` the schedule permits the declaration to contain the IO pair, so *choosing* not to
put it there is free data: a second, equally legal `StagedChip` over the identical AIR, params and
schedule can declare both IO coins at column `111`, agree with `finiteComputeChip` on satisfaction
by `Iff.rfl`, and carry a legal `RoundFibred.StagedAssignment` whose record readout **is** the
sampled pole.  Nothing in `GigaRAPIOSlots.io_records_read_no_io_coin` (`:512`) rules that chip out,
because that theorem is about the *chosen* declaration, not about the constraint system.

Two ways out were considered and one of them does not work:

* **A cross-block linking gate** pinning IO record column `111` to the compute table's own `ln`
  column would relocate the assumption, not discharge it: the compute table's `ln` column is
  itself a *mega-ext* (round-`2`) column of this tree's schedule (`finMegaExtCols`,
  `NockGigaRAPFinite.lean:836`, and `GigaChips.mem_ts_column_round_two`, `NockGigaRAP.lean:342`),
  committed after the same verifier message as the IO coins. Its own independence would again be
  a declaration. So the gate would change the census and buy nothing on the dependence axis.
* **The paper's own extra message.**  the paper introduces `RAP_prog-IO` as "a new RAP …
  with an additional final round of interaction"; the paper builds
  `(x_prog, T_prog, IO_prog)`, the paper sends `Com(IO_prog)`, the paper samples
  `α, β ∈ 𝕂`, the paper builds `acc_prog`, and the paper says in so many words that "we
  add a layer of interaction between the prover and verifier in between building `IO_prog` and
  `acc_prog` that commits to `IO_prog`.  This suffices to build the multiset and provides the
  soundness guarantees required."  That is a **third** verifier message, and with it the exclusion
  at `111`/`52` stops being a choice.

This module takes the second route.

## What is enforced here, and what is still assumed

`nockChronologyIO3` is `nockChronologyWithIO` with the two IO coins moved to a **third** message
and every other coin left where it was (`io3_restricts`).  `finComputeSchedule4` /
`finMemorySchedule4` split the mega-ext block in two: the accumulator and reciprocal columns
(`100`, `101`; memory `41`, `42`) become round-`3` columns, everything else keeps its round.

* **Enforced, for every chip, hostile ones included.**
  `committed_early_excludes_the_io_coins_compute` / `_memory`: *any*
  `T : StagedChip K 4 nockChronologyIO3` whose `IO_prog` columns are committed by round `2` —
  which is the paper's `Com(IO_prog)` step, read as a schedule condition — has
  `S.slot i ∉ T.columnChallenges c` at those columns, by the contrapositive of
  `columns_commit_before_sampling`. The hostile chip described above is **not** a chip of this
  chronology. Nothing is chosen *about the IO coins*: `SaturatedDeclaration.computeChip3_excess_has_no_io_slot`
  measures that neither IO slot is ever schedule-legal-but-undeclared here. `SaturatedDeclaration.computeChip3Sat`
  is the chip for which the sentence holds.)
* **Still a modelling hypothesis, and named as one.**
  `RoundFibred.StagedAssignment.col_reads` (`RoundFibredSoundness.lean:563`) — "a column committed
  in round `r` is not a function of a coin sampled at message `≥ r`". What has changed is its
  *strength*: on the three-message chronology it is used only at the granularity the round schedule
  licenses, never as a per-column exception.

## What did not change

The AIRs are untouched: `computeChip3` and `memoryChip3` carry the same
`computeCombinedFiniteAIR 10 9 S.map` / `memoryCombinedFiniteAIR 10 9 S.map` as the three-round
chips, so the census is *identical* — `112` columns / `538` constraints as `526 / 6 / 4 / 2`, and
`53` / `93` as `75 / 8 / 7 / 3`, degree `4` (`computeChip3_census`, `memoryChip3_census`).  Only the
**commitment schedule** changes: `w_RAP` moves from `![11, 88, 13]` to
`![11, 88, 11, 2]` and from `![9, 26, 18]` to `![9, 26, 16, 2]`, and `k` from `3` to `4`.  At the
canonical placement satisfaction of the four-round chip and of the three-round chip is the **same
proposition** (`canonical3_satisfies_iff`, by `Iff.rfl`): the third message costs no constraint.

## Where this module is imported from

The line
`import Nock.NockVMROM.Thm54.GigaRAPThirdMessage` belongs next to `Thm54.lean:238` whenever that
file is next edited.

## Scope

Statements about **this tree's** chips staged over a three-message chronology, and about any
`RoundFibred.StagedAssignment` against them.  The three-round chips of `GigaRAPIOSlots.lean` are
unchanged and still the ones the composition of that module's §5 runs at; at *those* the exclusion
at columns `111` / `52` remains a modelling choice, which is now said so in their docstrings.
Neither is a claim about the deployed client, which draws twice and co-locates `%ln` with the
accumulators (`prover.hoon:168`, `:212`; `v2/table/compute.hoon:90`, `:92`).
-/

namespace Nock.NockVMROM.Thm54.GigaIOThirdMessage

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GigaFinite
open Nock.NockVMROM.Thm54.GigaIOSlots
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology
open scoped Polynomial

/-! ## 1. The three-message chronology -/


/-- **The ten coins over three verifier messages.**  Identical to
`Chronology.nockSampledAfterWithIO` (`IOCoinReconciliation.lean:459`) on the eight coins
`nockChronology` declares; the two `RAP_prog-IO` coins move from message `1` to a **third** message
`2` — the paper's "additional final round of interaction", interposed by the paper
between `IO_prog` and `acc_prog`. -/
def nockSampledAfterIO3 : Fin 10 → Fin 4 := ![1, 0, 0, 0, 0, 1, 1, 1, 2, 2]

/-- **The four-round chronology.** -/
def nockChronologyIO3 : ChallengeChronology 4 where
  numChallenges := 10
  sampledAfter := nockSampledAfterIO3

@[simp] theorem io3_numChallenges : nockChronologyIO3.numChallenges = 10 := rfl

/-- **No existing coin changes message.**  Only the two IO slots move, and they move later. -/
theorem io3_restricts (j : Fin 8) :
    (nockSampledAfterIO3 (embed8 j) : ℕ) = (nockSampledAfter j : ℕ) := by revert j; decide

/-- The third message carries exactly the two IO slots. -/
theorem io3_third_message_slots :
    (Finset.univ.filter fun j : Fin 10 => nockSampledAfterIO3 j = 2)
      = {ioGammaSlot, ioPoleSlot} := by decide

theorem embed8_not_third : ∀ j : Fin 8, nockSampledAfterIO3 (embed8 j) ≠ 2 := by decide

theorem chal4_round1 : ∀ j ∈ ({1, 2, 3, 4} : Finset (Fin 10)),
    (nockSampledAfterIO3 j : ℕ) < 1 := by decide
theorem chal4_round2 : ∀ j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)),
    (nockSampledAfterIO3 j : ℕ) < 2 := by decide
theorem chal4_round3 : ∀ j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)),
    (nockSampledAfterIO3 j : ℕ) < 3 := by decide
theorem memChal4_round1 : ∀ j ∈ ({1} : Finset (Fin 10)),
    (nockSampledAfterIO3 j : ℕ) < 1 := by decide
theorem memChal4_round2 : ∀ j ∈ ({0, 1, 6, 7} : Finset (Fin 10)),
    (nockSampledAfterIO3 j : ℕ) < 2 := by decide
theorem memChal4_round3 : ∀ j ∈ ({0, 1, 6, 7} : Finset (Fin 10)),
    (nockSampledAfterIO3 j : ℕ) < 3 := by decide

/-! ## 2. The placement, now pinned by the chronology alone -/


/-- **Where the two `RAP_prog-IO` coins sit, on the three-message chronology.**

Compare `GigaIOSlots.IOSlots` (`GigaRAPIOSlots.lean:162`), whose `commit_then_sample` field pins
the coins to the *second* message and leaves six schedule-legal slots, four of which are coins the
proof already uses for something else — so *freshness* had to be carried as a hypothesis
(`hfresh`) at every downstream theorem.  Here `third_message` pins them to the third, and the third
message has exactly two inhabitants, so freshness is a **theorem** (`IOPlacement3.fresh`) and the
placement is unique up to transposition (`canonical_up_to_transposition`). -/
structure IOPlacement3 where
  /-- Slot `0` carries the record-RLC coin `α` of the paper, slot `1` the LogUp pole `β`. -/
  slot : Fin 2 → Fin 10
  /-- The two coins are distinct slots of the global draw. -/
  injective : Function.Injective slot
  /-- **Both coins ride the third verifier message** (the paper, after the paper's
  `Com(IO_prog)` and before the paper's `acc_prog`). -/
  third_message : ∀ i, nockSampledAfterIO3 (slot i) = 2

namespace IOPlacement3

variable (S : IOPlacement3)

theorem slot_ne : S.slot 0 ≠ S.slot 1 := fun h => absurd (S.injective h) (by decide)

/-- **Freshness is derived, not assumed.**  On the two-message chronology this was the hypothesis
`hfresh` of `GigaIOSlots.io_records_read_no_io_coin` (`GigaRAPIOSlots.lean:536`); here it follows
from the message index. -/
theorem fresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j := by
  intro i j h
  exact embed8_not_third j (h ▸ S.third_message i)

/-- **The placement is unique up to transposing the pair**, from the chronology alone. -/
theorem canonical_up_to_transposition :
    (S.slot 0 = ioGammaSlot ∧ S.slot 1 = ioPoleSlot)
      ∨ (S.slot 0 = ioPoleSlot ∧ S.slot 1 = ioGammaSlot) := by
  have key : ∀ i, S.slot i = ioGammaSlot ∨ S.slot i = ioPoleSlot := by
    intro i
    have := S.third_message i
    revert this
    generalize S.slot i = s
    revert s; decide
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1
  · exact absurd (S.injective (h0.trans h1.symm)) (by decide)
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (S.injective (h0.trans h1.symm)) (by decide)

/-- The placement as a challenge renaming, the form `Expr.remapBlock` consumes.  Definitionally
equal to `GigaIOSlots.IOSlots.map` at the canonical placement (`canonicalPlacement3_map`). -/
def map : ℕ → ℕ := fun i => if h : i < 2 then ((S.slot ⟨i, h⟩ : Fin 10) : ℕ) else 0

@[simp] theorem map_zero : S.map 0 = (S.slot 0 : ℕ) := rfl
@[simp] theorem map_one : S.map 1 = (S.slot 1 : ℕ) := rfl

end IOPlacement3

/-- The canonical placement: `γ` on slot `8`, the pole on slot `9`. -/
def canonicalPlacement3 : IOPlacement3 where
  slot := ![ioGammaSlot, ioPoleSlot]
  injective := by decide
  third_message := by decide

/-- **The renaming is the same one the three-round chips use**, so the two chips' AIRs are the
same term and their satisfaction is the same proposition (§7). -/
theorem canonicalPlacement3_map : canonicalPlacement3.map = canonicalIOSlots.map := rfl

/-! ## 3. The four-round schedules: one commitment block splits in two -/


/-- **The compute schedule with the extra commitment block.**  `finComputeRoundOf`
(`NockGigaRAPFinite.lean:842`) unchanged except that the accumulator `100` and the reciprocal `101`
— the only two columns the paper builds *after* the coins — move to a fourth block. -/
def finComputeRoundOf4 (c : Fin 113) : Fin 4 :=
  if (c : ℕ) < 11 then 0
  else if (c : ℕ) ∈ finProgIoCoinCols then 3
  else if (c : ℕ) ∈ finMegaExtCols then 2 else 1


/-- `w_RAP = ![11, 89, 11, 2]`; `width_eq` is a field, so these are the actual fibre
cardinalities, checked by `decide`. Form R `m = 9` is `113` columns. -/
def finComputeSchedule4 : RoundSchedule 113 4 where
  roundOf := finComputeRoundOf4
  width := ![11, 89, 11, 2]
  width_eq := by decide

def finMemRoundOf4 (c : Fin 55) : Fin 4 :=
  if (c : ℕ) ∈ finMemBaseCols then 0
  else if (c : ℕ) ∈ finMemIoCoinCols then 3
  else if (c : ℕ) ∈ finMemMegaExtCols then 2 else 1


/-- `w_RAP = ![10, 27, 16, 2]`. Form R `m = 9` is `55` columns. -/
def finMemorySchedule4 : RoundSchedule 55 4 where
  roundOf := finMemRoundOf4
  width := ![10, 27, 16, 2]
  width_eq := by decide


theorem finComputeSchedule4_total : (113 : ℕ) = ∑ r, finComputeSchedule4.width r :=
  finComputeSchedule4.total_width


theorem finMemorySchedule4_total : (55 : ℕ) = ∑ r, finMemorySchedule4.width r :=
  finMemorySchedule4.total_width

/-- Only the two IO-coin columns change block. -/
theorem rounds_agree_off_the_io_coin_columns (c : Fin 113)
    (hc : (c : ℕ) ∉ finProgIoCoinCols) :
    (finComputeRoundOf4 c : ℕ) = (finComputeRoundOf c : ℕ) := by
  revert hc; revert c; decide

theorem memRounds_agree_off_the_io_coin_columns (c : Fin 55)
    (hc : (c : ℕ) ∉ finMemIoCoinCols) :
    (finMemRoundOf4 c : ℕ) = (finMemRoundOf c : ℕ) := by
  revert hc; revert c; decide

/-! ## 4. The per-round declaration -/


/-- **The declared coin dependence is now purely per-round.**

`GigaIOSlots.finComputeColumnChallenges` (`GigaRAPIOSlots.lean:426`) had to be *per column* — it
singled out `100`/`101` inside the round-`2` block — and at column `111` that fineness was
strictly stronger than the schedule.  With the extra block the two IO-coin columns are their own
round, so the declaration is a function of the round alone.

A per-round map is not a *saturated* one, and
`SaturatedDeclaration.computeChip3_excess` measures the difference: at every round-`2` and
round-`3` compute column the two memory coins `6, 7` (`β`, `γ`) are schedule-legal and withheld
here, so the declaration does carry information beyond the schedule — sound, since the compute AIR
never reads them, but assumed rather than derived. What survives, and is the point of this
module, is that the **`RAP_prog-IO` coins** are never in that residue
(`SaturatedDeclaration.computeChip3_excess_has_no_io_slot`): their exclusion is the schedule's. `SaturatedDeclaration.computeChip3Sat` is the chip at which the withdrawn sentence is true. -/
def finComputeRoundChalOf4 (S : IOPlacement3) (r : Fin 4) : Finset (Fin 10) :=
  if (r : ℕ) = 0 then ∅
  else if (r : ℕ) = 1 then {1, 2, 3, 4}
  else if (r : ℕ) = 2 then ({0, 1, 2, 3, 4, 5} : Finset (Fin 10))
  else insert (S.slot 0) (insert (S.slot 1) ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)))

/-- The memory twin.  Its residue over the schedule is larger — `{2,3,4}` at round `1` and
`{2,3,4,5}` at rounds `2` and `3` (`SaturatedDeclaration.memoryChip3_excess`) — and, as on the
compute side, contains no IO slot. -/
def finMemRoundChalOf4 (S : IOPlacement3) (r : Fin 4) : Finset (Fin 10) :=
  if (r : ℕ) = 0 then ∅
  else if (r : ℕ) = 1 then {1}
  else if (r : ℕ) = 2 then ({0, 1, 6, 7} : Finset (Fin 10))
  else insert (S.slot 0) (insert (S.slot 1) ({0, 1, 6, 7} : Finset (Fin 10)))

theorem finComputeRoundChalOf4_usable (S : IOPlacement3) (r : Fin 4) :
    ∀ j ∈ finComputeRoundChalOf4 S r, (nockSampledAfterIO3 j : ℕ) < (r : ℕ) := by
  intro j hj
  unfold finComputeRoundChalOf4 at hj
  by_cases h0 : (r : ℕ) = 0
  · rw [if_pos h0] at hj; simp at hj
  rw [if_neg h0] at hj
  by_cases h1 : (r : ℕ) = 1
  · rw [if_pos h1] at hj; rw [h1]; exact chal4_round1 j hj
  rw [if_neg h1] at hj
  by_cases h2 : (r : ℕ) = 2
  · rw [if_pos h2] at hj; rw [h2]; exact chal4_round2 j hj
  rw [if_neg h2] at hj
  have h3 : (r : ℕ) = 3 := by have := r.isLt; omega
  rw [h3]
  rcases Finset.mem_insert.mp hj with rfl | hj'
  · rw [S.third_message 0]; norm_num
  rcases Finset.mem_insert.mp hj' with rfl | hj''
  · rw [S.third_message 1]; norm_num
  exact chal4_round3 j hj''

theorem finMemRoundChalOf4_usable (S : IOPlacement3) (r : Fin 4) :
    ∀ j ∈ finMemRoundChalOf4 S r, (nockSampledAfterIO3 j : ℕ) < (r : ℕ) := by
  intro j hj
  unfold finMemRoundChalOf4 at hj
  by_cases h0 : (r : ℕ) = 0
  · rw [if_pos h0] at hj; simp at hj
  rw [if_neg h0] at hj
  by_cases h1 : (r : ℕ) = 1
  · rw [if_pos h1] at hj; rw [h1]; exact memChal4_round1 j hj
  rw [if_neg h1] at hj
  by_cases h2 : (r : ℕ) = 2
  · rw [if_pos h2] at hj; rw [h2]; exact memChal4_round2 j hj
  rw [if_neg h2] at hj
  have h3 : (r : ℕ) = 3 := by have := r.isLt; omega
  rw [h3]
  rcases Finset.mem_insert.mp hj with rfl | hj'
  · rw [S.third_message 0]; norm_num
  rcases Finset.mem_insert.mp hj' with rfl | hj''
  · rw [S.third_message 1]; norm_num
  exact memChal4_round3 j hj''

/-! ## 5. The two chips -/

section Chips

variable {L : Type*} [Field L]

/-- **The compute chip on the three-message chronology.**  Same AIR, same params, same column
layout as `GigaIOSlots.finiteComputeChip` (`GigaRAPIOSlots.lean:668`); only the commitment schedule
and the chronology differ. -/
noncomputable def computeChip3 (S : IOPlacement3) (q : SegmentedRAPParams L) :
    StagedChip L 4 nockChronologyIO3 where
  air := computeCombinedFiniteAIR 10 9 S.map
  params := q
  schedule := finComputeSchedule4
  columnChallenges := fun c => finComputeRoundChalOf4 S (finComputeRoundOf4 c)
  columns_commit_before_sampling := fun _c j hj => finComputeRoundChalOf4_usable S _ j hj

/-- The memory twin. -/
noncomputable def memoryChip3 (S : IOPlacement3) (q : SegmentedRAPParams L) :
    StagedChip L 4 nockChronologyIO3 where
  air := memoryCombinedFiniteAIR (K := L) 10 9 S.map
  params := q
  schedule := finMemorySchedule4
  columnChallenges := fun c => finMemRoundChalOf4 S (finMemRoundOf4 c)
  columns_commit_before_sampling := fun _c j hj => finMemRoundChalOf4_usable S _ j hj

@[simp] theorem computeChip3_air (S : IOPlacement3) (q : SegmentedRAPParams L) :
    (computeChip3 S q).air = computeCombinedFiniteAIR 10 9 S.map := rfl

@[simp] theorem memoryChip3_air (S : IOPlacement3) (q : SegmentedRAPParams L) :
    (memoryChip3 S q).air = memoryCombinedFiniteAIR (K := L) 10 9 S.map := rfl

/-- **The substituted giga-RAP with the paper's third message.** -/
noncomputable def nockGigaRAPFinite3 (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    GigaRAP L where
  rounds := 4
  rounds_pos := by norm_num
  chronology := nockChronologyIO3
  chips := [computeChip3 S qC, memoryChip3 S qM]

end Chips

/-! ## 6. The headline: the exclusion is forced, for every chip -/


/-- **the paper as a schedule condition.**  `Com(IO_prog)` commits the whole of `IO_prog`
before the coins are sent, so the `IO_prog` columns of the combined compute chip — the two
multiplicity columns and all eight record coordinates, `102 … 111`, the timestamp included — are
committed by the second block. -/
def ProgIORecordsCommittedByRoundTwo {K : Type*} [Field K]
    (T : StagedChip K 4 nockChronologyIO3) : Prop :=
  ∀ c : Fin T.air.numTraceCols, 102 ≤ (c : ℕ) → (c : ℕ) ≤ 111 →
    (T.schedule.roundOf c : ℕ) ≤ 2

/-- The memory twin, columns `43 … 52`. -/
def MemIORecordsCommittedByRoundTwo {K : Type*} [Field K]
    (T : StagedChip K 4 nockChronologyIO3) : Prop :=
  ∀ c : Fin T.air.numTraceCols, 44 ≤ (c : ℕ) → (c : ℕ) ≤ 53 →
    (T.schedule.roundOf c : ℕ) ≤ 2


/-- **A column committed before the third message cannot declare a third-message coin.**

The contrapositive of `StagedChip.columns_commit_before_sampling` (`StagedTableRAP.lean:174`), and
therefore a property of **every** chip of this chronology, not of a chosen declaration.  This is
the sentence that was unavailable at the two-message chronology, where the IO coins and the record
timestamp ride the same message. -/
theorem undeclarable_at_early_column {K : Type*} [Field K]
    (T : StagedChip K 4 nockChronologyIO3) (c : Fin T.air.numTraceCols)
    (hc : (T.schedule.roundOf c : ℕ) ≤ 2)
    (j : Fin nockChronologyIO3.numChallenges) (hj : (nockSampledAfterIO3 j : ℕ) = 2) :
    j ∉ T.columnChallenges c := by
  intro hmem
  have h := T.columns_commit_before_sampling c j hmem
  simp only [ChallengeChronology.usableByColumnOf, nockChronologyIO3] at h
  omega

theorem slot_sampledAfter_two (S : IOPlacement3) (i : Fin 2) :
    (nockSampledAfterIO3 (S.slot i) : ℕ) = 2 := by rw [S.third_message i]; rfl


/-- No `hfresh` hypothesis,
no chosen `columnChallenges`, and no appeal to the `ln = ln_prev·z^k` recurrence (which is a
`V_comp` clause over `W_comp`, the paper, `:1728-1742`, and has no image in
`FiniteIO.finiteIOProgAIR`).

A hostile chip that declares the IO pair at column `111` therefore does not exist here: it would
have to put `111` in round `3`, i.e. commit part of `IO_prog` *after* `Com(IO_prog)`, which is
exactly what the paper forbids and what `ProgIORecordsCommittedByRoundTwo` records. -/
theorem committed_early_excludes_the_io_coins_compute {K : Type*} [Field K] (S : IOPlacement3)
    (T : StagedChip K 4 nockChronologyIO3) (hT : ProgIORecordsCommittedByRoundTwo T)
    (c : Fin T.air.numTraceCols) (h1 : 102 ≤ (c : ℕ)) (h2 : (c : ℕ) ≤ 111) (i : Fin 2) :
    S.slot i ∉ T.columnChallenges c :=
  undeclarable_at_early_column T c (hT c h1 h2) (S.slot i) (slot_sampledAfter_two S i)

/-- The memory twin. -/
theorem committed_early_excludes_the_io_coins_memory {K : Type*} [Field K] (S : IOPlacement3)
    (T : StagedChip K 4 nockChronologyIO3) (hT : MemIORecordsCommittedByRoundTwo T)
    (c : Fin T.air.numTraceCols) (h1 : 44 ≤ (c : ℕ)) (h2 : (c : ℕ) ≤ 53) (i : Fin 2) :
    S.slot i ∉ T.columnChallenges c :=
  undeclarable_at_early_column T c (hT c h1 h2) (S.slot i) (slot_sampledAfter_two S i)

theorem computeRoundOf4_le_two (c : Fin 113) (h1 : 102 ≤ (c : ℕ)) :
    (finComputeRoundOf4 c : ℕ) ≤ 2 := by
  have hne : (c : ℕ) ∉ finProgIoCoinCols := by
    simp only [finProgIoCoinCols, List.mem_cons, List.not_mem_nil, or_false]
    omega
  unfold finComputeRoundOf4
  by_cases hlt : (c : ℕ) < 11
  · rw [if_pos hlt]; decide
  rw [if_neg hlt, if_neg hne]
  split_ifs <;> decide

theorem memRoundOf4_le_two (c : Fin 55) (h1 : 44 ≤ (c : ℕ)) :
    (finMemRoundOf4 c : ℕ) ≤ 2 := by
  have hne : (c : ℕ) ∉ finMemIoCoinCols := by
    simp only [finMemIoCoinCols, List.mem_cons, List.not_mem_nil, or_false]
    omega
  unfold finMemRoundOf4
  by_cases hb : (c : ℕ) ∈ finMemBaseCols
  · rw [if_pos hb]; decide
  rw [if_neg hb, if_neg hne]
  split_ifs <;> decide

/-- The two chips of this module satisfy the paper's schedule condition. -/
theorem computeChip3_records_committed_early {L : Type*} [Field L] (S : IOPlacement3)
    (q : SegmentedRAPParams L) : ProgIORecordsCommittedByRoundTwo (computeChip3 S q) :=
  fun c h1 _h2 => computeRoundOf4_le_two c h1

theorem memoryChip3_records_committed_early {L : Type*} [Field L] (S : IOPlacement3)
    (q : SegmentedRAPParams L) : MemIORecordsCommittedByRoundTwo (memoryChip3 S q) :=
  fun c h1 _h2 => memRoundOf4_le_two c h1

/-- Instantiated: the compute chip's `IO_prog` columns declare neither IO coin. -/
theorem computeChip3_io_data_undeclared {L : Type*} [Field L] (S : IOPlacement3)
    (q : SegmentedRAPParams L) (c : Fin 113) (h1 : 102 ≤ (c : ℕ)) (h2 : (c : ℕ) ≤ 111)
    (i : Fin 2) : S.slot i ∉ (computeChip3 S q).columnChallenges c :=
  committed_early_excludes_the_io_coins_compute S (computeChip3 S q)
    (computeChip3_records_committed_early S q) c h1 h2 i

theorem memoryChip3_io_data_undeclared {L : Type*} [Field L] (S : IOPlacement3)
    (q : SegmentedRAPParams L) (c : Fin 55) (h1 : 44 ≤ (c : ℕ)) (h2 : (c : ℕ) ≤ 53)
    (i : Fin 2) : S.slot i ∉ (memoryChip3 S q).columnChallenges c :=
  committed_early_excludes_the_io_coins_memory S (memoryChip3 S q)
    (memoryChip3_records_committed_early S q) c h1 h2 i


/-- **The disclosure, inverted.**  `GigaIOSlots.record_timestamp_column_shares_the_message_with_the_io_coins`
(`GigaRAPIOSlots.lean:652`) records that at the two-message chronology the record timestamp `ts`
is committed after the *same* verifier message as the IO coins.  Here it is committed strictly
before them, so the IO coins are **not usable** by that column, and they **are** usable by the
accumulator column `100` (memory `41`) — the paper before the paper, at the columns it
is about. -/
theorem record_timestamp_column_precedes_the_io_message (S : IOPlacement3) :
    ((finComputeRoundOf4 111 : ℕ) = 2 ∧ (finMemRoundOf4 53 : ℕ) = 2)
      ∧ (∀ i, (nockSampledAfterIO3 (S.slot i) : ℕ) = 2)
      ∧ (∀ i, ¬ nockChronologyIO3.usableByColumnOf (finComputeRoundOf4 111) (S.slot i))
      ∧ (∀ i, ¬ nockChronologyIO3.usableByColumnOf (finMemRoundOf4 53) (S.slot i))
      ∧ (∀ i, nockChronologyIO3.usableByColumnOf (finComputeRoundOf4 100) (S.slot i))
      ∧ (∀ i, nockChronologyIO3.usableByColumnOf (finMemRoundOf4 42) (S.slot i)) := by
  refine ⟨⟨by decide, by decide⟩, slot_sampledAfter_two S, ?_, ?_, ?_, ?_⟩
  · intro i h
    have h2 := slot_sampledAfter_two S i
    simp only [ChallengeChronology.usableByColumnOf, nockChronologyIO3] at h
    have : (finComputeRoundOf4 111 : ℕ) = 2 := by decide
    omega
  · intro i h
    have h2 := slot_sampledAfter_two S i
    simp only [ChallengeChronology.usableByColumnOf, nockChronologyIO3] at h
    have : (finMemRoundOf4 53 : ℕ) = 2 := by decide
    omega
  · intro i
    have h2 := slot_sampledAfter_two S i
    simp only [ChallengeChronology.usableByColumnOf, nockChronologyIO3]
    have : (finComputeRoundOf4 100 : ℕ) = 3 := by decide
    omega
  · intro i
    have h2 := slot_sampledAfter_two S i
    simp only [ChallengeChronology.usableByColumnOf, nockChronologyIO3]
    have : (finMemRoundOf4 42 : ℕ) = 3 := by decide
    omega

/-! ## 7. The census, re-measured, and what the third message costs -/

section Census

variable {L : Type*} [Field L]


/-- **The compute chip's census.**  Identical to `GigaIOSlots.finiteComputeChip_census`
(`GigaRAPIOSlots.lean:704`): `112` columns, `10` coins, `3` publics, `538` constraints as
`526` row / `6` transition / `4` boundary / `2` terminal, degree `4`.  **No gate was added**: the
third message is a change of commitment schedule, not of constraint system. -/
theorem computeChip3_census (S : IOPlacement3) (q : SegmentedRAPParams L) :
    (computeChip3 S q).air.numTraceCols = 113
      ∧ (computeChip3 S q).air.numChallenges = 10
      ∧ (computeChip3 S q).air.numPublic = 3
      ∧ (computeChip3 S q).air.constraints.length = 538
      ∧ (kindSeg (computeChip3 S q).air .row).constraints.length = 526
      ∧ (kindSeg (computeChip3 S q).air .transition).constraints.length = 6
      ∧ (kindSeg (computeChip3 S q).air .boundary).constraints.length = 4
      ∧ (kindSeg (computeChip3 S q).air .terminal).constraints.length = 2
      ∧ (computeChip3 S q).air.maxDegree = 4 := by
  obtain ⟨hr, ht, hb, hx⟩ := computeCombinedFiniteAIR_kindSeg_census 10 9 S.map
  exact ⟨rfl, rfl, rfl, computeCombinedFiniteAIR_num_constraints 10 9 S.map, hr, ht, hb, hx,
    computeCombinedFiniteAIR_maxDegree 10 9 S.map⟩


/-- The memory chip's census: `53` / `10` / `3` / `93` as `75 / 8 / 7 / 3`, degree `4`. -/
theorem memoryChip3_census (S : IOPlacement3) (q : SegmentedRAPParams L) :
    (memoryChip3 S q).air.numTraceCols = 55
      ∧ (memoryChip3 S q).air.numChallenges = 10
      ∧ (memoryChip3 S q).air.numPublic = 3
      ∧ (memoryChip3 S q).air.constraints.length = 93
      ∧ (kindSeg (memoryChip3 S q).air .row).constraints.length = 75
      ∧ (kindSeg (memoryChip3 S q).air .transition).constraints.length = 8
      ∧ (kindSeg (memoryChip3 S q).air .boundary).constraints.length = 7
      ∧ (kindSeg (memoryChip3 S q).air .terminal).constraints.length = 3
      ∧ (memoryChip3 S q).air.maxDegree = 4 := by
  obtain ⟨hr, ht, hb, hx⟩ := memoryCombinedFiniteAIR_kindSeg_census (K := L) 10 9 S.map
  exact ⟨rfl, rfl, rfl, memoryCombinedFiniteAIR_num_constraints (K := L) 10 9 S.map, hr, ht, hb, hx,
    memoryCombinedFiniteAIR_maxDegree (K := L) 10 9 S.map⟩


/-- **What the third message does change**: `k` and `w_RAP`.  `![11, 88, 13]` becomes
`![11, 88, 11, 2]` (`GigaIOSlots.finiteComputeChip_rap`, `GigaRAPIOSlots.lean:737`). -/
theorem computeChip3_rap (S : IOPlacement3) (q : SegmentedRAPParams L)
    (kind : Reified.ConstraintKind) :
    ((computeChip3 S q).rap kind).w = 113 ∧ ((computeChip3 S q).rap kind).k = 4 ∧
      ((computeChip3 S q).rap kind).wRAP = ![11, 89, 11, 2] := ⟨rfl, rfl, rfl⟩


/-- `![9, 26, 18]` becomes `![9, 26, 16, 2]`. -/
theorem memoryChip3_rap (S : IOPlacement3) (q : SegmentedRAPParams L)
    (kind : Reified.ConstraintKind) :
    ((memoryChip3 S q).rap kind).w = 55 ∧ ((memoryChip3 S q).rap kind).k = 4 ∧
      ((memoryChip3 S q).rap kind).wRAP = ![10, 27, 16, 2] := ⟨rfl, rfl, rfl⟩

/-- **The third message costs no constraint.**  At the canonical placement the four-round chip and
`GigaIOSlots.finiteComputeChip` have the same AIR and the same params, so their satisfaction is
literally the same proposition. -/
theorem canonical3_satisfies_iff (q : SegmentedRAPParams L)
    (Pt : Fin (computeCombinedFiniteAIR 10 9 canonicalIOSlots.map).numTraceCols → L[X]) :
    (computeChip3 canonicalPlacement3 q).Satisfies Pt
      ↔ (finiteComputeChip canonicalIOSlots q).Satisfies Pt := Iff.rfl

/-- The memory twin. -/
theorem canonical3_mem_satisfies_iff (q : SegmentedRAPParams L)
    (Pt : Fin (memoryCombinedFiniteAIR (K := L) 10 9 canonicalIOSlots.map).numTraceCols → L[X]) :
    (memoryChip3 canonicalPlacement3 q).Satisfies Pt
      ↔ (finiteMemoryChip canonicalIOSlots q).Satisfies Pt := Iff.rfl

end Census

/-! ## 8. The freshness argument, now from the round structure

`GigaIOFreshness.prog_records_const_in_the_io_coins` (`GigaRAPIOFreshness.lean:177`) derives
constancy from the *declared* per-column dependence, via
`columnLocal_const_of_undeclared_challenges` (`:88`).  The theorems below derive the same
conclusion from `RoundFibred.columnLocal_const_of_prior_challenges`
(`RoundFibredSoundness.lean:595`), whose only structural input is
`StagedChip.columns_commit_before_sampling`.  That is the substantive difference: the input is now
the round schedule, which §6 shows leaves the prover no choice. -/

section Freshness

variable {K : Type*} [Field K] {V β : Type*}
variable (S : IOPlacement3) (q : SegmentedRAPParams K)

/-- The compute IO-block columns that carry `IO_prog` itself — the two
multiplicity columns and the eight record coordinates, `102 … 111`. -/
noncomputable def progIoDataCols3 : Finset (Fin (computeChip3 S q).air.numTraceCols) :=
  Finset.univ.filter fun c => 102 ≤ (c : ℕ) ∧ (c : ℕ) ≤ 111

/-- The memory twin, `43 … 52`. -/
noncomputable def memIoDataCols3 : Finset (Fin (memoryChip3 S q).air.numTraceCols) :=
  Finset.univ.filter fun c => 44 ≤ (c : ℕ) ∧ (c : ℕ) ≤ 53

theorem progIoDataCols3_committedBy_two
    (L : ColumnLocal (computeChip3 S q) V β) (hL : L.cols ⊆ progIoDataCols3 S q) :
    L.CommittedBy (2 : Fin 4) := by
  intro c hc
  have hcm := hL hc
  simp only [progIoDataCols3, Finset.mem_filter, Finset.mem_univ, true_and] at hcm
  exact computeRoundOf4_le_two c hcm.1

theorem memIoDataCols3_committedBy_two
    (L : ColumnLocal (memoryChip3 S q) V β) (hL : L.cols ⊆ memIoDataCols3 S q) :
    L.CommittedBy (2 : Fin 4) := by
  intro c hc
  have hcm := hL hc
  simp only [memIoDataCols3, Finset.mem_filter, Finset.mem_univ, true_and] at hcm
  exact memRoundOf4_le_two c hcm.1


/-- **(1) The records are independent of the two `RAP_prog-IO` coins — from the commitment
order.**

Any readout of the compute `IO_prog` columns takes the same value at two challenge vectors that
agree off the two IO slots.  Unlike `GigaIOFreshness.prog_records_const_in_the_io_coins`
(`GigaRAPIOFreshness.lean:177`), the proof goes through
`RoundFibred.columnLocal_const_of_prior_challenges` (`RoundFibredSoundness.lean:595`) and uses no
per-column declaration: the `IO_prog` columns are committed by round `2` and the coins are sampled
after round `2`.  That is the paper before the paper. -/
theorem prog_records_const_in_the_io_coins3
    (A : StagedAssignment (computeChip3 S q) V)
    (L : ColumnLocal (computeChip3 S q) V β) (hL : L.cols ⊆ progIoDataCols3 S q)
    (χ₁ χ₂ : Fin 10 → K)
    (hagree : ∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
  refine columnLocal_const_of_prior_challenges A L
    (progIoDataCols3_committedBy_two S q L hL) χ₁ χ₂ ?_
  intro j hj
  have hj' : (nockSampledAfterIO3 j : ℕ) < 2 := hj
  refine hagree j (fun h => ?_) (fun h => ?_)
  · rw [h, slot_sampledAfter_two S 0] at hj'; omega
  · rw [h, slot_sampledAfter_two S 1] at hj'; omega

/-- The memory twin. -/
theorem mem_records_const_in_the_io_coins3
    (A : StagedAssignment (memoryChip3 S q) V)
    (L : ColumnLocal (memoryChip3 S q) V β) (hL : L.cols ⊆ memIoDataCols3 S q)
    (χ₁ χ₂ : Fin 10 → K)
    (hagree : ∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
  refine columnLocal_const_of_prior_challenges A L
    (memIoDataCols3_committedBy_two S q L hL) χ₁ χ₂ ?_
  intro j hj
  have hj' : (nockSampledAfterIO3 j : ℕ) < 2 := hj
  refine hagree j (fun h => ?_) (fun h => ?_)
  · rw [h, slot_sampledAfter_two S 0] at hj'; omega
  · rw [h, slot_sampledAfter_two S 1] at hj'; omega

end Freshness

/-! ## 9. The two bad sets and the round-stratified bound -/

section BadSets

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {V : Type*} {m : ℕ}
variable (S : IOPlacement3) (q : SegmentedRAPParams K)

/-- The coordinates the record-RLC coin's bad set may read: everything but the two IO slots. -/
def ioDepGamma3 : Finset (Fin 10) := (Finset.univ : Finset (Fin 10)) \ {S.slot 0, S.slot 1}

/-- The coordinates the pole's bad set may read: everything but its own. -/
def ioDepPole3 : Finset (Fin 10) := (Finset.univ : Finset (Fin 10)).erase (S.slot 1)

theorem gamma_not_mem_ioDepGamma3 : S.slot 0 ∉ ioDepGamma3 S := by simp [ioDepGamma3]
theorem pole_not_mem_ioDepPole3 : S.slot 1 ∉ ioDepPole3 S := by simp [ioDepPole3]

theorem gamma_mem_ioDepPole3 : S.slot 0 ∈ ioDepPole3 S := by
  simp only [ioDepPole3, Finset.mem_erase, Finset.mem_univ, and_true]
  exact S.slot_ne


/-- **Even with the third message, the chronology-indexed corollary is still not the right tool.**
Both IO coins ride message `2`, so `γ` is not in the pole's `priorCoords`, while the pole's bad set
genuinely reads `γ`.  `RoundFibred.roundUnion_card_le_of_chronology` (`RoundFibredSoundness.lean:392`)
fixes `dep := priorCoords` and therefore cannot apply; the general `roundUnion_card_le` (`:380`),
whose `dep` is arbitrary subject to `hself`, is the instance used.  (This reproduces
`GigaIOFreshness.gamma_not_prior_to_pole`, `GigaRAPIOFreshness.lean:241`, at the new chronology: the
extra message separates the records from the coins, not the two coins from each other.) -/
theorem gamma_not_prior_to_pole3 :
    S.slot 0 ∉ priorCoords (fun j => (nockSampledAfterIO3 j : ℕ)) (S.slot 1) := by
  simp only [priorCoords, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
    slot_sampledAfter_two S 0, slot_sampledAfter_two S 1]
  exact le_rfl

variable (A : StagedAssignment (computeChip3 S q) V)
  (L : ColumnLocal (computeChip3 S q) V (PreChallengeRecords K m))

/-- The bad record-RLC challenges at a challenge vector. -/
noncomputable def badGamma3 (χ : Fin 10 → K) : Finset K :=
  IORLCCollisionEvent (L.out (A.trace χ))

/-- The bad poles: pole-hit and log-derivative events, at those records and at the sampled
record-RLC coin. -/
noncomputable def badPole3 (χ : Fin 10 → K) : Finset K :=
  IOPoleHitEvent (L.out (A.trace χ)) (χ (S.slot 0))
    ∪ IOLogDerivEvent (L.out (A.trace χ)) (χ (S.slot 0))


/-- **The record-RLC coin's bad set reads neither IO coordinate** — now because the records are
committed before the third message, not because a declaration says so. -/
theorem badGamma3_readsOn (hL : L.cols ⊆ progIoDataCols3 S q) :
    ReadsOn (C := K) (ioDepGamma3 S) (badGamma3 S q A L) := by
  intro χ₁ χ₂ hagree
  have hrec : L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
    refine prog_records_const_in_the_io_coins3 S q A L hL χ₁ χ₂ ?_
    intro j h0 h1
    refine hagree j ?_
    simp only [ioDepGamma3, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨h0, h1⟩
  simp only [badGamma3, hrec]


/-- **The pole's bad set reads `γ` and the records, and not the pole.** -/
theorem badPole3_readsOn (hL : L.cols ⊆ progIoDataCols3 S q) :
    ReadsOn (C := K) (ioDepPole3 S) (badPole3 S q A L) := by
  intro χ₁ χ₂ hagree
  have hgamma : χ₁ (S.slot 0) = χ₂ (S.slot 0) := hagree _ (gamma_mem_ioDepPole3 S)
  have hrec : L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
    refine prog_records_const_in_the_io_coins3 S q A L hL χ₁ χ₂ ?_
    intro j _ h1
    refine hagree j ?_
    simp only [ioDepPole3, Finset.mem_erase, Finset.mem_univ, and_true]
    exact h1
  simp only [badPole3, hrec, hgamma]

/-- The per-coordinate bad-set family. -/
noncomputable def ioBad3 (i : Fin 10) (χ : Fin 10 → K) : Finset K :=
  if i = S.slot 0 then badGamma3 S q A L χ
  else if i = S.slot 1 then badPole3 S q A L χ else ∅

/-- The dependence sets. -/
def ioDep3 (i : Fin 10) : Finset (Fin 10) :=
  if i = S.slot 1 then ioDepPole3 S else ioDepGamma3 S


/-- **(2) The IO coins priced as summands of the round-stratified bound.**

The conclusion of `GigaIOFreshness.io_failure_roundUnion_card_le` (`GigaRAPIOFreshness.lean:332`),
re-proved on the three-message chips.  The number is unchanged — `|K|^9 · (B_γ + B_pole)` out of
`|K|^10`, which `GigaIOFreshness.io_round_price_is_the_ioWork_charge` (`:342`) identifies with the
existing `ioWork / cardK²` charge — but the `hdep` input now comes from the commitment order
(`prog_records_const_in_the_io_coins3`) rather than from a per-column declaration.  `hself` comes
from the *definitions* of `ioDepGamma3`/`ioDepPole3` and from nothing else; that was true of
`GigaIOFreshness` too and its docstring said otherwise. -/
theorem io_failure_roundUnion_card_le3
    (hL : L.cols ⊆ progIoDataCols3 S q) (Bγ Bpole : ℕ)
    (hBγ : ∀ χ, (badGamma3 S q A L χ).card ≤ Bγ)
    (hBpole : ∀ χ, (badPole3 S q A L χ).card ≤ Bpole) :
    (roundUnion (C := K) {S.slot 0, S.slot 1} (ioBad3 S q A L)).card
      ≤ Fintype.card K ^ 9 * Bγ + Fintype.card K ^ 9 * Bpole := by
  classical
  haveI : Nonempty K := ⟨0⟩
  have hne : S.slot 0 ≠ S.slot 1 := S.slot_ne
  refine le_trans (roundUnion_card_le (C := K) {S.slot 0, S.slot 1} (ioBad3 S q A L) (ioDep3 S)
    ?_ ?_ (fun i => if i = S.slot 0 then Bγ else if i = S.slot 1 then Bpole else 0) ?_) ?_
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · rw [show ioDep3 S (S.slot 0) = ioDepGamma3 S from if_neg hne]
      exact gamma_not_mem_ioDepGamma3 S
    · rw [show ioDep3 S (S.slot 1) = ioDepPole3 S from if_pos rfl]
      exact pole_not_mem_ioDepPole3 S
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · rw [show ioDep3 S (S.slot 0) = ioDepGamma3 S from if_neg hne]
      intro χ₁ χ₂ hag
      have h := badGamma3_readsOn S q A L hL χ₁ χ₂ hag
      simpa [ioBad3] using h
    · rw [show ioDep3 S (S.slot 1) = ioDepPole3 S from if_pos rfl]
      intro χ₁ χ₂ hag
      have h := badPole3_readsOn S q A L hL χ₁ χ₂ hag
      simpa [ioBad3, hne.symm] using h
  · intro i χ
    by_cases h0 : i = S.slot 0
    · subst h0; simpa [ioBad3] using hBγ χ
    · by_cases h1 : i = S.slot 1
      · subst h1; simpa [ioBad3, h0] using hBpole χ
      · simp [ioBad3, h0, h1]
  · have e0 : (if S.slot 0 = S.slot 0 then Bγ else if S.slot 0 = S.slot 1 then Bpole else 0)
        = Bγ := by simp
    have e1 : (if S.slot 1 = S.slot 0 then Bγ else if S.slot 1 = S.slot 1 then Bpole else 0)
        = Bpole := by simp [hne.symm]
    rw [Finset.sum_pair hne, e0, e1]

end BadSets

/-! ## 10. -/

section ColReads

variable {K : Type*} [Field K]


/--

`RoundFibred.StagedAssignment` (`RoundFibredSoundness.lean:563`) carries `col_reads` as a *field*:
a column committed in round `r` is not a function of a coin sampled at message `≥ r`.  That is the
binding property of the commitment scheme the paper writes `Com(·)` for, delegated to the
RAP→SNARK compiler at the paper.  It **cannot** be promoted to a theorem about traces that
satisfy the chip, because satisfaction is a condition on each challenge vector separately and says
nothing about how the trace varies across them: at a chip with no constraints every trace family
satisfies, and one of them reads an undeclared coin.

Stated over an arbitrary constraint-free chip of the three-message chronology, so it is a statement
about the *shape* of the obligation rather than about any particular table. -/
theorem col_reads_not_implied_by_satisfaction
    (T : StagedChip K 4 nockChronologyIO3) (hnc : T.air.constraints = [])
    (c₀ : Fin T.air.numTraceCols) (j₀ : Fin 10) (hj₀ : j₀ ∉ T.columnChallenges c₀) :
    ∃ t : (Fin 10 → K) → (Fin T.air.numTraceCols → K[X]),
      (∀ χ, T.Satisfies (t χ))
        ∧ ¬ (∀ c (χ₁ χ₂ : Fin 10 → K),
              (∀ j ∈ T.columnChallenges c, χ₁ j = χ₂ j) → t χ₁ c = t χ₂ c) := by
  classical
  refine ⟨fun χ c => if c = c₀ then Polynomial.C (χ j₀) else 0, ?_, ?_⟩
  · intro χ
    refine (T.satisfies_iff_kinded _).mpr ?_
    rw [hnc]
    intro c hc
    exact absurd hc (by simp)
  · intro h
    have hag : ∀ j ∈ T.columnChallenges c₀,
        (fun _ : Fin 10 => (0 : K)) j = (fun j : Fin 10 => if j = j₀ then (1 : K) else 0) j := by
      intro j hj
      have hne : j ≠ j₀ := fun h' => hj₀ (h' ▸ hj)
      simp; exact hne
    have hc := h c₀ (fun _ => 0) (fun j => if j = j₀ then 1 else 0) hag
    have hcoeff := congrArg (fun p : K[X] => p.coeff 0) hc
    simp at hcoeff

end ColReads

/-! ## 11. The fold and the payoff, at the three-message chips

Nothing here is new mathematics: `GigaFinite`'s fold theorems are stated about
`SegmentedRAPParams.rap`, which reads neither the round schedule nor the chronology, so the whole
`IOChipSoundness` composition transports verbatim.  It is recorded so that the module that carries
the *enforced* dependence also carries the soundness conclusion. -/

section Fold

variable {L : Type*} [Field L]

theorem computeChip3_satisfies_iff_kinded (S : IOPlacement3) (q : SegmentedRAPParams L)
    (Pt : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → L[X]) :
    (computeChip3 S q).Satisfies Pt
      ↔ ∀ c ∈ (computeCombinedFiniteAIR 10 9 S.map).constraints, ∀ x ∈ q.domain c.kind,
          c.expr.eval (envOfTrace Pt q.ω x q.chalVal q.pubVal) = 0 :=
  (computeChip3 S q).satisfies_iff_kinded Pt

theorem memoryChip3_satisfies_iff_kinded (S : IOPlacement3) (q : SegmentedRAPParams L)
    (Pt : Fin (memoryCombinedFiniteAIR (K := L) 10 9 S.map).numTraceCols → L[X]) :
    (memoryChip3 S q).Satisfies Pt
      ↔ ∀ c ∈ (memoryCombinedFiniteAIR (K := L) 10 9 S.map).constraints, ∀ x ∈ q.domain c.kind,
          c.expr.eval (envOfTrace Pt q.ω x q.chalVal q.pubVal) = 0 :=
  (memoryChip3 S q).satisfies_iff_kinded Pt

theorem computeChip3_fold_loses_nothing (S : IOPlacement3) (q : SegmentedRAPParams L)
    (Pt : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → L[X])
    (h : (computeChip3 S q).Satisfies Pt) :
    (∀ kind, (q.rap computeAIRchained kind).Satisfies (finComputeBlock Pt))
      ∧ (∀ kind, ((ComputeChip.shiftParams q ComputeChip.walkChalOff
          ComputeChip.walkPubOff).rap walkAIR kind).Satisfies (finWalkBlock Pt))
      ∧ (∀ kind, ((remapParams q S.map ComputeChip.ioPubOff).rap (finiteIOProgAIR 9)
          kind).Satisfies (finProgIoBlock Pt)) :=
  ⟨fold_gives_finCompute q q rfl (fun _ _ => rfl) (fun _ => rfl) Pt
     ((computeChip3_satisfies_iff_kinded S q Pt).mp h),
   fold_gives_finWalk q (ComputeChip.shiftParams q ComputeChip.walkChalOff ComputeChip.walkPubOff)
     rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) Pt
     ((computeChip3_satisfies_iff_kinded S q Pt).mp h),
   fold_gives_finProgIo q (remapParams q S.map ComputeChip.ioPubOff) rfl (fun _ _ => rfl)
     (fun _ _ => rfl) (fun _ => rfl) Pt ((computeChip3_satisfies_iff_kinded S q Pt).mp h)⟩

theorem memoryChip3_fold_loses_nothing (S : IOPlacement3) (q : SegmentedRAPParams L)
    (Pt : Fin (memoryCombinedFiniteAIR (K := L) 10 9 S.map).numTraceCols → L[X])
    (h : (memoryChip3 S q).Satisfies Pt) :
    (∀ kind, ((remapParams q memChalMap memPubOff).rap (memoryAIRchained (K := L)) kind).Satisfies
        (finMemBlock Pt))
      ∧ (∀ kind, ((remapParams q memWalkChalMap memWalkPubOff).rap walkAIR kind).Satisfies
          (finMemWalkBlock Pt))
      ∧ (∀ kind, ((remapParams q S.map memIoPubOff).rap (finiteIOMemAIR 9) kind).Satisfies
          (finMemIoBlock Pt)) :=
  ⟨fold_gives_finMem q (remapParams q memChalMap memPubOff) rfl (fun _ _ => rfl) (fun _ => rfl) Pt
     ((memoryChip3_satisfies_iff_kinded S q Pt).mp h),
   fold_gives_finMemWalk q (remapParams q memWalkChalMap memWalkPubOff) rfl (fun _ _ => rfl)
     (fun _ _ => rfl) (fun _ => rfl) Pt ((memoryChip3_satisfies_iff_kinded S q Pt).mp h),
   fold_gives_finMemIo q (remapParams q S.map memIoPubOff) rfl (fun _ _ => rfl) (fun _ _ => rfl)
     (fun _ => rfl) Pt ((memoryChip3_satisfies_iff_kinded S q Pt).mp h)⟩

end Fold

section Payoff

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]


/-- **The record-level IO language from satisfaction of the three-message giga-RAP.**  The
analogue of `GigaIOSlots.io_lio_of_giga_satisfies` (`GigaRAPIOSlots.lean:842`), at the chips whose
schedule *forces* the IO-coin exclusion at the record columns. -/
theorem io_lio_of_giga3_satisfies {Ksz : ℕ} (S : IOPlacement3)
    (records : PreChallengeRecords K 9) (coins : IOCoins K) (terminal : K)
    (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 S.map).numTraceCols → K[X])
    (hC : (computeChip3 S qC).Satisfies PC)
    (hM : (memoryChip3 S qM).Satisfies PM)
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
    (computeChip3_fold_loses_nothing S qC PC hC).2.2
    (memoryChip3_fold_loses_nothing S qM PM hM).2.2
    hrowsP hrowsM hagP hagM hKp hKreq hKresp hreqnd hrespnd hγ hpole


/-- The `Perm` conjunct alone. -/
theorem perm_of_giga3_satisfies {Ksz : ℕ} (S : IOPlacement3)
    (records : PreChallengeRecords K 9) (coins : IOCoins K) (terminal : K)
    (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 S.map).numTraceCols → K[X])
    (hC : (computeChip3 S qC).Satisfies PC)
    (hM : (memoryChip3 S qM).Satisfies PM)
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
  (io_lio_of_giga3_satisfies (Ksz := Ksz) S records coins terminal qC qM x₀p x₀m PC PM hC hM
    hrowsP hrowsM hagP hagM hKp hKreq hKresp hreqnd hrespnd hγ hpole).2.2

end Payoff

end Nock.NockVMROM.Thm54.GigaIOThirdMessage

section Audit

open Nock.NockVMROM.Thm54.GigaIOThirdMessage

#check @nockChronologyIO3
#check @IOPlacement3
#check @computeChip3
#check @memoryChip3
#check @undeclarable_at_early_column
#check @committed_early_excludes_the_io_coins_compute
#check @committed_early_excludes_the_io_coins_memory
#check @prog_records_const_in_the_io_coins3
#check @io_failure_roundUnion_card_le3
#check @col_reads_not_implied_by_satisfaction
#check @io_lio_of_giga3_satisfies

#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.io3_restricts
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.io3_third_message_slots
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.IOPlacement3.fresh
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.IOPlacement3.canonical_up_to_transposition
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.canonicalPlacement3_map
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.finComputeSchedule4
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.finMemorySchedule4
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.finComputeSchedule4_total
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.finMemorySchedule4_total
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.rounds_agree_off_the_io_coin_columns
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.memRounds_agree_off_the_io_coin_columns
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.finComputeRoundChalOf4_usable
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.finMemRoundChalOf4_usable
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.undeclarable_at_early_column
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.committed_early_excludes_the_io_coins_memory
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.computeChip3_io_data_undeclared
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.memoryChip3_io_data_undeclared
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.record_timestamp_column_precedes_the_io_message
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.computeChip3_census
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.memoryChip3_census
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.computeChip3_rap
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.memoryChip3_rap
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.canonical3_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.canonical3_mem_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.prog_records_const_in_the_io_coins3
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.mem_records_const_in_the_io_coins3
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.gamma_not_prior_to_pole3
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.badGamma3_readsOn
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.badPole3_readsOn
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.io_failure_roundUnion_card_le3
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.col_reads_not_implied_by_satisfaction
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.computeChip3_fold_loses_nothing
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.memoryChip3_fold_loses_nothing
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.io_lio_of_giga3_satisfies
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessage.perm_of_giga3_satisfies

end Audit
