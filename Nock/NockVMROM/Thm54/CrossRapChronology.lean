import Nock.NockVMROM.Thm54.GigaRAPThirdMessage

/-!
# The six paper RAPs as `StagedChip`s: cross-RAP sequencing on the production object

Theorem 5.4 assembles **six** RAPs, not two chips:

| paper RAP | paper line | this tree |
|---|---|---|
| `RAP_comp` | the paper (`rap_inputs := (α,z,a,b,c) ∈ 𝕂⁵`) | compute block `0…93` |
| `RAP_walk` / `Thm:Walk_IOP` | the paper | compute block `94…99` |
| `RAP_prog-IO` | the paper | compute block `100…111` |
| `RAP_mem` | the paper | memory block `0…34` |
| `Corr:forest` | the paper | memory block `35…40` |
| `RAP_mem-IO` | the paper | memory block `41…52` |

and it ties them together by **sharing edges** — statements that one RAP's coin *is* another
RAP's coin.  the paper is the sharpest: the memory side's `α, β` are "obtained from the
computation table's `w_prog-IO` array" rather than drawn, which is why the paper gives
`RAP_mem-IO` `e+1` columns and **no round of its own** while the paper charges the round to
`RAP_prog-IO`.  the paper has the memory table consume timestamps `z^i` produced by the
compute table's line number; the paper makes the NPR encoding `NMR^{α,β}` global to both.

## The object this module uses, and the one it does not build

`Staged.StagedChip` (`StagedTableRAP.lean`) **is** the tree's round-carrying, proved,
production-bearing table object: it stores an AIR, a `RoundSchedule`, a per-column coin
declaration into the *proof's* one coin space, and carries commit-before-sample as the **proof
field** `columns_commit_before_sampling`.  `Staged.GigaRAP` bundles a `ChallengeChronology` with a
list of such chips, so chips of one proof agree about when each coin was sent *by typing*.

Earlier drafts of this module introduced a parallel `CrossRapSchedule` record that re-declared
`numRounds`, `numCoins`, `sampledAfter` and discharged its own `blocks_commit_before_sampling`
field.  That is a second type beside the one that already carries production.  This module instead
**places the six paper RAPs into `StagedChip` itself**: each block becomes a genuine
`StagedChip K 4 nockChronologyIO3` over the block's own AIR, its schedule the restriction of the
host chip's schedule to the block's columns, its declaration the block's own coin slots filtered
by usability.  The six assemble into a `GigaRAP` (`nockPaperSixRAP`), so the cross-RAP object is a
`GigaRAP` whose chips are the six paper RAPs rather than the two commitment chips.

Consequences that are the point of the re-base:

* the ordering obligation is **not restated**: `blockChip_commit_before_sampling` is literally
  each chip's own field, and `shared_coin_commits_before_both_readers` — a shared coin obeys
  *both* readers' obligations — is a two-line theorem about **arbitrary** `StagedChip`s of one
  chronology, so it applies to the shipped `computeChip3`/`memoryChip3` as much as to the blocks;
* `PoleDiscipline` is a predicate on a `StagedChip`, and its two headline measurements are made
  **on the shipped chips**, not on a model of them;
* `airToRAP` is untouched.  Nothing here sets `RAP.k`; the blocks inherit `rounds = 4` from the
  chronology they are staged over, exactly as `computeChip3` does.

## What is here

* §1 the cross-chip theory, generic over `StagedChip`: shared readers, `PoleDiscipline`, and the
  two facts that distinguish a *lower* bound on the sampling message from commit-before-sample.
* §4 the value layer: a shared *slot* is not a shared *value*.
* §5 why the object is needed — `bad_seed_keeps_every_local_obligation`, now a genuine
  `StagedChip` over a genuinely differently-remapped AIR.
* §6 the pole discipline measured on `computeChip3` / `memoryChip3`.
* §7 the repair, as a real chip: `memoryChip5 : StagedChip L 4 nockChronologyPole` with the
  `intermediate` columns in the fourth block — the obligation this module's predecessor could only
  name.  **No fourth verifier message.**
* §8 `S5` as a named residual, declined against the paper.

**This module adds no coin, changes no shipped chip, and changes no coin's value or round in the
shipped configuration.**  §7's chronology is a *design*, stated on its own objects.
-/

namespace Nock.NockVMROM.Thm54.CrossRap

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GigaFinite
open Nock.NockVMROM.Thm54.GigaIOThirdMessage
open scoped Polynomial

/-! ## 1. Cross-chip sequencing, generic over `StagedChip`

Nothing in this section mentions the Nock configuration.  These are the obligations two tables of
one proof impose on each other, stated on the type the deployed chips already run on. -/

section Generic

variable {K : Type*} [Field K] {rounds : ℕ} {C : ChallengeChronology rounds}

/-- **A shared coin obeys BOTH readers' commit-then-sample obligations.**

This is the cross-RAP content that a per-chip obligation cannot state, and it needs no new
carrier: because `rounds` and `chronology` are *type indices* of `StagedChip`, two chips of one
proof already quantify over one coin space, so a coin declared by a column of each is constrained
by both chips' `columns_commit_before_sampling` fields at once.  The two blocks' schedules
therefore constrain each other. -/
theorem shared_coin_commits_before_both_readers
    (T₁ T₂ : StagedChip K rounds C) (j : Fin C.numChallenges)
    {c₁ : Fin T₁.air.numTraceCols} {c₂ : Fin T₂.air.numTraceCols}
    (h₁ : j ∈ T₁.columnChallenges c₁) (h₂ : j ∈ T₂.columnChallenges c₂) :
    (C.sampledAfter j : ℕ) < (T₁.schedule.roundOf c₁ : ℕ)
      ∧ (C.sampledAfter j : ℕ) < (T₂.schedule.roundOf c₂ : ℕ) :=
  ⟨T₁.columns_commit_before_sampling c₁ j h₁, T₂.columns_commit_before_sampling c₂ j h₂⟩

/-- **The pole discipline.**  A coin that compresses or poles a *committed record* must be sampled
at or after the message that follows the commitment of that record — otherwise a prover chooses
the record after seeing the coin.

the paper writes the sequence out for `RAP_prog-IO`: build `IO_prog`, send
`Com(IO_prog)` (`:508`), *then* "Verifier responds with random elements `α, β ∈ 𝕂`" (`:509`), then
build `acc_prog` (`:510`); the paper says why in so many words — "we add a layer of
interaction … in between building `IO_prog` and `acc_prog` that commits to `IO_prog`.  This
suffices to build the multiset and provides the soundness guarantees required."

**`StagedChip.columns_commit_before_sampling` does not imply this.**  That field is an *upper*
bound on the sampling message — the coin must precede the columns that read it.  The pole
discipline is a *lower* bound — the coin must follow the columns of the record it is about.  The
two quantify over different column sets and neither implies the other. -/
def PoleDisciplined (T : StagedChip K rounds C)
    (recordCols : Finset (Fin T.air.numTraceCols))
    (poleCoins : Finset (Fin C.numChallenges)) : Prop :=
  ∀ c ∈ recordCols, ∀ j ∈ poleCoins,
    (T.schedule.roundOf c : ℕ) ≤ (C.sampledAfter j : ℕ)

/-- The discipline is exactly the *negation* of usability at the record columns: a record column
may not be one of the coin's legal readers. -/
theorem poleDisciplined_iff_not_usable (T : StagedChip K rounds C)
    (recordCols : Finset (Fin T.air.numTraceCols))
    (poleCoins : Finset (Fin C.numChallenges)) :
    PoleDisciplined T recordCols poleCoins
      ↔ ∀ c ∈ recordCols, ∀ j ∈ poleCoins,
          ¬ C.usableByColumnOf (T.schedule.roundOf c) j := by
  simp only [PoleDisciplined, ChallengeChronology.usableByColumnOf, not_lt]

/-- **Discipline forces non-declaration.**  Composed with the chip's own field, the pole
discipline says the record columns cannot even *declare* the pole coin — which is the shape
`GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute` states on the declaration axis.
So the two axes meet here rather than being two unrelated facts. -/
theorem poleDisciplined_excludes_declaration {T : StagedChip K rounds C}
    {recordCols : Finset (Fin T.air.numTraceCols)}
    {poleCoins : Finset (Fin C.numChallenges)}
    (h : PoleDisciplined T recordCols poleCoins)
    {c : Fin T.air.numTraceCols} (hc : c ∈ recordCols)
    {j : Fin C.numChallenges} (hj : j ∈ poleCoins) :
    j ∉ T.columnChallenges c :=
  fun hmem => T.commit_then_sample c j hmem (h c hc j hj)

/-- Consequently a disciplined record coin forces its record's columns strictly below any column
that reads it: **a record coin needs a verifier message of its own between the two**.  This is the
general form of the paper third-message argument, proved once. -/
theorem disciplined_record_coin_needs_a_gap {T : StagedChip K rounds C}
    {recordCols : Finset (Fin T.air.numTraceCols)}
    {poleCoins : Finset (Fin C.numChallenges)}
    (h : PoleDisciplined T recordCols poleCoins)
    {rc c : Fin T.air.numTraceCols} (hrc : rc ∈ recordCols)
    {j : Fin C.numChallenges} (hj : j ∈ poleCoins)
    (hread : j ∈ T.columnChallenges c) :
    (T.schedule.roundOf rc : ℕ) < (T.schedule.roundOf c : ℕ) :=
  lt_of_le_of_lt (h rc hrc j hj) (T.columns_commit_before_sampling c j hread)

end Generic

/-! ## 2. The six paper RAPs, as `StagedChip`s of the shipped chronology -/

/-- Which of the two commitment chips hosts a block. -/
inductive Chip
  | compute
  | memory
deriving DecidableEq, Repr

/-- **The six RAPs Theorem 5.4 assembles**.  Three are folded into the compute
chip and three into the memory chip; the folding is `GigaFinite.computeCombinedFiniteAIR` and
`memoryCombinedFiniteAIR`. -/
inductive PaperRap
  | comp
  | walk
  | progIO
  | mem
  | forest
  | memIO
deriving DecidableEq, Repr

/-! ### 2.1 The block AIRs

`numChallenges := 10` is the proof's coin space, as on the combined AIRs (`nc` there); it is inert
for satisfaction, since `airToRAP` never reads it. -/

/-- `RAP_comp`: `computeAIRchained`, coins `α, z, a, b, c` at slots `0…4`.  The
compute table's renaming is the identity, so these constraints are **literally** the first summand
of `computeCombinedFiniteAIR`. -/
def compTableBlockAIR : Reified.AIR where
  numTraceCols := 94
  numChallenges := 10
  numPublic := 0
  constraints := computeAIRchained.constraints

def walkBlockAIR (fC : ℕ → ℕ) : Reified.AIR where
  numTraceCols := 6
  numChallenges := 10
  numPublic := 2
  constraints := walkAIR.constraints.map (fun c => ⟨c.kind, c.expr.remapBlock 0 fC 0⟩)

noncomputable def memTableBlockAIR {K : Type*} [Field K] (fC : ℕ → ℕ) : Reified.AIR where
  numTraceCols := 36
  numChallenges := 10
  numPublic := 0
  constraints := (memoryAIRchained (K := K)).constraints.map (fun c => ⟨c.kind, c.expr.remapBlock 0 fC 0⟩)

/-- `RAP_prog-IO`: the prover-committed finite-field request chip. -/
def progIOBlockAIR (m : ℕ) (fC : ℕ → ℕ) : Reified.AIR where
  numTraceCols := m + 4
  numChallenges := 10
  numPublic := 1
  constraints := (finiteIOProgAIR m).constraints.map (fun c => ⟨c.kind, c.expr.remapBlock 0 fC 0⟩)

/-- `RAP_mem-IO`: the response chip.  Same coins as `RAP_prog-IO` — that is
edge `S1`. -/
def memIOBlockAIR (m : ℕ) (fC : ℕ → ℕ) : Reified.AIR where
  numTraceCols := m + 4
  numChallenges := 10
  numPublic := 1
  constraints := (finiteIOMemAIR m).constraints.map (fun c => ⟨c.kind, c.expr.remapBlock 0 fC 0⟩)

/-- **The compute-table block is the combined AIR's first summand, verbatim.** -/
theorem compTableBlockAIR_is_the_combined_first_block (nc m : ℕ) (fC : ℕ → ℕ) :
    compTableBlockAIR.constraints
      = (computeCombinedFiniteAIR nc m fC).constraints.take
          computeAIRchained.constraints.length := by
  simp [compTableBlockAIR, computeCombinedFiniteAIR]

/-- **And so is the memory-table block**, because its host offsets are zero
(`GigaChips.memTraceOff = 0`, `memPubOff = 0`): the block AIR's constraints are the combined
AIR's first summand as a *term*. -/
theorem memTableBlockAIR_is_the_combined_first_block {K : Type*} [Field K] (fC : ℕ → ℕ) :
    (memTableBlockAIR (K := K) fC).constraints
      = (memoryAIRchained (K := K)).constraints.map
          (fun c => ⟨c.kind, c.expr.remapBlock memTraceOff fC memPubOff⟩) := rfl

/-! ### 2.2 The block schedules: restrictions of the shipped host schedules

Nothing here is a second opinion about when a column is committed: a block column's round is the
host chip's round at the host column, by definition. -/

/-- The host chip's round, read at the block column's host index. -/
def blockRoundOf {W n : ℕ} (host : Fin W → Fin 4) (off : ℕ) (hb : off + n ≤ W) (c : Fin n) :
    Fin 4 :=
  host ⟨(c : ℕ) + off, by have := c.isLt; omega⟩

/-- **A block's round schedule is the host schedule restricted to the block.**  `width` is the
actual fibre cardinality, so `width_eq` is `rfl` and `RoundSchedule.total_width` gives
`n = Σ_r width r` for the block. -/
def blockSchedule {W n : ℕ} (host : Fin W → Fin 4) (off : ℕ) (hb : off + n ≤ W) :
    RoundSchedule n 4 where
  roundOf := blockRoundOf host off hb
  width := fun r => (Finset.univ.filter fun c : Fin n => blockRoundOf host off hb c = r).card
  width_eq := fun _ => rfl

/-- `RAP_comp`: compute columns `0…93`. -/
def compTableSchedule : RoundSchedule 94 4 := blockSchedule finComputeRoundOf4 0 (by norm_num)
/-- `RAP_walk`: compute columns `94…99` (`ComputeChip.walkTraceOff = 94`). -/
def walkSchedule : RoundSchedule 6 4 := blockSchedule finComputeRoundOf4 94 (by norm_num)
/-- `RAP_prog-IO`: compute columns `100…111` (`ComputeChip.ioTraceOff = 100`). -/
def progIOSchedule : RoundSchedule 13 4 := blockSchedule finComputeRoundOf4 100 (by norm_num)
/-- `RAP_mem`: memory columns `0…35` (`GigaChips.memTraceOff = 0`). -/
def memTableSchedule : RoundSchedule 36 4 := blockSchedule finMemRoundOf4 0 (by norm_num)
/-- `Corr:forest`: memory columns `36…41` (`GigaChips.memWalkTraceOff = 36`). -/
def forestSchedule : RoundSchedule 6 4 := blockSchedule finMemRoundOf4 36 (by norm_num)
/-- `RAP_mem-IO`: memory columns `42…54` (`GigaChips.memIoTraceOff = 42`). -/
def memIOSchedule : RoundSchedule 13 4 := blockSchedule finMemRoundOf4 42 (by norm_num)

/-- The block offsets are the shipped ones. -/
theorem block_offsets_eq_shipped :
    ComputeChip.walkTraceOff = 94 ∧ ComputeChip.ioTraceOff = 100
      ∧ memTraceOff = 0 ∧ memWalkTraceOff = 36 ∧ memIoTraceOff = 42 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The three compute blocks tile the shipped compute schedule, round by round.**  This is
strictly more than the column arithmetic `94 + 6 + 13 = 113`: at *every* commitment block the
three blocks' widths add up to `finComputeSchedule4`'s declared `w_RAP(r) = ![11, 89, 11, 2]`. -/
theorem compute_blocks_tile_by_round (r : Fin 4) :
    compTableSchedule.width r + walkSchedule.width r + progIOSchedule.width r
      = finComputeSchedule4.width r := by
  revert r; decide

/-- **The three memory blocks tile the shipped memory schedule, round by round**:
`![10, 27, 16, 2]`. -/
theorem memory_blocks_tile_by_round (r : Fin 4) :
    memTableSchedule.width r + forestSchedule.width r + memIOSchedule.width r
      = finMemorySchedule4.width r := by
  revert r; decide

/-- The column arithmetic, for the record: `94 + 6 + 13 = 113` and `36 + 6 + 13 = 55`. -/
theorem blocks_tile_the_chips : (94 + 6 + 13 : ℕ) = 113 ∧ (36 + 6 + 13 : ℕ) = 55 := ⟨rfl, rfl⟩

/-! ### 2.3 The block declarations

A block declares its own coins, filtered by usability at the column's round.  The filter is what
makes each chip's `columns_commit_before_sampling` a one-line proof shared by all six. -/

/-- The block's coins that a round-`r` column may legally read. -/
def usableSlots (slots : Finset (Fin 10)) (r : Fin 4) : Finset (Fin 10) :=
  slots.filter fun j => (nockSampledAfterIO3 j : ℕ) < (r : ℕ)

/-- The one obligation every block chip below discharges. -/
theorem usableSlots_usable (slots : Finset (Fin 10)) (r : Fin 4) :
    ∀ j ∈ usableSlots slots r, nockChronologyIO3.usableByColumnOf r j :=
  fun _ hj => (Finset.mem_filter.mp hj).2

theorem mem_usableSlots {slots : Finset (Fin 10)} {r : Fin 4} {j : Fin 10} :
    j ∈ usableSlots slots r ↔ j ∈ slots ∧ (nockSampledAfterIO3 j : ℕ) < (r : ℕ) :=
  Finset.mem_filter

/-- `RAP_comp`'s five coins are the proof's slots `0…4`: `α, z, a, b, c`. -/
def compTableSlots : Finset (Fin 10) := {0, 1, 2, 3, 4}
/-- `RAP_walk`'s single coin is the compute walk's index base at slot `5`
(`ComputeChip.walkChalOff`). -/
def walkSlots : Finset (Fin 10) := {5}
/-- `RAP_mem`'s three coins: the shared NPR seed `1`, the internal pole `6` and the internal record
RLC `7` (`GigaChips.memChalMap`). -/
def memTableSlots : Finset (Fin 10) := {1, 6, 7}
/-- `Corr:forest`'s single coin is the timestamp base at slot `0` (`GigaChips.memWalkChalMap`). -/
def forestSlots : Finset (Fin 10) := {0}
/-- The two `RAP_prog-IO` coins of the paper, at the placement's slots. -/
def ioSlots (S : IOPlacement3) : Finset (Fin 10) := {S.slot 0, S.slot 1}

/-- The compute walk's coin map is the shipped `ComputeChip.walkChalOff` shift. -/
def walkChalMapC : ℕ → ℕ := fun i => i + ComputeChip.walkChalOff

theorem walkChalMapC_eq_shipped : walkChalMapC 0 = ComputeChip.walkChalOff := by
  simp [walkChalMapC]

theorem walkSlots_eq_shipped : walkSlots = {(⟨ComputeChip.walkChalOff, by decide⟩ : Fin 10)} := rfl

theorem memTableSlots_eq_shipped_image :
    memTableSlots = {(⟨memChalMap 0, by decide⟩ : Fin 10), ⟨memChalMap 1, by decide⟩,
      ⟨memChalMap 2, by decide⟩} := by decide

theorem forestSlots_eq_shipped_image :
    forestSlots = {(⟨memWalkChalMap 0, by decide⟩ : Fin 10)} := rfl

/-! ### 2.4 The six chips -/

section Chips

variable {L : Type*} [Field L]

/-- **`RAP_comp` as a `StagedChip`.** -/
noncomputable def compTableChip (q : SegmentedRAPParams L) :
    StagedChip L 4 nockChronologyIO3 where
  air := compTableBlockAIR
  params := q
  schedule := compTableSchedule
  columnChallenges := fun c => usableSlots compTableSlots (compTableSchedule.roundOf c)
  columns_commit_before_sampling := fun _ j hj => usableSlots_usable _ _ j hj

/-- **`RAP_walk` as a `StagedChip`.** -/
noncomputable def walkChip (q : SegmentedRAPParams L) : StagedChip L 4 nockChronologyIO3 where
  air := walkBlockAIR walkChalMapC
  params := q
  schedule := walkSchedule
  columnChallenges := fun c => usableSlots walkSlots (walkSchedule.roundOf c)
  columns_commit_before_sampling := fun _ j hj => usableSlots_usable _ _ j hj

/-- **`RAP_prog-IO` as a `StagedChip`.** -/
noncomputable def progIOChip (S : IOPlacement3) (q : SegmentedRAPParams L) :
    StagedChip L 4 nockChronologyIO3 where
  air := progIOBlockAIR 9 S.map
  params := q
  schedule := progIOSchedule
  columnChallenges := fun c => usableSlots (ioSlots S) (progIOSchedule.roundOf c)
  columns_commit_before_sampling := fun _ j hj => usableSlots_usable _ _ j hj

/-- **`RAP_mem` as a `StagedChip`**, with its challenge renaming left free so that §5's bad seed
is *this* definition at a different map. -/
noncomputable def memTableChip (fC : ℕ → ℕ) (slots : Finset (Fin 10))
    (q : SegmentedRAPParams L) : StagedChip L 4 nockChronologyIO3 where
  air := memTableBlockAIR (K := L) fC
  params := q
  schedule := memTableSchedule
  columnChallenges := fun c => usableSlots slots (memTableSchedule.roundOf c)
  columns_commit_before_sampling := fun _ j hj => usableSlots_usable _ _ j hj

/-- **`Corr:forest` as a `StagedChip`.** -/
noncomputable def forestChip (q : SegmentedRAPParams L) : StagedChip L 4 nockChronologyIO3 where
  air := walkBlockAIR memWalkChalMap
  params := q
  schedule := forestSchedule
  columnChallenges := fun c => usableSlots forestSlots (forestSchedule.roundOf c)
  columns_commit_before_sampling := fun _ j hj => usableSlots_usable _ _ j hj

/-- **`RAP_mem-IO` as a `StagedChip`.** -/
noncomputable def memIOChip (S : IOPlacement3) (q : SegmentedRAPParams L) :
    StagedChip L 4 nockChronologyIO3 where
  air := memIOBlockAIR 9 S.map
  params := q
  schedule := memIOSchedule
  columnChallenges := fun c => usableSlots (ioSlots S) (memIOSchedule.roundOf c)
  columns_commit_before_sampling := fun _ j hj => usableSlots_usable _ _ j hj

/-- **The six paper RAPs, in one chip list over one chronology.** -/
noncomputable def paperSixChips (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    ChipList L 4 nockChronologyIO3 :=
  [compTableChip qC, walkChip qC, progIOChip S qC,
    memTableChip memChalMap memTableSlots qM, forestChip qM, memIOChip S qM]

/-- **The cross-RAP sequencing object: a `GigaRAP` whose chips are the six paper RAPs.**

`GigaIOThirdMessage.nockGigaRAPFinite3` is the same chronology with the two *commitment* chips;
this is the same chronology with the six *paper* RAPs.  Both are `GigaRAP`s, so the ordering
machinery — `firstRound_challenge_free`, `commit_then_sample`, the whole of §1 — applies to each
block individually and across blocks. -/
noncomputable def nockPaperSixRAP (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    GigaRAP L where
  rounds := 4
  rounds_pos := by norm_num
  chronology := nockChronologyIO3
  chips := paperSixChips S qC qM

theorem nockPaperSixRAP_chips_length (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    (nockPaperSixRAP S qC qM).chips.length = 6 := rfl

theorem nockPaperSixRAP_chronology (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    (nockPaperSixRAP S qC qM).chronology = nockChronologyIO3 := rfl

/-- Both objects are staged over the **same** chronology term — the six blocks and the two
commitment chips are the same proof. -/
theorem six_and_two_share_the_chronology (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    (nockPaperSixRAP S qC qM).chronology = (nockGigaRAPFinite3 S qC qM).chronology := rfl

end Chips

/-! ### 2.5 The thin adapter

The only data the six chips do not already carry is *which paper RAP a chip is* and *where its
block sits in its host*.  `PaperRapBlock` carries exactly that, plus the coherence field saying
the chip's declaration is the block's slots filtered by usability — which is what lets an edge
stated on `slots` be cashed at a column of the chip. -/

/-- **One paper RAP, placed.**  The `chip` is the production object; `slots` is the block's own
coin set in the proof's coin space; `declares` ties them. -/
structure PaperRapBlock (L : Type*) [Field L] where
  /-- Which of the six. -/
  rap : PaperRap
  /-- Which commitment chip hosts the block. -/
  host : Chip
  /-- The block's column offset inside the host chip. -/
  traceOff : ℕ
  /-- The block's coins, as slots of the proof's ten-coin space. -/
  slots : Finset (Fin 10)
  /-- The block, as a chip of the proof's chronology. -/
  chip : StagedChip L 4 nockChronologyIO3
  /-- The chip declares exactly the block's usable slots. -/
  declares : ∀ c, chip.columnChallenges c = usableSlots slots (chip.schedule.roundOf c)

namespace PaperRapBlock

variable {L : Type*} [Field L]

/-- Membership at a column, unfolded. -/
theorem declares_iff (B : PaperRapBlock L) (c : Fin B.chip.air.numTraceCols) (j : Fin 10) :
    j ∈ B.chip.columnChallenges c
      ↔ j ∈ B.slots ∧ (nockSampledAfterIO3 j : ℕ) < (B.chip.schedule.roundOf c : ℕ) := by
  rw [B.declares c]; exact mem_usableSlots

/-- A block coin is read somewhere iff some column of the block is late enough for it. -/
def Reads (B : PaperRapBlock L) (j : Fin 10) : Prop :=
  ∃ c, j ∈ B.chip.columnChallenges c

/-- **A sharing edge**: one slot of the proof's coin space belongs to two blocks. -/
def Shares (B₁ B₂ : PaperRapBlock L) (j : Fin 10) : Prop := j ∈ B₁.slots ∧ j ∈ B₂.slots

theorem shares_symm {B₁ B₂ : PaperRapBlock L} {j} (h : Shares B₁ B₂ j) : Shares B₂ B₁ j :=
  ⟨h.2, h.1⟩

/-- **A block that draws nothing**: every coin it reads is one of `src`'s.  This is
the paper's "obtained from the computation table's `w_prog-IO` array" as a property, and
the paper's "`e + 1` columns" with no round of its own is its consequence. -/
def Obtains (B src : PaperRapBlock L) : Prop := B.slots ⊆ src.slots

/-- **The cross-RAP obligation, cashed on the adapter.**  A shared coin read by a column of each
block is constrained by *both* chips' `columns_commit_before_sampling` fields.  Nothing is
restated: this is §1's generic theorem at two of the six blocks. -/
theorem shared_coin_binds_both_blocks (B₁ B₂ : PaperRapBlock L) (j : Fin 10)
    {c₁ : Fin B₁.chip.air.numTraceCols} {c₂ : Fin B₂.chip.air.numTraceCols}
    (h₁ : j ∈ B₁.chip.columnChallenges c₁) (h₂ : j ∈ B₂.chip.columnChallenges c₂) :
    (nockSampledAfterIO3 j : ℕ) < (B₁.chip.schedule.roundOf c₁ : ℕ)
      ∧ (nockSampledAfterIO3 j : ℕ) < (B₂.chip.schedule.roundOf c₂ : ℕ) :=
  shared_coin_commits_before_both_readers B₁.chip B₂.chip j h₁ h₂

end PaperRapBlock

section Blocks

variable {L : Type*} [Field L]

/-- `RAP_comp`, placed. -/
noncomputable def blockComp (q : SegmentedRAPParams L) : PaperRapBlock L where
  rap := .comp; host := .compute; traceOff := 0; slots := compTableSlots
  chip := compTableChip q
  declares := fun _ => rfl

/-- `RAP_walk`, placed. -/
noncomputable def blockWalk (q : SegmentedRAPParams L) : PaperRapBlock L where
  rap := .walk; host := .compute; traceOff := 94; slots := walkSlots
  chip := walkChip q
  declares := fun _ => rfl

/-- `RAP_prog-IO`, placed. -/
noncomputable def blockProgIO (S : IOPlacement3) (q : SegmentedRAPParams L) : PaperRapBlock L where
  rap := .progIO; host := .compute; traceOff := 100; slots := ioSlots S
  chip := progIOChip S q
  declares := fun _ => rfl

/-- `RAP_mem`, placed. -/
noncomputable def blockMem (q : SegmentedRAPParams L) : PaperRapBlock L where
  rap := .mem; host := .memory; traceOff := 0; slots := memTableSlots
  chip := memTableChip memChalMap memTableSlots q
  declares := fun _ => rfl

/-- `Corr:forest`, placed. -/
noncomputable def blockForest (q : SegmentedRAPParams L) : PaperRapBlock L where
  rap := .forest; host := .memory; traceOff := 35; slots := forestSlots
  chip := forestChip q
  declares := fun _ => rfl

/-- `RAP_mem-IO`, placed. -/
noncomputable def blockMemIO (S : IOPlacement3) (q : SegmentedRAPParams L) : PaperRapBlock L where
  rap := .memIO; host := .memory; traceOff := 41; slots := ioSlots S
  chip := memIOChip S q
  declares := fun _ => rfl

/-- The six, indexed. -/
noncomputable def nockBlocks (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    PaperRap → PaperRapBlock L
  | .comp => blockComp qC
  | .walk => blockWalk qC
  | .progIO => blockProgIO S qC
  | .mem => blockMem qM
  | .forest => blockForest qM
  | .memIO => blockMemIO S qM

/-- Every placed block's chip is one of the six chips of `nockPaperSixRAP`. -/
theorem nockBlocks_chip_mem (S : IOPlacement3) (qC qM : SegmentedRAPParams L) (r : PaperRap) :
    (nockBlocks S qC qM r).chip ∈ (nockPaperSixRAP S qC qM).chips := by
  cases r
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))))

/-- The hosts, as the paper assembles them: three blocks per commitment chip. -/
theorem hosts (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    (nockBlocks S qC qM .comp).host = .compute ∧ (nockBlocks S qC qM .walk).host = .compute
      ∧ (nockBlocks S qC qM .progIO).host = .compute
      ∧ (nockBlocks S qC qM .mem).host = .memory
      ∧ (nockBlocks S qC qM .forest).host = .memory
      ∧ (nockBlocks S qC qM .memIO).host = .memory :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Blocks

/-! A block's rounds are the host's rounds at the host's columns, and a block's declaration is
contained in the shipped chip's declaration at the same column.  So a change to a shipped chip
breaks a theorem here rather than silently diverging. -/

/-- The compute blocks' rounds are `finComputeRoundOf4` at the host column. -/
theorem compute_block_rounds_eq_shipped :
    (∀ c : Fin 94, (compTableSchedule.roundOf c : ℕ)
        = (finComputeRoundOf4 ⟨(c : ℕ), by omega⟩ : ℕ))
      ∧ (∀ c : Fin 6, (walkSchedule.roundOf c : ℕ)
        = (finComputeRoundOf4 ⟨(c : ℕ) + 94, by omega⟩ : ℕ))
      ∧ (∀ c : Fin 13, (progIOSchedule.roundOf c : ℕ)
        = (finComputeRoundOf4 ⟨(c : ℕ) + 100, by omega⟩ : ℕ)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The memory blocks' rounds are `finMemRoundOf4` at the host column. -/
theorem memory_block_rounds_eq_shipped :
    (∀ c : Fin 36, (memTableSchedule.roundOf c : ℕ)
        = (finMemRoundOf4 ⟨(c : ℕ), by omega⟩ : ℕ))
      ∧ (∀ c : Fin 6, (forestSchedule.roundOf c : ℕ)
        = (finMemRoundOf4 ⟨(c : ℕ) + 36, by omega⟩ : ℕ))
      ∧ (∀ c : Fin 13, (memIOSchedule.roundOf c : ℕ)
        = (finMemRoundOf4 ⟨(c : ℕ) + 42, by omega⟩ : ℕ)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Both IO coins ride the third verifier message, whatever the placement. -/
theorem ioSlots_sampledAfter_two (S : IOPlacement3) {j : Fin 10} (hj : j ∈ ioSlots S) :
    (nockSampledAfterIO3 j : ℕ) = 2 := by
  simp only [ioSlots, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact slot_sampledAfter_two S 0
  · exact slot_sampledAfter_two S 1

/-- The shipped compute declaration, round by round. -/
theorem computeRoundChalOf4_values (S : IOPlacement3) :
    finComputeRoundChalOf4 S 1 = ({1, 2, 3, 4} : Finset (Fin 10))
      ∧ finComputeRoundChalOf4 S 2 = ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) :=
  ⟨rfl, rfl⟩

/-- The shipped memory declaration, round by round. -/
theorem memRoundChalOf4_values (S : IOPlacement3) :
    finMemRoundChalOf4 S 1 = ({1} : Finset (Fin 10))
      ∧ finMemRoundChalOf4 S 2 = ({0, 1, 6, 7} : Finset (Fin 10)) :=
  ⟨rfl, rfl⟩

theorem compute_round_one_slots :
    ∀ j : Fin 10, j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) →
      (nockSampledAfterIO3 j : ℕ) < 1 → j ∈ ({1, 2, 3, 4} : Finset (Fin 10)) := by decide

theorem memory_round_one_slots :
    ∀ j : Fin 10, j ∈ ({0, 1, 6, 7} : Finset (Fin 10)) →
      (nockSampledAfterIO3 j : ℕ) < 1 → j ∈ ({1} : Finset (Fin 10)) := by decide

/-- **Each compute block declares no more than the shipped compute chip does at the same column.**
The shipped declaration `finComputeRoundChalOf4` is not saturated (`SaturatedDeclaration`), so the
containment is the right direction and the right statement. -/
theorem compute_declaration_refines (S : IOPlacement3) (r : Fin 4) (slots : Finset (Fin 10))
    (hsub : slots ⊆ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10))) :
    usableSlots slots r ⊆ finComputeRoundChalOf4 S r := by
  intro j hj
  obtain ⟨hjs, hlt⟩ := mem_usableSlots.mp hj
  have hj6 : j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) := hsub hjs
  unfold finComputeRoundChalOf4
  by_cases h0 : (r : ℕ) = 0
  · rw [h0] at hlt; exact absurd hlt (Nat.not_lt_zero _)
  rw [if_neg h0]
  by_cases h1 : (r : ℕ) = 1
  · rw [if_pos h1]
    rw [h1] at hlt
    exact compute_round_one_slots j hj6 hlt
  rw [if_neg h1]
  by_cases h2 : (r : ℕ) = 2
  · rw [if_pos h2]; exact hj6
  rw [if_neg h2]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj6)

/-- The memory twin. -/
theorem memory_declaration_refines (S : IOPlacement3) (r : Fin 4) (slots : Finset (Fin 10))
    (hsub : slots ⊆ ({0, 1, 6, 7} : Finset (Fin 10))) :
    usableSlots slots r ⊆ finMemRoundChalOf4 S r := by
  intro j hj
  obtain ⟨hjs, hlt⟩ := mem_usableSlots.mp hj
  have hj6 : j ∈ ({0, 1, 6, 7} : Finset (Fin 10)) := hsub hjs
  unfold finMemRoundChalOf4
  by_cases h0 : (r : ℕ) = 0
  · rw [h0] at hlt; exact absurd hlt (Nat.not_lt_zero _)
  rw [if_neg h0]
  by_cases h1 : (r : ℕ) = 1
  · rw [if_pos h1]
    rw [h1] at hlt
    exact memory_round_one_slots j hj6 hlt
  rw [if_neg h1]
  by_cases h2 : (r : ℕ) = 2
  · rw [if_pos h2]; exact hj6
  rw [if_neg h2]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj6)

theorem compute_block_declarations_refine_shipped (S : IOPlacement3) (r : Fin 4) :
    usableSlots compTableSlots r ⊆ finComputeRoundChalOf4 S r
      ∧ usableSlots walkSlots r ⊆ finComputeRoundChalOf4 S r :=
  ⟨compute_declaration_refines S r compTableSlots (by decide),
    compute_declaration_refines S r walkSlots (by decide)⟩

theorem memory_block_declarations_refine_shipped (S : IOPlacement3) (r : Fin 4) :
    usableSlots memTableSlots r ⊆ finMemRoundChalOf4 S r
      ∧ usableSlots forestSlots r ⊆ finMemRoundChalOf4 S r :=
  ⟨memory_declaration_refines S r memTableSlots (by decide),
    memory_declaration_refines S r forestSlots (by decide)⟩

/-- The two IO blocks' declarations are contained in the shipped chips' too — here the slots are
the placement's, so the statement is about `S` and is proved from `IOPlacement3.third_message`
rather than by `decide`. -/
theorem io_declaration_refines_compute (S : IOPlacement3) (r : Fin 4) :
    usableSlots (ioSlots S) r ⊆ finComputeRoundChalOf4 S r := by
  intro j hj
  obtain ⟨hjs, hlt⟩ := mem_usableSlots.mp hj
  have h2 : (nockSampledAfterIO3 j : ℕ) = 2 := ioSlots_sampledAfter_two S hjs
  have h3 : (r : ℕ) = 3 := by have := r.isLt; omega
  unfold finComputeRoundChalOf4
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp only [ioSlots, Finset.mem_insert, Finset.mem_singleton] at hjs
  rcases hjs with rfl | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem io_declaration_refines_memory (S : IOPlacement3) (r : Fin 4) :
    usableSlots (ioSlots S) r ⊆ finMemRoundChalOf4 S r := by
  intro j hj
  obtain ⟨hjs, hlt⟩ := mem_usableSlots.mp hj
  have h2 : (nockSampledAfterIO3 j : ℕ) = 2 := ioSlots_sampledAfter_two S hjs
  have h3 : (r : ℕ) = 3 := by have := r.isLt; omega
  unfold finMemRoundChalOf4
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp only [ioSlots, Finset.mem_insert, Finset.mem_singleton] at hjs
  rcases hjs with rfl | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem io_block_declarations_refine_shipped (S : IOPlacement3) (r : Fin 4) :
    usableSlots (ioSlots S) r ⊆ finComputeRoundChalOf4 S r
      ∧ usableSlots (ioSlots S) r ⊆ finMemRoundChalOf4 S r :=
  ⟨io_declaration_refines_compute S r, io_declaration_refines_memory S r⟩

/-! ## 3. The seven sharing edges, as theorems about the six chips -/

section Edges

variable {L : Type*} [Field L]

/-- **S1.**  `RAP_mem-IO` draws nothing: **every** coin of the
block is `RAP_prog-IO`'s.  The two blocks sit in different commitment chips, so this is a genuinely
cross-chip edge. -/
theorem s1_memIO_obtains_from_progIO (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    (blockMemIO S qM).Obtains (blockProgIO S qC)
      ∧ (blockMemIO S qM).host ≠ (blockProgIO S qC).host := by
  refine ⟨fun _ h => h, ?_⟩
  show Chip.memory ≠ Chip.compute
  decide

/-- Both IO blocks' declarations are literally the same function of the round, so the chip-level
reading of S1 is `rfl`: the memory chip's IO block declares exactly what the compute chip's does. -/
theorem memIOChip_columnChallenges (S : IOPlacement3) (q : SegmentedRAPParams L)
    (c : Fin (memIOChip S q).air.numTraceCols) :
    (memIOChip S q).columnChallenges c = usableSlots (ioSlots S) (memIOSchedule.roundOf c) := rfl

theorem progIOChip_columnChallenges (S : IOPlacement3) (q : SegmentedRAPParams L)
    (c : Fin (progIOChip S q).air.numTraceCols) :
    (progIOChip S q).columnChallenges c = usableSlots (ioSlots S) (progIOSchedule.roundOf c) := rfl

/-- S1 at the two accumulator columns: `acc_mem` (memory `41`, block column `0`) and `acc_prog`
(compute `100`, block column `0`) both declare the shared pole coin, both in the fourth block —
the paper after the paper. -/
theorem s1_declared_at_both_accumulators (S : IOPlacement3) :
    S.slot 1 ∈ usableSlots (ioSlots S) (memIOSchedule.roundOf 0)
      ∧ S.slot 1 ∈ usableSlots (ioSlots S) (progIOSchedule.roundOf 0) := by
  have hslot : S.slot 1 ∈ ioSlots S := by simp [ioSlots]
  have h2 : (nockSampledAfterIO3 (S.slot 1) : ℕ) = 2 := slot_sampledAfter_two S 1
  have hm : ((memIOSchedule.roundOf 0 : Fin 4) : ℕ) = 3 := by decide
  have hp : ((progIOSchedule.roundOf 0 : Fin 4) : ℕ) = 3 := by decide
  exact ⟨mem_usableSlots.mpr ⟨hslot, by omega⟩, mem_usableSlots.mpr ⟨hslot, by omega⟩⟩

/-- **S2.**  The memory forest walk's index base *is* the compute
table's timestamp base: slot `0` belongs to both blocks.  This is
`TemplateRawJointSoundness.sampledCoordinates`' `cfg.challenges.α = alphaM ω` at the chronology
layer. -/
theorem s2_timestamp_base_shared (qC qM : SegmentedRAPParams L) :
    (blockComp qC).Shares (blockForest qM) 0 := by
  refine ⟨?_, ?_⟩
  · show (0 : Fin 10) ∈ compTableSlots
    decide
  · show (0 : Fin 10) ∈ forestSlots
    decide

/-- **S3.**  Both tables fingerprint at one NPR seed: slot `1` belongs
to `RAP_comp` and to `RAP_mem`.  This is what `GigaChips.memChalMap 0 = 1` does, and
`GigaChips.seed_at_later_message_breaks_chip` is its teeth. -/
theorem s3_npr_seed_shared (qC qM : SegmentedRAPParams L) :
    (blockComp qC).Shares (blockMem qM) 1 := by
  refine ⟨?_, ?_⟩
  · show (1 : Fin 10) ∈ compTableSlots
    decide
  · show (1 : Fin 10) ∈ memTableSlots
    decide

/-- S3 at genuine columns of the two blocks: compute column `20` and memory column `4` are both
round-`1` fingerprint columns declaring the seed, so the seed is bound by **both** blocks'
commit-then-sample obligations (§1's `shared_coin_commits_before_both_readers`). -/
theorem s3_binds_both_blocks :
    (1 : Fin 10) ∈ usableSlots compTableSlots (compTableSchedule.roundOf 20)
      ∧ (1 : Fin 10) ∈ usableSlots memTableSlots (memTableSchedule.roundOf 4)
      ∧ (nockSampledAfterIO3 1 : ℕ) < (compTableSchedule.roundOf 20 : ℕ)
      ∧ (nockSampledAfterIO3 1 : ℕ) < (memTableSchedule.roundOf 4 : ℕ) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **S4.**  The two walks share the node-label RLC `γ` — and at the
*block* layer there is nothing to state, because `Trans.walkAIR` carries `numChallenges = 1`: the
node RLC is applied outside the committed AIR, by `RawVerifier.computeNodeVal`/`memoryNodeVal`.
So S4's witness stays `JointCoins.compute_memory_shared_gamma`, and the honest statement here is
that neither walk block has a second coin to state it on. -/
theorem s4_has_no_block_level_witness (qC qM : SegmentedRAPParams L) :
    walkAIR.numChallenges = 1 ∧ (blockWalk qC).slots.card = 1
      ∧ (blockForest qM).slots.card = 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · show walkSlots.card = 1
    decide
  · show forestSlots.card = 1
    decide

/-- **S5 — the named residual.**  The two walk index bases are
**not** shared: `RAP_walk` reads slot `5`, `Corr:forest` reads slot `0`.  This is
`PlusIOSegmentedRAP.computeWalkParams_independent_memoryWalkAlpha` at the chronology layer; §8
argues it is a correct reading of the paper rather than a defect. -/
theorem s5_walk_bases_are_not_shared (qC qM : SegmentedRAPParams L) :
    ¬ (blockWalk qC).Shares (blockForest qM) 5
      ∧ ¬ (blockWalk qC).Shares (blockForest qM) 0 := by
  constructor
  · rintro ⟨-, h⟩
    have h' : (5 : Fin 10) ∈ forestSlots := h
    revert h'; decide
  · rintro ⟨h, -⟩
    have h' : (0 : Fin 10) ∈ walkSlots := h
    revert h'; decide

/-- **S6.**  The external `RAP_prog-IO` pole and the memory table's
internal `intermediate` pole are **different coins** — in the paper (two `β`s), in the deployed
client (`bet` vs `gam`) and here (slots `6, 7` against the placement's two).

The proof is not `decide`: it is the *chronology* that separates them.  Every memory-table coin
rides message `0` or `1`, every IO coin rides message `2`. -/
theorem memTableSlots_not_third_message :
    ∀ j : Fin 10, j ∈ memTableSlots → (nockSampledAfterIO3 j : ℕ) ≠ 2 := by decide

theorem s6_the_two_poles_are_different_coins (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    ∀ j ∈ (blockMem qM).slots, j ∉ (blockProgIO S qC).slots := by
  intro j hj hmem
  have hj' : j ∈ memTableSlots := hj
  have hmem' : j ∈ ioSlots S := hmem
  exact memTableSlots_not_third_message j hj' (ioSlots_sampledAfter_two S hmem')

/-- **S7.**  The deployed client reuses `a, b, c` as the IO root
fingerprint packing; this tree does not — neither IO block's slots meet `{2, 3, 4}`, and again the
reason is the chronology: `a, b, c` ride message `0`. -/
theorem abc_not_third_message :
    ∀ j : Fin 10, j ∈ ({2, 3, 4} : Finset (Fin 10)) → (nockSampledAfterIO3 j : ℕ) ≠ 2 := by decide

theorem s7_abc_not_reused_by_the_io_blocks (S : IOPlacement3) (qC : SegmentedRAPParams L) :
    ∀ j ∈ (blockProgIO S qC).slots, j ∉ ({2, 3, 4} : Finset (Fin 10)) := by
  intro j hj habc
  have hj' : j ∈ ioSlots S := hj
  exact abc_not_third_message j habc (ioSlots_sampledAfter_two S hj')

/-- **The edge ledger.** -/
theorem edge_ledger (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    (blockMemIO S qM).Obtains (blockProgIO S qC)
      ∧ (blockComp qC).Shares (blockForest qM) 0
      ∧ (blockComp qC).Shares (blockMem qM) 1
      ∧ (walkAIR.numChallenges = 1 ∧ (blockForest qM).slots.card = 1)
      ∧ ¬ (blockWalk qC).Shares (blockForest qM) 5
      ∧ (∀ j ∈ (blockMem qM).slots, j ∉ (blockProgIO S qC).slots)
      ∧ (∀ j ∈ (blockProgIO S qC).slots, j ∉ ({2, 3, 4} : Finset (Fin 10))) :=
  ⟨(s1_memIO_obtains_from_progIO S qC qM).1, s2_timestamp_base_shared qC qM,
    s3_npr_seed_shared qC qM,
    ⟨rfl, (s4_has_no_block_level_witness qC qM).2.2⟩,
    (s5_walk_bases_are_not_shared qC qM).1,
    s6_the_two_poles_are_different_coins S qC qM,
    s7_abc_not_reused_by_the_io_blocks S qC⟩

end Edges

/-! ## 4. The value layer

A shared *slot* is not a shared *value*.  `Staged.GigaRAP` stores one chronology, but each chip
carries its own `SegmentedRAPParams`, whose `chalVal` is per chip; `GigaChips.chipsShareCoins`
states the agreement as a free-standing `Prop` that no structure requires.  So the slot equalities
of §3 are exactly half of each sharing edge. -/

/-- The two chips' challenge valuations agree on the whole coin space — `prover.hoon:168`/`:212`
/`:213`'s one global draw welded into one list and handed to every table. -/
def CoinsAgree {K : Type*} [Field K] (qC qM : SegmentedRAPParams K) : Prop :=
  ∀ j : Fin 10, qM.chalVal (j : ℕ) = qC.chalVal (j : ℕ)

/-- **The bridge.**  A shared slot gives a shared *value* only under `CoinsAgree`. -/
theorem shared_slot_same_value {K : Type*} [Field K] {qC qM : SegmentedRAPParams K}
    (hag : CoinsAgree qC qM) (j : Fin 10) :
    qM.chalVal (j : ℕ) = qC.chalVal (j : ℕ) := hag j

/-- **And the hypothesis is not removable.**  Two valuations may agree on a shared slot's *index*
and disagree on its *value*; nothing in `StagedChip`, and nothing in `Staged.GigaRAP`, rules that
out.  This is why `GigaChips.chipsShareCoins` has to be carried as a hypothesis at every theorem
that spends a sharing edge. -/
theorem sharing_a_slot_alone_does_not_share_a_value {K : Type*} [Field K] (j : Fin 10) :
    ∃ vC vM : ℕ → K, vM (j : ℕ) ≠ vC (j : ℕ) :=
  ⟨fun _ => 0, fun _ => 1, one_ne_zero⟩

/-- `GigaChips.chipsShareCoins` **is** `CoinsAgree` on the eight slots the two shipped chips
share. -/
theorem chipsShareCoins_is_CoinsAgree {K : Type*} [Field K]
    (qC qM : SegmentedRAPParams K) (h : GigaChips.chipsShareCoins qC qM) :
    ∀ j : Fin 8, qM.chalVal (j : ℕ) = qC.chalVal (j : ℕ) := fun j => h j

/-! ## 5. Why the object is needed: local obligations do not imply the edges

The failure mode a per-chip obligation cannot see, exhibited on the production type. -/

section BadSeed

variable {L : Type*} [Field L]

/-- A variant of `RAP_mem`'s challenge renaming whose NPR-seed coin is remapped from slot `1` to
slot `3` — the equality coefficient `a`, sampled at the *same* verifier message and therefore just
as legal for a round-`1` column. -/
def memChalMapBadSeed : ℕ → ℕ
  | 0 => 3
  | 1 => 6
  | 2 => 7
  | _ => 0

/-- Its slot set. -/
def memTableSlotsBadSeed : Finset (Fin 10) := {3, 6, 7}

/-- **The counterexample is a genuine `StagedChip`.**  Its AIR is `memTableBlockAIR` at the bad
map, so the constraints really do read slot `3`; its schedule is the shipped memory schedule; and
`columns_commit_before_sampling` is discharged by the same one-line proof as the honest block —
because it is true. -/
noncomputable def memTableChipBadSeed (q : SegmentedRAPParams L) :
    StagedChip L 4 nockChronologyIO3 :=
  memTableChip memChalMapBadSeed memTableSlotsBadSeed q

/-- The bad block, placed. -/
noncomputable def blockMemBadSeed (q : SegmentedRAPParams L) : PaperRapBlock L where
  rap := .mem; host := .memory; traceOff := 0; slots := memTableSlotsBadSeed
  chip := memTableChipBadSeed q
  declares := fun _ => rfl

/-- **Every local obligation still holds and `S3` is false.**

The chip's own `columns_commit_before_sampling` is a *field* of the object above, so it is
discharged by construction; the schedules, the widths and the host chip are untouched; and yet the
two tables now fingerprint at *different* NPR seeds — which the paper's global `NMR^{α,β}`
forbids and which **no within-chip theorem mentions**.  This is the gap the cross-RAP layer
closes, and it is why per-RAP ordering is not enough. -/
theorem bad_seed_keeps_every_local_obligation (qC qM : SegmentedRAPParams L) :
    (∀ c, ∀ j ∈ (memTableChipBadSeed qM).columnChallenges c,
        nockChronologyIO3.usableByColumnOf ((memTableChipBadSeed qM).schedule.roundOf c) j)
      ∧ (memTableChipBadSeed qM).schedule = (memTableChip memChalMap memTableSlots qM).schedule
      ∧ ¬ (blockComp qC).Shares (blockMemBadSeed qM) 1 := by
  refine ⟨(memTableChipBadSeed qM).columns_commit_before_sampling, rfl, ?_⟩
  rintro ⟨-, h⟩
  have h' : (1 : Fin 10) ∈ memTableSlotsBadSeed := h
  revert h'
  decide

/-- And the break is invisible to the **chronology**: the moved coin rides the same message as the
one it replaced, so no sampling-order fact changes anywhere in the proof. -/
theorem bad_seed_is_invisible_to_the_chronology :
    nockSampledAfterIO3 3 = nockSampledAfterIO3 1
      ∧ memChalMapBadSeed 0 ≠ memChalMap 0 := by
  refine ⟨by decide, by decide⟩

/-- The bad chip is a legal member of a six-block proof: swapping it in leaves a `GigaRAP`. -/
noncomputable def paperSixChipsBadSeed (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    GigaRAP L where
  rounds := 4
  rounds_pos := by norm_num
  chronology := nockChronologyIO3
  chips := [compTableChip qC, walkChip qC, progIOChip S qC,
    memTableChipBadSeed qM, forestChip qM, memIOChip S qM]

end BadSeed

/-! ## 6. The pole discipline, measured on the shipped chips

§1's `PoleDisciplined` is a predicate on a `StagedChip`, so it can be — and is — evaluated at
`GigaIOThirdMessage.computeChip3` and `memoryChip3` themselves, not at a model of them. -/

section Poles

variable {L : Type*} [Field L]

/-- `IO_prog`'s record columns: the two multiplicity columns and the eight record coordinates,
`102 … 111`, the timestamp included (the paper's `Com(IO_prog)`). -/
def progIORecordCols : Finset (Fin 113) :=
  {102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112}

/-- `IO_mem`'s record columns, `44 … 54`. -/
def memIORecordCols : Finset (Fin 55) := {44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54}

/-- The memory **table**'s record columns: `mem_record = ((mem_root, mem_child), axis, timestamp)` is columns `23…28` (the two fingerprint triples), `29` (`mem.axis`) and `30`
(the timestamp). -/
def memRecordCols : Finset (Fin 55) := {23, 24, 25, 26, 27, 28, 29, 30}

/-- The memory table's internal `intermediate` coins: the pole `β` (slot `6`) and the record RLC
`γ` (slot `7`) of the paper. -/
def memInternalPoleCoins : Finset (Fin 10) := {6, 7}

theorem progIORecordCols_ge (c : Fin 113) (hc : c ∈ progIORecordCols) : (102 : ℕ) ≤ (c : ℕ) := by
  revert hc; revert c; decide

theorem memIORecordCols_ge (c : Fin 55) (hc : c ∈ memIORecordCols) : (44 : ℕ) ≤ (c : ℕ) := by
  revert hc; revert c; decide

theorem memRecordCols_round_le_two (c : Fin 55) (hc : c ∈ memRecordCols) :
    (finMemRoundOf4 c : ℕ) ≤ 2 := by
  revert hc; revert c; decide

/-- **The positive control.**  Both external IO blocks satisfy the discipline: their record
columns are committed in round `2` and their coins ride message `2`.  *That is exactly what the
third message bought* — the same fact
`GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute` records on the declaration
axis, now on the sampling axis. -/
theorem external_prog_io_pole_is_disciplined (S : IOPlacement3) (q : SegmentedRAPParams L) :
    PoleDisciplined (computeChip3 S q) progIORecordCols (ioSlots S) := by
  intro c hc j hj
  have hrw : ((computeChip3 S q).schedule.roundOf c : ℕ) = (finComputeRoundOf4 c : ℕ) := rfl
  have hle : (finComputeRoundOf4 c : ℕ) ≤ 2 :=
    computeRoundOf4_le_two c (progIORecordCols_ge c hc)
  have h2 : (nockChronologyIO3.sampledAfter j : ℕ) = 2 := ioSlots_sampledAfter_two S hj
  omega

/-- The memory twin. -/
theorem external_mem_io_pole_is_disciplined (S : IOPlacement3) (q : SegmentedRAPParams L) :
    PoleDisciplined (memoryChip3 S q) memIORecordCols (ioSlots S) := by
  intro c hc j hj
  have hrw : ((memoryChip3 S q).schedule.roundOf c : ℕ) = (finMemRoundOf4 c : ℕ) := rfl
  have hle : (finMemRoundOf4 c : ℕ) ≤ 2 := memRoundOf4_le_two c (memIORecordCols_ge c hc)
  have h2 : (nockChronologyIO3.sampledAfter j : ℕ) = 2 := ioSlots_sampledAfter_two S hj
  omega

theorem memRecordCols_has_the_timestamp : (⟨30, by norm_num⟩ : Fin 55) ∈ memRecordCols := by
  decide

theorem memInternalPoleCoins_has_beta : (⟨6, by norm_num⟩ : Fin 10) ∈ memInternalPoleCoins := by
  decide

/-- **The finding, on the shipped memory chip.**  The memory table's internal pole `β` (slot `6`)
and record RLC `γ` (slot `7`) ride message `1`, while the record they compress is not complete
until round `2`: its timestamp column is memory column `30` and `finMemRoundOf4 30 = 2`.  So a prover would see both
coins *before* committing the timestamp. -/
theorem internal_pole_violates_the_discipline (S : IOPlacement3) (q : SegmentedRAPParams L) :
    ¬ PoleDisciplined (memoryChip3 S q) memRecordCols memInternalPoleCoins := by
  intro h
  have hcol : (⟨30, by norm_num⟩ : Fin 55) ∈ memRecordCols := memRecordCols_has_the_timestamp
  have hcoin : (⟨6, by norm_num⟩ : Fin 10) ∈ memInternalPoleCoins := memInternalPoleCoins_has_beta
  have hkey := h ⟨30, by norm_num⟩ hcol ⟨6, by norm_num⟩ hcoin
  have hrw : ((memoryChip3 S q).schedule.roundOf ⟨30, by norm_num⟩ : ℕ)
      = (finMemRoundOf4 ⟨30, by norm_num⟩ : ℕ) := rfl
  have hrw2 : (nockChronologyIO3.sampledAfter ⟨6, by norm_num⟩ : ℕ)
      = (nockSampledAfterIO3 ⟨6, by norm_num⟩ : ℕ) := rfl
  have h30 : (finMemRoundOf4 ⟨30, by norm_num⟩ : ℕ) = 2 := by decide
  have h6 : (nockSampledAfterIO3 ⟨6, by norm_num⟩ : ℕ) = 1 := by decide
  omega

/-- The two numbers the finding turns on, separately. -/
theorem mem_internal_shipped_rounds :
    (finMemRoundOf4 30 : ℕ) = 2 ∧ (finMemRoundOf4 31 : ℕ) = 2 ∧ (finMemRoundOf4 32 : ℕ) = 2
      ∧ (nockSampledAfterIO3 6 : ℕ) = 1 ∧ (nockSampledAfterIO3 7 : ℕ) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **The two obligations are independent, and here is the witness.**  The shipped memory chip
discharges `columns_commit_before_sampling` — it is a field of `memoryChip3` — and fails
`PoleDisciplined`.  So the pole discipline is not a consequence of the commit-then-sample
machinery; it is a second, opposite bound. -/
theorem pole_discipline_is_not_implied_by_commit_before_sampling
    (S : IOPlacement3) (q : SegmentedRAPParams L) :
    (∀ c, ∀ j ∈ (memoryChip3 S q).columnChallenges c,
        nockChronologyIO3.usableByColumnOf ((memoryChip3 S q).schedule.roundOf c) j)
      ∧ ¬ PoleDisciplined (memoryChip3 S q) memRecordCols memInternalPoleCoins :=
  ⟨(memoryChip3 S q).columns_commit_before_sampling,
    internal_pole_violates_the_discipline S q⟩

/-- **This is not unsoundness in the shipped tree**, and the module says so.
`ChallengeVector.β` and `.γ` are the constant `0` at every configuration this tree ships, so the
exclusion is the deterministic fixed-point test
`PairedRecordCountedEvent.interCoins_logDeriv_is_a_fixed_point_test`, not a sampled-pole argument.
The discipline is the obligation that would have to be discharged **if the coin were sampled** —
which §7 discharges, on its own objects. -/
theorem discipline_is_conditional_on_sampling :
    (finMemRoundOf4 30 : ℕ) = 2 ∧ (nockSampledAfterIO3 6 : ℕ) = 1 := ⟨by decide, by decide⟩

end Poles

/-! ## 7. The repair, as a real chip: no fourth verifier message

The two internal coins move to the **existing** third message (index `2`), the one
`GigaIOThirdMessage.nockChronologyIO3` already introduces for the `RAP_prog-IO` pair, and the
memory table's `intermediate` columns `31, 32, 33` move from the mega-ext block to the fourth
block, joining `acc_mem` (`41`) and its reciprocal (`42`).  That is the *whole* change: no coin is
added, no message is added, no column is added.

The predecessor of this module could only *name* the obligation this section discharges.  Here
`memoryChip5` is a `StagedChip`, so its `columns_commit_before_sampling` is discharged by
construction and `finMemorySchedule5.width_eq` is checked by `decide`. -/

/-- The repaired chronology: `![1,0,0,0,0,1,2,2,2,2]`. -/
def poleSampledAfter : Fin 10 → Fin 4 := ![1, 0, 0, 0, 0, 1, 2, 2, 2, 2]

/-- **The repaired chronology as a `ChallengeChronology`** — still four commitment blocks, still
three verifier messages. -/
def nockChronologyPole : ChallengeChronology 4 where
  numChallenges := 10
  sampledAfter := poleSampledAfter

@[simp] theorem pole_numChallenges : nockChronologyPole.numChallenges = 10 := rfl

/-- **No coin moves except the two internal ones, and they move later** — the exact analogue of
`GigaIOThirdMessage.io3_restricts`. -/
theorem pole_repair_restricts (j : Fin 10) (h6 : j ≠ 6) (h7 : j ≠ 7) :
    (poleSampledAfter j : ℕ) = (nockSampledAfterIO3 j : ℕ) := by
  revert h6 h7; revert j; decide

/-- The two that move, move from message `1` to message `2`. -/
theorem pole_repair_moves_exactly_two :
    (nockSampledAfterIO3 6 : ℕ) = 1 ∧ (nockSampledAfterIO3 7 : ℕ) = 1
      ∧ (poleSampledAfter 6 : ℕ) = 2 ∧ (poleSampledAfter 7 : ℕ) = 2 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **No fourth verifier message is needed.** -/
theorem pole_repair_needs_no_fourth_message :
    (∀ j : Fin 10, (poleSampledAfter j : ℕ) < 3)
      ∧ (poleSampledAfter 8 : ℕ) = (nockSampledAfterIO3 8 : ℕ)
      ∧ (poleSampledAfter 9 : ℕ) = (nockSampledAfterIO3 9 : ℕ) := by
  refine ⟨?_, by decide, by decide⟩
  intro j; revert j; decide

theorem poleSA_slot_two (S : IOPlacement3) (i : Fin 2) :
    (poleSampledAfter (S.slot i) : ℕ) = 2 := by
  have h := S.third_message i
  revert h
  generalize S.slot i = s
  revert s
  decide

/-- **But the column split is forced.**  Leave the `intermediate` columns in the mega-ext block
(round `2`) while moving the coins to message `2`, and commit-then-sample becomes **false**: a
round-`2` column would read a coin sent at round `2`.  So the repair is two moves, not one. -/
theorem pole_repair_needs_the_column_split :
    ¬ ((poleSampledAfter 6 : ℕ) < (finMemRoundOf4 31 : ℕ)) := by decide

/-- The memory columns that move to the fourth block: the `intermediate` pair `31, 32`, the free
inverse witness `33`, and the two mem-IO coin columns that were already there. -/
def finMemIoCoinCols5 : List ℕ := [31, 32, 33, 42, 43]

/-- The repaired memory round assignment. -/
def finMemRoundOf5 (c : Fin 55) : Fin 4 :=
  if (c : ℕ) ∈ finMemBaseCols then 0
  else if (c : ℕ) ∈ finMemIoCoinCols5 then 3
  else if (c : ℕ) ∈ finMemMegaExtCols then 2 else 1

/-- **`w_RAP = ![10, 27, 13, 5]`**; `width_eq` is a field, so these are the actual
fibre cardinalities.  The **total is unchanged** at `55`, so no column is added and
the paper's `61·e + 13` does not move: the repair is a re-blocking, not a widening. -/
def finMemorySchedule5 : RoundSchedule 55 4 where
  roundOf := finMemRoundOf5
  width := ![10, 27, 13, 5]
  width_eq := by decide

theorem finMemorySchedule5_total : (55 : ℕ) = ∑ r, finMemorySchedule5.width r :=
  finMemorySchedule5.total_width

/-- The width ledger against the shipped schedule: `![10,27,16,2] → ![10,27,13,5]`, same total. -/
theorem pole_repair_width_ledger :
    finMemorySchedule4.width = ![10, 27, 16, 2] ∧ finMemorySchedule5.width = ![10, 27, 13, 5]
      ∧ (∑ r, finMemorySchedule4.width r) = ∑ r, finMemorySchedule5.width r :=
  ⟨rfl, rfl, by decide⟩

/-- Only the three `intermediate` columns change block. -/
theorem pole_rounds_agree_off_the_intermediate_columns (c : Fin 55)
    (hc : (c : ℕ) ∉ ([31, 32, 33] : List ℕ)) :
    (finMemRoundOf5 c : ℕ) = (finMemRoundOf4 c : ℕ) := by
  revert hc; revert c; decide

/-- The repaired memory declaration: `z` at round `1`, the timestamp base joining at round `2`,
and the internal pair only at round `3` — together with the IO pair. -/
def memRoundChalOf5 (S : IOPlacement3) (r : Fin 4) : Finset (Fin 10) :=
  if (r : ℕ) = 0 then ∅
  else if (r : ℕ) = 1 then {1}
  else if (r : ℕ) = 2 then ({0, 1} : Finset (Fin 10))
  else insert (S.slot 0) (insert (S.slot 1) ({0, 1, 6, 7} : Finset (Fin 10)))

theorem poleChal_round1 : ∀ j ∈ ({1} : Finset (Fin 10)), (poleSampledAfter j : ℕ) < 1 := by decide
theorem poleChal_round2 : ∀ j ∈ ({0, 1} : Finset (Fin 10)),
    (poleSampledAfter j : ℕ) < 2 := by decide
theorem poleChal_round3 : ∀ j ∈ ({0, 1, 6, 7} : Finset (Fin 10)),
    (poleSampledAfter j : ℕ) < 3 := by decide

theorem memRoundChalOf5_usable (S : IOPlacement3) (r : Fin 4) :
    ∀ j ∈ memRoundChalOf5 S r, (poleSampledAfter j : ℕ) < (r : ℕ) := by
  intro j hj
  unfold memRoundChalOf5 at hj
  by_cases h0 : (r : ℕ) = 0
  · rw [if_pos h0] at hj; simp at hj
  rw [if_neg h0] at hj
  by_cases h1 : (r : ℕ) = 1
  · rw [if_pos h1] at hj; rw [h1]; exact poleChal_round1 j hj
  rw [if_neg h1] at hj
  by_cases h2 : (r : ℕ) = 2
  · rw [if_pos h2] at hj; rw [h2]; exact poleChal_round2 j hj
  rw [if_neg h2] at hj
  have h3 : (r : ℕ) = 3 := by have := r.isLt; omega
  rw [h3]
  rcases Finset.mem_insert.mp hj with rfl | hj'
  · rw [poleSA_slot_two S 0]; norm_num
  rcases Finset.mem_insert.mp hj' with rfl | hj''
  · rw [poleSA_slot_two S 1]; norm_num
  exact poleChal_round3 j hj''

/-- The compute declaration is unchanged, and still legal on the repaired chronology — the compute
chip never declares slot `6` or `7`. -/
theorem poleCompChal_round1 : ∀ j ∈ ({1, 2, 3, 4} : Finset (Fin 10)),
    (poleSampledAfter j : ℕ) < 1 := by decide
theorem poleCompChal_round2 : ∀ j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)),
    (poleSampledAfter j : ℕ) < 2 := by decide
theorem poleCompChal_round3 : ∀ j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)),
    (poleSampledAfter j : ℕ) < 3 := by decide

theorem computeRoundChalOf4_usable_pole (S : IOPlacement3) (r : Fin 4) :
    ∀ j ∈ finComputeRoundChalOf4 S r, (poleSampledAfter j : ℕ) < (r : ℕ) := by
  intro j hj
  unfold finComputeRoundChalOf4 at hj
  by_cases h0 : (r : ℕ) = 0
  · rw [if_pos h0] at hj; simp at hj
  rw [if_neg h0] at hj
  by_cases h1 : (r : ℕ) = 1
  · rw [if_pos h1] at hj; rw [h1]; exact poleCompChal_round1 j hj
  rw [if_neg h1] at hj
  by_cases h2 : (r : ℕ) = 2
  · rw [if_pos h2] at hj; rw [h2]; exact poleCompChal_round2 j hj
  rw [if_neg h2] at hj
  have h3 : (r : ℕ) = 3 := by have := r.isLt; omega
  rw [h3]
  rcases Finset.mem_insert.mp hj with rfl | hj'
  · rw [poleSA_slot_two S 0]; norm_num
  rcases Finset.mem_insert.mp hj' with rfl | hj''
  · rw [poleSA_slot_two S 1]; norm_num
  exact poleCompChal_round3 j hj''

section Repaired

variable {L : Type*} [Field L]

/-- **The repaired memory chip.**  This is the object the design needed: a `StagedChip` over the
repaired chronology whose `intermediate` columns sit in the fourth block.  Its
`columns_commit_before_sampling` is discharged here, which is exactly the obligation the
predecessor module could only name. -/
noncomputable def memoryChip5 (S : IOPlacement3) (q : SegmentedRAPParams L) :
    StagedChip L 4 nockChronologyPole where
  air := memoryCombinedFiniteAIR (K := L) 10 9 S.map
  params := q
  schedule := finMemorySchedule5
  columnChallenges := fun c => memRoundChalOf5 S (finMemRoundOf5 c)
  columns_commit_before_sampling := fun _c j hj => memRoundChalOf5_usable S _ j hj

/-- The compute chip carries over to the repaired chronology unchanged — same AIR, same schedule,
same declaration. -/
noncomputable def computeChip5 (S : IOPlacement3) (q : SegmentedRAPParams L) :
    StagedChip L 4 nockChronologyPole where
  air := computeCombinedFiniteAIR 10 9 S.map
  params := q
  schedule := finComputeSchedule4
  columnChallenges := fun c => finComputeRoundChalOf4 S (finComputeRoundOf4 c)
  columns_commit_before_sampling := fun _c j hj => computeRoundChalOf4_usable_pole S _ j hj

/-- **The repaired proof**, as a `GigaRAP`. -/
noncomputable def nockGigaRAPPole (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    GigaRAP L where
  rounds := 4
  rounds_pos := by norm_num
  chronology := nockChronologyPole
  chips := [computeChip5 S qC, memoryChip5 S qM]

/-- Both IO coins still ride the third message on the repaired chronology. -/
theorem ioSlots_poleSampledAfter_two (S : IOPlacement3) {j : Fin 10} (hj : j ∈ ioSlots S) :
    (poleSampledAfter j : ℕ) = 2 := by
  simp only [ioSlots, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact poleSA_slot_two S 0
  · exact poleSA_slot_two S 1

theorem memRecordCols_round5_le_two (c : Fin 55) (hc : c ∈ memRecordCols) :
    (finMemRoundOf5 c : ℕ) ≤ 2 := by
  revert hc; revert c; decide

theorem memIORecordCols_round5_le_two (c : Fin 55) (hc : c ∈ memIORecordCols) :
    (finMemRoundOf5 c : ℕ) ≤ 2 := by
  revert hc; revert c; decide

theorem poleSA_internal (j : Fin 10) (hj : j ∈ memInternalPoleCoins) :
    (poleSampledAfter j : ℕ) = 2 := by
  revert hj; revert j; decide

/-- **The repaired memory chip satisfies the pole discipline.**  Together with its own
`columns_commit_before_sampling` field, that is exactly what a sampled internal pole needs. -/
theorem memoryChip5_is_pole_disciplined (S : IOPlacement3) (q : SegmentedRAPParams L) :
    PoleDisciplined (memoryChip5 S q) memRecordCols memInternalPoleCoins := by
  intro c hc j hj
  have hrw : ((memoryChip5 S q).schedule.roundOf c : ℕ) = (finMemRoundOf5 c : ℕ) := rfl
  have hrw2 : (nockChronologyPole.sampledAfter j : ℕ) = (poleSampledAfter j : ℕ) := rfl
  have hle : (finMemRoundOf5 c : ℕ) ≤ 2 := memRecordCols_round5_le_two c hc
  have h2 : (poleSampledAfter j : ℕ) = 2 := poleSA_internal j hj
  omega

/-- And the repaired chip's external mem-IO pole is still disciplined. -/
theorem memoryChip5_external_pole_is_disciplined (S : IOPlacement3) (q : SegmentedRAPParams L) :
    PoleDisciplined (memoryChip5 S q) memIORecordCols (ioSlots S) := by
  intro c hc j hj
  have hrw : ((memoryChip5 S q).schedule.roundOf c : ℕ) = (finMemRoundOf5 c : ℕ) := rfl
  have hrw2 : (nockChronologyPole.sampledAfter j : ℕ) = (poleSampledAfter j : ℕ) := rfl
  have hle : (finMemRoundOf5 c : ℕ) ≤ 2 := memIORecordCols_round5_le_two c hc
  have h2 : (poleSampledAfter j : ℕ) = 2 := ioSlots_poleSampledAfter_two S hj
  omega

/-- **The repaired chip really is the shipped chip re-blocked**: same AIR, same width, only the
schedule and the declaration move. -/
theorem memoryChip5_is_the_shipped_air (S : IOPlacement3) (q : SegmentedRAPParams L) :
    (memoryChip5 S q).air = (memoryChip3 S q).air := rfl

/-- The design adds no coin: the repaired chronology has the same ten slots. -/
theorem pole_repair_adds_no_coin :
    nockChronologyPole.numChallenges = nockChronologyIO3.numChallenges := rfl

end Repaired

/-! ## 8. `S5`: the residual, and why it is a reading rather than a defect

the paper writes `RAP_walk`'s table construction with its own draw — "Verifier responds with
random elements `α, γ ∈ 𝕂`" — so, read literally, two instantiations of the gadget draw four coins
and both `S4` and `S5` fail.  What forces sharing is the cost line: the paper prices
`RAP_NockMem-IO` at "One round of interaction, providing **a** random element in `𝕂`", and the
memory chip's only gadget round is its forest walk (the paper names the same `(α, γ)`;
the paper give `RAP_mem-IO` no round of its own and the paper shares the NPR
seed).  One element means the forest walk **obtains one of its two coins and draws the other**,
and the paper never says which.

So `S4` and `S5` are the two readings of one clause and **exactly one of them can hold**: taking
both would leave the memory forest walk with two obtained coins and nothing drawn, i.e. *zero*
random elements, below the paper's one.  This tree takes `S4`
(`JointCoins.compute_memory_shared_gamma`, `rfl`) and declines `S5`, which is
the paper-exact. -/

section S5

variable {L : Type*} [Field L]

/-- **`S4` and `S5` cannot both hold.**  The forest block declares exactly one coin; `S4` already
shares the node RLC (off-AIR), so making the index base shared as well would leave the memory
forest walk drawing nothing at all — strictly below the paper. -/
theorem s4_and_s5_are_the_two_readings_of_one_clause (qC qM : SegmentedRAPParams L) :
    (blockForest qM).slots.card = 1 ∧ ¬ (blockWalk qC).Shares (blockForest qM) 5 :=
  ⟨(s4_has_no_block_level_witness qC qM).2.2, (s5_walk_bases_are_not_shared qC qM).1⟩

/-- **Merging `S5` is expressible but not recoverable.**  The tree's split is strictly the more
general choice: at `nockPaperSixRAP` a *valuation* may identify slot `5` with slot `0` and recover
the shared reading, whereas a schedule that mapped both walks to slot `0` could not express the
unshared one.  `ComputeStagedTable.lean`'s header makes the same argument about the compute chip's
six challenge slots. -/
@[reducible] def WalkBasesIdentified {K : Type*} (v : ℕ → K) : Prop := v 5 = v 0

/-- The shared reading is available at the shipped object as a condition on the valuation, with no
change to any chip. -/
theorem walk_bases_identified_is_inhabited {K : Type*} (c : K) :
    WalkBasesIdentified (fun _ : ℕ => c) := rfl

/-- And it is not forced: a valuation separating the two walk bases exists, which is
`PlusIOSegmentedRAP.computeWalkParams_independent_memoryWalkAlpha` at the chronology layer. -/
theorem walk_bases_identified_is_not_forced : ¬ WalkBasesIdentified (fun j : ℕ => j) := by decide

/-- The identification is exactly the slot equality `5 = 0`: what a merged schedule would
hard-wire and this one leaves to the valuation. -/
theorem walk_bases_identified_is_slot_five_eq_zero {K : Type*} (v : ℕ → K) :
    WalkBasesIdentified v ↔ v 5 = v 0 := Iff.rfl

end S5

end Nock.NockVMROM.Thm54.CrossRap

section Audit

open Nock.NockVMROM.Thm54.CrossRap

#check @Nock.NockVMROM.Thm54.CrossRap.PoleDisciplined
#check @Nock.NockVMROM.Thm54.CrossRap.PaperRapBlock
#check @Nock.NockVMROM.Thm54.CrossRap.compTableChip
#check @Nock.NockVMROM.Thm54.CrossRap.memTableChip
#check @Nock.NockVMROM.Thm54.CrossRap.nockPaperSixRAP
#check @Nock.NockVMROM.Thm54.CrossRap.memoryChip5
#check @Nock.NockVMROM.Thm54.CrossRap.nockGigaRAPPole

#print axioms Nock.NockVMROM.Thm54.CrossRap.shared_coin_commits_before_both_readers
#print axioms Nock.NockVMROM.Thm54.CrossRap.poleDisciplined_iff_not_usable
#print axioms Nock.NockVMROM.Thm54.CrossRap.poleDisciplined_excludes_declaration
#print axioms Nock.NockVMROM.Thm54.CrossRap.disciplined_record_coin_needs_a_gap
#print axioms Nock.NockVMROM.Thm54.CrossRap.compTableBlockAIR_is_the_combined_first_block
#print axioms Nock.NockVMROM.Thm54.CrossRap.memTableBlockAIR_is_the_combined_first_block
#print axioms Nock.NockVMROM.Thm54.CrossRap.compute_blocks_tile_by_round
#print axioms Nock.NockVMROM.Thm54.CrossRap.memory_blocks_tile_by_round
#print axioms Nock.NockVMROM.Thm54.CrossRap.compute_block_rounds_eq_shipped
#print axioms Nock.NockVMROM.Thm54.CrossRap.memory_block_rounds_eq_shipped
#print axioms Nock.NockVMROM.Thm54.CrossRap.compute_block_declarations_refine_shipped
#print axioms Nock.NockVMROM.Thm54.CrossRap.memory_block_declarations_refine_shipped
#print axioms Nock.NockVMROM.Thm54.CrossRap.io_block_declarations_refine_shipped
#print axioms Nock.NockVMROM.Thm54.CrossRap.s1_memIO_obtains_from_progIO
#print axioms Nock.NockVMROM.Thm54.CrossRap.s1_declared_at_both_accumulators
#print axioms Nock.NockVMROM.Thm54.CrossRap.s2_timestamp_base_shared
#print axioms Nock.NockVMROM.Thm54.CrossRap.s3_npr_seed_shared
#print axioms Nock.NockVMROM.Thm54.CrossRap.s3_binds_both_blocks
#print axioms Nock.NockVMROM.Thm54.CrossRap.s4_has_no_block_level_witness
#print axioms Nock.NockVMROM.Thm54.CrossRap.s5_walk_bases_are_not_shared
#print axioms Nock.NockVMROM.Thm54.CrossRap.s6_the_two_poles_are_different_coins
#print axioms Nock.NockVMROM.Thm54.CrossRap.s7_abc_not_reused_by_the_io_blocks
#print axioms Nock.NockVMROM.Thm54.CrossRap.edge_ledger
#print axioms Nock.NockVMROM.Thm54.CrossRap.shared_slot_same_value
#print axioms Nock.NockVMROM.Thm54.CrossRap.sharing_a_slot_alone_does_not_share_a_value
#print axioms Nock.NockVMROM.Thm54.CrossRap.chipsShareCoins_is_CoinsAgree
#print axioms Nock.NockVMROM.Thm54.CrossRap.bad_seed_keeps_every_local_obligation
#print axioms Nock.NockVMROM.Thm54.CrossRap.bad_seed_is_invisible_to_the_chronology
#print axioms Nock.NockVMROM.Thm54.CrossRap.external_prog_io_pole_is_disciplined
#print axioms Nock.NockVMROM.Thm54.CrossRap.external_mem_io_pole_is_disciplined
#print axioms Nock.NockVMROM.Thm54.CrossRap.internal_pole_violates_the_discipline
#print axioms Nock.NockVMROM.Thm54.CrossRap.pole_discipline_is_not_implied_by_commit_before_sampling
#print axioms Nock.NockVMROM.Thm54.CrossRap.pole_repair_restricts
#print axioms Nock.NockVMROM.Thm54.CrossRap.pole_repair_moves_exactly_two
#print axioms Nock.NockVMROM.Thm54.CrossRap.pole_repair_needs_no_fourth_message
#print axioms Nock.NockVMROM.Thm54.CrossRap.pole_repair_needs_the_column_split
#print axioms Nock.NockVMROM.Thm54.CrossRap.pole_repair_width_ledger
#print axioms Nock.NockVMROM.Thm54.CrossRap.pole_rounds_agree_off_the_intermediate_columns
#print axioms Nock.NockVMROM.Thm54.CrossRap.memoryChip5_is_pole_disciplined
#print axioms Nock.NockVMROM.Thm54.CrossRap.memoryChip5_external_pole_is_disciplined
#print axioms Nock.NockVMROM.Thm54.CrossRap.memoryChip5_is_the_shipped_air
#print axioms Nock.NockVMROM.Thm54.CrossRap.s4_and_s5_are_the_two_readings_of_one_clause
#print axioms Nock.NockVMROM.Thm54.CrossRap.walk_bases_identified_is_not_forced

end Audit
