import Nock.NockVMROM.Thm54.GigaRAPIOSlots
import Nock.NockVMROM.Thm54.RoundFibredSoundness

/-!
# The `RAP_prog-IO` coins, priced by dependence rather than by sequencing

`GigaRAPIOSlots.lean` §2.1 proves `io_records_read_no_io_coin`: at a fresh placement no record or
multiplicity column of either IO block declares either `RAP_prog-IO` coin — the record timestamp
`111`/`52` included, even though it is committed in the same column block, after the same verifier
message, as the accumulators.  This module spends that.

## Status: what is enforced here and what is assumed — read this first

**Everything in this module is conditional on a prover-side modelling hypothesis, and at exactly
one column per chip that hypothesis is strictly stronger than anything the round schedule gives.**

`StagedChip.columnChallenges` (`StagedTableRAP.lean:171`) is a *declaration*.  Its only obligation,
`columns_commit_before_sampling` (`:174`), checks the declaration against the round schedule; it
says nothing about what a column is.  The prover-side counterpart,
`RoundFibred.StagedAssignment.col_reads` (`RoundFibredSoundness.lean:563`), is a structure **field**
— a hypothesis about the prover, not a theorem about the constraint system.  On the two-message
chronology `Chronology.nockChronologyWithIO` the schedule *does* back the declaration at compute
columns `102 … 110` and memory `43 … 51` (they are round-`1` columns and the IO coins ride message
`1`, so `1 < 1` fails), but **not** at compute `111` / memory `52`, the record timestamp: those are
round-`2` columns committed after the same verifier message as the coins, so the declaration there
is a modelling choice and a differently-declared chip over the identical AIR, params and schedule
is equally legal.

Three things follow, and they are stated as they are rather than as they were:

* That recurrence is a clause of
  `V_comp` over `W_comp`, and it has no image in
  `FiniteIO.finiteIOProgAIR` (`FiniteFieldIOAIR.lean:153`: four gates, none pinning a record
  coordinate).  `ComputeChip.computeAIRchained_varsBelow` and
  `GigaFinite.finiteIOProgAIR_varsBelow` (`NockGigaRAPFinite.lean:152`) make the compute and IO
  blocks constraint-disjoint, so no gate of `computeCombinedFiniteAIR` mentions both a compute
  column and an IO record column.
* The claim that this module moves the `ioWork / cardK²` charge off
  `IOCoinReconciliation.ioCoins_free` (`:127`) and **onto the construction** is likewise too
  strong.  It moves it onto a *different* modelling restriction of comparable strength.  No number
  changes either way, and neither justification is consumed by the production bound.
* The fix that does discharge it is the paper's own extra verifier message, and it is carried in
  `GigaRAPThirdMessage.lean`: at a chronology where the IO coins ride a **third** message,
  `GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute` proves the exclusion for
  *every* chip whose `IO_prog` columns are committed by round `2` — no declaration is chosen, and
  the differently-declared chip does not exist there.  That module carries the enforced form of
  §2 and §4 below.

## What is being replaced

`OptimizedStrictPackage.optimizedProductionFailureProbabilityBound` (`:632`) charges the IO events
`ioWork / cardK ^ 2`, and the justification for that charge is
`IOCoinReconciliation.ioCoins_free` (`:127`): the production tuple's IO coordinate is a *free*
`K × K`.  That is a fact about the tuple **type** — it says the coordinate is unconstrained, not
that the prover's records are independent of it.  A hostile prover whose record columns read the
pole would still inhabit a free coordinate, and the union bound would be unjustified.

## What replaces it

The honest premise is the one `RoundFibred.roundUnion_card_le` (`RoundFibredSoundness.lean:380`)
asks for: `hself : i ∉ dep i` and `hdep : ReadsOn (dep i) (bad i)` — *coordinate `i`'s bad set does
not read coordinate `i`*.  `RoundFibred.cylinder_card_le_needs_dependence` (`:341`) shows the
bound is false without it, so this is where the content is.

The argument is **fibred, not sequential**:

* §2 — a readout of the IO data columns is constant along any variation of the two IO coins,
  because none of those columns declares either coin (`prog_records_const_in_the_io_coins`).  The
  input is `StagedAssignment.col_reads` and the *per-column* `columnChallenges` of
  `GigaRAPIOSlots.lean` §2 — **both modelling hypotheses**, and at column `111`/`52` the second is
  not backed by the schedule (see Status above).  No round ordering is used, which is what lets it
  be stated at all in the presence of the co-located `ln`/`ts` column; it is also why it is an
  assumption there rather than a consequence.
* §3 — hence the record-RLC bad set reads neither IO coordinate and the pole's bad set reads the
  `γ` coordinate but not its own (`badGamma_readsOn`, `badPole_readsOn`).  Conditioning on `γ` is
  exactly the fibring: at each fixed `γ` the records are determined and the bad poles are few.
* §4 — `roundUnion_card_le` then bounds the region on which either coin is bad by
  `|K|^9 · (B_γ + B_pole)` out of `|K|^10` (`io_failure_roundUnion_card_le`).
* §5 — that is the same number as `ioWork / cardK ^ 2`
  (`io_round_price_is_the_ioWork_charge`), so nothing in the probability bound changes.  What
  changes is not that the reason has become a fact about the construction — it has not, see
  Status — but that the reason is now a compiled theorem with its hypotheses on the page.

## Why the *chronology*-indexed corollary is not the right tool

`RoundFibred.roundUnion_card_le_of_chronology` (`:392`) specialises `dep` to
`priorCoords sampledAfter i`, the coins sampled at a strictly earlier verifier message.  That does
**not** cover this case: both IO coins ride message `1` of `nockChronologyWithIO`, so
`S.slot 0 ∉ priorCoords … (S.slot 1)` (`gamma_not_prior_to_pole` below) and the pole's bad set —
which genuinely reads `γ` — is not `ReadsOn (priorCoords …)`.  The general `roundUnion_card_le`,
whose `dep` is arbitrary subject to `hself`, is the one that applies.  Equivalently: what the
argument needs is a *dependence order* on the coins, and that order is finer than the message
order.

## Scope

Statements about **this tree's** three-round / two-message chips and about any prover assignment
against them — but `RoundFibred.StagedAssignment` quantifies only over assignments that respect
the chip's *declaration*, so a prover whose record columns read an undeclared coin is outside the
domain of every theorem below.  Not a claim about the paper's construction, and not a claim about
the deployed client.
-/

namespace Nock.NockVMROM.Thm54.GigaIOFreshness

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GigaFinite
open Nock.NockVMROM.Thm54.GigaIOSlots
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology
open scoped Polynomial

/-! ## 1. Constancy from declared dependence, not from message order -/

section Generic

variable {K : Type*} [Field K] {rounds : ℕ} {chronology : ChallengeChronology rounds}
variable {T : StagedChip K rounds chronology} {V β : Type*}

/-- **A column-local readout is constant in any coin set none of its columns declares.**

The companion of `RoundFibred.columnLocal_const_of_prior_challenges`
(`RoundFibredSoundness.lean:595`), which derives the same conclusion from the *round* structure.
This one derives it from the *declared per-column dependence* alone.

**That is a weaker footing, not a stronger one.**  `columnLocal_const_of_prior_challenges` consumes
`StagedChip.columns_commit_before_sampling`, an obligation every chip carries; this theorem consumes
the declaration itself, which at compute column `111` / memory `52` the schedule does not force.
It is used here because the two-message chronology gives nothing else — the IO coins ride the same
verifier message as the timestamp base — and the enforced replacement is
`GigaIOThirdMessage.prog_records_const_in_the_io_coins3` (`GigaRAPThirdMessage.lean`), which goes
back through the round structure at a chronology where the coins are sampled later. -/
theorem columnLocal_const_of_undeclared_challenges (A : StagedAssignment T V)
    (L : ColumnLocal T V β) (D : Finset (Fin chronology.numChallenges))
    (hL : ∀ c ∈ L.cols, ∀ j ∈ T.columnChallenges c, j ∉ D)
    (χ₁ χ₂ : Fin chronology.numChallenges → K)
    (hagree : ∀ j, j ∉ D → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) :=
  L.out_congr _ _ fun c hc => A.col_reads c χ₁ χ₂ fun j hj => hagree j (hL c hc j hj)

end Generic

/-! ## 2. The IO data columns, and their readouts -/

section Records

variable {K : Type*} [Field K] {V β : Type*}
variable (S : IOSlots) (q : SegmentedRAPParams K)

/-- **The compute IO-block columns that carry `IO_prog` itself** — the two multiplicity columns
and the eight record coordinates, `102 … 111`.  Not the accumulator `100`, not the reciprocal
`101`. -/
noncomputable def progIoDataCols : Finset (Fin (finiteComputeChip S q).air.numTraceCols) :=
  Finset.univ.filter fun c => 102 ≤ (c : ℕ) ∧ (c : ℕ) ≤ 111

/-- The memory twin, `43 … 52`. -/
noncomputable def memIoDataCols : Finset (Fin (finiteMemoryChip S q).air.numTraceCols) :=
  Finset.univ.filter fun c => 44 ≤ (c : ℕ) ∧ (c : ℕ) ≤ 53

/-- **(2) The records are independent of the two `RAP_prog-IO` coins.**

Any readout of the compute IO data columns takes the same value at two challenge vectors that
agree off the two IO slots.  So varying `γ` and the pole cannot change the record set the LogUp
argument is about — which is what the paper's commitment is for, obtained here from the
declared dependence rather than from the message order.

No round hypothesis appears, and none is available: the timestamp column `111` is committed after
the same verifier message as the coins
(`GigaIOSlots.record_timestamp_column_shares_the_message_with_the_io_coins`). -/
theorem prog_records_const_in_the_io_coins
    (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j)
    (A : StagedAssignment (finiteComputeChip S q) V)
    (L : ColumnLocal (finiteComputeChip S q) V β) (hL : L.cols ⊆ progIoDataCols S q)
    (χ₁ χ₂ : Fin 10 → K)
    (hagree : ∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
  refine L.out_congr _ _ fun c hc => A.col_reads c χ₁ χ₂ fun j hj => ?_
  have hcm := hL hc
  simp only [progIoDataCols, Finset.mem_filter, Finset.mem_univ, true_and] at hcm
  have h0 := (io_records_read_no_io_coin S hfresh).1 c hcm.1 hcm.2 0
  have h1 := (io_records_read_no_io_coin S hfresh).1 c hcm.1 hcm.2 1
  exact hagree j (fun h => h0 (h ▸ hj)) (fun h => h1 (h ▸ hj))

/-- The memory twin. -/
theorem mem_records_const_in_the_io_coins
    (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j)
    (A : StagedAssignment (finiteMemoryChip S q) V)
    (L : ColumnLocal (finiteMemoryChip S q) V β) (hL : L.cols ⊆ memIoDataCols S q)
    (χ₁ χ₂ : Fin 10 → K)
    (hagree : ∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
  refine L.out_congr _ _ fun c hc => A.col_reads c χ₁ χ₂ fun j hj => ?_
  have hcm := hL hc
  simp only [memIoDataCols, Finset.mem_filter, Finset.mem_univ, true_and] at hcm
  have h0 := (io_records_read_no_io_coin S hfresh).2 c hcm.1 hcm.2 0
  have h1 := (io_records_read_no_io_coin S hfresh).2 c hcm.1 hcm.2 1
  exact hagree j (fun h => h0 (h ▸ hj)) (fun h => h1 (h ▸ hj))

end Records

/-! ## 3. The two IO bad sets, as cylinders -/

section BadSets

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {V : Type*} {m : ℕ}
variable (S : IOSlots) (q : SegmentedRAPParams K)

/-- The coordinates the record-RLC coin's bad set is allowed to read: everything but the two IO
slots. -/
def ioDepGamma : Finset (Fin 10) := (Finset.univ : Finset (Fin 10)) \ {S.slot 0, S.slot 1}

/-- The coordinates the pole's bad set is allowed to read: everything but its own.  Wider than
`ioDepGamma` by exactly the `γ` coordinate, which is what "condition on `γ`, then union-bound over
the pole" means. -/
def ioDepPole : Finset (Fin 10) := (Finset.univ : Finset (Fin 10)).erase (S.slot 1)

theorem gamma_not_mem_ioDepGamma : S.slot 0 ∉ ioDepGamma S := by
  simp [ioDepGamma]

theorem pole_not_mem_ioDepPole : S.slot 1 ∉ ioDepPole S := by
  simp [ioDepPole]

theorem gamma_mem_ioDepPole : S.slot 0 ∈ ioDepPole S := by
  simp only [ioDepPole, Finset.mem_erase, Finset.mem_univ, and_true]
  exact S.slot_ne

/-- **Why the message order is the wrong order here.**  Both IO coins ride verifier message `1`,
so the `γ` coordinate is *not* in the pole coordinate's `priorCoords`; the pole's bad set does read
`γ`, so `roundUnion_card_le_of_chronology` — which fixes `dep := priorCoords` — cannot be the
instance used.  The general `roundUnion_card_le` can, because its `dep` is arbitrary subject to
`hself`. -/
theorem gamma_not_prior_to_pole :
    S.slot 0 ∉ priorCoords (fun j => (nockSampledAfterWithIO j : ℕ)) (S.slot 1) := by
  simp only [priorCoords, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
    S.final_round 0, S.final_round 1]
  exact le_rfl

variable (A : StagedAssignment (finiteComputeChip S q) V)
  (L : ColumnLocal (finiteComputeChip S q) V (PreChallengeRecords K m))

/-- The bad record-RLC challenges at a challenge vector: the collision event of whatever records
the trace carries there. -/
noncomputable def badGamma (χ : Fin 10 → K) : Finset K :=
  IORLCCollisionEvent (L.out (A.trace χ))

/-- The bad poles: the pole-hit and log-derivative events, at those records **and** at the sampled
record-RLC coin — so this one does read the other IO coordinate. -/
noncomputable def badPole (χ : Fin 10 → K) : Finset K :=
  IOPoleHitEvent (L.out (A.trace χ)) (χ (S.slot 0))
    ∪ IOLogDerivEvent (L.out (A.trace χ)) (χ (S.slot 0))

/-- **The record-RLC coin's bad set reads neither IO coordinate.**  It is a function of the
records alone, and the records declare no IO coin. -/
theorem badGamma_readsOn (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j)
    (hL : L.cols ⊆ progIoDataCols S q) :
    ReadsOn (C := K) (ioDepGamma S) (badGamma S q A L) := by
  intro χ₁ χ₂ hagree
  have hrec : L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
    refine prog_records_const_in_the_io_coins S q hfresh A L hL χ₁ χ₂ ?_
    intro j h0 h1
    refine hagree j ?_
    simp only [ioDepGamma, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨h0, h1⟩
  simp only [badGamma, hrec]

/-- **The pole's bad set reads `γ` and the records, and not the pole.**  That is
`roundUnion_card_le`'s `hdep` at the pole coordinate, with `hself` supplied by
`pole_not_mem_ioDepPole`. -/
theorem badPole_readsOn (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j)
    (hL : L.cols ⊆ progIoDataCols S q) :
    ReadsOn (C := K) (ioDepPole S) (badPole S q A L) := by
  intro χ₁ χ₂ hagree
  have hgamma : χ₁ (S.slot 0) = χ₂ (S.slot 0) := hagree _ (gamma_mem_ioDepPole S)
  have hrec : L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
    refine prog_records_const_in_the_io_coins S q hfresh A L hL χ₁ χ₂ ?_
    intro j _ h1
    refine hagree j ?_
    simp only [ioDepPole, Finset.mem_erase, Finset.mem_univ, and_true]
    exact h1
  simp only [badPole, hrec, hgamma]

end BadSets

/-! ## 4. The IO coins as summands of the round-stratified bound -/

section Bound

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {V : Type*} {m : ℕ}
variable (S : IOSlots) (q : SegmentedRAPParams K)
  (A : StagedAssignment (finiteComputeChip S q) V)
  (L : ColumnLocal (finiteComputeChip S q) V (PreChallengeRecords K m))

/-- The per-coordinate bad-set family: the record-RLC event at the `γ` slot, the pole events at
the pole slot, nothing anywhere else. -/
noncomputable def ioBad (i : Fin 10) (χ : Fin 10 → K) : Finset K :=
  if i = S.slot 0 then badGamma S q A L χ
  else if i = S.slot 1 then badPole S q A L χ else ∅

/-- The dependence sets. -/
def ioDep (i : Fin 10) : Finset (Fin 10) :=
  if i = S.slot 1 then ioDepPole S else ioDepGamma S

/-- **(3) The IO coins priced as summands of the round-stratified bound.**

`RoundFibred.roundUnion_card_le` applies verbatim: the two IO coordinates carry bad sets that read
only coordinates they do not themselves constrain, so the region of the ten-coin challenge space on
which either coin is bad has at most `|K|^9 · (B_γ + B_pole)` points out of `|K|^10`.

`hself` is `gamma_not_mem_ioDepGamma`/`pole_not_mem_ioDepPole` — and, correcting what this
docstring used to say, those two are `simp` on the *definitions* `ioDepGamma := univ \ {slot 0,
slot 1}` and `ioDepPole := univ.erase (slot 1)`; no column and no declaration appears in either.
Only `hdep` (§3) comes from `GigaIOSlots.io_records_read_no_io_coin`, i.e. from what the columns
declare, and at column `111`/`52` that declaration is a modelling restriction rather than a
consequence of the schedule (module header, Status).  So this theorem is **not** a replacement for
`IOCoinReconciliation.ioCoins_free` as a fact about the construction: it is a differently-shaped
assumption of comparable strength, with the same arithmetic (§5).  The enforced version is
`GigaIOThirdMessage.io_failure_roundUnion_card_le3` (`GigaRAPThirdMessage.lean`). -/
theorem io_failure_roundUnion_card_le
    (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j)
    (hL : L.cols ⊆ progIoDataCols S q) (Bγ Bpole : ℕ)
    (hBγ : ∀ χ, (badGamma S q A L χ).card ≤ Bγ)
    (hBpole : ∀ χ, (badPole S q A L χ).card ≤ Bpole) :
    (roundUnion (C := K) {S.slot 0, S.slot 1} (ioBad S q A L)).card
      ≤ Fintype.card K ^ 9 * Bγ + Fintype.card K ^ 9 * Bpole := by
  classical
  haveI : Nonempty K := ⟨0⟩
  have hne : S.slot 0 ≠ S.slot 1 := S.slot_ne
  refine le_trans (roundUnion_card_le (C := K) {S.slot 0, S.slot 1} (ioBad S q A L) (ioDep S)
    ?_ ?_ (fun i => if i = S.slot 0 then Bγ else if i = S.slot 1 then Bpole else 0) ?_) ?_
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · rw [show ioDep S (S.slot 0) = ioDepGamma S from if_neg hne]
      exact gamma_not_mem_ioDepGamma S
    · rw [show ioDep S (S.slot 1) = ioDepPole S from if_pos rfl]
      exact pole_not_mem_ioDepPole S
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · rw [show ioDep S (S.slot 0) = ioDepGamma S from if_neg hne]
      intro χ₁ χ₂ hag
      have h := badGamma_readsOn S q A L hfresh hL χ₁ χ₂ hag
      simpa [ioBad] using h
    · rw [show ioDep S (S.slot 1) = ioDepPole S from if_pos rfl]
      intro χ₁ χ₂ hag
      have h := badPole_readsOn S q A L hfresh hL χ₁ χ₂ hag
      simpa [ioBad, hne.symm] using h
  · intro i χ
    by_cases h0 : i = S.slot 0
    · subst h0; simpa [ioBad] using hBγ χ
    · by_cases h1 : i = S.slot 1
      · subst h1; simpa [ioBad, h0] using hBpole χ
      · simp [ioBad, h0, h1]
  · have e0 : (if S.slot 0 = S.slot 0 then Bγ else if S.slot 0 = S.slot 1 then Bpole else 0)
        = Bγ := by simp
    have e1 : (if S.slot 1 = S.slot 0 then Bγ else if S.slot 1 = S.slot 1 then Bpole else 0)
        = Bpole := by simp [hne.symm]
    rw [Finset.sum_pair hne, e0, e1]

end Bound

/-! ## 5. The number the dependence argument produces is the one already charged -/

section Price

/-- **`ioFailureUnionBound` factors as `|K| · (B_γ + B_pole)`.**
`FiniteFieldIOSoundness.lean:278` defines it as `((k₁+k₂)²(m−1))·cardK + cardK·(2(k₁+k₂))`, and its
own proof (`IOFailureEvent_card_le`, `:283`) is already a two-cylinder union: the `γ`-cylinder
`IORLCCollisionEvent ×ˢ univ`, and the `γ`-indexed pole fibres.  So the free-coordinate charge and
the dependence-stratified charge were always the same arithmetic; §4 supplies the *reason*, and the
existing proof's shape is evidence that the reason was the intended one. -/
theorem ioFailureUnionBound_factors (m k₁ k₂ cardK : ℕ) :
    ioFailureUnionBound m k₁ k₂ cardK
      = cardK * ((k₁ + k₂) * (k₁ + k₂) * (m - 1) + 2 * (k₁ + k₂)) := by
  simp only [ioFailureUnionBound]
  ring

/-- **The price is unchanged.**  `optimizedProductionFailureProbabilityBound`'s IO summand
`ioWork / cardK²` (`OptimizedStrictPackage.lean:635`) equals `(B_γ + B_pole) / cardK`, which is
what `io_failure_roundUnion_card_le`'s `|K|^9 · (B_γ + B_pole)` out of `|K|^10` gives.  So moving
the justification off `ioCoins_free` costs nothing and changes no number. -/
theorem io_round_price_is_the_ioWork_charge (m k₁ k₂ cardK : ℕ) (hk : cardK ≠ 0) :
    (ioFailureUnionBound m k₁ k₂ cardK : ℚ) / (cardK : ℚ) ^ 2
      = (((k₁ + k₂) * (k₁ + k₂) * (m - 1) + 2 * (k₁ + k₂) : ℕ) : ℚ) / (cardK : ℚ) := by
  have hq : (cardK : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [ioFailureUnionBound_factors]
  push_cast
  field_simp

/-- The same statement read off `io_failure_roundUnion_card_le`'s conclusion: the bound is
`|K|^9 · (B_γ + B_pole)` out of the `|K|^10` points of the ten-coin challenge space. -/
theorem roundUnion_bound_normalizes (cardK Bγ Bpole : ℕ) (hk : cardK ≠ 0) :
    ((cardK ^ 9 * Bγ + cardK ^ 9 * Bpole : ℕ) : ℚ) / ((cardK : ℚ) ^ 10)
      = ((Bγ + Bpole : ℕ) : ℚ) / (cardK : ℚ) := by
  have hq : (cardK : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  push_cast
  field_simp

end Price

end Nock.NockVMROM.Thm54.GigaIOFreshness

section Audit

open Nock.NockVMROM.Thm54.GigaIOFreshness

#check @columnLocal_const_of_undeclared_challenges
#check @prog_records_const_in_the_io_coins
#check @badGamma_readsOn
#check @badPole_readsOn
#check @gamma_not_prior_to_pole
#check @io_failure_roundUnion_card_le
#check @io_round_price_is_the_ioWork_charge

#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.columnLocal_const_of_undeclared_challenges
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.prog_records_const_in_the_io_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.mem_records_const_in_the_io_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.gamma_not_mem_ioDepGamma
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.pole_not_mem_ioDepPole
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.gamma_not_prior_to_pole
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.badGamma_readsOn
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.badPole_readsOn
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.io_failure_roundUnion_card_le
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.ioFailureUnionBound_factors
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.io_round_price_is_the_ioWork_charge
#print axioms Nock.NockVMROM.Thm54.GigaIOFreshness.roundUnion_bound_normalizes

end Audit
