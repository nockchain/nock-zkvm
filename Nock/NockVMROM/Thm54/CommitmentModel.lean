import Nock.NockVMROM.Thm54.GigaRAPThirdMessage

/-!
# What `col_reads` assumes, measured against the binding property of `Com(·)`

the paper delegates "the compilation of RAPs into SNARKs" to an external IOP framework, and
the paper names the object that delegation buys: "We denote by `Com(·)` a **binding**
commitment scheme, as per standard RAP interactive constructions."  So a modelling hypothesis
standing in for binding is legitimate — the paper says in so many words that it is not going to
prove one.

This module asks the next question: **is `RoundFibred.StagedAssignment.col_reads`
(`RoundFibredSoundness.lean:563`) that hypothesis, or is it more?**  The answer is *more*, by an
amount that is exactly measurable, and the excess is not needed by the argument that consumes it.

## The two properties

* `RespectsDeclaration T col` is `col_reads` unbundled from the structure: column `c`'s committed
  value is a function of the challenges `T.columnChallenges c` **declares**.
* `ReadsOnlyPriorRounds T col` is the binding property: column `c`'s committed value is a function
  of the challenges sampled **strictly before `c`'s own commitment round**.  This is what
  the paper-then-`:509` buys — `Com(IO_prog)` is sent, *then* `α, β` are sampled, so the
  committed `IO_prog` cannot be a function of `α, β` — and nothing finer.  Binding is a statement
  about *when* a value was fixed; it knows nothing about *which* of the already-public coins the
  prover chose to look at.

## The three results

1. **`col_reads` implies binding** (`respectsDeclaration_readsOnlyPriorRounds`,
   `stagedAssignment_readsOnlyPriorRounds`), via `StagedChip.columns_commit_before_sampling`
   (`StagedTableRAP.lean:174`).  So the assumption is *at least* binding.
2. **It is strictly stronger, and the gap is exactly the un-saturation of the declaration**
   (`binding_col_not_respecting_declaration`, `binding_implies_declaration_iff_saturated`).  At
   any column `c₀` for which some coin `j₀` is schedule-legal (`usableByColumnOf`) but not
   declared, there is a prover column map that is binding-legal and violates `col_reads`:
   `col c₀ χ := χ j₀`.  A commitment scheme does not stop a prover from reading a coin it has
   already been sent.  Conversely, if the declaration is **saturated** — equal to the whole
   schedule-legal set at every column — the two properties coincide.
3. **The bridge does not consume the excess** (`columnLocal_const_of_binding`,
   `staged_error_union_card_le_of_binding`).  `RoundFibred.columnLocal_const_of_prior_challenges`
   (`RoundFibredSoundness.lean:595`) uses `col_reads` only after collapsing it through
   `columns_commit_before_sampling`, i.e. only at round granularity.  So §4 of
   `RoundFibredSoundness.lean` — and with it the whole counting chain up to
   `staged_error_union_card_le` (`:648`) — is re-derivable from binding alone.  That is the
   *correct weaker assumption*: `BindingAssignment` below, whose single field is the paper's
   binding and nothing else.

## Where the excess actually bites, and where it does not

`saturate` (§5) sends any chip to the chip with the same `air`, `params` and `schedule` and the
maximal declaration; satisfaction is unchanged (`saturate_satisfies_iff`, `Iff.rfl`), so
saturating is free on the AIR side and deletes precisely the unjustified data.  Two instances:

* At
  `GigaIOSlots.finiteComputeChip` (`GigaRAPIOSlots.lean:668`) the record timestamp column `111` is
  a round-`2` column while both `RAP_prog-IO` coins ride message `1`
  (`GigaIOSlots.record_timestamp_column_shares_the_message_with_the_io_coins`,
  `GigaRAPIOSlots.lean:652`), so the pair is schedule-legal there and undeclared.
  `two_message_timestamp_admits_a_binding_legal_io_read` therefore produces a **binding-legal
  prover column map, over that very chip, whose timestamp column is the sampled IO coin**.  The
  earlier exhibit needed a second, hostile `StagedChip`; this one does not — the chip the
  composition uses already admits the prover.
* **Three-message chronology.**  At `GigaIOThirdMessage.computeChip3`
  (`GigaRAPThirdMessage.lean:340`) the same columns are committed by round `2` and the coins are
  sampled after round `2`, so no binding-legal prover reads them there:
  `prog_records_const_in_the_io_coins_from_binding` reproduces
  `GigaIOThirdMessage.prog_records_const_in_the_io_coins3` (`:653`) with `col_reads` replaced by
  binding.

## Scope, and what is *not* claimed

Everything here is about the Lean model.  Nothing in this module is a statement about the deployed
client, which draws twice (`prover.hoon:168`, `:212`) and builds `%ln` in the same mega-extend
block as the multiset accumulators (`v2/table/compute.hoon:90`, `:92`).

One asymmetry with the client is worth recording, because it is what makes the declaration
necessary *here* and not there.  So in the client the timestamp column's dependence
on a coin is a *fixed, constraint-forced* function of that coin and of earlier-committed data,
not a prover choice.  This tree's `FiniteIO.finiteIOProgAIR` block is constraint-disjoint from the
compute block (`GigaRAPIOSlots.lean:522`), so its `ts` really is free — which is why the model has
to reach for a declaration or a schedule where the client reaches for a constraint.

Nor is this a claim that binding is *sufficient* for the composition as it stands: the residual
declarations of `GigaIOSlots.finComputeColumnChallenges` (`GigaRAPIOSlots.lean:426`) and of
`GigaIOThirdMessage.finComputeRoundChalOf4` (`GigaRAPThirdMessage.lean:288`) are still
un-saturated at other columns — `finComputeRoundChalOf4` withholds the two memory coins `6, 7`
from every compute column, which the schedule does not withhold — and
`GigaRAPIOFreshness.lean:144,183,198` spends `col_reads` directly.
-/

namespace Nock.NockVMROM.Thm54.CommitmentModel

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.RoundFibred
open scoped Polynomial

variable {K : Type*} [Field K]
variable {rounds : ℕ} {chronology : ChallengeChronology rounds}

/-! ## 1. The two properties: the declaration, and binding -/

/-- **The declaration-respecting property** — `RoundFibred.StagedAssignment.col_reads`
(`RoundFibredSoundness.lean:563`) unbundled from the structure so that it can be compared with
something else.  Column `c`'s committed value is a function of the challenges the chip's
`columnChallenges` field *declares* for `c`. -/
def RespectsDeclaration (T : StagedChip K rounds chronology) {V : Type*}
    (col : Fin T.air.numTraceCols → (Fin chronology.numChallenges → K) → V) : Prop :=
  ∀ c (χ₁ χ₂ : Fin chronology.numChallenges → K),
    (∀ j ∈ T.columnChallenges c, χ₁ j = χ₂ j) → col c χ₁ = col c χ₂

/-- **The binding property of `Com(·)`, as a property of a prover's column map.**

the paper posits a *binding* commitment scheme; the paper has the prover send
`Com(IO_prog)` and the paper has the verifier answer with `α, β`.  What binding gives is
exactly this: a value committed in round `r` was already fixed when the round-`r` coin was sent,
so it is a function of the coins sampled **strictly before** round `r` — which is
`ChallengeChronology.usableByColumnOf` (`MultiRoundRAP.lean:118`), a `<` and not a `≤`.

It gives nothing finer.  Once a coin has been sent to the prover, no property of the commitment
scheme prevents the prover from reading it. -/
def ReadsOnlyPriorRounds (T : StagedChip K rounds chronology) {V : Type*}
    (col : Fin T.air.numTraceCols → (Fin chronology.numChallenges → K) → V) : Prop :=
  ∀ c (χ₁ χ₂ : Fin chronology.numChallenges → K),
    (∀ j, chronology.usableByColumnOf (T.schedule.roundOf c) j → χ₁ j = χ₂ j) →
      col c χ₁ = col c χ₂

/-- **The honest prover-side assumption.**  `RoundFibred.StagedAssignment`
(`RoundFibredSoundness.lean:559`) with `col_reads` replaced by the binding property alone.  This
is the assumption the paper's delegation to the RAP→SNARK compiler actually licenses. -/
structure BindingAssignment (T : StagedChip K rounds chronology) (V : Type*) where
  /-- The committed value of each column, as a function of the challenge vector. -/
  col : Fin T.air.numTraceCols → (Fin chronology.numChallenges → K) → V
  /-- **Binding.**  A round-`r` column is not a function of a coin sampled at message `≥ r`. -/
  col_binding : ReadsOnlyPriorRounds T col

/-- The trace a binding assignment produces at a given challenge vector — the analogue of
`RoundFibred.StagedAssignment.trace` (`RoundFibredSoundness.lean:570`). -/
def BindingAssignment.trace {T : StagedChip K rounds chronology} {V : Type*}
    (A : BindingAssignment T V) (χ : Fin chronology.numChallenges → K) :
    Fin T.air.numTraceCols → V :=
  fun c => A.col c χ

/-! ## 2. The declaration implies binding -/

/-- **`col_reads` is at least binding.**  Immediate from
`StagedChip.columns_commit_before_sampling` (`StagedTableRAP.lean:174`): every declared coin is
schedule-legal, so agreeing on all schedule-legal coins entails agreeing on the declared ones. -/
theorem respectsDeclaration_readsOnlyPriorRounds {T : StagedChip K rounds chronology} {V : Type*}
    {col : Fin T.air.numTraceCols → (Fin chronology.numChallenges → K) → V}
    (h : RespectsDeclaration T col) : ReadsOnlyPriorRounds T col := by
  intro c χ₁ χ₂ hagree
  exact h c χ₁ χ₂ fun j hj => hagree j (T.columns_commit_before_sampling c j hj)

/-- Restated at the structure: every `StagedAssignment` is binding-legal. -/
theorem stagedAssignment_readsOnlyPriorRounds {T : StagedChip K rounds chronology} {V : Type*}
    (A : StagedAssignment T V) : ReadsOnlyPriorRounds T A.col :=
  respectsDeclaration_readsOnlyPriorRounds (T := T) (col := A.col) A.col_reads

/-- The forgetful map: a `StagedAssignment` is in particular a `BindingAssignment`.  Named
without dot notation so that it does not shadow `RoundFibred.StagedAssignment`'s own fields. -/
def bindingOfStagedAssignment {T : StagedChip K rounds chronology} {V : Type*}
    (A : StagedAssignment T V) : BindingAssignment T V where
  col := A.col
  col_binding := stagedAssignment_readsOnlyPriorRounds A

@[simp] theorem bindingOfStagedAssignment_trace {T : StagedChip K rounds chronology} {V : Type*}
    (A : StagedAssignment T V) (χ : Fin chronology.numChallenges → K) :
    (bindingOfStagedAssignment A).trace χ = A.trace χ := rfl

/-! ## 3. The converse fails, and the gap is exactly the undeclared-but-legal coins -/

/-- **The excess, exhibited.**  Let `j₀` be a coin that the *schedule* lets column `c₀` read and
the *declaration* withholds.  Then the prover column map `col c₀ χ := χ j₀` (and `0` elsewhere) is
binding-legal and violates `col_reads`.

No commitment scheme rules this prover out: `j₀` was sent to it before it committed `c₀`.  So
`col_reads` assumes away a behaviour a real prover has, and the amount it assumes away is exactly
the difference between `T.columnChallenges c` and the schedule-legal set. -/
theorem binding_col_not_respecting_declaration (T : StagedChip K rounds chronology)
    (c₀ : Fin T.air.numTraceCols) (j₀ : Fin chronology.numChallenges)
    (hlegal : chronology.usableByColumnOf (T.schedule.roundOf c₀) j₀)
    (hundeclared : j₀ ∉ T.columnChallenges c₀) :
    ∃ col : Fin T.air.numTraceCols → (Fin chronology.numChallenges → K) → K,
      ReadsOnlyPriorRounds T col ∧ ¬ RespectsDeclaration T col := by
  classical
  refine ⟨fun c χ => if c = c₀ then χ j₀ else 0, ?_, ?_⟩
  · intro c χ₁ χ₂ hagree
    by_cases hc : c = c₀
    · subst hc
      simp only [if_pos rfl]
      exact hagree j₀ hlegal
    · simp [hc]
  · intro h
    have hagree : ∀ j ∈ T.columnChallenges c₀,
        (fun _ : Fin chronology.numChallenges => (0 : K)) j
          = (fun j : Fin chronology.numChallenges => if j = j₀ then (1 : K) else 0) j := by
      intro j hj
      have hne : j ≠ j₀ := fun h' => hundeclared (h' ▸ hj)
      show (0 : K) = if j = j₀ then (1 : K) else 0
      rw [if_neg hne]
    have hc := h c₀ (fun _ => 0) (fun j => if j = j₀ then 1 else 0) hagree
    simp only [if_pos rfl] at hc
    exact one_ne_zero (α := K) hc.symm

/-! ## 4. Saturation: the exact condition under which the two coincide -/

/-- **A saturated declaration** declares every coin the schedule permits.  The reverse inclusion
is `StagedChip.columns_commit_before_sampling`, so a saturated chip's `columnChallenges` field
carries *no information at all* beyond `schedule` and `chronology`. -/
def Saturated (T : StagedChip K rounds chronology) : Prop :=
  ∀ c j, chronology.usableByColumnOf (T.schedule.roundOf c) j → j ∈ T.columnChallenges c

/-- At a saturated chip the declared set *is* the schedule-legal set. -/
theorem saturated_columnChallenges_eq (T : StagedChip K rounds chronology) (hsat : Saturated T)
    (c : Fin T.air.numTraceCols) :
    T.columnChallenges c
      = Finset.univ.filter fun j => chronology.usableByColumnOf (T.schedule.roundOf c) j := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => T.columns_commit_before_sampling c j h, hsat c j⟩

/-- **At a saturated chip, `col_reads` *is* binding** — no excess. -/
theorem respectsDeclaration_iff_readsOnlyPriorRounds_of_saturated
    {T : StagedChip K rounds chronology} (hsat : Saturated T) {V : Type*}
    (col : Fin T.air.numTraceCols → (Fin chronology.numChallenges → K) → V) :
    RespectsDeclaration T col ↔ ReadsOnlyPriorRounds T col := by
  refine ⟨respectsDeclaration_readsOnlyPriorRounds, fun h c χ₁ χ₂ hagree => ?_⟩
  exact h c χ₁ χ₂ fun j hj => hagree j (hsat c j hj)

/-- **The measurement.**  Binding entails the declaration *exactly* when the declaration is
saturated.  This is the sharp answer to "is `col_reads` stronger than binding, and by how much":
the excess is precisely the set of schedule-legal-but-undeclared `(column, coin)` pairs, and it is
non-empty iff `Saturated` fails.

Stated at `V := K`, which is where the counterexample of §3 lives; the direction that needs no
counterexample holds at every `V`. -/
theorem binding_implies_declaration_iff_saturated (T : StagedChip K rounds chronology) :
    (∀ col : Fin T.air.numTraceCols → (Fin chronology.numChallenges → K) → K,
        ReadsOnlyPriorRounds T col → RespectsDeclaration T col)
      ↔ Saturated T := by
  refine ⟨fun h c j hlegal => ?_, fun hsat col hcol =>
    (respectsDeclaration_iff_readsOnlyPriorRounds_of_saturated hsat col).mpr hcol⟩
  by_contra hmem
  obtain ⟨col, hbind, hnot⟩ := binding_col_not_respecting_declaration (K := K) T c j hlegal hmem
  exact hnot (h col hbind)

/-! ## 5. Saturation as an operation on chips -/

/-- **The saturated chip.**  Same AIR, same params, same schedule; the declaration replaced by the
schedule-legal set.  This is the chip whose `columnChallenges` field is *derived*, so that
`col_reads` against it is literally binding (`saturate_respectsDeclaration_iff`). -/
noncomputable def saturate (T : StagedChip K rounds chronology) :
    StagedChip K rounds chronology where
  air := T.air
  params := T.params
  schedule := T.schedule
  columnChallenges := fun c =>
    Finset.univ.filter fun j => chronology.usableByColumnOf (T.schedule.roundOf c) j
  columns_commit_before_sampling := by
    intro c j hj
    simpa using (Finset.mem_filter.mp hj).2

@[simp] theorem saturate_air (T : StagedChip K rounds chronology) : (saturate T).air = T.air := rfl

@[simp] theorem saturate_schedule (T : StagedChip K rounds chronology) :
    (saturate T).schedule = T.schedule := rfl

/-- Saturation changes no constraint: satisfaction is the same proposition. -/
theorem saturate_satisfies_iff (T : StagedChip K rounds chronology)
    (P : Fin T.air.numTraceCols → K[X]) : (saturate T).Satisfies P ↔ T.Satisfies P := Iff.rfl

theorem saturate_saturated (T : StagedChip K rounds chronology) : Saturated (saturate T) := by
  intro c j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩

/-- Against the saturated chip, `col_reads` and binding are the same property. -/
theorem saturate_respectsDeclaration_iff (T : StagedChip K rounds chronology) {V : Type*}
    (col : Fin (saturate T).air.numTraceCols → (Fin chronology.numChallenges → K) → V) :
    RespectsDeclaration (saturate T) col ↔ ReadsOnlyPriorRounds (saturate T) col :=
  respectsDeclaration_iff_readsOnlyPriorRounds_of_saturated (saturate_saturated T) col

/-- So every binding-legal prover against `T` *is* a legal `StagedAssignment` against
`saturate T`: dropping the excess loses no prover and no constraint. -/
def BindingAssignment.toStagedAssignmentSaturate {T : StagedChip K rounds chronology} {V : Type*}
    (A : BindingAssignment T V) : StagedAssignment (saturate T) V where
  col := A.col
  col_reads := (saturate_respectsDeclaration_iff T A.col).mpr A.col_binding

/-! ## 6. The §4 bridge, re-derived from binding alone -/

/-- **The bridge does not consume the excess.**
`RoundFibred.columnLocal_const_of_prior_challenges` (`RoundFibredSoundness.lean:595`) with
`StagedAssignment` replaced by `BindingAssignment`: a function of the trace that reads only
columns committed by round `i` is constant along any variation of the challenges sampled at round
`i` or later.

The original proof passes through `col_reads` and immediately collapses it with
`columns_commit_before_sampling`; here the collapsed form is the hypothesis, so the per-column
declaration never appears. -/
theorem columnLocal_const_of_binding {T : StagedChip K rounds chronology} {V β : Type*}
    (A : BindingAssignment T V) (L : ColumnLocal T V β) {i : Fin rounds}
    (hL : L.CommittedBy i) (χ₁ χ₂ : Fin chronology.numChallenges → K)
    (hagree : ∀ j : Fin chronology.numChallenges,
      (chronology.sampledAfter j : ℕ) < (i : ℕ) → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
  refine L.out_congr _ _ ?_
  intro c hc
  refine A.col_binding c χ₁ χ₂ ?_
  intro j hj
  exact hagree j (lt_of_lt_of_le hj (hL c hc))

/-- The factorisation (`RoundFibredSoundness.lean:614`) from binding alone. -/
theorem columnLocal_factors_through_prior_challenges_of_binding
    {T : StagedChip K rounds chronology} {V β : Type*}
    (A : BindingAssignment T V) (L : ColumnLocal T V β) {i : Fin rounds} (hL : L.CommittedBy i) :
    ∃ g : ({j : Fin chronology.numChallenges //
              (chronology.sampledAfter j : ℕ) < (i : ℕ)} → K) → β,
      ∀ χ : Fin chronology.numChallenges → K,
        L.out (A.trace χ) = g (fun j => χ j.1) := by
  classical
  refine ⟨fun r => L.out (A.trace (fun j =>
    if h : (chronology.sampledAfter j : ℕ) < (i : ℕ) then r ⟨j, h⟩ else 0)), ?_⟩
  intro χ
  refine columnLocal_const_of_binding A L hL _ _ ?_
  intro j hj
  simp [hj]

/-- The glue to §3 of `RoundFibredSoundness.lean` (`:632`) from binding alone. -/
theorem columnLocal_readsOn_priorCoords_of_binding {T : StagedChip K rounds chronology}
    {V : Type*} (A : BindingAssignment T V) (L : ColumnLocal T V (Finset K))
    (j : Fin chronology.numChallenges)
    (hL : L.CommittedBy (chronology.sampledAfter j)) :
    ReadsOn (C := K) (priorCoords (fun j' => (chronology.sampledAfter j' : ℕ)) j)
      (fun χ => L.out (A.trace χ)) := by
  intro χ₁ χ₂ hagree
  refine columnLocal_const_of_binding A L hL _ _ ?_
  intro j' hj'
  exact hagree j' (by simpa [priorCoords] using hj')

/-- **The counting conclusion from binding alone.**  `RoundFibred.staged_error_union_card_le`
(`RoundFibredSoundness.lean:648`) with `col_reads` weakened to the paper's binding.  The
bound is identical, so the excess bought nothing on the counting axis. -/
theorem staged_error_union_card_le_of_binding [Fintype K] [DecidableEq K]
    {T : StagedChip K rounds chronology} {V : Type*}
    (A : BindingAssignment T V)
    (badAt : Fin chronology.numChallenges → ColumnLocal T V (Finset K))
    (hcommit : ∀ j, (badAt j).CommittedBy (chronology.sampledAfter j))
    (B : Fin chronology.numChallenges → ℕ)
    (hB : ∀ j χ, ((badAt j).out (A.trace χ)).card ≤ B j) :
    (roundUnion (C := K) Finset.univ (fun j χ => (badAt j).out (A.trace χ))).card
      ≤ ∑ j, Fintype.card K ^ (chronology.numChallenges - 1) * B j := by
  haveI : Nonempty K := ⟨0⟩
  exact roundUnion_card_le_of_chronology
    (fun j' => (chronology.sampledAfter j' : ℕ)) Finset.univ _
    (fun j _ => columnLocal_readsOn_priorCoords_of_binding A (badAt j) j (hcommit j)) B
    (fun j χ => hB j χ)

end Nock.NockVMROM.Thm54.CommitmentModel

/-! ## 7. The two chronologies, measured -/

namespace Nock.NockVMROM.Thm54.CommitmentModel

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.GigaIOSlots
open Nock.NockVMROM.Thm54.GigaIOThirdMessage
open Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology
open scoped Polynomial

variable {K : Type*} [Field K]

/-- **At the two-message chronology the IO-coin exclusion at the record timestamp is the excess,
and a binding-legal prover realises it.**

Column `111` of `GigaIOSlots.finiteComputeChip` (`GigaRAPIOSlots.lean:668`) is committed in round
`2`, both `RAP_prog-IO` coins are sampled after message `1`, and the chip's declaration withholds
them (`GigaIOSlots.record_timestamp_column_shares_the_message_with_the_io_coins`,
`GigaRAPIOSlots.lean:652`).  So §3 applies at that column: there is a prover column map over
**that very chip** which respects the paper's binding and whose record timestamp column is
the sampled coin `S.slot i`.

The earlier exhibit of this defect needed a second, hostile `StagedChip` agreeing with
`finiteComputeChip` on `air`, `params` and `schedule`.  This one needs no second chip: the
assumption `RoundFibred.StagedAssignment.col_reads` excludes a prover that the commitment scheme
does not exclude. -/
theorem two_message_timestamp_admits_a_binding_legal_io_read
    (S : IOSlots) (q : SegmentedRAPParams K) (i : Fin 2)
    (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j) :
    ∃ col : Fin (finiteComputeChip S q).air.numTraceCols → (Fin 10 → K) → K,
      ReadsOnlyPriorRounds (finiteComputeChip S q) col
        ∧ ¬ RespectsDeclaration (finiteComputeChip S q) col := by
  have hshare := record_timestamp_column_shares_the_message_with_the_io_coins S hfresh
  refine binding_col_not_respecting_declaration (K := K) (finiteComputeChip S q)
    (111 : Fin 113) (S.slot i) ?_ (hshare.2.2.1 i)
  have hs : nockChronologyWithIO.sampledAfter (S.slot i) = (1 : Fin 3) := hshare.2.1 i
  have hr : (finiteComputeChip (L := K) S q).schedule.roundOf (111 : Fin 113) = (2 : Fin 3) :=
    hshare.1.1
  have hlt : ((nockChronologyWithIO.sampledAfter (S.slot i) : Fin 3) : ℕ)
      < (((finiteComputeChip (L := K) S q).schedule.roundOf (111 : Fin 113) : Fin 3) : ℕ) := by
    rw [hs, hr]; decide
  exact hlt

/-- The memory twin, at column `52`. -/
theorem two_message_mem_timestamp_admits_a_binding_legal_io_read
    (S : IOSlots) (q : SegmentedRAPParams K) (i : Fin 2)
    (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j) :
    ∃ col : Fin (finiteMemoryChip S q).air.numTraceCols → (Fin 10 → K) → K,
      ReadsOnlyPriorRounds (finiteMemoryChip S q) col
        ∧ ¬ RespectsDeclaration (finiteMemoryChip S q) col := by
  have hshare := record_timestamp_column_shares_the_message_with_the_io_coins S hfresh
  refine binding_col_not_respecting_declaration (K := K) (finiteMemoryChip S q)
    (53 : Fin 55) (S.slot i) ?_ (hshare.2.2.2 i)
  have hs : nockChronologyWithIO.sampledAfter (S.slot i) = (1 : Fin 3) := hshare.2.1 i
  have hr : (finiteMemoryChip (L := K) S q).schedule.roundOf (53 : Fin 55) = (2 : Fin 3) :=
    hshare.1.2
  have hlt : ((nockChronologyWithIO.sampledAfter (S.slot i) : Fin 3) : ℕ)
      < (((finiteMemoryChip (L := K) S q).schedule.roundOf (53 : Fin 55) : Fin 3) : ℕ) := by
    rw [hs, hr]; decide
  exact hlt

/-- **At the three-message chronology the same conclusion needs only binding.**

`GigaIOThirdMessage.prog_records_const_in_the_io_coins3` (`GigaRAPThirdMessage.lean:653`) with
`StagedAssignment` replaced by `BindingAssignment`: any readout of the compute `IO_prog` columns
`102 … 111` — the record timestamp included — takes the same value at two challenge vectors that
agree off the two IO slots, for **every** prover the commitment scheme admits. -/
theorem prog_records_const_in_the_io_coins_from_binding {V β : Type*}
    (S : IOPlacement3) (q : SegmentedRAPParams K)
    (A : BindingAssignment (computeChip3 S q) V)
    (L : ColumnLocal (computeChip3 S q) V β) (hL : L.cols ⊆ progIoDataCols3 S q)
    (χ₁ χ₂ : Fin 10 → K)
    (hagree : ∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
  refine columnLocal_const_of_binding A L (progIoDataCols3_committedBy_two S q L hL) χ₁ χ₂ ?_
  intro j hj
  have hj' : (nockSampledAfterIO3 j : ℕ) < 2 := hj
  refine hagree j (fun h => ?_) (fun h => ?_)
  · rw [h, slot_sampledAfter_two S 0] at hj'; omega
  · rw [h, slot_sampledAfter_two S 1] at hj'; omega

/-- The memory twin. -/
theorem mem_records_const_in_the_io_coins_from_binding {V β : Type*}
    (S : IOPlacement3) (q : SegmentedRAPParams K)
    (A : BindingAssignment (memoryChip3 S q) V)
    (L : ColumnLocal (memoryChip3 S q) V β) (hL : L.cols ⊆ memIoDataCols3 S q)
    (χ₁ χ₂ : Fin 10 → K)
    (hagree : ∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
  refine columnLocal_const_of_binding A L (memIoDataCols3_committedBy_two S q L hL) χ₁ χ₂ ?_
  intro j hj
  have hj' : (nockSampledAfterIO3 j : ℕ) < 2 := hj
  refine hagree j (fun h => ?_) (fun h => ?_)
  · rw [h, slot_sampledAfter_two S 0] at hj'; omega
  · rw [h, slot_sampledAfter_two S 1] at hj'; omega

/-- **No binding-legal prover reads an IO coin at the three-message `IO_prog` columns.**  The
contrapositive face: the coins are sampled *after* those columns are committed, so §3's
counterexample cannot be built there — its `hlegal` hypothesis fails. -/
theorem three_message_io_coin_not_legal_at_records
    (S : IOPlacement3) (q : SegmentedRAPParams K)
    (c : Fin (computeChip3 S q).air.numTraceCols)
    (h1 : 102 ≤ (c : ℕ)) (_h2 : (c : ℕ) ≤ 111) (i : Fin 2) :
    ¬ nockChronologyIO3.usableByColumnOf ((computeChip3 S q).schedule.roundOf c) (S.slot i) := by
  intro hlegal
  have hle : ((computeChip3 S q).schedule.roundOf c : ℕ) ≤ 2 :=
    computeRoundOf4_le_two c h1
  have : (nockSampledAfterIO3 (S.slot i) : ℕ) < 2 := lt_of_lt_of_le hlegal hle
  rw [slot_sampledAfter_two S i] at this
  omega

end Nock.NockVMROM.Thm54.CommitmentModel

section Audit

open Nock.NockVMROM.Thm54.CommitmentModel

#check @RespectsDeclaration
#check @ReadsOnlyPriorRounds
#check @BindingAssignment
#check @respectsDeclaration_readsOnlyPriorRounds
#check @binding_col_not_respecting_declaration
#check @binding_implies_declaration_iff_saturated
#check @saturate
#check @columnLocal_const_of_binding
#check @staged_error_union_card_le_of_binding
#check @two_message_timestamp_admits_a_binding_legal_io_read
#check @prog_records_const_in_the_io_coins_from_binding
#check @three_message_io_coin_not_legal_at_records

#print axioms Nock.NockVMROM.Thm54.CommitmentModel.respectsDeclaration_readsOnlyPriorRounds
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.stagedAssignment_readsOnlyPriorRounds
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.binding_col_not_respecting_declaration
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.respectsDeclaration_iff_readsOnlyPriorRounds_of_saturated
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.binding_implies_declaration_iff_saturated
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.saturate_saturated
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.saturate_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.saturate_respectsDeclaration_iff
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.columnLocal_const_of_binding
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.columnLocal_factors_through_prior_challenges_of_binding
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.columnLocal_readsOn_priorCoords_of_binding
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.staged_error_union_card_le_of_binding
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.two_message_timestamp_admits_a_binding_legal_io_read
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.two_message_mem_timestamp_admits_a_binding_legal_io_read
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.prog_records_const_in_the_io_coins_from_binding
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.mem_records_const_in_the_io_coins_from_binding
#print axioms Nock.NockVMROM.Thm54.CommitmentModel.three_message_io_coin_not_legal_at_records

end Audit
