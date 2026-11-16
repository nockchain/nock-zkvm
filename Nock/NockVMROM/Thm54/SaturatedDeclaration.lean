import Nock.NockVMROM.Thm54.CommitmentModel
import Nock.NockVMROM.Thm54.GigaRAPThirdMessage

/-!
# The declaration, measured and deleted: saturating the shipped chips

`StagedChip.columnChallenges` (`StagedTableRAP.lean::Nock.NockVMROM.Thm54.Staged.StagedChip`) is a
*declared* field whose only obligation, `columns_commit_before_sampling`, checks it against the
round schedule.  `GigaIOThirdMessageProduction.two_message_exclusion_is_a_choice_three_message_is_not`
compiles the consequence: two equally legal chips can sit over one identical AIR, params and
schedule and disagree about which coins a column reads, with `Satisfies` agreement by `Iff.rfl`.
So the soundness statements that quantify over `RoundFibred.StagedAssignment` quantify over
*(coins, a chosen declaration)* rather than over *(coins, round order)*.

## What can and cannot be derived, measured rather than hoped

**It cannot be, and the tree
already contains the proof that it cannot**: `StagedAssignment.col` is a *prover* object — the
committed value of each column as a function of the coin vector — and
`CommitmentModel.binding_col_not_respecting_declaration` exhibits, at any column/coin pair the
schedule permits and the declaration withholds, a prover column map that is legal for every
binding commitment scheme and violates the declaration. `GigaIOThirdMessage.col_reads_not_implied_by_satisfaction`
says the same thing on the satisfaction axis. No AIR-level fact can rule those provers out,
because the AIR constrains a trace and does not produce one.

What *can* be done is the other half of the same measurement, and it is the half that removes the
prover's annotation freedom:

* `CommitmentModel.Saturated` is the condition "the declaration is the schedule-legal set", under
  which `RespectsDeclaration` and `ReadsOnlyPriorRounds` are the same
  property, so the declaration field carries **no information beyond `schedule` and `chronology`**.
* §1 below measures the failure of that condition as a `Finset`, the **excess**, and §4 computes it
  for each shipped chip.
* §2 proves the excess is the *only* freedom: every legal declaration is a subset of the saturated
  one, so `saturate T` is the unique maximum, and two saturated chips over the same AIR, params and
  schedule are **equal**.  That is the sharp closure of the two-legal-chips construction.
* §3 exhibits the type-level consequence: `StagedAssignment (saturate T) V` and
  `CommitmentModel.BindingAssignment T V` are the same type up to an explicit `Equiv`.  A
  soundness statement at a saturated chip therefore ranges over the round order and nothing else.

## What §4 measures, and the one number that matters

At the **shipped** three-message chips `GigaIOThirdMessage.computeChip3` / `memoryChip3` — the ones
`GigaRAPThirdMessageProduction.lean` moved the composition onto — the excess is

| chip | round `0` | round `1` | round `2` | round `3` |
|---|---|---|---|---|
| `computeChip3` | `∅` | `∅` | `{6,7}` | `{6,7}` |
| `memoryChip3` | `∅` | `{2,3,4}` | `{2,3,4,5}` | `{2,3,4,5}` |

and **neither IO slot ever appears in it** (`computeChip3_excess_has_no_io_slot`).  That is the
precise sense in which the IO-coin exclusion is *derived* at the shipped chips: it is not in the
excess, so it is a consequence of the round order, which is
`GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute` restated as a measurement.  The
residue `{6,7}` (the memory table's `β, γ`) and `{2,3,4,5}` (the compute table's `a, b, c` and
`α_C`) is real, is *not* derived, and nothing in the tree spends it — §4.3 deletes it by moving to
`computeChip3Sat` / `memoryChip3Sat`, whose satisfaction is the same proposition by `Iff.rfl` and
at which every consumer re-derives.

At the legacy two-message chips `GigaIOSlots.finiteComputeChip` / `finiteMemoryChip` the excess
**does** contain both IO slots, at compute column `111` and memory column `52`
(`finiteComputeChip_excess_contains_the_io_slots_at_111`).  That is the same defect
`GigaIOThirdMessage.lean`'s header tabulates, now as a `Finset` rather than as a case split, and it
is why those chips are legacy.

## One in-tree prose claim this contradicts

`GigaRAPThirdMessage.lean`'s header says of `finComputeRoundChalOf4` that "the declaration carries
no information the schedule does not already carry (`finComputeRoundChalOf4` is a *per-round*
map)".  A per-round map is not a saturated one, and §4.1 measures the difference: `{6,7}` at every
round-`2` and round-`3` compute column.  `CommitmentModel.lean`'s scope note already said so in
prose ("`finComputeRoundChalOf4` withholds the two memory coins `6, 7` from every compute column,
which the schedule does not withhold"); this module compiles it, and §4.3 supplies the chip at
which the header's sentence is *true*.

## Where these chips are consumed

`GigaRAPThirdMessageProduction.lean` §1-§2 — the deployed composition — now names
`computeChip3Sat` / `memoryChip3Sat` rather than the shipped chips.  The import edge between the
two modules was reversed to make that possible: this module referenced
`GigaIOThirdMessageProduction` only in docstrings, so the `import` was dropped and that module
imports this one.  The prose references to it below are therefore forward references.

Two halves of that move, and they are not alike.  On the `Satisfies` hypotheses it is a
definitional no-op — `Satisfies` reads `air` and `params`, `saturate` touches only
`columnChallenges`, and the production module quantifies over no `StagedAssignment` at all, so
there was no prover class there for saturation to shrink.  On the two declaration conjuncts it is
a strengthening, over a chip that `computeChip3Sat_unique` shows is the only one of its kind.

## Scope

Statements about this tree's chips and about prover assignments against them.  Nothing here is a
claim about the deployed client, which pins its `%ln` column by constraint
(`v2/table/verifier/compute.hoon`'s `%ln-starts-at-z`, `%ln-inc`, `%ln-dec`) rather than by
declaration — the asymmetry `CommitmentModel.lean`'s scope note records.  Nothing here changes an
AIR, a constraint, a census or a bound.
-/

namespace Nock.NockVMROM.Thm54.SaturatedDeclaration

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.CommitmentModel
open scoped Polynomial

variable {K : Type*} [Field K]
variable {rounds : ℕ} {chronology : ChallengeChronology rounds}

/-! ## 1. The excess: how far a declaration falls short of the schedule -/

/-- **The coins the schedule permits column `c` to read.**  This is `saturate`'s declaration
(`CommitmentModel.saturate`), named on its own so that the gap can be subtracted. -/
noncomputable def scheduleLegal (T : StagedChip K rounds chronology)
    (c : Fin T.air.numTraceCols) : Finset (Fin chronology.numChallenges) :=
  Finset.univ.filter fun j => chronology.usableByColumnOf (T.schedule.roundOf c) j

@[simp] theorem mem_scheduleLegal (T : StagedChip K rounds chronology)
    (c : Fin T.air.numTraceCols) (j : Fin chronology.numChallenges) :
    j ∈ scheduleLegal T c ↔ chronology.usableByColumnOf (T.schedule.roundOf c) j := by
  simp [scheduleLegal]

/-- The saturated chip's declaration *is* the schedule-legal set, definitionally. -/
theorem saturate_columnChallenges (T : StagedChip K rounds chronology)
    (c : Fin T.air.numTraceCols) : (saturate T).columnChallenges c = scheduleLegal T c := rfl

/-- **The excess of a declaration**: the `(column, coin)` pairs the schedule permits and the
declaration withholds.  This is the exact measure of what `RoundFibred.StagedAssignment.col_reads`
assumes beyond the paper's binding — `binding_implies_declaration_iff_saturated` is the
statement that the two properties coincide iff this is everywhere empty. -/
noncomputable def excess (T : StagedChip K rounds chronology)
    (c : Fin T.air.numTraceCols) : Finset (Fin chronology.numChallenges) :=
  scheduleLegal T c \ T.columnChallenges c

theorem mem_excess (T : StagedChip K rounds chronology) (c : Fin T.air.numTraceCols)
    (j : Fin chronology.numChallenges) :
    j ∈ excess T c ↔
      chronology.usableByColumnOf (T.schedule.roundOf c) j ∧ j ∉ T.columnChallenges c := by
  simp [excess]

/-- **`Saturated` is exactly "the excess is empty everywhere".** -/
theorem saturated_iff_excess_eq_empty (T : StagedChip K rounds chronology) :
    Saturated T ↔ ∀ c, excess T c = ∅ := by
  constructor
  · intro hsat c
    refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
    exact ((mem_excess T c j).mp hj).2 (hsat c j ((mem_excess T c j).mp hj).1)
  · intro h c j hlegal
    by_contra hmem
    have : j ∈ excess T c := (mem_excess T c j).mpr ⟨hlegal, hmem⟩
    rw [h c] at this
    exact absurd this (Finset.notMem_empty _)

/-- The saturated chip has no excess. -/
theorem excess_saturate (T : StagedChip K rounds chronology) (c : Fin T.air.numTraceCols) :
    excess (saturate T) c = ∅ :=
  (saturated_iff_excess_eq_empty _).mp (saturate_saturated T) c

/-! ## 2. The excess is the only freedom: maximality and uniqueness -/

/-- **Every legal declaration is contained in the saturated one.**  This is
`StagedChip.columns_commit_before_sampling` read as an inclusion: a chip can only ever *withhold*
coins the schedule permits, never add ones it forbids. -/
theorem columnChallenges_subset_scheduleLegal (T : StagedChip K rounds chronology)
    (c : Fin T.air.numTraceCols) : T.columnChallenges c ⊆ scheduleLegal T c := by
  intro j hj
  exact (mem_scheduleLegal T c j).mpr (T.columns_commit_before_sampling c j hj)

/-- So `saturate T` is the **maximum** legal chip over `T`'s AIR, params and schedule, and the
excess is the distance to it. -/
theorem scheduleLegal_eq_columnChallenges_union_excess (T : StagedChip K rounds chronology)
    (c : Fin T.air.numTraceCols) :
    scheduleLegal T c = T.columnChallenges c ∪ excess T c := by
  rw [excess, Finset.union_sdiff_self_eq_union,
    Finset.union_eq_right.mpr (columnChallenges_subset_scheduleLegal T c)]

/-- The declaration equals the saturated one exactly when the chip is saturated. -/
theorem columnChallenges_eq_scheduleLegal_iff_saturated (T : StagedChip K rounds chronology) :
    (∀ c, T.columnChallenges c = scheduleLegal T c) ↔ Saturated T := by
  constructor
  · intro h c j hlegal
    rw [h c]
    exact (mem_scheduleLegal T c j).mpr hlegal
  · intro hsat c
    exact saturated_columnChallenges_eq T hsat c

/--

`GigaIOThirdMessageProduction.two_message_exclusion_is_a_choice_three_message_is_not` builds a
second legal chip over `GigaIOSlots.finiteComputeChip`'s AIR, params and schedule; by this theorem
no such second chip exists once both are saturated. -/
theorem eq_of_saturated {T₁ T₂ : StagedChip K rounds chronology}
    (hsat₁ : Saturated T₁) (hsat₂ : Saturated T₂)
    (hair : T₁.air = T₂.air) (hpar : T₁.params = T₂.params)
    (hsch : HEq T₁.schedule T₂.schedule) : T₁ = T₂ := by
  have hcc : ∀ c, T₁.columnChallenges c = scheduleLegal T₁ c :=
    (columnChallenges_eq_scheduleLegal_iff_saturated T₁).mpr hsat₁
  have hcc₂ : ∀ c, T₂.columnChallenges c = scheduleLegal T₂ c :=
    (columnChallenges_eq_scheduleLegal_iff_saturated T₂).mpr hsat₂
  obtain ⟨a₁, p₁, s₁, cc₁, hb₁⟩ := T₁
  obtain ⟨a₂, p₂, s₂, cc₂, hb₂⟩ := T₂
  simp only at hair hpar hsch hcc hcc₂
  subst hair
  subst hpar
  obtain rfl : s₁ = s₂ := eq_of_heq hsch
  have : cc₁ = cc₂ := by
    funext c
    rw [hcc c, hcc₂ c]
    exact rfl
  subst this
  rfl

/-- The same statement in the form the concrete chips use, with no `HEq`: at a common AIR and a
common round map, two saturated declarations agree column by column. -/
theorem columnChallenges_eq_of_saturated {T₁ T₂ : StagedChip K rounds chronology}
    (hsat₁ : Saturated T₁) (hsat₂ : Saturated T₂)
    (c₁ : Fin T₁.air.numTraceCols) (c₂ : Fin T₂.air.numTraceCols)
    (hround : T₁.schedule.roundOf c₁ = T₂.schedule.roundOf c₂) :
    T₁.columnChallenges c₁ = T₂.columnChallenges c₂ := by
  rw [saturated_columnChallenges_eq T₁ hsat₁ c₁, saturated_columnChallenges_eq T₂ hsat₂ c₂,
    hround]

/-! ## 3. At a saturated chip, `col_reads` *is* the round order

`CommitmentModel.BindingAssignment.toStagedAssignmentSaturate` already sends a binding-legal
prover to a legal `StagedAssignment` against `saturate T`.  The converse holds too, so the two
types are equivalent: the declaration-respecting provers against the saturated chip are *exactly*
the provers the paper's commitment scheme admits.  There is nothing left for a prover to
choose. -/

/-- The inverse of `CommitmentModel.BindingAssignment.toStagedAssignmentSaturate`. -/
def bindingOfStagedAssignmentSaturate {T : StagedChip K rounds chronology} {V : Type*}
    (A : StagedAssignment (saturate T) V) : BindingAssignment T V where
  col := A.col
  col_binding := (saturate_respectsDeclaration_iff T A.col).mp A.col_reads


/-- **The headline of §3.**  At a saturated chip the prover class quantified over by
`RoundFibred.StagedAssignment` is *literally* the prover class the paper's binding commitment
scheme admits.  So a soundness statement at `saturate T` ranges over `(coins, round order)` and
over nothing else. -/
def stagedAssignmentSaturateEquiv (T : StagedChip K rounds chronology) (V : Type*) :
    StagedAssignment (saturate T) V ≃ BindingAssignment T V where
  toFun := bindingOfStagedAssignmentSaturate
  invFun := BindingAssignment.toStagedAssignmentSaturate
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem stagedAssignmentSaturateEquiv_trace (T : StagedChip K rounds chronology)
    {V : Type*} (A : StagedAssignment (saturate T) V)
    (χ : Fin chronology.numChallenges → K) :
    (stagedAssignmentSaturateEquiv T V A).trace χ = A.trace χ := rfl

/-- Saturation costs nothing on the AIR side: the same trace satisfies both chips, by `Iff.rfl`. -/
theorem saturate_satisfies_iff' (T : StagedChip K rounds chronology)
    (P : Fin T.air.numTraceCols → K[X]) : (saturate T).Satisfies P ↔ T.Satisfies P := Iff.rfl

end Nock.NockVMROM.Thm54.SaturatedDeclaration

/-! ## 4. The shipped chips, measured -/

namespace Nock.NockVMROM.Thm54.SaturatedDeclaration

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GigaFinite
open Nock.NockVMROM.Thm54.GigaIOSlots
open Nock.NockVMROM.Thm54.GigaIOThirdMessage
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.CommitmentModel
open Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology
open scoped Polynomial

/-! ### 4.1 The three-message (shipped) chips -/

/-- The schedule-legal coin set of the three-message chronology, per round.  Round `1` admits the
four round-`0` coins `z, a, b, c`; round `2` admits those plus `α, α_C, β, γ`; round `3` admits all
ten, the two `RAP_prog-IO` slots included. -/
theorem io3_legal_by_round (r : Fin 4) :
    (Finset.univ.filter fun j : Fin 10 => nockChronologyIO3.usableByColumnOf r j)
      = ![(∅ : Finset (Fin 10)), {1, 2, 3, 4}, {0, 1, 2, 3, 4, 5, 6, 7}, Finset.univ] r := by
  revert r; decide

/-- **The compute declaration is placement-independent.**  `IOPlacement3.canonical_up_to_transposition`
pins `{S.slot 0, S.slot 1} = {8, 9}`, so `finComputeRoundChalOf4` takes the same four values at
every placement. -/
theorem finComputeRoundChalOf4_eq (S : IOPlacement3) (r : Fin 4) :
    finComputeRoundChalOf4 S r
      = ![(∅ : Finset (Fin 10)), {1, 2, 3, 4}, {0, 1, 2, 3, 4, 5},
          {0, 1, 2, 3, 4, 5, 8, 9}] r := by
  rcases S.canonical_up_to_transposition with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    · unfold finComputeRoundChalOf4
      rw [h0, h1]
      revert r
      decide

theorem finMemRoundChalOf4_eq (S : IOPlacement3) (r : Fin 4) :
    finMemRoundChalOf4 S r
      = ![(∅ : Finset (Fin 10)), {1}, {0, 1, 6, 7}, {0, 1, 6, 7, 8, 9}] r := by
  rcases S.canonical_up_to_transposition with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    · unfold finMemRoundChalOf4
      rw [h0, h1]
      revert r
      decide

variable {K : Type*} [Field K]


/-- **The compute chip's excess, per column.**  Empty at rounds `0` and `1`; the two *memory*
coins `β, γ` (slots `6, 7`) at every round-`2` and round-`3` column.

Those two coins are schedule-legal for every compute column of the mega-ext block and the
declaration withholds them from all of them.  The withholding is sound — the compute AIR does not
read slots `6, 7` — but it is not *derived*: `CommitmentModel.binding_col_not_respecting_declaration`
builds a binding-legal prover that violates it.  §4.3 deletes it. -/
theorem computeChip3_excess (S : IOPlacement3) (q : SegmentedRAPParams K) (c : Fin 113) :
    excess (computeChip3 S q) c
      = if ((finComputeRoundOf4 c : Fin 4) : ℕ) ≤ 1 then (∅ : Finset (Fin 10)) else {6, 7} := by
  show (Finset.univ.filter fun j : Fin 10 =>
      nockChronologyIO3.usableByColumnOf (finComputeRoundOf4 c) j)
        \ finComputeRoundChalOf4 S (finComputeRoundOf4 c) = _
  rw [io3_legal_by_round, finComputeRoundChalOf4_eq]
  generalize finComputeRoundOf4 c = r
  revert r; decide

/-- The memory twin: the three compute-only round-`0` coins `a, b, c` at round `1`, and those plus
the compute walk's own `α_C` at rounds `2` and `3`. -/
theorem memoryChip3_excess (S : IOPlacement3) (q : SegmentedRAPParams K) (c : Fin 55) :
    excess (memoryChip3 S q) c
      = ![(∅ : Finset (Fin 10)), {2, 3, 4}, {2, 3, 4, 5}, {2, 3, 4, 5}] (finMemRoundOf4 c) := by
  show (Finset.univ.filter fun j : Fin 10 =>
      nockChronologyIO3.usableByColumnOf (finMemRoundOf4 c) j)
        \ finMemRoundChalOf4 S (finMemRoundOf4 c) = _
  rw [io3_legal_by_round, finMemRoundChalOf4_eq]
  generalize finMemRoundOf4 c = r
  revert r; decide


/-- **The number that matters: no IO slot is ever in the excess.**

So at the shipped chips the `RAP_prog-IO` exclusion of
`GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute` is **derived from the round
order**, not declared: at every column that does not declare an IO slot, the schedule does not
permit one either.  This is that theorem restated as a measurement, and it is the property the
two-message chips fail (§4.2). -/
theorem computeChip3_excess_has_no_io_slot (S : IOPlacement3) (q : SegmentedRAPParams K)
    (c : Fin 113) (i : Fin 2) :
    S.slot i ∉ excess (computeChip3 S q) c := by
  rw [computeChip3_excess S q c]
  have hmem : ∀ j : Fin 10, nockSampledAfterIO3 j = 2 → j ∉ ({6, 7} : Finset (Fin 10)) := by
    decide
  split
  · exact Finset.notMem_empty _
  · exact hmem (S.slot i) (S.third_message i)

theorem memoryChip3_excess_has_no_io_slot (S : IOPlacement3) (q : SegmentedRAPParams K)
    (c : Fin 55) (i : Fin 2) :
    S.slot i ∉ excess (memoryChip3 S q) c := by
  rw [memoryChip3_excess S q c]
  have hmem : ∀ r : Fin 4, ∀ j : Fin 10, nockSampledAfterIO3 j = 2 →
      j ∉ ![(∅ : Finset (Fin 10)), {2, 3, 4}, {2, 3, 4, 5}, {2, 3, 4, 5}] r := by decide
  exact hmem _ (S.slot i) (S.third_message i)

/-- **But the shipped chips are still not saturated**, so `GigaRAPThirdMessage.lean`'s header
claim that `finComputeRoundChalOf4` "carries no information the schedule does not already carry"
is false as stated.  Witness: column `65` is a round-`2` compute column and coin `6` is
schedule-legal there and undeclared. -/
theorem computeChip3_not_saturated (S : IOPlacement3) (q : SegmentedRAPParams K) :
    ¬ Saturated (computeChip3 S q) := by
  intro hsat
  have hlegal : nockChronologyIO3.usableByColumnOf
      ((computeChip3 (L := K) S q).schedule.roundOf (65 : Fin 113)) (6 : Fin 10) := by
    show (nockSampledAfterIO3 6 : ℕ) < ((finComputeRoundOf4 (65 : Fin 113) : Fin 4) : ℕ)
    decide
  have hmem := hsat (65 : Fin 113) (6 : Fin 10) hlegal
  rw [show (computeChip3 (L := K) S q).columnChallenges (65 : Fin 113)
        = finComputeRoundChalOf4 S (finComputeRoundOf4 (65 : Fin 113)) from rfl,
    finComputeRoundChalOf4_eq] at hmem
  rw [show finComputeRoundOf4 (65 : Fin 113) = 2 by decide] at hmem
  simp only [Matrix.cons_val, Matrix.cons_val_one] at hmem
  change (6 : Fin 10) ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) at hmem
  revert hmem
  decide

theorem memoryChip3_not_saturated (S : IOPlacement3) (q : SegmentedRAPParams K) :
    ¬ Saturated (memoryChip3 S q) := by
  intro hsat
  have hlegal : nockChronologyIO3.usableByColumnOf
      ((memoryChip3 (L := K) S q).schedule.roundOf (4 : Fin 55)) (2 : Fin 10) := by
    show (nockSampledAfterIO3 2 : ℕ) < ((finMemRoundOf4 (4 : Fin 55) : Fin 4) : ℕ)
    decide
  have hmem := hsat (4 : Fin 55) (2 : Fin 10) hlegal
  rw [show (memoryChip3 (L := K) S q).columnChallenges (4 : Fin 55)
        = finMemRoundChalOf4 S (finMemRoundOf4 (4 : Fin 55)) from rfl,
    finMemRoundChalOf4_eq] at hmem
  rw [show finMemRoundOf4 (4 : Fin 55) = 1 by decide] at hmem
  simp only [Matrix.cons_val, Matrix.cons_val_one] at hmem
  change (2 : Fin 10) ∈ ({1} : Finset (Fin 10)) at hmem
  revert hmem
  decide

/-! ### 4.2 The legacy two-message chips: the IO slots *are* in the excess -/

theorem withIO_legal_by_round (r : Fin 3) :
    (Finset.univ.filter fun j : Fin 10 => nockChronologyWithIO.usableByColumnOf r j)
      = ![(∅ : Finset (Fin 10)), {1, 2, 3, 4}, Finset.univ] r := by
  revert r; decide


/-- **The two-message defect, as a `Finset`.**  At compute column `111` — the `IO_prog` record
timestamp — both `RAP_prog-IO` slots are schedule-legal and undeclared, i.e. they are in the
excess.  That is exactly the co-location
`GigaIOSlots.record_timestamp_column_shares_the_message_with_the_io_coins` records, and exactly
what `computeChip3_excess_has_no_io_slot` shows the third message removes. -/
theorem finiteComputeChip_excess_contains_the_io_slots_at_111 (S : IOSlots)
    (q : SegmentedRAPParams K) (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j) (i : Fin 2) :
    S.slot i ∈ excess (finiteComputeChip S q) (111 : Fin 113) := by
  have hshare := record_timestamp_column_shares_the_message_with_the_io_coins S hfresh
  refine (mem_excess (finiteComputeChip S q) (111 : Fin 113) (S.slot i)).mpr ⟨?_, ?_⟩
  · have hr : (finiteComputeChip (L := K) S q).schedule.roundOf (111 : Fin 113) = (2 : Fin 3) :=
      hshare.1.1
    rw [hr]
    exact (S.commit_then_sample i).2
  · exact (io_records_read_no_io_coin S hfresh).1 111 (by decide) (by decide) i

theorem finiteMemoryChip_excess_contains_the_io_slots_at_52 (S : IOSlots)
    (q : SegmentedRAPParams K) (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j) (i : Fin 2) :
    S.slot i ∈ excess (finiteMemoryChip S q) (53 : Fin 55) := by
  have hshare := record_timestamp_column_shares_the_message_with_the_io_coins S hfresh
  refine (mem_excess (finiteMemoryChip S q) (53 : Fin 55) (S.slot i)).mpr ⟨?_, ?_⟩
  · have hr : (finiteMemoryChip (L := K) S q).schedule.roundOf (53 : Fin 55) = (2 : Fin 3) :=
      hshare.1.2
    rw [hr]
    exact (S.commit_then_sample i).2
  · exact (io_records_read_no_io_coin S hfresh).2 53 (by decide) (by decide) i


/-- **The separation, on the excess axis.**  The IO slots are in the excess of the two-message
compute chip and in the excess of no column of the three-message one.  This is
`GigaIOThirdMessageProduction.two_message_exclusion_is_a_choice_three_message_is_not` measured
rather than case-split, and it says the same thing: the migration was necessary. -/
theorem io_exclusion_is_excess_at_two_messages_and_derived_at_three
    (S : IOSlots) (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j)
    (S3 : IOPlacement3) (q : SegmentedRAPParams K) :
    (∀ i, S.slot i ∈ excess (finiteComputeChip S q) (111 : Fin 113))
      ∧ (∀ i, S.slot i ∈ excess (finiteMemoryChip S q) (53 : Fin 55))
      ∧ (∀ c : Fin 113, ∀ i, S3.slot i ∉ excess (computeChip3 S3 q) c)
      ∧ (∀ c : Fin 55, ∀ i, S3.slot i ∉ excess (memoryChip3 S3 q) c) :=
  ⟨fun i => finiteComputeChip_excess_contains_the_io_slots_at_111 S q hfresh i,
   fun i => finiteMemoryChip_excess_contains_the_io_slots_at_52 S q hfresh i,
   fun c i => computeChip3_excess_has_no_io_slot S3 q c i,
   fun c i => memoryChip3_excess_has_no_io_slot S3 q c i⟩

/-! ### 4.3 The saturated shipped chips: the declaration deleted -/

/-- **The shipped compute chip with its declaration derived.**  Same AIR, same params, same
schedule, same chronology; `columnChallenges` is now the schedule-legal set, so the field carries
no data. -/
noncomputable def computeChip3Sat (S : IOPlacement3) (q : SegmentedRAPParams K) :
    StagedChip K 4 nockChronologyIO3 :=
  saturate (computeChip3 S q)

/-- The memory twin. -/
noncomputable def memoryChip3Sat (S : IOPlacement3) (q : SegmentedRAPParams K) :
    StagedChip K 4 nockChronologyIO3 :=
  saturate (memoryChip3 S q)

@[simp] theorem computeChip3Sat_air (S : IOPlacement3) (q : SegmentedRAPParams K) :
    (computeChip3Sat S q).air = (computeChip3 S q).air := rfl

@[simp] theorem memoryChip3Sat_air (S : IOPlacement3) (q : SegmentedRAPParams K) :
    (memoryChip3Sat S q).air = (memoryChip3 S q).air := rfl

@[simp] theorem computeChip3Sat_schedule (S : IOPlacement3) (q : SegmentedRAPParams K) :
    (computeChip3Sat S q).schedule = (computeChip3 S q).schedule := rfl

@[simp] theorem memoryChip3Sat_schedule (S : IOPlacement3) (q : SegmentedRAPParams K) :
    (memoryChip3Sat S q).schedule = (memoryChip3 S q).schedule := rfl


theorem computeChip3Sat_satisfies_iff (S : IOPlacement3) (q : SegmentedRAPParams K)
    (P : Fin (computeChip3 S q).air.numTraceCols → K[X]) :
    (computeChip3Sat S q).Satisfies P ↔ (computeChip3 S q).Satisfies P := Iff.rfl

theorem memoryChip3Sat_satisfies_iff (S : IOPlacement3) (q : SegmentedRAPParams K)
    (P : Fin (memoryChip3 S q).air.numTraceCols → K[X]) :
    (memoryChip3Sat S q).Satisfies P ↔ (memoryChip3 S q).Satisfies P := Iff.rfl

theorem computeChip3Sat_saturated (S : IOPlacement3) (q : SegmentedRAPParams K) :
    Saturated (computeChip3Sat S q) := saturate_saturated _

theorem memoryChip3Sat_saturated (S : IOPlacement3) (q : SegmentedRAPParams K) :
    Saturated (memoryChip3Sat S q) := saturate_saturated _


/-- **What the migration buys, type-level.**  The prover class the soundness statements quantify
over at `computeChip3Sat` is exactly `CommitmentModel.BindingAssignment (computeChip3 S q)` — the
provers the paper's binding commitment scheme admits — with no per-column annotation left to
choose. -/
noncomputable def computeChip3Sat_assignments (S : IOPlacement3) (q : SegmentedRAPParams K) (V : Type*) :
    StagedAssignment (computeChip3Sat S q) V ≃ BindingAssignment (computeChip3 S q) V :=
  stagedAssignmentSaturateEquiv (computeChip3 S q) V

noncomputable def memoryChip3Sat_assignments (S : IOPlacement3) (q : SegmentedRAPParams K) (V : Type*) :
    StagedAssignment (memoryChip3Sat S q) V ≃ BindingAssignment (memoryChip3 S q) V :=
  stagedAssignmentSaturateEquiv (memoryChip3 S q) V

/-- **No rival chip.**  Any legal chip of the three-message chronology with the shipped AIR, params
and schedule whose declaration is saturated *is* `computeChip3Sat`.  So the two-legal-chips
construction of `GigaIOThirdMessageProduction.two_message_exclusion_is_a_choice_three_message_is_not`
has no instance here: it needs a second declaration, and there is only one. -/
theorem computeChip3Sat_unique (S : IOPlacement3) (q : SegmentedRAPParams K)
    (T : StagedChip K 4 nockChronologyIO3) (hsat : Saturated T)
    (hair : T.air = (computeChip3Sat S q).air)
    (hpar : T.params = (computeChip3Sat S q).params)
    (hsch : HEq T.schedule (computeChip3Sat S q).schedule) :
    T = computeChip3Sat S q :=
  eq_of_saturated hsat (computeChip3Sat_saturated S q) hair hpar hsch

theorem memoryChip3Sat_unique (S : IOPlacement3) (q : SegmentedRAPParams K)
    (T : StagedChip K 4 nockChronologyIO3) (hsat : Saturated T)
    (hair : T.air = (memoryChip3Sat S q).air)
    (hpar : T.params = (memoryChip3Sat S q).params)
    (hsch : HEq T.schedule (memoryChip3Sat S q).schedule) :
    T = memoryChip3Sat S q :=
  eq_of_saturated hsat (memoryChip3Sat_saturated S q) hair hpar hsch

/-! ### 4.4 The consumers survive the deletion

The freshness argument of `GigaIOThirdMessage.lean` §8 goes through
`RoundFibred.columnLocal_const_of_prior_challenges`, whose only structural input is
`StagedChip.columns_commit_before_sampling`; it therefore re-derives verbatim at the saturated
chips.  the paper's schedule condition is a theorem about them for the same reason. -/

theorem computeChip3Sat_records_committed_early (S : IOPlacement3) (q : SegmentedRAPParams K) :
    ProgIORecordsCommittedByRoundTwo (computeChip3Sat S q) :=
  computeChip3_records_committed_early S q

theorem memoryChip3Sat_records_committed_early (S : IOPlacement3) (q : SegmentedRAPParams K) :
    MemIORecordsCommittedByRoundTwo (memoryChip3Sat S q) :=
  memoryChip3_records_committed_early S q


/-- **The IO-coin exclusion at the saturated chip**, from the round order alone — the same
instance of `GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute`, which quantifies
over every chip of the chronology and so does not notice that the declaration changed. -/
theorem computeChip3Sat_io_data_undeclared (S : IOPlacement3) (q : SegmentedRAPParams K)
    (c : Fin (computeChip3Sat S q).air.numTraceCols) (h1 : 102 ≤ (c : ℕ)) (h2 : (c : ℕ) ≤ 111)
    (i : Fin 2) : S.slot i ∉ (computeChip3Sat S q).columnChallenges c :=
  committed_early_excludes_the_io_coins_compute S (computeChip3Sat S q)
    (computeChip3Sat_records_committed_early S q) c h1 h2 i

theorem memoryChip3Sat_io_data_undeclared (S : IOPlacement3) (q : SegmentedRAPParams K)
    (c : Fin (memoryChip3Sat S q).air.numTraceCols) (h1 : 44 ≤ (c : ℕ)) (h2 : (c : ℕ) ≤ 53)
    (i : Fin 2) : S.slot i ∉ (memoryChip3Sat S q).columnChallenges c :=
  committed_early_excludes_the_io_coins_memory S (memoryChip3Sat S q)
    (memoryChip3Sat_records_committed_early S q) c h1 h2 i


/-- **The freshness conclusion at the saturated chip.**  `GigaIOThirdMessage.prog_records_const_in_the_io_coins3`
with the declaration deleted: any readout of the compute `IO_prog` columns takes the same value at
two coin vectors agreeing off the two IO slots, for **every** prover the commitment scheme admits.

-/
theorem prog_records_const_in_the_io_coins3_sat {V β : Type*}
    (S : IOPlacement3) (q : SegmentedRAPParams K)
    (A : StagedAssignment (computeChip3Sat S q) V)
    (L : ColumnLocal (computeChip3 S q) V β) (hL : L.cols ⊆ progIoDataCols3 S q)
    (χ₁ χ₂ : Fin 10 → K)
    (hagree : ∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) :=
  prog_records_const_in_the_io_coins_from_binding (K := K) (V := V) (β := β) S q
    (bindingOfStagedAssignmentSaturate A) L hL χ₁ χ₂ hagree

theorem mem_records_const_in_the_io_coins3_sat {V β : Type*}
    (S : IOPlacement3) (q : SegmentedRAPParams K)
    (A : StagedAssignment (memoryChip3Sat S q) V)
    (L : ColumnLocal (memoryChip3 S q) V β) (hL : L.cols ⊆ memIoDataCols3 S q)
    (χ₁ χ₂ : Fin 10 → K)
    (hagree : ∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) :=
  mem_records_const_in_the_io_coins_from_binding (K := K) (V := V) (β := β) S q
    (bindingOfStagedAssignmentSaturate A) L hL χ₁ χ₂ hagree

/-! ### 4.5 The priced bound depends on the chip only through the constancy fact

`GigaIOThirdMessage.io_failure_roundUnion_card_le3` takes `A : StagedAssignment (computeChip3 S q) V`
and `L` and runs the union bound.  Nothing in that proof reads the chip again after
`prog_records_const_in_the_io_coins3` has been applied, so the bound is really a theorem about a
*record family* `rec : (Fin 10 → K) → PreChallengeRecords K m` that is constant off the two IO
slots.  Stating it that way is what lets the same number be quoted at the saturated chip without
re-proving anything. -/

section GenericBound

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}

/-- The per-coordinate bad-set family of a record family: the record-RLC collisions on the `γ`
coordinate, the pole-hit and log-derivative events on the pole coordinate, nothing elsewhere.
Definitionally `GigaIOThirdMessage.ioBad3` at `rec := fun χ => L.out (A.trace χ)`. -/
noncomputable def ioBadOf (S : IOPlacement3) (rec : (Fin 10 → K) → PreChallengeRecords K m)
    (i : Fin 10) (χ : Fin 10 → K) : Finset K :=
  if i = S.slot 0 then IORLCCollisionEvent (rec χ)
  else if i = S.slot 1 then
    IOPoleHitEvent (rec χ) (χ (S.slot 0)) ∪ IOLogDerivEvent (rec χ) (χ (S.slot 0))
  else ∅

theorem ioBadOf_eq_ioBad3 {V : Type*} (S : IOPlacement3) (q : SegmentedRAPParams K)
    (A : StagedAssignment (computeChip3 S q) V)
    (L : ColumnLocal (computeChip3 S q) V (PreChallengeRecords K m)) :
    ioBadOf S (fun χ => L.out (A.trace χ)) = ioBad3 S q A L := rfl


/-- **The `|K|^9 · (B_γ + B_pole)` bound, with the chip abstracted away.**  The only input about
the prover is `hconst`: the records do not move when the two IO coins move.  At the shipped chips
that is `GigaIOThirdMessage.prog_records_const_in_the_io_coins3`; at the saturated chips it is
`prog_records_const_in_the_io_coins3_sat`, which derives it from the paper's binding alone.

The proof is `GigaIOThirdMessage.io_failure_roundUnion_card_le3`'s, with `A`/`L` replaced by `rec`
and the two `readsOn` facts obtained from `hconst` rather than from the chip. -/
theorem io_failure_roundUnion_card_le_of_const (S : IOPlacement3)
    (rec : (Fin 10 → K) → PreChallengeRecords K m)
    (hconst : ∀ χ₁ χ₂ : Fin 10 → K,
      (∀ j, j ≠ S.slot 0 → j ≠ S.slot 1 → χ₁ j = χ₂ j) → rec χ₁ = rec χ₂)
    (Bγ Bpole : ℕ)
    (hBγ : ∀ χ, (IORLCCollisionEvent (rec χ)).card ≤ Bγ)
    (hBpole : ∀ χ, (IOPoleHitEvent (rec χ) (χ (S.slot 0))
      ∪ IOLogDerivEvent (rec χ) (χ (S.slot 0))).card ≤ Bpole) :
    (roundUnion (C := K) {S.slot 0, S.slot 1} (ioBadOf S rec)).card
      ≤ Fintype.card K ^ 9 * Bγ + Fintype.card K ^ 9 * Bpole := by
  classical
  haveI : Nonempty K := ⟨0⟩
  have hne : S.slot 0 ≠ S.slot 1 := S.slot_ne
  refine le_trans (roundUnion_card_le (C := K) {S.slot 0, S.slot 1} (ioBadOf S rec) (ioDep3 S)
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
      have hrec : rec χ₁ = rec χ₂ := by
        refine hconst χ₁ χ₂ fun j h0 h1 => hag j ?_
        simp only [ioDepGamma3, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or]
        exact ⟨h0, h1⟩
      simp [ioBadOf, hrec]
    · rw [show ioDep3 S (S.slot 1) = ioDepPole3 S from if_pos rfl]
      intro χ₁ χ₂ hag
      have hgamma : χ₁ (S.slot 0) = χ₂ (S.slot 0) := hag _ (gamma_mem_ioDepPole3 S)
      have hrec : rec χ₁ = rec χ₂ := by
        refine hconst χ₁ χ₂ fun j _ h1 => hag j ?_
        simp only [ioDepPole3, Finset.mem_erase, Finset.mem_univ, and_true]
        exact h1
      simp only [ioBadOf, if_neg hne.symm, if_pos rfl, hrec, hgamma]
  · intro i χ
    by_cases h0 : i = S.slot 0
    · subst h0; simpa [ioBadOf] using hBγ χ
    · by_cases h1 : i = S.slot 1
      · subst h1; simpa [ioBadOf, h0] using hBpole χ
      · simp [ioBadOf, h0, h1]
  · have e0 : (if S.slot 0 = S.slot 0 then Bγ else if S.slot 0 = S.slot 1 then Bpole else 0)
        = Bγ := by simp
    have e1 : (if S.slot 1 = S.slot 0 then Bγ else if S.slot 1 = S.slot 1 then Bpole else 0)
        = Bpole := by simp [hne.symm]
    rw [Finset.sum_pair hne, e0, e1]


/-- **The priced bound at the saturated chip.**  Same number as
`GigaIOThirdMessage.io_failure_roundUnion_card_le3` — `|K|^9 · (B_γ + B_pole)` out of `|K|^10`,
which `GigaIOFreshness.io_round_price_is_the_ioWork_charge` identifies with the existing
`ioWork / cardK²` charge — now quantified over *every* prover the commitment scheme admits, with
no per-column declaration anywhere in the hypothesis list. -/
theorem io_failure_roundUnion_card_le3_sat {V : Type*} (S : IOPlacement3)
    (q : SegmentedRAPParams K)
    (A : StagedAssignment (computeChip3Sat S q) V)
    (L : ColumnLocal (computeChip3 S q) V (PreChallengeRecords K m))
    (hL : L.cols ⊆ progIoDataCols3 S q) (Bγ Bpole : ℕ)
    (hBγ : ∀ χ, (IORLCCollisionEvent (L.out (A.trace χ))).card ≤ Bγ)
    (hBpole : ∀ χ, (IOPoleHitEvent (L.out (A.trace χ)) (χ (S.slot 0))
      ∪ IOLogDerivEvent (L.out (A.trace χ)) (χ (S.slot 0))).card ≤ Bpole) :
    (roundUnion (C := K) {S.slot 0, S.slot 1}
        (ioBadOf S (fun χ => L.out (A.trace χ)))).card
      ≤ Fintype.card K ^ 9 * Bγ + Fintype.card K ^ 9 * Bpole :=
  io_failure_roundUnion_card_le_of_const S (fun χ => L.out (A.trace χ))
    (fun χ₁ χ₂ hagree =>
      prog_records_const_in_the_io_coins3_sat (β := PreChallengeRecords K m) S q A L hL
        χ₁ χ₂ hagree)
    Bγ Bpole hBγ hBpole

end GenericBound

end Nock.NockVMROM.Thm54.SaturatedDeclaration

section Audit

open Nock.NockVMROM.Thm54.SaturatedDeclaration

#check @excess
#check @saturated_iff_excess_eq_empty
#check @columnChallenges_subset_scheduleLegal
#check @eq_of_saturated
#check @stagedAssignmentSaturateEquiv
#check @computeChip3_excess
#check @memoryChip3_excess
#check @computeChip3_excess_has_no_io_slot
#check @computeChip3_not_saturated
#check @finiteComputeChip_excess_contains_the_io_slots_at_111
#check @io_exclusion_is_excess_at_two_messages_and_derived_at_three
#check @computeChip3Sat_assignments
#check @computeChip3Sat_unique
#check @prog_records_const_in_the_io_coins3_sat
#check @io_failure_roundUnion_card_le_of_const
#check @io_failure_roundUnion_card_le3_sat

#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.saturated_iff_excess_eq_empty
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.columnChallenges_subset_scheduleLegal
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.scheduleLegal_eq_columnChallenges_union_excess
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.eq_of_saturated
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.columnChallenges_eq_of_saturated
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.computeChip3_excess
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.memoryChip3_excess
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.computeChip3_excess_has_no_io_slot
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.memoryChip3_excess_has_no_io_slot
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.computeChip3_not_saturated
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.memoryChip3_not_saturated
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.finiteComputeChip_excess_contains_the_io_slots_at_111
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.finiteMemoryChip_excess_contains_the_io_slots_at_52
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.io_exclusion_is_excess_at_two_messages_and_derived_at_three
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.computeChip3Sat_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.computeChip3Sat_saturated
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.computeChip3Sat_unique
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.memoryChip3Sat_unique
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.computeChip3Sat_io_data_undeclared
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.memoryChip3Sat_io_data_undeclared
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.prog_records_const_in_the_io_coins3_sat
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.mem_records_const_in_the_io_coins3_sat
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.ioBadOf_eq_ioBad3
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.io_failure_roundUnion_card_le_of_const
#print axioms Nock.NockVMROM.Thm54.SaturatedDeclaration.io_failure_roundUnion_card_le3_sat

end Audit
