import Nock.NockVMROM.Thm54.CanonicalRAP
import Nock.NockVMROM.Thm54.MultiRoundRAP
import Nock.Framework.Thm54.SegmentedRAP
import Mathlib.Data.Nat.Size

/-!
# Staged, kind-segmented tables: the two RAP axes over one column layout

Two *independent* partitions of one RAP, both already typed in this tree:

* **rounds** partition the *columns* by which challenges they may read
  (`Staging.RoundSchedule`, `Staging.ChallengeChronology`, `MultiRoundRAP.lean:60,101`);
* **kinds** partition the *constraints* by which rows they apply to
  (`SegmentedRAPParams.domain : Reified.ConstraintKind → Finset K`, `CanonicalRAP.lean:47`),
  each enforced by its own evaluation domain — the deployed client divides each constraint
  category by its own zerofier (`stark/verifier.hoon:639-655`) rather than masking rows.

They cross: the client's `%ln-inc` is a `transition` constraint on `%ln`, a mega-ext column, so
neither axis determines the other.

## The gap this module closes

`Reify.airToRAP` (`Framework/NockInstances.lean:307`) sets `k := 1` and
`wRAP := fun _ => air.numTraceCols` (`:310-311`), so every RAP derived from a `Reified.AIR`
carries a *trivial* round structure and `Def:RAP`'s per-round widths `w_RAP(i)`
have no home on the AIR route.  `SegmentedRAPParams.rapStaged` is the `airToRAP` variant that
takes a `RoundSchedule` and sets `k`/`wRAP`/`w_eq` from it, discharging `w = Σ_i w_RAP(i)` with
the already-proved `RoundSchedule.total_width`.

Every other `RAP` field is *literally* `airToRAP`'s, so `RAP.Satisfies` — which reads only
`s`, `H`, `ω`, `C` and `w` — is unchanged: `rapStaged_satisfies_iff` is `Iff.rfl`.  That is what
lets every existing `Satisfies`-based result transfer to the staged object.

## FRI degree bound

`StagedChip.compDegree` / `GigaRAP.friDegBound` mirror the client's `degree-processing`
(`ztd/eight.hoon:180-202`): a per-constraint composition degree that depends on the constraint's
*kind*, a running max over every constraint of every table, and a final round-up to `2^k - 1`
(`:183`, `(dec (bex (xeb (dec d))))`).  **This is a separate quantity from `RAP.d`**: `RAP.d` is
`Def:RAP`'s maximal constraint degree and `airToRAP` already sets it to the actual supremum
(`NockInstances.lean:315`); the FRI bound is the *resource* claim computed alongside, and it is
not an admissibility condition — nothing in the client rejects a larger one.
-/

namespace Nock.NockVMROM.Thm54

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.Staging
open scoped Polynomial

/-! ## 1. `rapStaged`: `airToRAP` with a real round structure -/

namespace SegmentedRAPParams

variable {K : Type*} [Field K]

/-- **The per-kind ordinary RAP of one problem, with its round structure set from a schedule.**

Identical to `SegmentedRAPParams.rap` (`CanonicalRAP.lean:59`) in every field except `k`, `wRAP`
and `w_eq`: `k` is the schedule's round count, `wRAP` is the schedule's per-round width
(`Def:RAP`'s `w_RAP(i)`, the paper), and `w = Σ_i w_RAP(i)` is discharged by
`RoundSchedule.total_width` rather than by `simp` on the trivial one-round sum. -/
@[reducible] noncomputable def rapStaged (q : SegmentedRAPParams K) (air : Reified.AIR)
    {rounds : ℕ} (S : RoundSchedule air.numTraceCols rounds)
    (kind : Reified.ConstraintKind) : RAP K :=
  { q.rap air kind with
    k := rounds
    wRAP := S.width
    w_eq := S.total_width }

variable (q : SegmentedRAPParams K) (air : Reified.AIR) {rounds : ℕ}
  (S : RoundSchedule air.numTraceCols rounds) (kind : Reified.ConstraintKind)

/-! ### Agreement with `airToRAP` on everything except `k` / `wRAP` / `w_eq` -/

theorem rapStaged_e : (q.rapStaged air S kind).e = (q.rap air kind).e := rfl
theorem rapStaged_w : (q.rapStaged air S kind).w = (q.rap air kind).w := rfl
theorem rapStaged_h : (q.rapStaged air S kind).h = (q.rap air kind).h := rfl
theorem rapStaged_d : (q.rapStaged air S kind).d = (q.rap air kind).d := rfl
theorem rapStaged_s : (q.rapStaged air S kind).s = (q.rap air kind).s := rfl
theorem rapStaged_ω : (q.rapStaged air S kind).ω = (q.rap air kind).ω := rfl
theorem rapStaged_β : (q.rapStaged air S kind).β = (q.rap air kind).β := rfl
theorem rapStaged_I : (q.rapStaged air S kind).I = (q.rap air kind).I := rfl
theorem rapStaged_C : (q.rapStaged air S kind).C = (q.rap air kind).C := rfl
theorem rapStaged_H : (q.rapStaged air S kind).H = (q.rap air kind).H := rfl

/-- The column layout is `air`'s, shared across kinds by `kindSeg_numTraceCols`
(`SegmentedRAP.lean:26`). -/
theorem rapStaged_w_eq_numTraceCols :
    (q.rapStaged air S kind).w = air.numTraceCols := rfl

/-! ### The round fields, which are the point -/

/-- `k` is the schedule's round count — not `airToRAP`'s `1`. -/
theorem rapStaged_k : (q.rapStaged air S kind).k = rounds := rfl

/-- `w_RAP` is the schedule's per-round width. -/
theorem rapStaged_wRAP : (q.rapStaged air S kind).wRAP = S.width := rfl

/-- **`w = Σ_i w_RAP(i)`** holds for the real per-round widths. -/
theorem rapStaged_width_sum :
    (q.rapStaged air S kind).w = ∑ r, (q.rapStaged air S kind).wRAP r :=
  (q.rapStaged air S kind).w_eq

/-- The declared per-round widths really are the schedule's column-fibre cardinalities. -/
theorem rapStaged_wRAP_eq_fibre (r : Fin rounds) :
    (q.rapStaged air S kind).wRAP r
      = (Finset.univ.filter fun c : Fin air.numTraceCols => S.roundOf c = r).card :=
  S.width_eq r

/-! ### `Satisfies` is unchanged -/

/-- **The agreement lemma.**  `RAP.Satisfies` reads only `s`, `H` and `compose` (which reads `w`,
`ω`, `C`), and `rapStaged` leaves all of those literally alone, so staging the round structure
does not change the semantics.  Every existing `Satisfies`-based result about
`SegmentedRAPParams.rap` therefore transfers verbatim. -/
theorem rapStaged_satisfies_iff (P : Fin air.numTraceCols → K[X]) :
    (q.rapStaged air S kind).Satisfies P ↔ (q.rap air kind).Satisfies P := Iff.rfl

/-! ### Staging is not metadata -/

/-- The round structure `airToRAP` supplies is trivial: `k = 1` (`NockInstances.lean:310`). -/
theorem rap_k_eq_one : (q.rap air kind).k = 1 := rfl

/-- `airToRAP`'s single "round" is the whole trace (`NockInstances.lean:311`). -/
theorem rap_wRAP : (q.rap air kind).wRAP = fun _ => air.numTraceCols := rfl

/-- So `rapStaged` is a *different* RAP whenever the schedule has more than one round: the round
structure is real data, not a relabelling. -/
theorem rapStaged_k_ne_rap_k (h : rounds ≠ 1) :
    (q.rapStaged air S kind).k ≠ (q.rap air kind).k := h

end SegmentedRAPParams

end Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.Staged

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging
open scoped Polynomial

variable {K : Type*} [Field K]

/-! ## 2. `StagedChip`: shared data once, the four per-kind RAPs derived -/

/-- **One chip of the giga-RAP.**  The column layout, the AIR, the segment parameters and the
round schedule are stored *once*; the four per-kind RAPs are derived, not stored, since
`kindSeg_numTraceCols` (`SegmentedRAP.lean:26`) makes the layout shared by `rfl`.

**The round count and the challenge chronology are *parameters*, not fields.**  So
the interaction schedule is a property of the **proof**, not of a chip: two chips of one proof
share one chronology *by typing*, and a `GigaRAP` cannot be assembled from chips that disagree
about when the coins were sent.  Carrying `rounds`/`chronology` as fields would have let two
chips of one proof declare two independent schedules — modelling something the client does not
do. -/
structure StagedChip (K : Type*) [Field K] (rounds : ℕ)
    (chronology : ChallengeChronology rounds) where
  /-- The backend-neutral AIR of this chip. -/
  air : Reified.AIR
  /-- The per-kind evaluation domains and the common RAP parameters. -/
  params : SegmentedRAPParams K
  /-- Which round commits each column. -/
  schedule : RoundSchedule air.numTraceCols rounds
  /-- The sampled challenges each column's committed values may depend on. -/
  columnChallenges : Fin air.numTraceCols → Finset (Fin chronology.numChallenges)
  /-- **Commit before sample.**  A round-`i` column depends only on challenges sampled strictly
  before round `i`. -/
  columns_commit_before_sampling :
    ∀ c, ∀ j ∈ columnChallenges c, chronology.usableByColumnOf (schedule.roundOf c) j

namespace StagedChip

variable {rounds : ℕ} {chronology : ChallengeChronology rounds}
variable (T : StagedChip K rounds chronology)

/-- The derived per-kind staged RAP.  Four of these per table — one per `ConstraintKind`. -/
@[reducible] noncomputable def rap (kind : Reified.ConstraintKind) : RAP K :=
  T.params.rapStaged T.air T.schedule kind

/-- All four derived RAPs share the table's column layout. -/
theorem rap_w (kind : Reified.ConstraintKind) : (T.rap kind).w = T.air.numTraceCols := rfl

/-- All four derived RAPs carry the table's round count. -/
theorem rap_k (kind : Reified.ConstraintKind) : (T.rap kind).k = rounds := rfl

/-- All four derived RAPs carry the table's per-round widths. -/
theorem rap_wRAP (kind : Reified.ConstraintKind) : (T.rap kind).wRAP = T.schedule.width := rfl

/-- **The table's trace satisfies the table** iff it satisfies all four per-kind RAPs. -/
def Satisfies (P : Fin T.air.numTraceCols → K[X]) : Prop :=
  ∀ kind : Reified.ConstraintKind, (T.rap kind).Satisfies P

/-- Staging the round structure does not change table satisfaction: it is exactly the four
unstaged `SegmentedRAPParams.rap` obligations of `CanonicalRAP.lean:59`. -/
theorem satisfies_iff_segmented (P : Fin T.air.numTraceCols → K[X]) :
    T.Satisfies P ↔ ∀ kind : Reified.ConstraintKind, (T.params.rap T.air kind).Satisfies P :=
  Iff.rfl

/-! ## 3. The bridge: table satisfaction is per-constraint domain vanishing -/

/-- **`StagedChip.Satisfies` is exactly per-constraint, per-kind-domain vanishing.**

Composition of the item-1 agreement lemma with `Thm54.segmented_is_kinded`
(`SegmentedRAP.lean:31`).  Note the right-hand side quantifies over the *unfiltered*
`air.constraints` and reads each constraint's own kind's domain, so no `List.filter` index
bookkeeping appears. -/
theorem satisfies_iff_kinded (P : Fin T.air.numTraceCols → K[X]) :
    T.Satisfies P
      ↔ ∀ c ∈ T.air.constraints, ∀ x ∈ T.params.domain c.kind,
          c.expr.eval (envOfTrace P T.params.ω x T.params.chalVal T.params.pubVal) = 0 := by
  show (∀ kind : Reified.ConstraintKind,
      (airToRAP (kindSeg T.air kind) T.params.chalVal T.params.pubVal T.params.eDeg
        T.params.hExp T.params.ω T.params.βcoset (T.params.domain kind)
        T.params.βcoset_ne_zero T.params.hExp_pos).Satisfies P) ↔ _
  exact segmented_is_kinded T.air T.params.chalVal T.params.pubVal T.params.eDeg T.params.hExp
    T.params.ω T.params.βcoset T.params.βcoset_ne_zero T.params.hExp_pos T.params.domain P

/-- Restated at one kind: the derived staged RAP for `kind` is exactly the vanishing of that
kind's constraints on that kind's domain. -/
theorem rap_satisfies_iff (kind : Reified.ConstraintKind)
    (P : Fin T.air.numTraceCols → K[X]) :
    (T.rap kind).Satisfies P
      ↔ ∀ x ∈ T.params.domain kind,
          ∀ c ∈ (kindSeg T.air kind).constraints,
            c.expr.eval (envOfTrace P T.params.ω x T.params.chalVal T.params.pubVal) = 0 :=
  airToRAP_satisfies_iff (kindSeg T.air kind) T.params.chalVal T.params.pubVal T.params.eDeg
    T.params.hExp T.params.ω T.params.βcoset (T.params.domain kind) T.params.βcoset_ne_zero
    T.params.hExp_pos P

/-! ## 4. Chronology guarantees, at table level over the unfiltered constraint list -/

/-- **`RespectsChronology` at table level.**  The analogue of
`Staging.RespectsChronology` (`MultiRoundRAP.lean:143`), stated over `T.air.constraints`
*unfiltered* — deliberately stronger than the per-kind version, and free of the `List.filter`
index bookkeeping that mapping a `kindSeg` index back to the original would need.

The column half is checked against the *actual* variable set of the reified constraint
polynomial `airC`, not against declared metadata. -/
def RespectsChronology
    (constraintRound : Fin T.air.constraints.length → Fin rounds)
    (constraintChallenges :
      Fin T.air.constraints.length → Finset (Fin chronology.numChallenges)) : Prop :=
  ∀ c : Fin T.air.constraints.length,
    (∀ v ∈ (airC T.air T.params.chalVal T.params.pubVal c).vars,
        T.schedule.columnAvailableBy (constraintRound c) v.1)
      ∧ (∀ j ∈ constraintChallenges c, chronology.availableBy (constraintRound c) j)

/-- **`commit_then_sample` at table level** (cf. `MultiRoundRAP.lean:219`).  A column committed in
round `i` cannot depend on a challenge that is only sampled at round `i` or later.  This needs no
chronology assignment: it is a field of the table. -/
theorem commit_then_sample (c : Fin T.air.numTraceCols)
    (j : Fin chronology.numChallenges) (hj : j ∈ T.columnChallenges c)
    (hlate : (T.schedule.roundOf c : ℕ) ≤ (chronology.sampledAfter j : ℕ)) : False := by
  have := T.columns_commit_before_sampling c j hj
  exact absurd this (by simpa [ChallengeChronology.usableByColumnOf] using hlate)

/-- No challenge is usable by a round-`0` column. -/
theorem round_zero_column_challenge_free (c : Fin T.air.numTraceCols)
    (hc : (T.schedule.roundOf c : ℕ) = 0) : T.columnChallenges c = ∅ := by
  refine Finset.eq_empty_of_forall_notMem ?_
  intro j hj
  exact T.commit_then_sample c j hj (by omega)

variable {T}

/-- **A round-`i` constraint cannot read a round-`> i` column** (cf.
`MultiRoundRAP.lean:227`), stated on the actual variable set of the reified constraint
polynomial, over the unfiltered constraint list. -/
theorem constraint_cannot_read_late_column
    {cr : Fin T.air.constraints.length → Fin rounds}
    {cc : Fin T.air.constraints.length → Finset (Fin chronology.numChallenges)}
    (h : T.RespectsChronology cr cc) (c : Fin T.air.constraints.length)
    (v : Fin T.air.numTraceCols × ℕ)
    (hlate : (cr c : ℕ) < (T.schedule.roundOf v.1 : ℕ)) :
    v ∉ (airC T.air T.params.chalVal T.params.pubVal c).vars := by
  intro hv
  have hle := (h c).1 v hv
  exact absurd hle (by simpa [RoundSchedule.columnAvailableBy] using hlate)

/-- Dually: every column a constraint actually reads is committed by that constraint's round. -/
theorem constraint_columns_committed
    {cr : Fin T.air.constraints.length → Fin rounds}
    {cc : Fin T.air.constraints.length → Finset (Fin chronology.numChallenges)}
    (h : T.RespectsChronology cr cc) (c : Fin T.air.constraints.length)
    (v : Fin T.air.numTraceCols × ℕ)
    (hv : v ∈ (airC T.air T.params.chalVal T.params.pubVal c).vars) :
    (T.schedule.roundOf v.1 : ℕ) ≤ (cr c : ℕ) :=
  (h c).1 v hv

/-- **A round-`i` constraint cannot use a challenge sampled after round `i`.** -/
theorem constraint_cannot_use_late_challenge
    {cr : Fin T.air.constraints.length → Fin rounds}
    {cc : Fin T.air.constraints.length → Finset (Fin chronology.numChallenges)}
    (h : T.RespectsChronology cr cc) (c : Fin T.air.constraints.length)
    (j : Fin chronology.numChallenges)
    (hlate : (cr c : ℕ) < (chronology.sampledAfter j : ℕ)) : j ∉ cc c := by
  intro hj
  have hle := (h c).2 j hj
  exact absurd hle (by simpa [ChallengeChronology.availableBy] using hlate)

end StagedChip

/-! ## 5. The FRI degree bound -/

/-- A member's value is bounded by a `foldr max` accumulation over the list. -/
theorem le_foldr_max {α : Type*} (f : α → ℕ) (l : List α) {a : α} (ha : a ∈ l) :
    f a ≤ l.foldr (fun x acc => max (f x) acc) 0 := by
  induction l with
  | nil => exact absurd ha (by simp)
  | cons b rest ih =>
      rcases List.mem_cons.mp ha with h | h
      · subst h; exact Nat.le_max_left _ _
      · exact le_trans (ih h) (Nat.le_max_right _ _)

/-- **The client's per-constraint composition degree, per constraint kind**
(`ztd/eight.hoon:193-245`).  The four categories do **not** share one formula:

* `boundary` (`:201-202`) and `terminal` (`:232-233`): `0` if `height = 1`, else
  `deg·(height−1) − 1`;
* `row` (`:212-213`) (and `extra`, `:244-245`): `0` if `height = 1` or `deg = 1`, else
  `deg·(height−1) − height`;
* `transition` (`:222`): `(deg−1)·(height−1)`, with no `height = 1` special case (it is `0`
  there anyway).

Subtraction is `ℕ`-truncated, matching hoon's guarded `dec`/`sub`. -/
def kindCompDegree (kind : Reified.ConstraintKind) (deg height : ℕ) : ℕ :=
  match kind with
  | .boundary   => if height = 1 then 0 else deg * (height - 1) - 1
  | .terminal   => if height = 1 then 0 else deg * (height - 1) - 1
  | .row        => if height = 1 then 0 else if deg = 1 then 0 else deg * (height - 1) - height
  | .transition => (deg - 1) * (height - 1)

@[simp] theorem kindCompDegree_height_one (kind : Reified.ConstraintKind) (deg : ℕ) :
    kindCompDegree kind deg 1 = 0 := by
  cases kind <;> simp [kindCompDegree]

/-- **Round-up to `2^k − 1`** (`ztd/eight.hoon:183`, `(dec (bex (xeb (dec d))))`).  Hoon's `xeb`
is `(met 0 ·)`, the bit width, which is Lean's `Nat.size`. -/
def friRoundUp (d : ℕ) : ℕ := 2 ^ Nat.size (d - 1) - 1

/-- The bound really is one less than a power of two — the `2^k − 1` shape. -/
theorem friRoundUp_succ (d : ℕ) : friRoundUp d + 1 = 2 ^ Nat.size (d - 1) := by
  have h : 1 ≤ 2 ^ Nat.size (d - 1) := Nat.one_le_two_pow
  show 2 ^ Nat.size (d - 1) - 1 + 1 = 2 ^ Nat.size (d - 1)
  omega

theorem friRoundUp_isPowTwo_succ (d : ℕ) : ∃ k : ℕ, friRoundUp d + 1 = 2 ^ k :=
  ⟨Nat.size (d - 1), friRoundUp_succ d⟩

/-- The round-up does not lose the degree it was computed from: `d − 1 ≤ friRoundUp d`.

Note this is `d − 1`, not `d`: the client's `fri-deg-bound` is documented as "`D-1`, where `D` is
the next power of 2 greater than the degree bounds" (`ztd/eight.hoon:178-179`), so at `d = 4` it
is `3`.  Claiming `d ≤ friRoundUp d` would be false there. -/
theorem sub_one_le_friRoundUp (d : ℕ) : d - 1 ≤ friRoundUp d := by
  have h := Nat.lt_size_self (d - 1)
  show d - 1 ≤ 2 ^ Nat.size (d - 1) - 1
  omega

theorem friRoundUp_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) : friRoundUp d₁ ≤ friRoundUp d₂ := by
  show 2 ^ Nat.size (d₁ - 1) - 1 ≤ 2 ^ Nat.size (d₂ - 1) - 1
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num)
    (Nat.size_le_size (Nat.sub_le_sub_right h 1))) 1

namespace StagedChip

variable {rounds : ℕ} {chronology : ChallengeChronology rounds}
variable (T : StagedChip K rounds chronology)

/-- **The table's height**: the number of rows the `row` constraints are enforced on, i.e. the
cardinality of the `row` evaluation domain.  This is the client's `height` (`eight.hoon:186`,
supplied per table from `heights`). -/
def height : ℕ := (T.params.domain .row).card

/-- Per-constraint composition degree of this table's constraint `c`.  The trace degree is the
`K`-free symbolic `Constraint.degree` (`AIR.lean:142`), not a field-dependent `totalDegree`. -/
def constraintCompDegree (c : Reified.Constraint) : ℕ :=
  kindCompDegree c.kind c.expr.degree T.height

/-- **The table's composition degree**: the running max of `constraintCompDegree` over every
constraint of the *unfiltered* list — the same quantity the client accumulates as
`:(max d d.bnd d.row d.trn d.trm d.xta)` (`eight.hoon:188`), since every constraint carries its
own kind. -/
def compDegree : ℕ :=
  T.air.constraints.foldr (fun c acc => max (T.constraintCompDegree c) acc) 0

/-- The number of DEEP evaluations one table consumes: two rows (current and next) per column.
The client peels exactly `(mul 2 width)` per table with `scag`/`slag`
(`stark/verifier.hoon:657-658`). -/
def evalWidth : ℕ := 2 * T.air.numTraceCols

theorem constraintCompDegree_le_compDegree {c : Reified.Constraint}
    (hc : c ∈ T.air.constraints) : T.constraintCompDegree c ≤ T.compDegree :=
  le_foldr_max T.constraintCompDegree T.air.constraints hc

end StagedChip

/-! ## 6. The chips of one proof, in canonical order -/

/-- **A list of chips sharing one interaction schedule**, in canonical order.  The deployed client
sorts tables by `t-order` (`ztd/eight.hoon:76-77`) and then folds through them positionally, so
the canonical order *is* the list order here.  `GigaRAP` (item 7) bundles such a list with the
`rounds`/`chronology` the chips are indexed by. -/
abbrev ChipList (K : Type*) [Field K] (rounds : ℕ) (chronology : ChallengeChronology rounds) :=
  List (StagedChip K rounds chronology)

namespace ChipList

variable {rounds : ℕ} {chronology : ChallengeChronology rounds}
variable (G : ChipList K rounds chronology)

/-- **Satisfaction is the conjunction over tables**.  Each table is given its own trace over its own column layout. -/
def Satisfies
    (P : (T : StagedChip K rounds chronology) → Fin T.air.numTraceCols → K[X]) : Prop :=
  ∀ T ∈ G, T.Satisfies (P T)

@[simp] theorem satisfies_nil
    (P : (T : StagedChip K rounds chronology) → Fin T.air.numTraceCols → K[X]) :
    Satisfies ([] : ChipList K rounds chronology) P := by
  intro T hT; exact absurd hT (List.not_mem_nil)

theorem satisfies_cons (T : StagedChip K rounds chronology) (G : ChipList K rounds chronology)
    (P : (T : StagedChip K rounds chronology) → Fin T.air.numTraceCols → K[X]) :
    Satisfies (T :: G) P ↔ T.Satisfies (P T) ∧ Satisfies G P := by
  simp only [Satisfies, List.mem_cons, forall_eq_or_imp]

/-- **The whole giga-RAP is per-constraint domain vanishing, table by table.**  Item 3's bridge
lifted through the conjunction. -/
theorem satisfies_iff_kinded
    (P : (T : StagedChip K rounds chronology) → Fin T.air.numTraceCols → K[X]) :
    G.Satisfies P
      ↔ ∀ T ∈ G, ∀ c ∈ T.air.constraints, ∀ x ∈ T.params.domain c.kind,
          c.expr.eval (envOfTrace (P T) T.params.ω x T.params.chalVal T.params.pubVal) = 0 := by
  refine forall_congr' fun T => ?_
  exact forall_congr' fun _ => T.satisfies_iff_kinded (P T)

/-! ### The FRI degree bound across all tables -/

/-- Running max of `StagedChip.compDegree` over every table (`eight.hoon:184-188`). -/
def compDegree : ℕ := G.foldr (fun T acc => max T.compDegree acc) 0

theorem table_compDegree_le {T : StagedChip K rounds chronology} (hT : T ∈ G) :
    T.compDegree ≤ G.compDegree :=
  le_foldr_max StagedChip.compDegree G hT

/-- **`fri-deg-bound`** (`ztd/eight.hoon:183`): the running max across every table and every
constraint kind, rounded up to `2^k − 1`. -/
def friDegBound : ℕ := friRoundUp G.compDegree

theorem friDegBound_succ_isPowTwo : ∃ k : ℕ, G.friDegBound + 1 = 2 ^ k :=
  friRoundUp_isPowTwo_succ _

/-- Every table's every constraint is accounted for by the global bound, up to the documented
`D − 1` offset. -/
theorem constraint_compDegree_le_friDegBound {T : StagedChip K rounds chronology} (hT : T ∈ G)
    {c : Reified.Constraint} (hc : c ∈ T.air.constraints) :
    T.constraintCompDegree c - 1 ≤ G.friDegBound :=
  le_trans (Nat.sub_le_sub_right
      (le_trans (T.constraintCompDegree_le_compDegree hc) (G.table_compDegree_le hT)) 1)
    (sub_one_le_friRoundUp _)

/-! ### The table-major offset column layout -/

/-- **Table-major offset**: the global index at which table `i`'s block starts. -/
def offset (i : ℕ) : ℕ := ((G.take i).map StagedChip.evalWidth).sum

/-- Total global index range. -/
def totalEvalWidth : ℕ := (G.map StagedChip.evalWidth).sum

@[simp] theorem offset_zero : G.offset 0 = 0 := by simp [offset]

@[simp] theorem offset_nil (i : ℕ) :
    offset ([] : ChipList K rounds chronology) i = 0 := by simp [offset]

@[simp] theorem totalEvalWidth_nil : totalEvalWidth ([] : ChipList K rounds chronology) = 0 := by
  simp [totalEvalWidth]

theorem offset_cons_succ (T : StagedChip K rounds chronology)
    (G : ChipList K rounds chronology) (i : ℕ) :
    offset (T :: G) (i + 1) = T.evalWidth + offset G i := by
  simp [offset]

theorem totalEvalWidth_cons (T : StagedChip K rounds chronology)
    (G : ChipList K rounds chronology) :
    totalEvalWidth (T :: G) = T.evalWidth + totalEvalWidth G := by
  simp [totalEvalWidth]

/-- **The offsets telescope**: table `i`'s block ends exactly where table `i+1`'s begins.  This
is the `zip-roll` + `scag`/`slag` fold of `stark/verifier.hoon:643-658`. -/
theorem offset_succ {G : ChipList K rounds chronology} {i : ℕ} (hi : i < G.length) :
    G.offset (i + 1) = G.offset i + G[i].evalWidth := by
  induction G generalizing i with
  | nil => exact absurd hi (by simp)
  | cons a rest ih =>
      cases i with
      | zero => simp [offset]
      | succ n =>
          have hn : n < rest.length := by simpa using hi
          rw [offset_cons_succ, offset_cons_succ, ih hn]
          simp [Nat.add_assoc]

/-- The offsets exhaust the global range: the last block ends at `totalEvalWidth`. -/
theorem offset_length : G.offset G.length = G.totalEvalWidth := by
  simp [offset, totalEvalWidth]

theorem offset_mono {G : ChipList K rounds chronology} {i j : ℕ} (h : i ≤ j) :
    G.offset i ≤ G.offset j := by
  simp only [offset]
  induction G generalizing i j with
  | nil => simp
  | cons a rest ih =>
      cases i with
      | zero => simp
      | succ m =>
          obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
          have : m ≤ n := by omega
          simpa [List.take_succ_cons] using ih this

theorem offset_le_total {G : ChipList K rounds chronology} {i : ℕ} (hi : i ≤ G.length) :
    G.offset i ≤ G.totalEvalWidth := by
  rw [← offset_length]; exact offset_mono hi

/-- **The blocks are disjoint**: an earlier table's block ends at or before a later table's
begins. -/
theorem block_disjoint {G : ChipList K rounds chronology} {i j : ℕ} (hi : i < G.length)
    (hij : i < j) :
    G.offset i + G[i].evalWidth ≤ G.offset j := by
  rw [← offset_succ hi]; exact offset_mono hij

/-- **The blocks cover the global range**: every global index below `totalEvalWidth` lies in
exactly one table's block (existence here, uniqueness from `block_disjoint`). -/
theorem exists_block {G : ChipList K rounds chronology} {n : ℕ} (hn : n < G.totalEvalWidth) :
    ∃ i, ∃ _ : i < G.length, G.offset i ≤ n ∧ n < G.offset i + G[i].evalWidth := by
  induction G generalizing n with
  | nil => exact absurd hn (by simp)
  | cons a rest ih =>
      rw [totalEvalWidth_cons] at hn
      by_cases hlt : n < a.evalWidth
      · exact ⟨0, by simp, by simp [offset], by simpa [offset] using hlt⟩
      · have hn' : n - a.evalWidth < totalEvalWidth rest := by omega
        obtain ⟨i, hi, h1, h2⟩ := ih hn'
        have hi' : i + 1 < (a :: rest).length := by simpa using hi
        have hget : (a :: rest)[i + 1] = rest[i] := by simp
        refine ⟨i + 1, hi', ?_, ?_⟩
        · rw [offset_cons_succ]; omega
        · rw [offset_cons_succ, hget]; omega

/-- Conversely every in-block index is in range. -/
theorem block_subset_range {G : ChipList K rounds chronology} {i n : ℕ} (hi : i < G.length)
    (h : n < G.offset i + G[i].evalWidth) : n < G.totalEvalWidth :=
  lt_of_lt_of_le h (by rw [← offset_succ hi]; exact offset_le_total (by omega))

end ChipList

/-! ## 7. `GigaRAP`: the whole proof, one interaction schedule, many chips

The round count and the chronology live **here**, at the proof, and every chip is indexed by
them.  A chip cannot declare its own schedule,
so two chips of one `GigaRAP` agree about when each coin was sent *by typing*. -/

/-- **The giga-RAP**: one interaction schedule and the chips committed against it. -/
structure GigaRAP (K : Type*) [Field K] where
  /-- Rounds of interaction `k`, shared by every chip. -/
  rounds : ℕ
  /-- There is at least one round, so `Fin rounds` is inhabited. -/
  rounds_pos : 0 < rounds
  /-- Which verifier message delivers each challenge — one global draw, all chips. -/
  chronology : ChallengeChronology rounds
  /-- The chips, in canonical order (`ztd/eight.hoon:76-77`). -/
  chips : ChipList K rounds chronology

namespace GigaRAP

variable (G : GigaRAP K)

/-- **Satisfaction is the conjunction over chips**.  Indexed by the chip itself rather than by a dependent list
position, so the trace family is total. -/
def Satisfies
    (P : (T : StagedChip K G.rounds G.chronology) → Fin T.air.numTraceCols → K[X]) : Prop :=
  ChipList.Satisfies G.chips P

/-- Unfolded: every chip of the proof is satisfied. -/
theorem satisfies_iff_forall
    (P : (T : StagedChip K G.rounds G.chronology) → Fin T.air.numTraceCols → K[X]) :
    G.Satisfies P ↔ ∀ T ∈ G.chips, T.Satisfies (P T) := Iff.rfl

/-- **The whole giga-RAP is per-constraint domain vanishing, chip by chip.**  Item 3's bridge
lifted through the conjunction. -/
theorem satisfies_iff_kinded
    (P : (T : StagedChip K G.rounds G.chronology) → Fin T.air.numTraceCols → K[X]) :
    G.Satisfies P
      ↔ ∀ T ∈ G.chips, ∀ c ∈ T.air.constraints, ∀ x ∈ T.params.domain c.kind,
          c.expr.eval (envOfTrace (P T) T.params.ω x T.params.chalVal T.params.pubVal) = 0 :=
  ChipList.satisfies_iff_kinded G.chips P

/-- The first round exists, since `rounds_pos`. -/
def firstRound : Fin G.rounds := ⟨0, G.rounds_pos⟩

@[simp] theorem firstRound_val : (G.firstRound : ℕ) = 0 := rfl

/-- No coin is usable by a first-round column: nothing has been sampled when they are
committed. -/
theorem firstRound_challenge_free (T : StagedChip K G.rounds G.chronology)
    (c : Fin T.air.numTraceCols) (hc : T.schedule.roundOf c = G.firstRound) :
    T.columnChallenges c = ∅ :=
  T.round_zero_column_challenge_free c (by rw [hc]; rfl)

/-! ### The FRI degree bound and the offset layout, at the proof level -/

/-- Running max of `StagedChip.compDegree` over every chip (`eight.hoon:184-188`). -/
def compDegree : ℕ := ChipList.compDegree G.chips

theorem chip_compDegree_le {T : StagedChip K G.rounds G.chronology} (hT : T ∈ G.chips) :
    T.compDegree ≤ G.compDegree :=
  ChipList.table_compDegree_le G.chips hT

/-- **`fri-deg-bound`** (`ztd/eight.hoon:183`). -/
def friDegBound : ℕ := ChipList.friDegBound G.chips

theorem friDegBound_succ_isPowTwo : ∃ k : ℕ, G.friDegBound + 1 = 2 ^ k :=
  ChipList.friDegBound_succ_isPowTwo G.chips

theorem constraint_compDegree_le_friDegBound
    {T : StagedChip K G.rounds G.chronology} (hT : T ∈ G.chips)
    {c : Reified.Constraint} (hc : c ∈ T.air.constraints) :
    T.constraintCompDegree c - 1 ≤ G.friDegBound :=
  ChipList.constraint_compDegree_le_friDegBound G.chips hT hc

/-- Table-major offset of chip `i`'s DEEP-evaluation block. -/
def offset (i : ℕ) : ℕ := ChipList.offset G.chips i

/-- Total global index range. -/
def totalEvalWidth : ℕ := ChipList.totalEvalWidth G.chips

theorem offset_succ {i : ℕ} (hi : i < G.chips.length) :
    G.offset (i + 1) = G.offset i + G.chips[i].evalWidth :=
  ChipList.offset_succ hi

theorem block_disjoint {i j : ℕ} (hi : i < G.chips.length) (hij : i < j) :
    G.offset i + G.chips[i].evalWidth ≤ G.offset j :=
  ChipList.block_disjoint hi hij

theorem exists_block {n : ℕ} (hn : n < G.totalEvalWidth) :
    ∃ i, ∃ _ : i < G.chips.length,
      G.offset i ≤ n ∧ n < G.offset i + G.chips[i].evalWidth :=
  ChipList.exists_block hn

end GigaRAP

end Nock.NockVMROM.Thm54.Staged

section Audit

open Nock.NockVMROM.Thm54.Staged

#check @Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged
#check @Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_satisfies_iff
#check @Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_width_sum
#check @Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_k
#check @Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_k_ne_rap_k
#check @Nock.NockVMROM.Thm54.Staged.StagedChip.satisfies_iff_segmented
#check @Nock.NockVMROM.Thm54.Staged.StagedChip.satisfies_iff_kinded
#check @Nock.NockVMROM.Thm54.Staged.StagedChip.RespectsChronology
#check @Nock.NockVMROM.Thm54.Staged.kindCompDegree
#check @Nock.NockVMROM.Thm54.Staged.GigaRAP.compDegree
#check @Nock.NockVMROM.Thm54.Staged.StagedChip.commit_then_sample
#check @Nock.NockVMROM.Thm54.Staged.StagedChip.constraint_cannot_read_late_column
#check @Nock.NockVMROM.Thm54.Staged.GigaRAP.satisfies_iff_kinded
#check @Nock.NockVMROM.Thm54.Staged.GigaRAP.friDegBound
#check @Nock.NockVMROM.Thm54.Staged.GigaRAP.exists_block
#check @Nock.NockVMROM.Thm54.Staged.StagedChip
#check @Nock.NockVMROM.Thm54.Staged.GigaRAP
#check @Nock.NockVMROM.Thm54.Staged.GigaRAP.Satisfies
#check @Nock.NockVMROM.Thm54.Staged.GigaRAP.satisfies_iff_forall
#check @Nock.NockVMROM.Thm54.Staged.ChipList.exists_block

#print axioms Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_k
#print axioms Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_k_ne_rap_k
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.satisfies_iff_segmented
#print axioms Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_width_sum
#print axioms Nock.NockVMROM.Thm54.SegmentedRAPParams.rapStaged_wRAP_eq_fibre
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.satisfies_iff_kinded
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.rap_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.commit_then_sample
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.round_zero_column_challenge_free
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.constraint_cannot_read_late_column
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.constraint_columns_committed
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.constraint_cannot_use_late_challenge
#print axioms Nock.NockVMROM.Thm54.Staged.StagedChip.constraintCompDegree_le_compDegree
#print axioms Nock.NockVMROM.Thm54.Staged.le_foldr_max
#print axioms Nock.NockVMROM.Thm54.Staged.friRoundUp_isPowTwo_succ
#print axioms Nock.NockVMROM.Thm54.Staged.sub_one_le_friRoundUp
#print axioms Nock.NockVMROM.Thm54.Staged.friRoundUp_mono
#print axioms Nock.NockVMROM.Thm54.Staged.GigaRAP.satisfies_iff_kinded
#print axioms Nock.NockVMROM.Thm54.Staged.GigaRAP.constraint_compDegree_le_friDegBound
#print axioms Nock.NockVMROM.Thm54.Staged.ChipList.offset_succ
#print axioms Nock.NockVMROM.Thm54.Staged.ChipList.offset_length
#print axioms Nock.NockVMROM.Thm54.Staged.GigaRAP.block_disjoint
#print axioms Nock.NockVMROM.Thm54.Staged.GigaRAP.exists_block
#print axioms Nock.NockVMROM.Thm54.Staged.ChipList.block_subset_range
#print axioms Nock.NockVMROM.Thm54.Staged.ChipList.satisfies_cons
#print axioms Nock.NockVMROM.Thm54.Staged.ChipList.table_compDegree_le
#print axioms Nock.NockVMROM.Thm54.Staged.GigaRAP.friDegBound_succ_isPowTwo
#print axioms Nock.NockVMROM.Thm54.Staged.kindCompDegree_height_one
#print axioms Nock.NockVMROM.Thm54.Staged.GigaRAP.satisfies_iff_forall
#print axioms Nock.NockVMROM.Thm54.Staged.GigaRAP.firstRound_challenge_free
#print axioms Nock.NockVMROM.Thm54.Staged.GigaRAP.offset_succ
#print axioms Nock.NockVMROM.Thm54.Staged.ChipList.exists_block

end Audit
