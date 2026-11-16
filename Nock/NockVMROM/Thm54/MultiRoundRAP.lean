import Nock.NockVMROM.Thm54.ExtensionField
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
Theorem 5.4 does not only fix row and column counts; it fixes the *interaction*
of each chip:

* `RAP_NockComp-IO`: "**Two rounds** of interaction, providing **three** random elements in `K`";
* `RAP_NockMem-IO`: "**One round** of interaction, providing **a** random element in `K`".

`Nock.Framework.RAP` already carries `k` and `w_RAP : Fin k → ℕ`,
but nothing in it ties a *column* to a round, ties a *challenge* to a sampling point, or forbids
a constraint from reading a column that has not been committed yet.  Nor does it enforce
`Def:RAP`'s own requirement that `ω` have multiplicative order exactly `e·2^h` —
`RAP` only records `ω : F`.  This module supplies both, as *typed* data with proofs, so that
`k > 1` cannot be metadata.

## The modeled timeline

```
  round 0 columns committed → verifier sends challenge set 0
→ round 1 columns committed → verifier sends challenge set 1
→ …
→ round (k-1) columns committed → verifier sends challenge set (k-1)
→ all constraints checked
```

So `k` is exactly the number of verifier messages, i.e. the paper's "rounds of interaction":
`k = 2` for the compute chip and `k = 1` for the memory chip, with the total number of sampled
elements recorded by `ChallengeChronology.numChallenges` (`3` and `1`).

Two chronology conditions are enforced, and both have teeth:

* **commit-then-sample** (`columns_commit_before_sampling`): a column committed in round `i` may
  only depend on challenges sampled *strictly before* round `i`.  A prover cannot commit a
  round-`i` column as a function of the round-`i` (or later) coin.
* **availability** (`RespectsChronology`): a constraint discharged at round `i` may only read
  columns committed by round `i` and challenges sampled by round `i`.  The column half is not
  declared metadata: it is checked against the *actual* variable set `(C c).vars` of the
  constraint polynomial, which is what `commit_then_sample` below exploits.

`metadataOnlyStaging_rejected` shows the predicate is non-trivial: a `k = 2` schedule with an
empty chronology whose round-`0` constraint reads the round-`1` column is refuted.
-/

namespace Nock.NockVMROM.Thm54.Staging

open Nock.Framework
open Nock.NockVMROM.Thm54.StrictExtension

/-! ## Round schedules -/

/-- **A round schedule for `w` columns over `k` interaction rounds.** -/
structure RoundSchedule (w k : ℕ) where
  /-- The round in which column `c` is committed. -/
  roundOf : Fin w → Fin k
  /-- The number of columns committed in round `r` (`w_RAP(r)`, the paper). -/
  width : Fin k → ℕ
  /-- The declared width of a round really is the number of columns assigned to it. -/
  width_eq : ∀ r, width r = (Finset.univ.filter fun c : Fin w => roundOf c = r).card

namespace RoundSchedule

variable {w k : ℕ}

/-- **`w = Σ_r w_RAP(r)`** — a theorem, not an axiom of the structure: it follows
from every column being assigned to exactly one round. -/
theorem total_width (S : RoundSchedule w k) : w = ∑ r, S.width r := by
  classical
  have hfib :
      (Finset.univ : Finset (Fin w)).card
        = ∑ r ∈ (Finset.univ : Finset (Fin k)),
            (Finset.univ.filter fun c : Fin w => S.roundOf c = r).card :=
    Finset.card_eq_sum_card_fiberwise (fun c _ => Finset.mem_univ (S.roundOf c))
  calc w = (Finset.univ : Finset (Fin w)).card := by simp
    _ = ∑ r ∈ (Finset.univ : Finset (Fin k)),
          (Finset.univ.filter fun c : Fin w => S.roundOf c = r).card := hfib
    _ = ∑ r, S.width r := Finset.sum_congr rfl (fun r _ => (S.width_eq r).symm)

/-- A column is available to anything scheduled at round `i` iff it was committed by then. -/
abbrev columnAvailableBy (S : RoundSchedule w k) (i : Fin k) (c : Fin w) : Prop :=
  (S.roundOf c : ℕ) ≤ (i : ℕ)

theorem columnAvailableBy_self (S : RoundSchedule w k) (c : Fin w) :
    S.columnAvailableBy (S.roundOf c) c := le_rfl

end RoundSchedule

/-! ## Challenge chronology -/

/-- **Which verifier message delivers each challenge.**  `sampledAfter j = r` means challenge `j`
is sampled by the verifier immediately after the round-`r` columns are committed.  With `k`
rounds there are exactly `k` verifier messages, matching the paper's "rounds of interaction"
count. -/
structure ChallengeChronology (k : ℕ) where
  /-- Total number of sampled field elements. -/
  numChallenges : ℕ
  /-- The round after which each challenge is sampled. -/
  sampledAfter : Fin numChallenges → Fin k

namespace ChallengeChronology

variable {k : ℕ}

/-- A challenge is available to anything scheduled at round `i` iff it has been sampled by the
end of round `i`'s interaction. -/
abbrev availableBy (C : ChallengeChronology k) (i : Fin k) (j : Fin C.numChallenges) : Prop :=
  (C.sampledAfter j : ℕ) ≤ (i : ℕ)

/-- A challenge is usable by a *column* of round `i` only if it was sampled strictly earlier:
the round-`i` columns are committed before the round-`i` coin is sent. -/
abbrev usableByColumnOf (C : ChallengeChronology k) (i : Fin k) (j : Fin C.numChallenges) : Prop :=
  (C.sampledAfter j : ℕ) < (i : ℕ)

theorem usableByColumnOf_imp_availableBy (C : ChallengeChronology k) (i : Fin k)
    (j : Fin C.numChallenges) (h : C.usableByColumnOf i j) : C.availableBy i j :=
  le_of_lt h

/-- No challenge is usable by a round-`0` column: nothing has been sampled yet. -/
theorem not_usableByColumnOf_zero (C : ChallengeChronology k) (i : Fin k) (hi : (i : ℕ) = 0)
    (j : Fin C.numChallenges) : ¬ C.usableByColumnOf i j := by
  simp [usableByColumnOf, hi]

end ChallengeChronology

/-! ## The chronology predicate -/

variable {F : Type*} [Field F]

/-- **`RespectsChronology`** — the real staging predicate.  A constraint discharged at round
`constraintRound c`

* may read only columns committed by that round (checked against the *actual* variables of the
  constraint polynomial, `(R.C c).vars`), and
* may use only challenges sampled by that round.
-/
def RespectsChronology (R : RAP F) (S : RoundSchedule R.w R.k)
    (C : ChallengeChronology R.k) (constraintRound : Fin R.s → Fin R.k)
    (constraintChallenges : Fin R.s → Finset (Fin C.numChallenges)) : Prop :=
  ∀ c : Fin R.s,
    (∀ q ∈ (R.C c).vars, S.columnAvailableBy (constraintRound c) q.1)
      ∧ (∀ j ∈ constraintChallenges c, C.availableBy (constraintRound c) j)

/-! ## Staged RAPs -/

/-- **A staged RAP.**  A `Def:RAP` together with the data that makes its `k` rounds real:

* a round schedule whose per-round widths are the RAP's declared `w_RAP`;
* a challenge chronology;
* per-constraint round and challenge assignments satisfying `RespectsChronology`;
* per-column challenge dependencies satisfying commit-then-sample.
-/
structure StagedRAP (F : Type*) [Field F] where
  /-- The underlying `Def:RAP`. -/
  rap : RAP F
  /-- The strict evaluation orbit: `ω` of exact order `e·2^h`. -/
  orbit : StrictOrbitDomain F rap.e rap.h
  /-- The orbit generator is the RAP's own `ω`, so the order statement is about this RAP. -/
  orbit_ω : orbit.ω = rap.ω
  /-- The orbit coset representative is the RAP's own `β`. -/
  orbit_β : orbit.βcoset = rap.β
  /-- Which round commits each column. -/
  schedule : RoundSchedule rap.w rap.k
  /-- The schedule's per-round widths are the RAP's declared `w_RAP`. -/
  width_eq_wRAP : ∀ r, schedule.width r = rap.wRAP r
  /-- Which verifier message delivers each challenge. -/
  chronology : ChallengeChronology rap.k
  /-- The round at which each constraint is discharged. -/
  constraintRound : Fin rap.s → Fin rap.k
  /-- The sampled challenges each constraint uses. -/
  constraintChallenges : Fin rap.s → Finset (Fin chronology.numChallenges)
  /-- The sampled challenges each column's committed values depend on. -/
  columnChallenges : Fin rap.w → Finset (Fin chronology.numChallenges)
  /-- **Availability.**  A round-`i` constraint reads only round-`≤ i` columns and only
  challenges sampled by round `i`. -/
  constraints_respect_chronology :
    RespectsChronology rap schedule chronology constraintRound constraintChallenges
  /-- **Commit before sample.**  A round-`i` column depends only on challenges sampled strictly
  before round `i`. -/
  columns_commit_before_sampling :
    ∀ c : Fin rap.w, ∀ j ∈ columnChallenges c,
      chronology.usableByColumnOf (schedule.roundOf c) j

namespace StagedRAP

variable (T : StagedRAP F)

/-- **The orbit really has order `e·2^h`.** -/
theorem stagedRAP_orbit_order : orderOf T.orbit.ω = T.rap.e * 2 ^ T.rap.h :=
  T.orbit.order_ω

/-- **The RAP's own generator has exact order `e·2^h`.**  This is the `Def:RAP` condition that
the bare `RAP` structure leaves unenforced; staging supplies it. -/
theorem rap_ω_order : orderOf T.rap.ω = T.rap.e * 2 ^ T.rap.h := by
  rw [← T.orbit_ω]; exact T.orbit.order_ω

theorem rap_e_pos : 1 ≤ T.rap.e := T.orbit.e_pos

theorem rap_h_pos : 1 ≤ T.rap.h := T.orbit.h_pos

/-- The staged widths reproduce `Def:RAP`'s `w = Σ w_RAP(i)`. -/
theorem width_sum : T.rap.w = ∑ r, T.rap.wRAP r := by
  rw [← T.rap.w_eq]

/-- The schedule's fibre widths sum to the total column count. -/
theorem schedule_total_width : T.rap.w = ∑ r, T.schedule.width r :=
  T.schedule.total_width

/-- **`commit_then_sample`.**  A column committed in round `i` cannot depend on a challenge that
is only sampled at round `i` or later. -/
theorem commit_then_sample (c : Fin T.rap.w) (j : Fin T.chronology.numChallenges)
    (hj : j ∈ T.columnChallenges c)
    (hlate : (T.schedule.roundOf c : ℕ) ≤ (T.chronology.sampledAfter j : ℕ)) : False := by
  have := T.columns_commit_before_sampling c j hj
  exact absurd this (by simpa [ChallengeChronology.usableByColumnOf] using hlate)

/-- **A round-`i` constraint cannot read a round-`> i` column.**  Stated on the actual variable
set of the constraint polynomial, so it is a statement about the constraint itself. -/
theorem constraint_cannot_read_late_column (c : Fin T.rap.s) (q : Fin T.rap.w × ℕ)
    (hlate : (T.constraintRound c : ℕ) < (T.schedule.roundOf q.1 : ℕ)) :
    q ∉ (T.rap.C c).vars := by
  intro hq
  have hle := (T.constraints_respect_chronology c).1 q hq
  exact absurd hle (by simpa [RoundSchedule.columnAvailableBy] using hlate)

/-- Dually: every column a constraint actually reads is committed by the constraint's round. -/
theorem constraint_columns_committed (c : Fin T.rap.s) (q : Fin T.rap.w × ℕ)
    (hq : q ∈ (T.rap.C c).vars) :
    (T.schedule.roundOf q.1 : ℕ) ≤ (T.constraintRound c : ℕ) :=
  (T.constraints_respect_chronology c).1 q hq

/-- **A round-`i` constraint cannot use a challenge sampled after round `i`.** -/
theorem constraint_cannot_use_late_challenge (c : Fin T.rap.s)
    (j : Fin T.chronology.numChallenges)
    (hlate : (T.constraintRound c : ℕ) < (T.chronology.sampledAfter j : ℕ)) :
    j ∉ T.constraintChallenges c := by
  intro hj
  have hle := (T.constraints_respect_chronology c).2 j hj
  exact absurd hle (by simpa [ChallengeChronology.availableBy] using hlate)

end StagedRAP

/-! ## The two Theorem 5.4 instances -/

section Instances

/-- The staging witnesses live over `𝔽₁₃`, which carries an element of exact order
`e·2^h = 3·2² = 12`. -/
abbrev SF := ZMod 13

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- `2` generates the full unit group of `𝔽₁₃`, of order `12 = 3 · 2²`. -/
theorem omega13_order : orderOf (2 : SF) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- The strict orbit domain used by both instances: `ω = 2` of exact order `3 · 2²`. -/
def stagingOrbit : StrictOrbitDomain SF 3 2 where
  ω := 2
  βcoset := 1
  e_pos := by norm_num
  h_pos := by norm_num
  order_ω := by rw [omega13_order]; norm_num
  βcoset_ne_zero := by decide

/-! ### Compute chip: `k = 2` rounds, `3` sampled elements -/

/-- A two-round compute-shaped RAP: one column committed in round `0`, one post-challenge column
committed in round `1`, and a single constraint reading the round-`1` column. -/
@[reducible] noncomputable def computeBase : RAP SF where
  e := 3
  k := 2
  wRAP := ![1, 1]
  w := 2
  w_eq := by simp [Fin.sum_univ_two]
  h := 2
  d := 1
  s := 1
  ω := 2
  β := 1
  I := {((1 : Fin 2), 0)}
  C := fun _ => MvPolynomial.X ((1 : Fin 2), 0)
  C_vars := by
    intro i
    simp [MvPolynomial.vars_X]
  C_deg := by
    intro i
    simp [MvPolynomial.totalDegree_X]
  H := {1}
  β_ne_zero := by decide
  I_bound := by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    norm_num

/-- Column `0` is committed in round `0`, column `1` in round `1`. -/
@[reducible] def computeSchedule : RoundSchedule 2 2 where
  roundOf := ![0, 1]
  width := ![1, 1]
  width_eq := by decide

/-- Two verifier messages delivering three elements: two after round `0`, one after round `1`. -/
@[reducible] def computeChronology : ChallengeChronology 2 where
  numChallenges := 3
  sampledAfter := ![0, 0, 1]

/-- The single compute constraint is discharged at round `1`. -/
@[reducible] def computeConstraintRound : Fin 1 → Fin 2 := fun _ => 1

/-- It uses all three sampled elements. -/
@[reducible] def computeConstraintChallenges : Fin 1 → Finset (Fin 3) := fun _ => {0, 1, 2}

/-- The round-`0` column is challenge-free; the round-`1` column may use the two elements
sampled after round `0`. -/
@[reducible] def computeColumnChallenges : Fin 2 → Finset (Fin 3) := ![∅, {0, 1}]

/-- The only variable of the compute constraint is the round-`1` column. -/
theorem computeBase_vars (c : Fin computeBase.s) :
    (computeBase.C c).vars = {((1 : Fin 2), (0 : ℕ))} := by
  show (MvPolynomial.X ((1 : Fin 2), (0 : ℕ)) : MvPolynomial (Fin 2 × ℕ) SF).vars = _
  rw [MvPolynomial.vars_X]

theorem computeRespects :
    RespectsChronology computeBase computeSchedule computeChronology
      computeConstraintRound computeConstraintChallenges := by
  intro c
  fin_cases c
  refine ⟨?_, ?_⟩
  · intro q hq
    rw [computeBase_vars _, Finset.mem_singleton] at hq
    subst hq
    decide
  · intro j hj
    fin_cases j <;> decide

theorem computeCommitFirst :
    ∀ c : Fin 2, ∀ j ∈ computeColumnChallenges c,
      computeChronology.usableByColumnOf (computeSchedule.roundOf c) j := by
  decide

/-- **The compute instance: `k = 2` rounds of interaction, three sampled `K` elements.** -/
@[reducible] noncomputable def computeStagedRAP : StagedRAP SF where
  rap := computeBase
  orbit := stagingOrbit
  orbit_ω := rfl
  orbit_β := rfl
  schedule := computeSchedule
  width_eq_wRAP := fun _ => rfl
  chronology := computeChronology
  constraintRound := computeConstraintRound
  constraintChallenges := computeConstraintChallenges
  columnChallenges := computeColumnChallenges
  constraints_respect_chronology := computeRespects
  columns_commit_before_sampling := computeCommitFirst

/-- The compute chip has exactly two rounds of interaction. -/
theorem computeStagedRAP_rounds : computeStagedRAP.rap.k = 2 := rfl

/-- The compute chip samples exactly three `K` elements. -/
theorem computeStagedRAP_challenges : computeStagedRAP.chronology.numChallenges = 3 := rfl

/-- The compute chip's generator has exact order `e·2^h = 3·2² = 12`. -/
theorem computeStagedRAP_order :
    orderOf computeStagedRAP.rap.ω
      = computeStagedRAP.rap.e * 2 ^ computeStagedRAP.rap.h :=
  computeStagedRAP.rap_ω_order

/-! ### Memory chip: `k = 1` round, `1` sampled element -/

/-- A one-round memory-shaped RAP: both columns are committed in the single round `0`, and the
single constraint is discharged at round `0` using the one sampled element. -/
@[reducible] noncomputable def memoryBase : RAP SF where
  e := 3
  k := 1
  wRAP := ![2]
  w := 2
  w_eq := by simp
  h := 2
  d := 1
  s := 1
  ω := 2
  β := 1
  I := {((0 : Fin 2), 0)}
  C := fun _ => MvPolynomial.X ((0 : Fin 2), 0)
  C_vars := by
    intro i
    simp [MvPolynomial.vars_X]
  C_deg := by
    intro i
    simp [MvPolynomial.totalDegree_X]
  H := {1}
  β_ne_zero := by decide
  I_bound := by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    norm_num

/-- Both memory columns are committed in the single round `0`. -/
@[reducible] def memorySchedule : RoundSchedule 2 1 where
  roundOf := ![0, 0]
  width := ![2]
  width_eq := by decide

/-- One verifier message delivering one element. -/
@[reducible] def memoryChronology : ChallengeChronology 1 where
  numChallenges := 1
  sampledAfter := ![0]

/-- The single memory constraint is discharged at the single round. -/
@[reducible] def memoryConstraintRound : Fin 1 → Fin 1 := fun _ => 0

/-- It uses the one sampled element. -/
@[reducible] def memoryConstraintChallenges : Fin 1 → Finset (Fin 1) := fun _ => {0}

/-- With a single round there are no post-challenge columns. -/
@[reducible] def memoryColumnChallenges : Fin 2 → Finset (Fin 1) := ![∅, ∅]

/-- The only variable of the memory constraint is the round-`0` column. -/
theorem memoryBase_vars (c : Fin memoryBase.s) :
    (memoryBase.C c).vars = {((0 : Fin 2), (0 : ℕ))} := by
  show (MvPolynomial.X ((0 : Fin 2), (0 : ℕ)) : MvPolynomial (Fin 2 × ℕ) SF).vars = _
  rw [MvPolynomial.vars_X]

theorem memoryRespects :
    RespectsChronology memoryBase memorySchedule memoryChronology
      memoryConstraintRound memoryConstraintChallenges := by
  intro c
  fin_cases c
  refine ⟨?_, ?_⟩
  · intro q hq
    rw [memoryBase_vars _, Finset.mem_singleton] at hq
    subst hq
    decide
  · intro j hj
    fin_cases j
    decide

theorem memoryCommitFirst :
    ∀ c : Fin 2, ∀ j ∈ memoryColumnChallenges c,
      memoryChronology.usableByColumnOf (memorySchedule.roundOf c) j := by
  decide

/-- **The memory instance: `k = 1` round of interaction, one sampled `K` element.** -/
@[reducible] noncomputable def memoryStagedRAP : StagedRAP SF where
  rap := memoryBase
  orbit := stagingOrbit
  orbit_ω := rfl
  orbit_β := rfl
  schedule := memorySchedule
  width_eq_wRAP := fun _ => rfl
  chronology := memoryChronology
  constraintRound := memoryConstraintRound
  constraintChallenges := memoryConstraintChallenges
  columnChallenges := memoryColumnChallenges
  constraints_respect_chronology := memoryRespects
  columns_commit_before_sampling := memoryCommitFirst

/-- The memory chip has exactly one round of interaction. -/
theorem memoryStagedRAP_rounds : memoryStagedRAP.rap.k = 1 := rfl

/-- The memory chip samples exactly one `K` element. -/
theorem memoryStagedRAP_challenges : memoryStagedRAP.chronology.numChallenges = 1 := rfl

/-- The memory chip's generator has exact order `e·2^h = 3·2² = 12`. -/
theorem memoryStagedRAP_order :
    orderOf memoryStagedRAP.rap.ω
      = memoryStagedRAP.rap.e * 2 ^ memoryStagedRAP.rap.h :=
  memoryStagedRAP.rap_ω_order

/-- The two chips differ in their interaction counts exactly as Theorem 5.4 requires. -/
theorem staged_round_counts :
    computeStagedRAP.rap.k = 2 ∧ computeStagedRAP.chronology.numChallenges = 3
      ∧ memoryStagedRAP.rap.k = 1 ∧ memoryStagedRAP.chronology.numChallenges = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

end Instances

/-! ## Non-triviality: metadata-only staging is rejected -/

section Regression

/-- An empty chronology over a `k = 2` schedule: `k > 1` is claimed but no element is sampled. -/
@[reducible] def emptyChronology : ChallengeChronology 2 where
  numChallenges := 0
  sampledAfter := fun j => absurd j.isLt (by omega)

/-- **`constraints_respect_chronology` is not vacuous.**  Take the two-round compute RAP with an
empty chronology and claim its only constraint — which really does read the round-`1` column —
is discharged at round `0`.  The predicate refutes it, so `k > 1` cannot be metadata. -/
theorem metadataOnlyStaging_rejected :
    ¬ RespectsChronology computeBase computeSchedule emptyChronology
        (fun _ => 0) (fun _ => ∅) := by
  intro h
  have hq : ((1 : Fin 2), (0 : ℕ)) ∈ (computeBase.C 0).vars := by
    rw [computeBase_vars 0]
    exact Finset.mem_singleton_self _
  have hle := (h 0).1 _ hq
  revert hle
  decide

/-- The very same RAP and schedule *are* accepted once the constraint is honestly discharged at
round `1`: the predicate rejects the chronology violation, not the construction. -/
theorem honestStaging_accepted :
    RespectsChronology computeBase computeSchedule emptyChronology
      (fun _ => 1) (fun _ => ∅) := by
  intro c
  fin_cases c
  refine ⟨?_, ?_⟩
  · intro q hq
    rw [computeBase_vars _, Finset.mem_singleton] at hq
    subst hq
    decide
  · intro j hj
    exact absurd hj (by simp)

/-- A chronology with its one element sampled only after round `1`. -/
@[reducible] def lateChronology : ChallengeChronology 2 where
  numChallenges := 1
  sampledAfter := ![1]

/-- **The challenge half of the predicate also has teeth.**  A constraint discharged at round `0`
may not use a challenge that is only sampled after round `1`. -/
theorem lateChallengeStaging_rejected :
    ¬ RespectsChronology computeBase computeSchedule lateChronology
        (fun _ => 0) (fun _ => {0}) := by
  intro h
  have hle := (h 0).2 0 (Finset.mem_singleton_self _)
  revert hle
  decide

end Regression

end Nock.NockVMROM.Thm54.Staging

#print axioms Nock.NockVMROM.Thm54.Staging.RoundSchedule.total_width
#print axioms Nock.NockVMROM.Thm54.Staging.ChallengeChronology.usableByColumnOf_imp_availableBy
#print axioms Nock.NockVMROM.Thm54.Staging.ChallengeChronology.not_usableByColumnOf_zero
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.stagedRAP_orbit_order
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.rap_ω_order
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.rap_e_pos
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.rap_h_pos
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.width_sum
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.schedule_total_width
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.commit_then_sample
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.constraint_cannot_read_late_column
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.constraint_columns_committed
#print axioms Nock.NockVMROM.Thm54.Staging.StagedRAP.constraint_cannot_use_late_challenge
#print axioms Nock.NockVMROM.Thm54.Staging.omega13_order
#print axioms Nock.NockVMROM.Thm54.Staging.computeStagedRAP_rounds
#print axioms Nock.NockVMROM.Thm54.Staging.computeStagedRAP_challenges
#print axioms Nock.NockVMROM.Thm54.Staging.computeStagedRAP_order
#print axioms Nock.NockVMROM.Thm54.Staging.memoryStagedRAP_rounds
#print axioms Nock.NockVMROM.Thm54.Staging.memoryStagedRAP_challenges
#print axioms Nock.NockVMROM.Thm54.Staging.memoryStagedRAP_order
#print axioms Nock.NockVMROM.Thm54.Staging.staged_round_counts
#print axioms Nock.NockVMROM.Thm54.Staging.metadataOnlyStaging_rejected
#print axioms Nock.NockVMROM.Thm54.Staging.honestStaging_accepted
#print axioms Nock.NockVMROM.Thm54.Staging.lateChallengeStaging_rejected
