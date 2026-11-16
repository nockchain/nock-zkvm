import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.StagedTableRAP
-- `scripts/gate.sh`: `scripts/check-correspondence.py:252`'s import check covers only
-- `Nock/RedTeam/`, so an unimported module under `Nock/NockVMROM/Thm54/` never compiles under
-- `lake build` and the gate does not notice.  Its proper home is a line in
-- `Thm54.lean` next to `:229`; move it there when landing.  Nothing below uses it.

/-!
# Round-fibred soundness: the commit-before-sample premise made checkable

The joint soundness composition (`JointSoundness.lean`, `ProductionP8Containment.lean`) rests on a
premise that is currently discharged by *reading* each summand's definition: **every bad-challenge
set is a function of data committed before its own challenge is sampled.**  This module turns that
premise into a hypothesis with a proof obligation, and re-derives the existing cardinality bounds
from it.

Nothing here asserts independence.  Every bound is a counting bound, in the sense of
`SeedFibers.fiberEvent_card_le`'s docstring; the only structural input is which coordinates a bad
set is allowed to read.

## What the three layers are

1. **The fibre principle** (`card_le_mul_of_fibre_card_le`).  The honest generalisation of
   `SeedFibers.fiberEvent_card_le` (`SeedFibers.lean:31`): it drops the requirement that the event
   be a filtered product and asks only for a projection with bounded fibres.  `fiberEvent_card_le`
   is recovered as the case `π = Prod.fst` (`fiberEvent_card_le_via_fibre`).

2. **The chain**, in two forms, because the chain has two honest forms and they are not the same
   statement:

   * *heterogeneous blocks, product form*: the accumulated bad region of a chain of blocks is
     `fiberEvent` iterated **with the base taken to be the previous stage's event rather than a
     full block space**.  `fiberEvent_card_le_of_base` is that induction step, and
     `fiberEvent₂/₃_card_le` are the depth-2 and depth-3 telescopes
     `|seeds| · B₁ · B₂ (· B₃)`.  Depth `k` is the same two lines; a single statement uniform in
     `k` needs a dependent list of block *types*, which is why the general-depth theory below is
     stated at a uniform coin type instead.
   * *uniform coin type, arbitrary depth*: `chainBelow_card_le` gives
     `(∏_{i < m} B i) · |C|^{n-m}` for the first `m` coordinates constrained — the telescope with
     the unconstrained tail's free factor left visible — and `chainAll_card_le` its `m = n` face
     `∏ i, B i`.

3. **The union form, which is what a soundness error actually is.**  `FailureUnion` is a *union*
   of per-coordinate events, not a chain, so the shape that matters is
   `roundUnion_card_le`: `Σ_i |C|^{n-1} · B i`.  Note the free factor: coordinate `i`'s cylinder
   leaves the *prior* coordinates free as well as the later ones, so the honest summand is
   `(∏_{j < i} |C|) · B i · (∏_{j > i} |C|) = |C|^{n-1} · B i`, **not** `(prior sizes) · B i`.  At
   `n = 4` — the four `JointCoins` coordinates — this is `|K|³ · B i`, which is exactly the shape
   of every one of `FailureUnion`'s five summand bounds.

`cylinder_card_le_needs_dependence` shows the union form is *false* without the
commit-before-sample hypothesis: a bad set allowed to read its own coordinate can be a singleton
and still cover the whole space.  So the premise has teeth; it is not bookkeeping.

## The bridge (§4)

`columnLocal_const_of_prior_challenges` is the theorem the premise reduces to.  Its dependence
hypothesis is an **agreement congruence**, modelled on `Reified.Expr.eval_congr_of_varsBelow`
(`ComputeStagedTable.lean:83`): a `StagedAssignment` says each column's committed value is a
function of the challenge vector that agrees whenever the vector agrees on that column's declared
`columnChallenges`, and a `ColumnLocal` says the bad set agrees whenever the trace agrees on a
declared column set.  Given those, `StagedChip.columns_commit_before_sampling`
(`StagedTableRAP.lean:174`, the field) forces the bad set of a round-`≤ i` column set to be
constant along any variation of the challenges sampled at round `i` or later — and
`columnLocal_factors_through_prior_challenges` turns that into a literal factorisation through the
strictly-earlier challenges.  `staged_error_union_card_le` then feeds that into §3.

## What §6-§7 do, and the seam they expose

Three of `FailureUnion`'s five summands are exhibited as §3 cylinders, **without changing any of
them**: `zeroSeedFailureEvent` at the `z` coordinate with `dep = ∅`, `guardedAxisFailureEvent` at
the `αM` coordinate with `dep = {z}`, and `specializedTopologyFailureEvent` at the `γ` coordinate
with `dep = {z, αM}` — a genuine two-deep dependence.  In each case the bad set is first extracted
as a function of the earlier coordinates *alone* (`guardedAxisBad`, `topologyBad`), its dependence
is proved (`…_readsOn_prior`), the summand is proved equal to that cylinder
(`…_eq_cylinder`), and the existing cardinality bound is then re-derived from `cylinder_card_le`
(`…_card_le_of_cylinder`) instead of from a per-summand `biUnion` computation.  The remaining two,
`collisionFailureEvent` and `SizeWindowFailure`, are handled by `liftSeed_eq_cylinder`, which
covers every `liftSeed`-shaped summand at once — so **all five** summands are exhibited as §3
cylinders.

The seam this makes visible: the `JointCoins` chronology (§5, four coins) and a `StagedChip`'s
chronology (§4, `numChallenges` challenges over `rounds` rounds) are **two different objects in
this tree**.  There is no `StagedChip` for the production verifier — `StagedChip` was introduced
for the compute chip — so §4's `ColumnLocal` premise and §6-§7's cylinders are connected only
through §3's framework, not composed end to end.  §4 says what the premise *is* and what shape a
summand must take to satisfy it; wiring `FailureUnion` through it needs a `StagedChip` for the
production verifier, which does not exist yet.  That gap is recorded, not papered over.

## Scope

Instances are taken only where forced.  §1-§2 need `[Fintype C] [DecidableEq C] [Nonempty C]` on
the coin type and no algebra at all: `Nonempty` is used to extend a partial challenge vector, and
`Fintype`/`DecidableEq` to form the `Finset`s.  §3 needs `[Field K]` only because
`Staged.StagedChip` is stated over a field, plus `[Fintype K] [DecidableEq K]` for the counting
face.  §4 inherits `K : Type` (universe `0`) from `ProductionP8Containment`, which is where the
summands live; that is a pre-existing universe pin of those definitions, not one introduced here.
No hypothesis anywhere fixes a prime, a program, a fixture, or a challenge value, except where the
fixed value *is* the content of the statement (`zeroSeed…`'s `{0}`).
-/

namespace Nock.NockVMROM.Thm54.RoundFibred

open scoped Classical BigOperators
open Nock.NockVMROM.Thm54

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The fibre principle -/

/-- **The fibre principle.**  If `S` maps into `T` under `π` and every `π`-fibre of `S` has at
most `B` points, then `|S| ≤ |T| · B`.

This is `SeedFibers.fiberEvent_card_le` (`SeedFibers.lean:31`) with the product shape removed: it
needs no `Fintype` on either side and no assumption that `S` is a filtered product.  It is a
counting statement, not an independence statement. -/
theorem card_le_mul_of_fibre_card_le {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (π : X → Y) (T : Finset Y) (hmap : ∀ x ∈ S, π x ∈ T) (B : ℕ)
    (hB : ∀ y ∈ T, (S.filter fun x => π x = y).card ≤ B) : S.card ≤ T.card * B := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (t := T) (fun x hx => hmap x hx)]
  calc ∑ y ∈ T, (S.filter fun x => π x = y).card ≤ ∑ _y ∈ T, B := Finset.sum_le_sum hB
    _ = T.card * B := by rw [Finset.sum_const, smul_eq_mul]

/-- `SeedFibers.fiberEvent_card_le` is the `π = Prod.fst` case of the fibre principle. -/
theorem fiberEvent_card_le_via_fibre {A Ω : Type*} [Fintype Ω] [DecidableEq A] [DecidableEq Ω]
    (seeds : Finset A) (bad : A → Finset Ω) (B : ℕ)
    (hB : ∀ a ∈ seeds, (bad a).card ≤ B) :
    (fiberEvent seeds bad).card ≤ seeds.card * B := by
  classical
  refine card_le_mul_of_fibre_card_le _ Prod.fst seeds (fun x hx => ?_) B (fun a ha => ?_)
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  · refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) (hB a ha)
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have := (Finset.mem_filter.mp hx1).2
      simpa [hx2] using this
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      exact Prod.ext (hx.2.trans hy.2.symm) hxy

/-! ## 2. The chain over heterogeneous blocks: the induction step and its telescopes -/

/-- **The chain induction step.**  `fiberEvent`'s base may itself be a *bounded event* rather than
a full block space.  This is the only new content in the heterogeneous chain: iterating it is what
produces the product telescope, with `A` instantiated at the accumulated history. -/
theorem fiberEvent_card_le_of_base {A Ω : Type*} [Fintype Ω] [DecidableEq A] [DecidableEq Ω]
    (seeds : Finset A) (bad : A → Finset Ω) (Bbase B : ℕ)
    (hbase : seeds.card ≤ Bbase) (hB : ∀ a ∈ seeds, (bad a).card ≤ B) :
    (fiberEvent seeds bad).card ≤ Bbase * B :=
  (fiberEvent_card_le seeds bad B hB).trans (Nat.mul_le_mul_right _ hbase)

/-- Depth-2 chain: block `Ω₁` bad as a function of the base, block `Ω₂` bad as a function of
`base × Ω₁`. -/
def fiberEvent₂ {A Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [DecidableEq A] [DecidableEq Ω₁] [DecidableEq Ω₂]
    (seeds : Finset A) (bad₁ : A → Finset Ω₁) (bad₂ : A × Ω₁ → Finset Ω₂) :
    Finset ((A × Ω₁) × Ω₂) :=
  fiberEvent (fiberEvent seeds bad₁) bad₂

theorem fiberEvent₂_card_le {A Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [DecidableEq A] [DecidableEq Ω₁] [DecidableEq Ω₂]
    (seeds : Finset A) (bad₁ : A → Finset Ω₁) (bad₂ : A × Ω₁ → Finset Ω₂) (B₁ B₂ : ℕ)
    (hB₁ : ∀ a ∈ seeds, (bad₁ a).card ≤ B₁)
    (hB₂ : ∀ a ∈ fiberEvent seeds bad₁, (bad₂ a).card ≤ B₂) :
    (fiberEvent₂ seeds bad₁ bad₂).card ≤ seeds.card * B₁ * B₂ :=
  fiberEvent_card_le_of_base _ _ _ _ (fiberEvent_card_le seeds bad₁ B₁ hB₁) hB₂

/-- Depth-3 chain, proved by applying the depth-2 telescope as the base bound. -/
def fiberEvent₃ {A Ω₁ Ω₂ Ω₃ : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype Ω₃]
    [DecidableEq A] [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq Ω₃]
    (seeds : Finset A) (bad₁ : A → Finset Ω₁) (bad₂ : A × Ω₁ → Finset Ω₂)
    (bad₃ : (A × Ω₁) × Ω₂ → Finset Ω₃) :
    Finset ((((A × Ω₁) × Ω₂)) × Ω₃) :=
  fiberEvent (fiberEvent₂ seeds bad₁ bad₂) bad₃

theorem fiberEvent₃_card_le {A Ω₁ Ω₂ Ω₃ : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype Ω₃]
    [DecidableEq A] [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq Ω₃]
    (seeds : Finset A) (bad₁ : A → Finset Ω₁) (bad₂ : A × Ω₁ → Finset Ω₂)
    (bad₃ : (A × Ω₁) × Ω₂ → Finset Ω₃) (B₁ B₂ B₃ : ℕ)
    (hB₁ : ∀ a ∈ seeds, (bad₁ a).card ≤ B₁)
    (hB₂ : ∀ a ∈ fiberEvent seeds bad₁, (bad₂ a).card ≤ B₂)
    (hB₃ : ∀ a ∈ fiberEvent₂ seeds bad₁ bad₂, (bad₃ a).card ≤ B₃) :
    (fiberEvent₃ seeds bad₁ bad₂ bad₃).card ≤ seeds.card * B₁ * B₂ * B₃ :=
  fiberEvent_card_le_of_base _ _ _ _ (fiberEvent₂_card_le seeds bad₁ bad₂ B₁ B₂ hB₁ hB₂) hB₃

/-! ### The existing single-level instances, re-derived from the step lemma

Each of these is the tree's own bound, obtained from `fiberEvent_card_le_of_base` instead of from
`fiberEvent_card_le` plus a hand-written `Nat.mul_le_mul_right`.  The originals stay untouched. -/

/-- `SeedFibers.seedBadJoint_card_le` (`SeedFibers.lean:285`) as an instance of the chain step:
one block (the bad seeds, bounded by `B`), one unconstrained block (`Ω`). -/
theorem seedBadJoint_card_le_of_chain {K Ω : Type*} [Fintype Ω] [DecidableEq K] [DecidableEq Ω]
    (badSeeds : Finset K) (B : ℕ) (hbad : badSeeds.card ≤ B) :
    (seedBadJoint (Ω := Ω) badSeeds).card ≤ B * Fintype.card Ω :=
  fiberEvent_card_le_of_base badSeeds (fun _ => Finset.univ) B (Fintype.card Ω) hbad
    (fun _ _ => by simp)

/-- `SeedFibers.sepSeedJointBad_card_le` (`SeedFibers.lean:310`) as an instance: the NPR
separating-seed block bounded by `2Λ - 1`, then the unconstrained `(α, γ)` block. -/
theorem sepSeedJointBad_card_le_of_chain {K : Type*} [Fintype K] [DecidableEq K]
    (SepSeed : K → Nock.Noun → Nock.Noun → Prop) (Λ : ℕ) (P Q : Nock.Noun)
    (hsep : (Finset.univ.filter (fun z : K => ¬ SepSeed z P Q)).card ≤ 2 * Λ - 1) :
    (sepSeedJointBad SepSeed P Q).card ≤ (2 * Λ - 1) * (Fintype.card K * Fintype.card K) := by
  have := seedBadJoint_card_le_of_chain (Ω := K × K)
    (Finset.univ.filter (fun z : K => ¬ SepSeed z P Q)) (2 * Λ - 1) hsep
  simpa [sepSeedJointBad, Fintype.card_prod] using this

/-- `SeedFibers.walkBadJoint_card_le` (`SeedFibers.lean:180`) as an instance of the chain step:
the nonzero-seed block has *exactly* `|K| - 1` elements, and the second block is the walk's
`(α, γ)` pair whose bad set is the fixed-seed walk event. -/
theorem walkBadJoint_card_le_of_chain {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : Nock.Walk.StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Nock.Walk.Sf fo h + 1 = h) (hvalid : Nock.Walk.BFSValid fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none)) :
    (walkBadJoint St enc labels fo h).card ≤
      (Fintype.card K - 1) *
        (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) :=
  fiberEvent_card_le_of_base (validSeeds K) (walkBadFiber St enc labels fo h)
    (Fintype.card K - 1) _ (le_of_eq validSeeds_card)
    (fun z _ => walkBadFiber_card_le St enc hEnc labels fo hSf hvalid harity hfo hF z)

/-- `SeedFibers.walkBadForestJoint_card_le` (`SeedFibers.lean:255`) likewise. -/
theorem walkBadForestJoint_card_le_of_chain {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : Nock.Walk.StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Nock.Walk.Sf fo h = h)
    (hvalid : Nock.Walk.BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none)) :
    (walkBadForestJoint St enc labels fo kroots h).card ≤
      (Fintype.card K - 1) *
        (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) :=
  fiberEvent_card_le_of_base (validSeeds K) (walkBadForestFiber St enc labels fo kroots h)
    (Fintype.card K - 1) _ (le_of_eq validSeeds_card)
    (fun z _ => walkBadForestFiber_card_le St enc hEnc labels fo hk hSf hvalid harity hfo hF z)

/-! ## 3. The round-indexed framework at a uniform coin type -/

section Uniform

variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- **The dependence hypothesis, in agreement form.**  `f` depends only on the coordinates in
`dep`: any two challenge vectors agreeing there give the same value.  Modelled on
`Reified.Expr.eval_congr_of_varsBelow` (`ComputeStagedTable.lean:83`). -/
def ReadsOn {β : Type*} (dep : Finset (Fin n)) (f : (Fin n → C) → β) : Prop :=
  ∀ x y : Fin n → C, (∀ j ∈ dep, x j = y j) → f x = f y

/-- The coordinates strictly below `m`. -/
def coordsBelow (n m : ℕ) : Finset (Fin n) := Finset.univ.filter fun j : Fin n => (j : ℕ) < m

/-- The coordinates sampled strictly earlier than `i` under a round map.  This is
`ChallengeChronology.usableByColumnOf`'s condition (`MultiRoundRAP.lean:118`) read as a set of
coordinates. -/
def priorCoords (rnd : Fin n → ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j : Fin n => rnd j < rnd i

theorem not_mem_priorCoords (rnd : Fin n → ℕ) (i : Fin n) : i ∉ priorCoords rnd i := by
  simp [priorCoords]

theorem coordsBelow_subset_priorCoords_id (i : Fin n) :
    coordsBelow n (i : ℕ) = priorCoords (fun j => (j : ℕ)) i := rfl

/-! ### The single-coordinate cylinder -/

/-- The event that coordinate `i` lands in a bad set determined by the whole vector.  The
dependence hypothesis is supplied separately, so that its absence is visible. -/
def cylinder (i : Fin n) (bad : (Fin n → C) → Finset C) : Finset (Fin n → C) :=
  Finset.univ.filter fun x => x i ∈ bad x

theorem card_free_coords (i : Fin n) :
    Fintype.card ({j : Fin n // j ≠ i} → C) = Fintype.card C ^ (n - 1) := by
  rw [Fintype.card_fun]
  congr 1
  simp [Fintype.card_subtype_compl]

/-- **The cylinder bound.**  If the bad set of coordinate `i` reads only coordinates in `dep` and
`i ∉ dep`, its cylinder has at most `|C|^{n-1} · B` points: every coordinate other than `i` is
free, and `i` itself is confined to a set of size `≤ B` determined by the free ones. -/
theorem cylinder_card_le (i : Fin n) (dep : Finset (Fin n)) (hi : i ∉ dep)
    (bad : (Fin n → C) → Finset C) (hdep : ReadsOn dep bad) (B : ℕ)
    (hB : ∀ x, (bad x).card ≤ B) :
    (cylinder i bad).card ≤ Fintype.card C ^ (n - 1) * B := by
  classical
  let ext : ({j : Fin n // j ≠ i} → C) → (Fin n → C) :=
    fun r j => if h : j = i then Classical.arbitrary C else r ⟨j, h⟩
  let g : ({j : Fin n // j ≠ i} → C) → Finset C := fun r => bad (ext r)
  have key : ∀ x : Fin n → C, g (fun j : {j : Fin n // j ≠ i} => x j.1) = bad x := by
    intro x
    refine hdep _ _ ?_
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [ext, hji]
  have h1 : (cylinder i bad).card
      ≤ (fiberEvent (Finset.univ : Finset ({j : Fin n // j ≠ i} → C)) g).card := by
    refine Finset.card_le_card_of_injOn
      (fun x : Fin n → C => ((fun j : {j : Fin n // j ≠ i} => x j.1), x i)) ?_ ?_
    · intro x hx
      have hx' : x i ∈ bad x := by simpa [cylinder] using hx
      refine (mem_fiberEvent_iff (Finset.univ : Finset ({j : Fin n // j ≠ i} → C)) g _ _).2
        ⟨Finset.mem_univ _, ?_⟩
      rw [key]
      exact hx'
    · intro x _ y _ hxy
      funext j
      by_cases hj : j = i
      · subst hj; exact congrArg Prod.snd hxy
      · exact congrFun (congrArg Prod.fst hxy) ⟨j, hj⟩
  refine h1.trans ?_
  refine le_trans (fiberEvent_card_le (Finset.univ : Finset ({j : Fin n // j ≠ i} → C)) g B
    (fun r _ => hB _)) ?_
  simp [card_free_coords i]

/-- The counterexample's bad set is perfectly `ReadsOn`-respecting for `dep = {0}`; what it
violates is only `i ∉ dep`.  So the load-bearing part of the premise is the *strictness* of
`ChallengeChronology.usableByColumnOf` (`MultiRoundRAP.lean:118`, a `<` and not a `≤`). -/
theorem cylinder_bad_may_read_own_coordinate :
    ReadsOn (C := C) ({0} : Finset (Fin 1)) (fun x : Fin 1 → C => ({x 0} : Finset C)) := by
  intro x y h
  show ({x 0} : Finset C) = {y 0}
  rw [h 0 (by simp)]

/-- **The commit-before-sample hypothesis has teeth.**  Drop `i ∉ dep` — equivalently, let a bad
set read the very coordinate it constrains, which `cylinder_bad_may_read_own_coordinate` shows is
compatible with `ReadsOn` — and the cylinder bound fails, already at one coordinate with `B = 1`:
`bad x = {x 0}` makes the cylinder the whole space. -/
theorem cylinder_card_le_needs_dependence {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (hC : 1 < Fintype.card C) :
    ¬ (∀ bad : (Fin 1 → C) → Finset C, (∀ x, (bad x).card ≤ 1) →
        (cylinder (0 : Fin 1) bad).card ≤ Fintype.card C ^ (1 - 1) * 1) := by
  intro h
  have hbad : ∀ x : Fin 1 → C, (({x 0} : Finset C)).card ≤ 1 := by intro x; simp
  have := h (fun x => {x 0}) hbad
  have hfull : (cylinder (0 : Fin 1) (fun x : Fin 1 → C => ({x 0} : Finset C)))
      = (Finset.univ : Finset (Fin 1 → C)) := by
    ext x; simp [cylinder]
  rw [hfull] at this
  have hcard : (Finset.univ : Finset (Fin 1 → C)).card = Fintype.card C := by
    simp [Finset.card_univ]
  rw [hcard] at this
  simp at this
  omega

/-! ### The union form: what a soundness-error union actually is -/

/-- The accumulated bad region of a family of per-coordinate bad sets. -/
def roundUnion (s : Finset (Fin n)) (bad : Fin n → (Fin n → C) → Finset C) :
    Finset (Fin n → C) :=
  Finset.univ.filter fun x => ∃ i ∈ s, x i ∈ bad i x

theorem roundUnion_subset_biUnion (s : Finset (Fin n)) (bad : Fin n → (Fin n → C) → Finset C) :
    roundUnion s bad ⊆ s.biUnion fun i => cylinder i (bad i) := by
  intro x hx
  simp only [roundUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  exact Finset.mem_biUnion.mpr ⟨i, hi, by simpa [cylinder] using hxi⟩

/-- **The round-indexed iterated bound, union form.**  For a family of bad sets each of which
reads only coordinates it does not itself constrain, the accumulated bad region is bounded by
`Σ_i |C|^{n-1} · B i`.

The free factor is `|C|^{n-1}` for *every* `i`: coordinate `i`'s cylinder leaves the earlier
coordinates free as well as the later ones.  So the honest summand is
`(∏_{j<i}|C|) · B i · (∏_{j>i}|C|)`, and a telescope of the form `(prior sizes) · B i` would
understate it by the later blocks' factor. -/
theorem roundUnion_card_le (s : Finset (Fin n)) (bad : Fin n → (Fin n → C) → Finset C)
    (dep : Fin n → Finset (Fin n)) (hself : ∀ i ∈ s, i ∉ dep i)
    (hdep : ∀ i ∈ s, ReadsOn (dep i) (bad i)) (B : Fin n → ℕ)
    (hB : ∀ i x, (bad i x).card ≤ B i) :
    (roundUnion s bad).card ≤ ∑ i ∈ s, Fintype.card C ^ (n - 1) * B i := by
  refine le_trans (Finset.card_le_card (roundUnion_subset_biUnion s bad)) ?_
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum fun i hi =>
    cylinder_card_le i (dep i) (hself i hi) (bad i) (hdep i hi) (B i) (fun x => hB i x)

/-- The same bound under a **round map**: each coordinate's bad set may read exactly the
coordinates sampled strictly earlier.  `rnd` is `ChallengeChronology.sampledAfter`. -/
theorem roundUnion_card_le_of_chronology (rnd : Fin n → ℕ) (s : Finset (Fin n))
    (bad : Fin n → (Fin n → C) → Finset C)
    (hdep : ∀ i ∈ s, ReadsOn (priorCoords rnd i) (bad i)) (B : Fin n → ℕ)
    (hB : ∀ i x, (bad i x).card ≤ B i) :
    (roundUnion s bad).card ≤ ∑ i ∈ s, Fintype.card C ^ (n - 1) * B i :=
  roundUnion_card_le s bad (priorCoords rnd) (fun i _ => not_mem_priorCoords rnd i) hdep B hB

/-! ### The chain form: the product telescope at arbitrary depth -/

/-- Forget every coordinate from `m` on. -/
def trunc (m : ℕ) (x : Fin n → C) : Fin n → C :=
  fun j => if (j : ℕ) < m then x j else Classical.arbitrary C

theorem trunc_trunc_le {m m' : ℕ} (h : m ≤ m') (x : Fin n → C) :
    trunc m (trunc m' x) = trunc m x := by
  funext j
  by_cases hj : (j : ℕ) < m
  · simp [trunc, hj, lt_of_lt_of_le hj h]
  · simp [trunc, hj]

theorem trunc_apply_of_lt {m : ℕ} {x : Fin n → C} {j : Fin n} (hj : (j : ℕ) < m) :
    trunc m x j = x j := by simp [trunc, hj]

/-- The chain event: every coordinate below `m` lands in its own bad set. -/
def chainBelow (m : ℕ) (bad : Fin n → (Fin n → C) → Finset C) : Finset (Fin n → C) :=
  Finset.univ.filter fun x => ∀ i : Fin n, (i : ℕ) < m → x i ∈ bad i x

theorem chainBelow_mono {m m' : ℕ} (h : m ≤ m') (bad : Fin n → (Fin n → C) → Finset C) :
    chainBelow m' bad ⊆ chainBelow m bad := by
  intro x hx
  simp only [chainBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact fun i hi => hx i (lt_of_lt_of_le hi h)

/-- **The telescope.**  With coordinate `i`'s bad set reading only coordinates below `i`, the
`m`-prefix chain event's truncations number at most `∏_{i<m} B i`. -/
theorem chainBelow_image_card_le
    (bad : Fin n → (Fin n → C) → Finset C) (B : Fin n → ℕ)
    (hdep : ∀ i : Fin n, ReadsOn (coordsBelow n (i : ℕ)) (bad i))
    (hB : ∀ i x, (bad i x).card ≤ B i) :
    ∀ m : ℕ, ((chainBelow m bad).image (trunc m)).card ≤ ∏ i ∈ coordsBelow n m, B i := by
  intro m
  induction m with
  | zero =>
      have hsub : (chainBelow 0 bad).image (trunc (C := C) 0)
          ⊆ {(fun _ : Fin n => Classical.arbitrary C)} := by
        intro z hz
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
        refine Finset.mem_singleton.mpr ?_
        rw [← hx]; funext j; simp [trunc]
      simpa [coordsBelow] using Finset.card_le_card hsub
  | succ m ih =>
      by_cases hm : m < n
      · set i₀ : Fin n := ⟨m, hm⟩ with hi₀
        have hbelow : coordsBelow n (m + 1) = insert i₀ (coordsBelow n m) := by
          ext j
          simp only [coordsBelow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
            · exact Or.inr h
            · exact Or.inl (by ext; simpa [hi₀] using h)
          · rintro (rfl | h)
            · simp [hi₀]
            · omega
        have hnot : i₀ ∉ coordsBelow n m := by simp [coordsBelow, hi₀]
        have hstep : ((chainBelow (m + 1) bad).image (trunc (m + 1))).card
            ≤ ((chainBelow m bad).image (trunc m)).card * B i₀ := by
          refine card_le_mul_of_fibre_card_le _ (trunc m) _ ?_ (B i₀) ?_
          · intro z hz
            obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
            refine Finset.mem_image.mpr ⟨x, chainBelow_mono (Nat.le_succ m) bad hx, ?_⟩
            rw [← hxz, trunc_trunc_le (Nat.le_succ m)]
          · intro y _
            refine le_trans (Finset.card_le_card_of_injOn (fun z => z i₀) ?_ ?_) (hB i₀ y)
            · intro z hz
              simp only [Finset.coe_filter, Set.mem_setOf_eq] at hz
              obtain ⟨hz1, hz2⟩ := hz
              obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz1
              have hxi : x i₀ ∈ bad i₀ x := by
                simp only [chainBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hx
                exact hx i₀ (by simp [hi₀])
              have hbadeq : bad i₀ x = bad i₀ y := by
                refine hdep i₀ _ _ ?_
                intro j hj
                have hjm : (j : ℕ) < m := by simpa [coordsBelow, hi₀] using hj
                have hzy : trunc m z j = y j := by rw [hz2]
                rw [trunc_apply_of_lt hjm] at hzy
                rw [← hzy, ← hxz, trunc_apply_of_lt (Nat.lt_succ_of_lt hjm)]
              have hzx : z i₀ = x i₀ := by
                rw [← hxz, trunc_apply_of_lt (by simp [hi₀])]
              simp only [Finset.mem_coe]
              rw [hzx, ← hbadeq]
              exact hxi
            · intro z hz w hw hzw
              simp only [Finset.coe_filter, Set.mem_setOf_eq] at hz hw
              obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz.1
              obtain ⟨x', hx', hxw⟩ := Finset.mem_image.mp hw.1
              funext j
              by_cases hj : (j : ℕ) < m
              · have h1 : trunc m z j = y j := by rw [hz.2]
                have h2 : trunc m w j = y j := by rw [hw.2]
                rw [trunc_apply_of_lt hj] at h1 h2
                rw [h1, h2]
              · by_cases hj2 : (j : ℕ) = m
                · have hji : j = i₀ := by ext; simpa [hi₀] using hj2
                  rw [hji]; exact hzw
                · have hge : ¬ (j : ℕ) < m + 1 := by omega
                  rw [← hxz, ← hxw]
                  simp [trunc, hge]
        refine hstep.trans ?_
        rw [hbelow, Finset.prod_insert hnot, Nat.mul_comm]
        exact Nat.mul_le_mul_left _ ih
      · have hall : ∀ j : Fin n, (j : ℕ) < m := fun j => lt_of_lt_of_le j.isLt (by omega)
        have h1 : chainBelow (m + 1) bad = chainBelow m bad := by
          refine Finset.Subset.antisymm (chainBelow_mono (Nat.le_succ m) bad) ?_
          intro x hx
          simp only [chainBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact fun i _ => hx i (hall i)
        have h2 : trunc (C := C) (n := n) (m + 1) = trunc m := by
          funext x j; simp [trunc, hall j, Nat.lt_succ_of_lt (hall j)]
        have h3 : coordsBelow n (m + 1) = coordsBelow n m := by
          ext j; simp only [coordsBelow, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun _ => hall j, fun _ => Nat.lt_succ_of_lt (hall j)⟩
        rw [h1, h2, h3]
        exact ih

theorem trunc_self (x : Fin n → C) : trunc n x = x := by
  funext j; simp [trunc, j.isLt]

/-- **The chain product bound.**  Every coordinate constrained, each bad set reading only strictly
earlier coordinates: the accumulated bad region has at most `∏ i, B i` points — no `|C|` factor
survives. -/
theorem chainAll_card_le (bad : Fin n → (Fin n → C) → Finset C) (B : Fin n → ℕ)
    (hdep : ∀ i : Fin n, ReadsOn (coordsBelow n (i : ℕ)) (bad i))
    (hB : ∀ i x, (bad i x).card ≤ B i) :
    (chainBelow n bad).card ≤ ∏ i, B i := by
  have h := chainBelow_image_card_le bad B hdep hB n
  have himg : (chainBelow n bad).image (trunc (C := C) n) = chainBelow n bad := by
    ext z
    simp only [Finset.mem_image]
    refine ⟨?_, fun hz => ⟨z, hz, trunc_self z⟩⟩
    rintro ⟨x, hx, hxz⟩
    rw [trunc_self] at hxz
    exact hxz ▸ hx
  rw [himg] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  ext j
  simp [coordsBelow]

end Uniform

/-! ## 4. The bridge: a bad set of round-`≤ i` columns factors through earlier challenges -/

section Bridge

open Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged

variable {K : Type*} [Field K]
variable {rounds : ℕ} {chronology : ChallengeChronology rounds}

/-- **A staged prover assignment.**  Column `c`'s committed value is a function of the sampled
challenge vector, and — this is the honest form of "column `c` depends only on the challenges it
declares" — two challenge vectors agreeing on `T.columnChallenges c` give the same column.

This is the prover-side counterpart of `StagedChip.columnChallenges`: the table *declares* which
challenges a column may read, and an assignment *is* one that respects the declaration. -/
structure StagedAssignment (T : StagedChip K rounds chronology) (V : Type*) where
  /-- The committed value of each column, as a function of the challenge vector. -/
  col : Fin T.air.numTraceCols → (Fin chronology.numChallenges → K) → V
  /-- Column `c` reads only the challenges `T.columnChallenges c` declares. -/
  col_reads : ∀ c (χ₁ χ₂ : Fin chronology.numChallenges → K),
      (∀ j ∈ T.columnChallenges c, χ₁ j = χ₂ j) → col c χ₁ = col c χ₂

/-- The trace an assignment produces at a given challenge vector. -/
def StagedAssignment.trace {T : StagedChip K rounds chronology} {V : Type*} (A : StagedAssignment T V)
    (χ : Fin chronology.numChallenges → K) : Fin T.air.numTraceCols → V :=
  fun c => A.col c χ

/-- **A column-local function of the trace.**  `cols` is the column set it reads and `out_congr`
is the agreement congruence that makes "depends only on `cols`" a proof obligation rather than a
comment.  The model is `Reified.Expr.eval_congr_of_varsBelow` (`ComputeStagedTable.lean:83`). -/
structure ColumnLocal (T : StagedChip K rounds chronology) (V β : Type*) where
  /-- The columns the output is allowed to read. -/
  cols : Finset (Fin T.air.numTraceCols)
  /-- The output. -/
  out : (Fin T.air.numTraceCols → V) → β
  /-- Traces agreeing on `cols` give the same output. -/
  out_congr : ∀ t₁ t₂ : Fin T.air.numTraceCols → V,
      (∀ c ∈ cols, t₁ c = t₂ c) → out t₁ = out t₂

/-- Every column read is committed by round `i` — `RoundSchedule.columnAvailableBy`
(`MultiRoundRAP.lean:87`). -/
def ColumnLocal.CommittedBy {T : StagedChip K rounds chronology} {V β : Type*} (L : ColumnLocal T V β)
    (i : Fin rounds) : Prop :=
  ∀ c ∈ L.cols, T.schedule.columnAvailableBy i c

/-- **The bridge.**  A function of the trace that reads only columns committed by round `i` is
constant along any variation of the challenges sampled at round `i` or later.

The only structural input is `StagedChip.columns_commit_before_sampling`
(`StagedTableRAP.lean:174`): a round-`r` column may read only challenges sampled strictly before
round `r`, so a round-`≤ i` column may read only challenges sampled strictly before round `i`. -/
theorem columnLocal_const_of_prior_challenges {T : StagedChip K rounds chronology} {V β : Type*}
    (A : StagedAssignment T V) (L : ColumnLocal T V β) {i : Fin rounds}
    (hL : L.CommittedBy i) (χ₁ χ₂ : Fin chronology.numChallenges → K)
    (hagree : ∀ j : Fin chronology.numChallenges,
      (chronology.sampledAfter j : ℕ) < (i : ℕ) → χ₁ j = χ₂ j) :
    L.out (A.trace χ₁) = L.out (A.trace χ₂) := by
  refine L.out_congr _ _ ?_
  intro c hc
  refine A.col_reads c χ₁ χ₂ ?_
  intro j hj
  have hearly : (chronology.sampledAfter j : ℕ) < (T.schedule.roundOf c : ℕ) :=
    T.columns_commit_before_sampling c j hj
  have hcommit : (T.schedule.roundOf c : ℕ) ≤ (i : ℕ) := hL c hc
  exact hagree j (lt_of_lt_of_le hearly hcommit)

/-- **The factorisation.**  The bad set really is a function of the challenges sampled strictly
before round `i` — exhibited as a genuine `g` on the restricted challenge vector. -/
theorem columnLocal_factors_through_prior_challenges {T : StagedChip K rounds chronology} {V β : Type*}
    (A : StagedAssignment T V) (L : ColumnLocal T V β) {i : Fin rounds}
    (hL : L.CommittedBy i) :
    ∃ g : ({j : Fin chronology.numChallenges //
              (chronology.sampledAfter j : ℕ) < (i : ℕ)} → K) → β,
      ∀ χ : Fin chronology.numChallenges → K,
        L.out (A.trace χ) = g (fun j => χ j.1) := by
  classical
  refine ⟨fun r => L.out (A.trace (fun j =>
    if h : (chronology.sampledAfter j : ℕ) < (i : ℕ) then r ⟨j, h⟩ else 0)), ?_⟩
  intro χ
  refine columnLocal_const_of_prior_challenges A L hL _ _ ?_
  intro j hj
  simp [hj]

/-- **Glue to §3.**  A bad *challenge* set that is column-local at its own sampling round reads
only the challenges sampled strictly earlier — i.e. it satisfies `ReadsOn (priorCoords …)`, the
hypothesis of `roundUnion_card_le_of_chronology`. -/
theorem columnLocal_readsOn_priorCoords {T : StagedChip K rounds chronology} {V : Type*}
    (A : StagedAssignment T V) (L : ColumnLocal T V (Finset K))
    (j : Fin chronology.numChallenges)
    (hL : L.CommittedBy (chronology.sampledAfter j)) :
    ReadsOn (C := K) (priorCoords (fun j' => (chronology.sampledAfter j' : ℕ)) j)
      (fun χ => L.out (A.trace χ)) := by
  intro χ₁ χ₂ hagree
  refine columnLocal_const_of_prior_challenges A L hL _ _ ?_
  intro j' hj'
  exact hagree j' (by simpa [priorCoords] using hj')

/-- **The composed statement.**  For *any* family of bad challenge sets that are column-local at
their own sampling round, the accumulated bad region over the challenge space is bounded by
`Σ_j |K|^{numChallenges-1} · B j`.

This is the premise the soundness composition needs, discharged by proof: the only inputs are the
two agreement congruences (which the prover-side assignment and the bad-set family must supply)
and the table's own `columns_commit_before_sampling`.  No independence is used, and no bad set is
inspected. -/
theorem staged_error_union_card_le [Fintype K] [DecidableEq K] {T : StagedChip K rounds chronology} {V : Type*}
    (A : StagedAssignment T V) (badAt : Fin chronology.numChallenges → ColumnLocal T V (Finset K))
    (hcommit : ∀ j, (badAt j).CommittedBy (chronology.sampledAfter j))
    (B : Fin chronology.numChallenges → ℕ)
    (hB : ∀ j χ, ((badAt j).out (A.trace χ)).card ≤ B j) :
    (roundUnion (C := K) Finset.univ (fun j χ => (badAt j).out (A.trace χ))).card
      ≤ ∑ j, Fintype.card K ^ (chronology.numChallenges - 1) * B j := by
  haveI : Nonempty K := ⟨0⟩
  exact roundUnion_card_le_of_chronology
    (fun j' => (chronology.sampledAfter j' : ℕ)) Finset.univ _
    (fun j _ => columnLocal_readsOn_priorCoords A (badAt j) j (hcommit j)) B
    (fun j χ => hB j χ)

end Bridge

/-! ## 5. The four-coordinate coin space and its chronology -/

section JointSpace

variable {K : Type*}

/-- The four `JointCoins` coordinates as a vector: `0 = αC`, `1 = γ`, `2 = αM`, `3 = z`
(`JointCoins.lean:27,30,33,36`). -/
def vecOfJoint (ω : JointCoins K) : Fin 4 → K :=
  ![alphaC ω, gamma ω, alphaM ω, nprSeed ω]

/-- The inverse packing. -/
def jointOfVec (x : Fin 4 → K) : JointCoins K := ((x 0, x 1), (x 2, x 3))

/-- `JointCoins K` is the four-coordinate coin space of §3. -/
def jointVecEquiv : (Fin 4 → K) ≃ JointCoins K where
  toFun := jointOfVec
  invFun := vecOfJoint
  left_inv := by
    intro x; funext j; fin_cases j <;> rfl
  right_inv := by
    rintro ⟨⟨a, g⟩, ⟨m, z⟩⟩; rfl

@[simp] theorem jointVecEquiv_symm_apply (ω : JointCoins K) :
    jointVecEquiv.symm ω = vecOfJoint ω := rfl

@[simp] theorem vecOfJoint_zero (ω : JointCoins K) : vecOfJoint ω 0 = alphaC ω := rfl
@[simp] theorem vecOfJoint_one (ω : JointCoins K) : vecOfJoint ω 1 = gamma ω := rfl
@[simp] theorem vecOfJoint_two (ω : JointCoins K) : vecOfJoint ω 2 = alphaM ω := rfl
@[simp] theorem vecOfJoint_three (ω : JointCoins K) : vecOfJoint ω 3 = nprSeed ω := rfl

/-- **The `JointCoins` chronology.**  `z` is sampled first, then `αM`, then `γ`: that is the order
the strategy tower stages them in (`Strategy.afterSeed`, then `Strategy.afterAlphaM`, then the
topology `γ`).  `αC` — the compute walk's own challenge — is restricted by *no* summand of
`FailureUnion`, so its position is not forced; it is placed last, which is the choice that forbids
every other summand from reading it, and is therefore the one with content.  As a round map on the
four coordinates `(αC, γ, αM, z)` that is `![3, 2, 1, 0]`. -/
def jointChronology : Fin 4 → ℕ := ![3, 2, 1, 0]

theorem seed_coord_prior : priorCoords jointChronology (3 : Fin 4) = (∅ : Finset (Fin 4)) := by
  decide

theorem alphaM_coord_prior :
    priorCoords jointChronology (2 : Fin 4) = ({3} : Finset (Fin 4)) := by
  decide

theorem gamma_coord_prior :
    priorCoords jointChronology (1 : Fin 4) = ({2, 3} : Finset (Fin 4)) := by
  decide

end JointSpace

/-! ### Every `liftSeed` summand is the `dep = ∅` cylinder at the seed coordinate

`liftSeed` (`JointCoins.lean:98`) restricts only `z`, against a `Finset` fixed *before* any
challenge is sampled.  That is exactly a seed-coordinate cylinder with an empty dependence set, so
all three `liftSeed`-shaped summands of `FailureUnion` — `zeroSeedFailureEvent`,
`collisionFailureEvent`, `SizeWindowFailure` — are instances at once. -/

section LiftSeedInstances

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem liftSeed_eq_cylinder (B : Finset K) :
    liftSeed B = (cylinder (3 : Fin 4) (fun _ : Fin 4 → K => B)).map jointVecEquiv.toEmbedding := by
  haveI : Nonempty K := ⟨0⟩
  ext ω
  rw [Finset.mem_map_equiv, mem_liftSeed_iff]
  simp [cylinder]

/-- A constant bad set reads nothing. -/
theorem const_bad_readsOn_empty (B : Finset K) :
    ReadsOn (C := K) (n := 4) (priorCoords jointChronology (3 : Fin 4))
      (fun _ : Fin 4 → K => B) := fun _ _ _ => rfl

/-- The `liftSeed` bound re-derived from `cylinder_card_le`: `|K|³ · |B|`, matching
`card_liftSeed` (`JointCoins.lean:135`). -/
theorem liftSeed_card_le_of_cylinder (B : Finset K) (b : ℕ) (hb : B.card ≤ b) :
    (liftSeed B).card ≤ Fintype.card K ^ 3 * b := by
  haveI : Nonempty K := ⟨0⟩
  rw [liftSeed_eq_cylinder, Finset.card_map]
  exact cylinder_card_le (3 : Fin 4) (priorCoords jointChronology (3 : Fin 4))
    (not_mem_priorCoords _ _) _ (const_bad_readsOn_empty B) b (fun _ => hb)

section Universe0

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `collisionFailureEvent` (`JointSoundness.lean:615`) is the seed cylinder of the census's own
bad-seed set — data fixed before any challenge. -/
theorem collisionFailureEvent_eq_cylinder {Λ : ℕ} (C : ComparisonCensus Λ) :
    collisionFailureEvent (K := K) C =
      (cylinder (3 : Fin 4) (fun _ : Fin 4 → K => C.badSeeds (K := K))).map
        jointVecEquiv.toEmbedding :=
  liftSeed_eq_cylinder _

/-- `SizeWindowFailure` (`SizeWindowCounting.lean:60`) likewise: its bad-seed filter is a function
of the semantic skeleton, which is fixed before any challenge. -/
theorem SizeWindowFailure_eq_cylinder (S : SemanticStrategy.SemanticSkeleton) :
    SizeWindowCounting.SizeWindowFailure (K := K) S =
      (cylinder (3 : Fin 4)
        (fun _ : Fin 4 → K => SizeWindowCounting.sizeWindowFailureSeeds (K := K) S)).map
        jointVecEquiv.toEmbedding :=
  liftSeed_eq_cylinder _

end Universe0

end LiftSeedInstances

/-! ## 6. Instantiation at the real failure union -/

section JointInstance

open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]

/-! ### `zeroSeedFailureEvent` is the `dep = ∅` cylinder at the seed coordinate -/

/-- `zeroSeedFailureEvent` (`JointSoundness.lean:601`) *is* the seed-coordinate cylinder whose bad
set is the constant `{0}` — a bad set with no dependence at all, which is why it is legitimately
sampled before everything else. -/
theorem zeroSeedFailureEvent_eq_cylinder :
    (zeroSeedFailureEvent : Finset (JointCoins K)) =
      (cylinder (3 : Fin 4) (fun _ : Fin 4 → K => ({0} : Finset K))).map
        jointVecEquiv.toEmbedding := by
  haveI : Nonempty K := ⟨0⟩
  ext ω
  rw [Finset.mem_map_equiv, mem_zeroSeedFailureEvent_iff]
  simp [cylinder]

/-- The constant bad set reads no coordinate. -/
theorem zeroSeed_bad_readsOn_empty :
    ReadsOn (C := K) (n := 4) (priorCoords jointChronology (3 : Fin 4))
      (fun _ : Fin 4 → K => ({0} : Finset K)) := fun _ _ _ => rfl

/-- `zeroSeedFailureEvent`'s bound, re-derived from `cylinder_card_le` rather than from
`card_liftSeed`.  `|K|^{4-1} = |K|³`, matching `zeroSeedFailureEvent_card`. -/
theorem zeroSeedFailureEvent_card_le_of_cylinder :
    (zeroSeedFailureEvent : Finset (JointCoins K)).card ≤ Fintype.card K ^ 3 * 1 := by
  haveI : Nonempty K := ⟨0⟩
  rw [zeroSeedFailureEvent_eq_cylinder, Finset.card_map]
  exact cylinder_card_le (3 : Fin 4) (priorCoords jointChronology (3 : Fin 4))
    (not_mem_priorCoords _ _) _ zeroSeed_bad_readsOn_empty 1 (fun _ => by simp)

/-! ### `guardedAxisFailureEvent` is the `dep = {z}` cylinder at the `αM` coordinate -/

/-- The checker-guarded bad-`αM` set **as a function of the seed alone**.  Extracting it this way
is the whole point: the seed is the only coordinate it reads, and the seed is sampled strictly
before `αM`. -/
def guardedAxisBad (T : ProductionStrategy F K) (lmb : K) (z : K) : Finset K :=
  if hz : z ≠ 0 then verifierGuardedRootUnion (committedTemplate T.verifier z hz) lmb else ∅

theorem mem_guardedAxisBad_iff (T : ProductionStrategy F K) (lmb z α : K) :
    α ∈ guardedAxisBad T lmb z ↔
      ∃ hz : z ≠ 0, α ∈ verifierGuardedRootUnion (committedTemplate T.verifier z hz) lmb := by
  by_cases hz : z ≠ 0
  · simp [guardedAxisBad, hz]
  · simp only [ne_eq, not_not] at hz
    simp [guardedAxisBad, hz]

/-- **The dependence, as a theorem.**  The bad-`αM` set reads only the seed coordinate, so it
satisfies `ReadsOn` for the chronology's prior set of the `αM` coordinate. -/
theorem guardedAxisBad_readsOn_prior (T : ProductionStrategy F K) (lmb : K) :
    ReadsOn (C := K) (n := 4) (priorCoords jointChronology (2 : Fin 4))
      (fun x : Fin 4 → K => guardedAxisBad T lmb (x 3)) := by
  intro x y hagree
  have h3 : x 3 = y 3 := by
    refine hagree 3 ?_
    rw [alphaM_coord_prior]
    simp
  show guardedAxisBad T lmb (x 3) = guardedAxisBad T lmb (y 3)
  rw [h3]

/-- `guardedAxisFailureEvent` (`ProductionP8Containment.lean:417`) *is* the `αM`-coordinate
cylinder of a bad set that reads only the seed.  The summand is unchanged; this identifies it. -/
theorem guardedAxisFailureEvent_eq_cylinder (T : ProductionStrategy F K) (lmb : K) :
    guardedAxisFailureEvent T lmb =
      (cylinder (2 : Fin 4) (fun x : Fin 4 → K => guardedAxisBad T lmb (x 3))).map
        jointVecEquiv.toEmbedding := by
  haveI : Nonempty K := ⟨0⟩
  ext ω
  rw [Finset.mem_map_equiv, mem_guardedAxisFailureEvent_iff]
  simp only [jointVecEquiv_symm_apply, cylinder, Finset.mem_filter, Finset.mem_univ, true_and,
    vecOfJoint_two, vecOfJoint_three]
  rw [mem_guardedAxisBad_iff]

/-- **The summand's bound, re-derived from the general principle.**  `axisWorkload * |K|³` is
`guardedAxisFailureEvent_card_le` (`ProductionP8Containment.lean:459`); here it comes out of
`cylinder_card_le` applied to a bad set proved to read only the seed, with no `biUnion`
computation of its own. -/
theorem guardedAxisFailureEvent_card_le_of_cylinder
    (h2 : (2 : K) ≠ 0) (T : ProductionStrategy F K) (lmb : K) (axisWorkload : ℕ)
    (hwork : ∀ z (hz : z ≠ 0),
      TemplateAxisCounting.templateAxisWorkload (committedTemplate T.verifier z hz)
        ≤ axisWorkload) :
    (guardedAxisFailureEvent T lmb).card ≤ axisWorkload * Fintype.card K ^ 3 := by
  haveI : Nonempty K := ⟨0⟩
  have hB : ∀ x : Fin 4 → K, (guardedAxisBad T lmb (x 3)).card ≤ axisWorkload := by
    intro x
    by_cases hz : x 3 ≠ 0
    · simp only [guardedAxisBad, dif_pos hz]
      exact (production_guarded_axis_cardinal h2 T.verifier (x 3) hz lmb).trans (hwork (x 3) hz)
    · simp only [ne_eq, not_not] at hz
      simp [guardedAxisBad, hz]
  rw [guardedAxisFailureEvent_eq_cylinder, Finset.card_map]
  refine le_trans (cylinder_card_le (2 : Fin 4) (priorCoords jointChronology (2 : Fin 4))
    (not_mem_priorCoords _ _) _ (guardedAxisBad_readsOn_prior T lmb) axisWorkload hB) ?_
  simpa using le_of_eq (Nat.mul_comm _ _)

end JointInstance

/-! ## 7. The depth-2 instance: `specializedTopologyFailureEvent` at the `γ` coordinate

This is the informative one.  Its bad set reads **two** earlier coordinates, `z` *and* `αM`, so it
is a genuine two-deep dependence rather than a one-level fibre — and the chronology `![3,2,1,0]`
is what makes `{z, αM} = priorCoords jointChronology 1` true rather than asserted. -/

section TopologyInstance

open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]
variable [Fintype K] [DecidableEq K]

/-- The topology bad-`γ` set **as a function of `(z, αM)` alone**. -/
def topologyBad (T : Strategy F K p) (lmb z alphaMValue : K) : Finset K :=
  if hz : z ≠ 0 then
    topologyBadGammas (T.afterAlphaM z hz alphaMValue lmb).familyData.base
  else ∅

theorem mem_topologyBad_iff (T : Strategy F K p) (lmb : K) (z alphaMValue g : K) :
    g ∈ topologyBad T lmb z alphaMValue ↔
      ∃ hz : z ≠ 0,
        g ∈ topologyBadGammas (T.afterAlphaM z hz alphaMValue lmb).familyData.base := by
  by_cases hz : z ≠ 0
  · simp [topologyBad, hz]
  · simp only [ne_eq, not_not] at hz
    simp [topologyBad, hz]

/-- **The dependence, as a theorem.**  The bad-`γ` set reads only the `z` and `αM` coordinates. -/
theorem topologyBad_readsOn_prior (T : Strategy F K p) (lmb : K) :
    ReadsOn (C := K) (n := 4) (priorCoords jointChronology (1 : Fin 4))
      (fun x : Fin 4 → K => topologyBad T lmb (x 3) (x 2)) := by
  intro x y hagree
  have h3 : x 3 = y 3 := hagree 3 (by rw [gamma_coord_prior]; decide)
  have h2 : x 2 = y 2 := hagree 2 (by rw [gamma_coord_prior]; decide)
  show topologyBad T lmb (x 3) (x 2) = topologyBad T lmb (y 3) (y 2)
  rw [h3, h2]

/-- `specializedTopologyFailureEvent` (`TemplateRawJointSoundness.lean:552`) *is* the
`γ`-coordinate cylinder of a bad set reading only `(z, αM)`. -/
theorem specializedTopologyFailureEvent_eq_cylinder (T : Strategy F K p) (lmb : K) :
    specializedTopologyFailureEvent T lmb =
      (cylinder (1 : Fin 4) (fun x : Fin 4 → K => topologyBad T lmb (x 3) (x 2))).map
        jointVecEquiv.toEmbedding := by
  haveI : Nonempty K := ⟨0⟩
  ext ω
  rw [Finset.mem_map_equiv, mem_specializedTopologyFailureEvent_iff]
  simp only [jointVecEquiv_symm_apply, cylinder, Finset.mem_filter, Finset.mem_univ, true_and,
    vecOfJoint_one, vecOfJoint_two, vecOfJoint_three]
  rw [mem_topologyBad_iff]

/-- The summand's bound, re-derived from `cylinder_card_le`.  Compare
`specializedTopologyFailureEvent_card_le` (`TemplateRawJointSoundness.lean:589`), which computes a
`biUnion` over `K × K` by hand. -/
theorem specializedTopologyFailureEvent_card_le_of_cylinder
    (T : Strategy F K p) (lmb : K) (workload : ℕ)
    (hwork : ∀ z (hz : z ≠ 0) alphaMValue,
      topologyWorkload (T.afterAlphaM z hz alphaMValue lmb).familyData.base ≤ workload) :
    (specializedTopologyFailureEvent T lmb).card ≤ workload * Fintype.card K ^ 3 := by
  haveI : Nonempty K := ⟨0⟩
  have hB : ∀ x : Fin 4 → K, (topologyBad T lmb (x 3) (x 2)).card ≤ workload := by
    intro x
    by_cases hz : x 3 ≠ 0
    · simp only [topologyBad, dif_pos hz]
      exact (topologyBadGammas_card_le _).trans (hwork (x 3) hz (x 2))
    · simp only [ne_eq, not_not] at hz
      simp [topologyBad, hz]
  rw [specializedTopologyFailureEvent_eq_cylinder, Finset.card_map]
  refine le_trans (cylinder_card_le (1 : Fin 4) (priorCoords jointChronology (1 : Fin 4))
    (not_mem_priorCoords _ _) _ (topologyBad_readsOn_prior T lmb) workload hB) ?_
  simpa using le_of_eq (Nat.mul_comm _ _)

end TopologyInstance

end

end Nock.NockVMROM.Thm54.RoundFibred

#print axioms Nock.NockVMROM.Thm54.RoundFibred.card_le_mul_of_fibre_card_le
#print axioms Nock.NockVMROM.Thm54.RoundFibred.fiberEvent_card_le_via_fibre
#print axioms Nock.NockVMROM.Thm54.RoundFibred.fiberEvent_card_le_of_base
#print axioms Nock.NockVMROM.Thm54.RoundFibred.fiberEvent₂_card_le
#print axioms Nock.NockVMROM.Thm54.RoundFibred.fiberEvent₃_card_le
#print axioms Nock.NockVMROM.Thm54.RoundFibred.seedBadJoint_card_le_of_chain
#print axioms Nock.NockVMROM.Thm54.RoundFibred.sepSeedJointBad_card_le_of_chain
#print axioms Nock.NockVMROM.Thm54.RoundFibred.walkBadJoint_card_le_of_chain
#print axioms Nock.NockVMROM.Thm54.RoundFibred.walkBadForestJoint_card_le_of_chain
#print axioms Nock.NockVMROM.Thm54.RoundFibred.cylinder_card_le
#print axioms Nock.NockVMROM.Thm54.RoundFibred.cylinder_bad_may_read_own_coordinate
#print axioms Nock.NockVMROM.Thm54.RoundFibred.cylinder_card_le_needs_dependence
#print axioms Nock.NockVMROM.Thm54.RoundFibred.roundUnion_card_le
#print axioms Nock.NockVMROM.Thm54.RoundFibred.roundUnion_card_le_of_chronology
#print axioms Nock.NockVMROM.Thm54.RoundFibred.chainBelow_image_card_le
#print axioms Nock.NockVMROM.Thm54.RoundFibred.chainAll_card_le
#print axioms Nock.NockVMROM.Thm54.RoundFibred.columnLocal_const_of_prior_challenges
#print axioms Nock.NockVMROM.Thm54.RoundFibred.columnLocal_factors_through_prior_challenges
#print axioms Nock.NockVMROM.Thm54.RoundFibred.columnLocal_readsOn_priorCoords
#print axioms Nock.NockVMROM.Thm54.RoundFibred.staged_error_union_card_le
#print axioms Nock.NockVMROM.Thm54.RoundFibred.liftSeed_eq_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.liftSeed_card_le_of_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.collisionFailureEvent_eq_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.SizeWindowFailure_eq_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.zeroSeedFailureEvent_eq_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.zeroSeedFailureEvent_card_le_of_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.guardedAxisFailureEvent_eq_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.guardedAxisFailureEvent_card_le_of_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.specializedTopologyFailureEvent_eq_cylinder
#print axioms Nock.NockVMROM.Thm54.RoundFibred.specializedTopologyFailureEvent_card_le_of_cylinder
