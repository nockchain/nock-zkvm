/-
  Nock/NockVMROM/Thm54/TraceGen/GenGuardedRom.lean

  **The guarded ROM evaluator `evalGRom q`, and its two refinements.**

  `nockCompiles_of_rom` (`GenNockCompiles.lean::nockCompiles_of_rom`) takes the paper's ROM
  restriction as its antecedent, `hrom : evalRom fuel subject formula = some result`.  Two of its premises — `hb` (`SemanticSkeleton.BoundedBy q`) and `haxis`
  (`SkeletonAxisRange q`) — have `∀ program` suppliers, `genComputeSkeleton_skeletonBounded`
  (`GenGenericBounded.lean::genComputeSkeleton_skeletonBounded`) and
  `genComputeSkeleton_axisRange` (`GenGenericAxisRange.lean::genComputeSkeleton_axisRange`), but
  both suppliers want a *guarded* run, `FieldEmbedding.evalGBy q fuel subject formula = some
  result`: the statement "this run never lets an `OP_4` increment reach `q`".

  Stating that guarded run **beside** `hrom` would trade two premises for three.  It is not
  needed: the two conditions are the same run under two different restrictions, and one evaluator
  carries both.  `evalGRom q` is `evalRom` verbatim with `Noun.lus` replaced by
  `FieldEmbedding.lusGBy q` at `OP_4`, exactly as `Nock.evalGPaper` is `evalPaperMod` with that
  replacement (`PaperFieldBridge.lean::evalGPaper`).  So

  * `evalGRom_le_evalGBy` — a guarded ROM run is a guarded full run (drop the ROM restriction),
    which is what the two suppliers consume.

  **This is a strictly stronger antecedent than `hrom`, and deliberately so.**  `evalGRom_ne_evalRom_at_overflow`
  (`Nock/RedTeam/Batch263Thm54BoundedPremisesAtTierA.lean`) exhibits a ROM program where the two
  disagree, so the strengthening is real and must not be read as a restatement.

  Axis-guard lemmas **moved** from `Batch557Thm54RangeGadget.lean`
  (do not re-prove): `evalGAxRom`, `evalGRom_boundedBy_axes`, `RunAxesBoundedBy`,
  `runAxesBoundedBy_of_hyps`, `result_boundedBy_of_hyps`, `exists_cert`.  `Batch556.evalGRom_op0_unguarded` remains true and is
  why `hbound` alone does not bound axes.
-/
import Mathlib.Data.Nat.Size
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.TraceGen.GenRomComplete
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock

/-! ## The guarded ROM transition function

`evalRom` (`GenRomComplete.lean::evalRom`) with the crashing increment `FieldEmbedding.lusGBy q`
in place of `Noun.lus`.  Every other arm is character-for-character `evalRom`'s, and `OP_10` and
above are rejected exactly as there -/

/-- **`*[subject formula]` in `NockVMROM^Λ`, without overflowing `q`** — fuel-indexed, `OP_10` and
above rejected, `OP_4` crashing rather than producing an atom `≥ q`. -/
def evalGRom (q : Nat) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalGRom q fuel subj (.cell b c), evalGRom q fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => Noun.slot ax subj
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalGRom q fuel subj b, evalGRom q fuel subj c with
             | some sb, some sc => evalGRom q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalGRom q fuel subj tail).map Noun.wut
    | 4 => (evalGRom q fuel subj tail).bind (FieldEmbedding.lusGBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalGRom q fuel subj b, evalGRom q fuel subj c with
             | some sb, some sc => some (Noun.tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalGRom q fuel subj b with
             | some (.atom 0) => evalGRom q fuel subj c
             | some (.atom 1) => evalGRom q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalGRom q fuel subj b with
             | some sb => evalGRom q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalGRom q fuel subj b with
             | some sb => evalGRom q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalGRom q fuel subj c with
             | some core =>
               match Noun.slot ax core with
               | some arm => evalGRom q fuel core arm
               | none => none
             | none => none
           | _ => none
    | _ => none

/-! ## The guard on the increment

The only arm where `evalGRom` and `evalRom` can differ.  A successful `lusGBy q` pins `n + 1 < q`,
and there the crashing increment and `Noun.lus` produce the same atom. -/

/-- A successful guarded increment is the unbounded increment. -/
theorem lusGBy_lus {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : Noun.lus x = some m := by
  cases x with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        simp [Noun.lus, ← h]
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h

/-- A successful guarded increment produces an atom `< q`. -/
theorem lusGBy_boundedBy {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : FieldEmbedding.BoundedBy q m := by
  cases x with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        simpa [FieldEmbedding.BoundedBy, ← h] using hlt
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h

/-- **Atoms are bounded at creation.**  `evalGRom` only mints a leaf at `OP_4`
(`lusGBy`); every other arm returns a sub-noun, a `0`/`1`, a `cons` of results, or
the result of a sub-run.  `Batch556.evalGRom_op0_unguarded` is correct (the lookup
itself does not cap `ax`) and irrelevant once every atom of `s`/`f` and every
created atom is `< q` -/
theorem evalGRom_boundedBy {q : Nat} :
    ∀ (n : Nat) (s f r : Noun),
      FieldEmbedding.BoundedBy q s → FieldEmbedding.BoundedBy q f →
        evalGRom q n s f = some r → FieldEmbedding.BoundedBy q r := by
  intro n
  induction n with
  | zero => intro s f r _ _ h; simp [evalGRom] at h
  | succ fuel ih =>
    intro s f r hs hf h
    match f with
    | .atom _ => simp [evalGRom] at h
    | .cell (.cell b c) d =>
        obtain ⟨hfbc, hfd⟩ := hf
        simp only [evalGRom] at h
        cases hbc : evalGRom q fuel s (.cell b c) with
        | none => rw [hbc] at h; simp at h
        | some l =>
          cases hd : evalGRom q fuel s d with
          | none => rw [hbc, hd] at h; simp at h
          | some r' =>
            rw [hbc, hd] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨ih s (.cell b c) l hs hfbc hbc, ih s d r' hs hfd hd⟩
    | .cell (.atom op) tail =>
        obtain ⟨hop, hft⟩ := hf
        match op, hop with
        | 0, _ =>
            simp only [evalGRom] at h
            match tail with
            | .atom ax => exact FieldEmbedding.slot_boundedBy q ax s hs h
            | .cell _ _ => simp at h
        | 1, _ =>
            simp only [evalGRom] at h
            obtain rfl := Option.some.inj h
            exact hft
        | 2, _ =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGRom] at h
                cases hb : evalGRom q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  cases hc : evalGRom q fuel s c with
                  | none => rw [hb, hc] at h; simp at h
                  | some sc =>
                    rw [hb, hc] at h
                    exact ih sb sc r
                      (ih s b sb hs hfb hb) (ih s c sc hs hfc hc) h
            | .atom _ => simp [evalGRom] at h
        | 3, hop =>
            have hq : 1 < q := Nat.lt_trans (by decide : 1 < 3) hop
            simp only [evalGRom] at h
            cases ht : evalGRom q fuel s tail with
            | none => rw [ht] at h; simp at h
            | some v =>
              rw [ht] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              exact FieldEmbedding.wut_boundedBy hq v
        | 4, _ =>
            simp only [evalGRom] at h
            cases ht : evalGRom q fuel s tail with
            | none => rw [ht] at h; simp at h
            | some v =>
              rw [ht] at h
              exact lusGBy_boundedBy h
        | 5, hop =>
            have hq : 1 < q := Nat.lt_trans (by decide : 1 < 5) hop
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGRom] at h
                cases hb : evalGRom q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  cases hc : evalGRom q fuel s c with
                  | none => rw [hb, hc] at h; simp at h
                  | some sc =>
                    rw [hb, hc] at h
                    simp only [Option.some.injEq] at h
                    subst h
                    exact FieldEmbedding.tis_boundedBy hq sb sc
            | .atom _ => simp [evalGRom] at h
        | 6, _ =>
            match tail with
            | .cell b (.cell c d) =>
                obtain ⟨hfb, hfc, hfd⟩ := hft
                simp only [evalGRom] at h
                cases hb : evalGRom q fuel s b with
                | none => rw [hb] at h; simp at h
                | some vb =>
                  rw [hb] at h
                  match vb with
                  | .atom 0 => exact ih s c r hs hfc h
                  | .atom 1 => exact ih s d r hs hfd h
                  | .atom (_ + 2) => simp at h
                  | .cell _ _ => simp at h
            | .cell _ (.atom _) => simp [evalGRom] at h
            | .atom _ => simp [evalGRom] at h
        | 7, _ =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGRom] at h
                cases hb : evalGRom q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  rw [hb] at h
                  exact ih sb c r (ih s b sb hs hfb hb) hfc h
            | .atom _ => simp [evalGRom] at h
        | 8, _ =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGRom] at h
                cases hb : evalGRom q fuel s b with
                | none => rw [hb] at h; simp at h
                | some sb =>
                  rw [hb] at h
                  exact ih (.cell sb s) c r ⟨ih s b sb hs hfb hb, hs⟩ hfc h
            | .atom _ => simp [evalGRom] at h
        | 9, _ =>
            match tail with
            | .cell (.atom ax) c =>
                obtain ⟨_, hfc⟩ := hft
                simp only [evalGRom] at h
                cases hc : evalGRom q fuel s c with
                | none => rw [hc] at h; simp at h
                | some core =>
                  rw [hc] at h
                  dsimp only at h
                  have hBcore : FieldEmbedding.BoundedBy q core :=
                    ih s c core hs hfc hc
                  cases harm : Noun.slot ax core with
                  | none => rw [harm] at h; simp at h
                  | some arm =>
                    rw [harm] at h
                    dsimp only at h
                    exact ih core arm r hBcore
                      (FieldEmbedding.slot_boundedBy q ax core hBcore harm) h
            | .cell (.cell _ _) _ => simp [evalGRom] at h
            | .atom _ => simp [evalGRom] at h
        | _ + 10, _ => simp [evalGRom] at h

/-! `evalGAxRom q` is `evalGRom q` with the `OP_0` / `OP_9` axis atom rejected when
`ax ≥ q`.  `RunAxesBoundedBy` is the analogue of `RunBoundedBy`
(`GenNockCompilesCarrier.lean::RunBoundedBy`) -/

/-- **`evalGRom q` with the OP0 tail atom and the OP9 axis atom guarded `< q`**
    (`Batch557.evalGAxRom`, moved). -/
def evalGAxRom (q : Nat) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalGAxRom q fuel subj (.cell b c), evalGAxRom q fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => if ax < q then Noun.slot ax subj else none
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalGAxRom q fuel subj b, evalGAxRom q fuel subj c with
             | some sb, some sc => evalGAxRom q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalGAxRom q fuel subj tail).map Noun.wut
    | 4 => (evalGAxRom q fuel subj tail).bind (FieldEmbedding.lusGBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalGAxRom q fuel subj b, evalGAxRom q fuel subj c with
             | some sb, some sc => some (Noun.tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalGAxRom q fuel subj b with
             | some (.atom 0) => evalGAxRom q fuel subj c
             | some (.atom 1) => evalGAxRom q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalGAxRom q fuel subj b with
             | some sb => evalGAxRom q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalGAxRom q fuel subj b with
             | some sb => evalGAxRom q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             if ax < q then
               match evalGAxRom q fuel subj c with
               | some core =>
                 match Noun.slot ax core with
                 | some arm => evalGAxRom q fuel core arm
                 | none => none
               | none => none
             else none
           | _ => none
    | _ => none

abbrev evalGAx := evalGAxRom

/-- **The invariant `hbound`, `hs`, `hf` carry** (`Batch557.evalGRom_boundedBy_axes`,
    moved).  A guarded ROM run on a `BoundedBy q` subject and formula (`1 < q`)
    never reaches an OP0/OP9 axis atom `≥ q` — it is an axis-guarded run — and
    its result is `BoundedBy q` -/
theorem evalGRom_boundedBy_axes (q : ℕ) (hq : 1 < q) :
    ∀ (fuel : ℕ) (s f : Noun), ∀ r : Noun,
      FieldEmbedding.BoundedBy q s → FieldEmbedding.BoundedBy q f →
      evalGRom q fuel s f = some r →
        FieldEmbedding.BoundedBy q r ∧ evalGAxRom q fuel s f = some r := by
  intro fuel s f
  induction fuel, s, f using evalGRom.induct q <;> intro r hs hf h <;>
    simp only [evalGRom, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] at h <;>
    simp only [evalGAxRom, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq] <;>
    grind [FieldEmbedding.slot_boundedBy, FieldEmbedding.wut_boundedBy,
      FieldEmbedding.tis_boundedBy, lusGBy_boundedBy, FieldEmbedding.BoundedBy_cell,
      FieldEmbedding.BoundedBy_atom]

/-- The axis guard is redundant on nouns whose every atom is `< q`. -/
theorem evalGAxRom_eq_evalGRom_of_bounded {q : Nat} :
    ∀ (n : Nat) (s form : Noun),
      FieldEmbedding.BoundedBy q s → FieldEmbedding.BoundedBy q form →
        evalGAxRom q n s form = evalGRom q n s form := by
  intro n
  induction n with
  | zero => intro s form _ _; rfl
  | succ fuel ih =>
    intro s form hs hf
    match form with
    | .atom _ => rfl
    | .cell (.cell b c) d =>
        obtain ⟨hfbc, hfd⟩ := hf
        simp only [evalGAxRom, evalGRom, ih s (.cell b c) hs hfbc, ih s d hs hfd]
    | .cell (.atom op) tail =>
        obtain ⟨_, hft⟩ := hf
        match op with
        | 0 =>
            match tail with
            | .atom ax =>
                have hax : ax < q := hft
                simp [evalGAxRom, evalGRom, hax]
            | .cell _ _ => rfl
        | 1 => rfl
        | 2 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGAxRom, evalGRom, ih s b hs hfb, ih s c hs hfc]
                cases hb : evalGRom q fuel s b with
                | none => rfl
                | some sb =>
                  cases hc : evalGRom q fuel s c with
                  | none => rfl
                  | some sc =>
                    exact ih sb sc (evalGRom_boundedBy _ _ _ _ hs hfb hb)
                      (evalGRom_boundedBy _ _ _ _ hs hfc hc)
            | .atom _ => rfl
        | 3 =>
            simp only [evalGAxRom, evalGRom, ih s tail hs hft]
        | 4 =>
            simp only [evalGAxRom, evalGRom, ih s tail hs hft]
        | 5 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGAxRom, evalGRom, ih s b hs hfb, ih s c hs hfc]
            | .atom _ => rfl
        | 6 =>
            match tail with
            | .cell b (.cell c d) =>
                obtain ⟨hfb, hfc, hfd⟩ := hft
                simp only [evalGAxRom, evalGRom, ih s b hs hfb]
                cases hb : evalGRom q fuel s b with
                | none => rfl
                | some vb =>
                  match vb with
                  | .atom 0 => exact ih s c hs hfc
                  | .atom 1 => exact ih s d hs hfd
                  | .atom (_ + 2) => rfl
                  | .cell _ _ => rfl
            | .cell _ (.atom _) => rfl
            | .atom _ => rfl
        | 7 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGAxRom, evalGRom, ih s b hs hfb]
                cases hb : evalGRom q fuel s b with
                | none => rfl
                | some sb =>
                  exact ih sb c (evalGRom_boundedBy _ _ _ _ hs hfb hb) hfc
            | .atom _ => rfl
        | 8 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGAxRom, evalGRom, ih s b hs hfb]
                cases hb : evalGRom q fuel s b with
                | none => rfl
                | some sb =>
                  exact ih (.cell sb s) c
                    ⟨evalGRom_boundedBy _ _ _ _ hs hfb hb, hs⟩ hfc
            | .atom _ => rfl
        | 9 =>
            match tail with
            | .cell (.atom ax) c =>
                obtain ⟨haxB, hfc⟩ := hft
                have hax : ax < q := haxB
                simp only [evalGAxRom, evalGRom, hax, ite_true, ih s c hs hfc]
                cases hc : evalGRom q fuel s c with
                | none => rfl
                | some core =>
                  have hBcore : FieldEmbedding.BoundedBy q core :=
                    evalGRom_boundedBy _ _ _ _ hs hfc hc
                  cases harm : Noun.slot ax core with
                  | none => simp [harm]
                  | some arm =>
                    simp [harm]
                    exact ih core arm hBcore
                      (FieldEmbedding.slot_boundedBy q ax core hBcore harm)
            | .cell (.cell _ _) _ => rfl
            | .atom _ => rfl
        | _ + 10 => rfl

/-- Axis atoms of a successful run stay `< q`.  Same shape as
`RunBoundedBy` (`GenNockCompilesCarrier.lean::RunBoundedBy`); the first
argument of `runAxesBoundedBy_of_run` is that exists, definitionally. -/
def RunAxesBoundedBy (q fuel : Nat) (subject formula : Noun) : Prop :=
  ∃ result, evalGAxRom q fuel subject formula = some result

/-- `hbound + hs + hf` discharge the axis bound: every atom of a successful
`evalGRom` run is `< q`, so the axis guard never fires.
`Batch556.evalGRom_op0_unguarded` remains true and is the reason this lemma
needs `hs`/`hf` rather than `hbound` alone -/
theorem runAxesBoundedBy_of_run {q fuel : Nat} {subject formula : Noun}
    (hbound : ∃ result, evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula) :
    RunAxesBoundedBy q fuel subject formula := by
  obtain ⟨r, hr⟩ := hbound
  refine ⟨r, ?_⟩
  rwa [evalGAxRom_eq_evalGRom_of_bounded _ _ _ hs hf]

/-- **`hax` is a theorem of the tree's hypotheses** (`Batch557.runAxesBoundedBy_of_hyps`,
    moved): `hp : 25 ≤ p`, `hbound` (exists/`RunBoundedBy`), `hs`, `hf` give
    `RunAxesBoundedBy p`.  No new `nockCompiles_zmod` hypothesis. -/
theorem runAxesBoundedBy_of_hyps {p fuel : ℕ} {subject formula : Noun} (hp : 25 ≤ p)
    (hbound : ∃ result, evalGRom p fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula) :
    RunAxesBoundedBy p fuel subject formula := by
  obtain ⟨r, hr⟩ := hbound
  exact ⟨r, (evalGRom_boundedBy_axes p (by omega) fuel subject formula r hs hf hr).2⟩

/-- The same run's result is `BoundedBy p` (the invariant's other half). -/
theorem result_boundedBy_of_hyps {p fuel : ℕ} {subject formula result : Noun}
    (hp : 25 ≤ p)
    (hr : evalGRom p fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula) :
    FieldEmbedding.BoundedBy p result :=
  (evalGRom_boundedBy_axes p (by omega) fuel subject formula result hs hf hr).1

/-! ## Axis certificate representability (`Batch557.exists_cert`, moved)

`cert` is `Batch555.cert` (same formula).  Every `1 ≤ a < p` is certified with
`m ≤ Nat.size p − 1`.  Certificate *gates* stay last. -/

def bitsOf (m : ℕ) (c : ℕ → Bool) : List Bool :=
  List.ofFn fun i : Fin m => c (i.val + 1)

def val : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat * 2 ^ bs.length + val bs

theorem bitsOf_length (m : ℕ) (c : ℕ → Bool) : (bitsOf m c).length = m := by
  simp [bitsOf]

theorem bitsOf_succ (m : ℕ) (c : ℕ → Bool) :
    bitsOf (m + 1) c = c 1 :: bitsOf m (fun j => c (j + 1)) := by
  simp only [bitsOf, List.ofFn_succ, Fin.val_zero, zero_add, Fin.val_succ]

theorem val_bitsOf (m : ℕ) : ∀ c : ℕ → Bool,
    val (bitsOf m c) = ∑ j ∈ Finset.range m, (c (j + 1)).toNat * 2 ^ (m - (j + 1)) := by
  induction m with
  | zero => intro c; simp [bitsOf, val]
  | succ m ih =>
      intro c
      rw [bitsOf_succ, Finset.sum_range_succ']
      simp only [val, bitsOf_length, ih (fun j => c (j + 1)), Nat.add_sub_cancel]
      have : ∀ j ∈ Finset.range m,
          (c (j + 1 + 1)).toNat * 2 ^ (m - (j + 1)) =
            (c (j + 1 + 1)).toNat * 2 ^ (m + 1 - (j + 1 + 1)) := by
        intro j _
        rw [show m + 1 - (j + 1 + 1) = m - (j + 1) by omega]
      rw [Finset.sum_congr rfl this, zero_add, add_comm]

/-- Integer axis certificate (`Batch555.cert`, same formula). -/
def cert (m : ℕ) (c : ℕ → Bool) : ℕ :=
  2 ^ m + ∑ j ∈ Finset.range m, (c (j + 1)).toNat * 2 ^ (m - (j + 1))

theorem cert_eq_val (m : ℕ) (c : ℕ → Bool) : cert m c = val (true :: bitsOf m c) := by
  simp [cert, val, bitsOf_length, val_bitsOf]

def pbits (n p : ℕ) : List Bool := List.ofFn fun i : Fin n => p.testBit (n - 1 - i)

theorem pbits_succ (n p : ℕ) : pbits (n + 1) p = p.testBit n :: pbits n p := by
  simp only [pbits, List.ofFn_succ, Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ]
  congr 1
  exact congrArg List.ofFn (funext fun i => by congr 1; omega)

theorem pbits_length (n p : ℕ) : (pbits n p).length = n := by simp [pbits]

theorem val_pbits (n p : ℕ) : val (pbits n p) = p % 2 ^ n := by
  induction n with
  | zero => simp [pbits, val, Nat.mod_one]
  | succ n ih =>
      rw [pbits_succ, val, pbits_length, ih, Nat.toNat_testBit, Nat.mod_pow_succ]
      ring

theorem size_spec (n : ℕ) (hn : 0 < n) :
    2 ^ (Nat.size n - 1) ≤ n ∧ n < 2 ^ Nat.size n :=
  ⟨Nat.lt_size.mp (Nat.sub_lt (Nat.size_pos.mpr hn) Nat.one_pos), Nat.lt_size_self n⟩

private theorem toNat_eq_one {b : Bool} (h : b.toNat = 1) : b = true := by
  cases b <;> simp at h ⊢

/-- **Every axis `1 ≤ a < p` is certified with `m ≤ n − 1`.**
    (`Batch557.exists_cert`, moved.) -/
theorem exists_cert (p a : ℕ) (ha : 0 < a) (hap : a < p) :
    ∃ m c, m ≤ Nat.size p - 1 ∧ cert m c = a := by
  obtain ⟨hlo, hhi⟩ := size_spec a ha
  have hn : 1 ≤ Nat.size a := Nat.size_pos.mpr ha
  refine ⟨Nat.size a - 1, fun j => a.testBit (Nat.size a - 1 - j), ?_, ?_⟩
  · have := Nat.size_le_size (le_of_lt hap)
    omega
  · set m := Nat.size a - 1 with hm
    have htop : a.testBit m = true := by
      apply toNat_eq_one
      rw [Nat.toNat_testBit]
      have h2 : (1 + 1) * 2 ^ m = 2 ^ Nat.size a := by
        rw [show 1 + 1 = 2 by rfl, ← pow_succ', show m + 1 = Nat.size a by omega]
      have hdiv : a / 2 ^ m = 1 :=
        Nat.div_eq_of_lt_le (by rw [one_mul]; exact hlo) (by rw [h2]; exact hhi)
      rw [hdiv]
    have hlist : true :: bitsOf m (fun j => a.testBit (m - j)) = pbits (m + 1) a := by
      rw [pbits_succ, htop]
      congr 1
      simp only [bitsOf, pbits]
      exact congrArg List.ofFn (funext fun i => by congr 1; omega)
    rw [cert_eq_val, hlist, val_pbits, show m + 1 = Nat.size a by omega, Nat.mod_eq_of_lt hhi]

/-! ## The two refinements -/

/-- **`evalGRom q` refines `evalRom`.**  Dropping the guard: a guarded ROM run is a ROM run with
the same value. -/
theorem evalGRom_le_evalRom {q n : Nat} {s form r : Noun}
    (h : evalGRom q n s form = some r) : evalRom n s form = some r := by
  induction n, s, form using evalGRom.induct q generalizing r <;>
    simp_all only [evalGRom, evalRom, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind [lusGBy_lus]

/-- **`evalGRom q` refines `FieldEmbedding.evalGBy q`.**  Dropping the ROM restriction: a guarded
ROM run is a guarded full run with the same value.  This is what
`genComputeSkeleton_skeletonBounded` and `genComputeSkeleton_axisRange` consume. -/
theorem evalGRom_le_evalGBy {q n : Nat} {s form r : Noun}
    (h : evalGRom q n s form = some r) : FieldEmbedding.evalGBy q n s form = some r := by
  induction n, s, form using evalGRom.induct q generalizing r <;>
    simp_all only [evalGRom, FieldEmbedding.evalGBy, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind [lusGBy_lus]

theorem evalGRom_evalN {q n : Nat} {s form r : Noun}
    (h : evalGRom q n s form = some r) : Nock.evalN n s form = some r :=
  evalRom_evalN (evalGRom_le_evalRom h)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.lusGBy_lus
#print axioms Nock.NockVMROM.Thm54.TraceGen.lusGBy_boundedBy
#print axioms Nock.NockVMROM.Thm54.TraceGen.evalGRom_boundedBy
#print axioms Nock.NockVMROM.Thm54.TraceGen.evalGRom_boundedBy_axes
#print axioms Nock.NockVMROM.Thm54.TraceGen.evalGAxRom_eq_evalGRom_of_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.runAxesBoundedBy_of_run
#print axioms Nock.NockVMROM.Thm54.TraceGen.runAxesBoundedBy_of_hyps
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_cert
#print axioms Nock.NockVMROM.Thm54.TraceGen.evalGRom_le_evalRom
#print axioms Nock.NockVMROM.Thm54.TraceGen.evalGRom_le_evalGBy
#print axioms Nock.NockVMROM.Thm54.TraceGen.evalGRom_evalN
