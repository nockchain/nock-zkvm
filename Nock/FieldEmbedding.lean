import Nock.Reference
import Nock.Field

/-!
# B1 — Nat-valued Nock ↔ field-valued Nock embedding

The paper's Nock is **field-valued**: nouns are proper binary trees whose leaves carry
elements of the Goldilocks field `𝔽_p`, `p = 2^64 − 2^32 + 1`,
and the increment operator reduces modulo `p`:  `+(n) = (1 + n) mod p`.  The Lean reference semantics `Nock.evalN` (`Nock/Reference.lean`)
is the standard **Nat-valued** Urbit Nock: atoms are `ℕ`, increment is `n ↦ n + 1` with no
reduction.

The two semantics agree EXCEPT at atoms that reach `p`: Nat increment gives `p`, field
increment gives `0`; and a Nat atom `≥ p` compared for equality or
dispatched as an opcode/axis behaves differently from its field image `n mod p`.

This module makes the embedding and the agreement precise, under an **honest, non-vacuous
no-overflow side condition**:

* `BoundedBy q n`           — every atom of `n` is `< q`.
* `evalF`                   — the **field-valued** evaluator.
* `evalG`                   — the Nat evaluator with a *guard* that **crashes** rather than
                              letting any increment reach `p`.  `evalG fuel s f = some r` is
                              exactly the statement "this computation runs without overflow".
* Top theorem `noOverflow_agree` — on field-noun inputs (`Bounded s`, `Bounded f`), whenever the
                              computation is overflow-free (`evalG fuel s f = some r`), the
                              Nat-valued reference `evalN` and the field-valued `evalF` BOTH
                              return `r` (and `r` is again a field noun).

The no-overflow condition is a *genuine* hypothesis, not vacuous: it holds for every ordinary
Nock program whose atoms stay below `2^64 − 2^32 + 1` (see the `#eval` witnesses at the end),
and it fails exactly on computations that would wrap the field.

The field connection to Mathlib's `ZMod p` (`Nock.Field`) is proved at the atom level in
`lusF_eq_zmod` / `emb_inj_on_bounded`: the canonical representative `(n mod p)` used by `evalF`
is `((n : ZMod p)).val`, and the field increment is `(· + 1)` in `ZMod p`.

**Axioms.**  The core agreement theorems (`agree`, `noOverflow_agree`, `evalG_le_evalN`) use
only `{propext, Classical.choice, Quot.sound}` — not even `goldilocks_prime`.  The `ZMod p`
bridge lemmas (`emb_inj_on_bounded`, `lusF_eq_zmod`, `natCast_inj_of_lt`) additionally pull in
the single blessed axiom `Nock.Field.goldilocks_prime`, via Mathlib's `ZMod p` field/`NeZero`
instances; this is within the sprint's allowed axiom set.
-/

namespace Nock.FieldEmbedding

open Nock Nock.Noun

/-- The Goldilocks modulus, re-exported from `Nock.Field`. -/
abbrev p : ℕ := Field.p

theorem p_pos : 0 < p := by norm_num [Field.p]
theorem one_lt_p : 1 < p := by norm_num [Field.p]

/-! ## Field nouns: bounded leaf labels -/

/-- `BoundedBy q n` means that every atom (leaf) of `n` is in the numeric range `[0,q)`.
    This is the bound needed when the operative prime varies with a security parameter. -/
def BoundedBy (q : ℕ) : Noun → Prop
  | .atom n   => n < q
  | .cell l r => BoundedBy q l ∧ BoundedBy q r

@[simp] theorem BoundedBy_atom {q n : ℕ} : BoundedBy q (.atom n) ↔ n < q := Iff.rfl
@[simp] theorem BoundedBy_cell {q : ℕ} {l r : Noun} :
    BoundedBy q (.cell l r) ↔ BoundedBy q l ∧ BoundedBy q r := Iff.rfl

abbrev Bounded : Noun → Prop := BoundedBy p

@[simp] theorem Bounded_atom {n : ℕ} : Bounded (.atom n) ↔ n < p := Iff.rfl
@[simp] theorem Bounded_cell {l r : Noun} : Bounded (.cell l r) ↔ Bounded l ∧ Bounded r := Iff.rfl

/-! ## The field increment `+(n) = (1 + n) mod p` -/

/-- Increment modulo `q` on an atom, crash on a cell. -/
def lusFBy (q : ℕ) : Noun → Option Noun
  | .atom n   => some (.atom ((n + 1) % q))
  | .cell _ _ => none

abbrev lusF : Noun → Option Noun := lusFBy p

/-- Guarded Nat increment: like `Noun.lus` (`n ↦ n+1`) but **crashes** instead of overflowing
    the selected range, i.e. it refuses to produce an atom `≥ q`.  A successful guarded run
    witnesses that no increment reached `q` — this is how the no-overflow side condition is
    encoded honestly. -/
def lusGBy (q : ℕ) : Noun → Option Noun
  | .atom n   => if n + 1 < q then some (.atom (n + 1)) else none
  | .cell _ _ => none

abbrev lusG : Noun → Option Noun := lusGBy p

/-! ## The field-valued evaluator `evalF`

`evalFBy q` is `Nock.evalN` verbatim EXCEPT that OP_4 (`+`) uses increment modulo `q`.
All other operators are structural (they only rearrange existing leaves) or produce the
constants `0`/`1`, so over field nouns they coincide with the Nat versions; hence `evalF`
reuses `Noun.slot`, `Noun.edit`, `Noun.wut`, `Noun.tis` from `Nock/Reference.lean`.  Equality compares nouns structurally; over `Bounded` nouns this is field equality
(distinct `< p` atoms are distinct in `𝔽_p`). -/
def evalFBy (q : ℕ) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalFBy q fuel subj (.cell b c), evalFBy q fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => slot ax subj
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b, evalFBy q fuel subj c with
             | some sb, some sc => evalFBy q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalFBy q fuel subj tail).map wut
    | 4 => (evalFBy q fuel subj tail).bind (lusFBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b, evalFBy q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalFBy q fuel subj b with
             | some (.atom 0) => evalFBy q fuel subj c
             | some (.atom 1) => evalFBy q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b with
             | some sb => evalFBy q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b with
             | some sb => evalFBy q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalFBy q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalFBy q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalFBy q fuel subj c, evalFBy q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | 11 => match tail with
            | .cell (.cell _ clue) body =>
              match evalFBy q fuel subj clue with
              | some _ => evalFBy q fuel subj body
              | none => none
            | .cell (.atom _) body => evalFBy q fuel subj body
            | _ => none
    | _ => none

abbrev evalF : Nat → Noun → Noun → Option Noun := evalFBy p

/-! ## The guarded (no-overflow) evaluator `evalG`

`evalGBy q` is `Nock.evalN` verbatim EXCEPT that OP_4 uses `lusGBy q`, which crashes on overflow. -/
def evalGBy (q : ℕ) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalGBy q fuel subj (.cell b c), evalGBy q fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => slot ax subj
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b, evalGBy q fuel subj c with
             | some sb, some sc => evalGBy q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalGBy q fuel subj tail).map wut
    | 4 => (evalGBy q fuel subj tail).bind (lusGBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b, evalGBy q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalGBy q fuel subj b with
             | some (.atom 0) => evalGBy q fuel subj c
             | some (.atom 1) => evalGBy q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b with
             | some sb => evalGBy q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b with
             | some sb => evalGBy q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalGBy q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalGBy q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalGBy q fuel subj c, evalGBy q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | 11 => match tail with
            | .cell (.cell _ clue) body =>
              match evalGBy q fuel subj clue with
              | some _ => evalGBy q fuel subj body
              | none => none
            | .cell (.atom _) body => evalGBy q fuel subj body
            | _ => none
    | _ => none

abbrev evalG : Nat → Noun → Noun → Option Noun := evalGBy p

/-! ## `BoundedBy` is preserved by the structural operators -/

/-- `slot` returns a subtree of `n`, so it preserves every numeric leaf bound. -/
theorem slot_boundedBy (q : ℕ) (ax : Nat) (n : Noun) :
    BoundedBy q n → ∀ {m : Noun}, slot ax n = some m → BoundedBy q m := by
  induction ax, n using Nock.Noun.slot.induct with
  | case1 x => intro _ m h; simp [slot] at h
  | case2 n => intro hn m h; simp only [slot] at h; obtain rfl := Option.some.inj h; exact hn
  | case3 a n l r hrec ih =>
      intro hn m h
      have hlr : BoundedBy q (Noun.cell l r) := ih hn hrec
      simp only [slot, hrec] at h
      split at h
      · obtain rfl := Option.some.inj h; exact hlr.1
      · obtain rfl := Option.some.inj h; exact hlr.2
  | case4 a n hno ih =>
      intro hn m h
      simp only [slot] at h
      cases hs : slot ((a + 2) / 2) n with
      | none => simp at h
      | some w =>
        cases w with
        | atom k => simp at h
        | cell l r => exact (hno l r hs).elim

theorem slot_bounded (ax : Nat) (n : Noun) :
    Bounded n → ∀ {m : Noun}, slot ax n = some m → Bounded m :=
  slot_boundedBy p ax n

/-- `edit` grafts `new` into `old`, so it preserves every numeric leaf bound. -/
theorem edit_boundedBy (q : ℕ) (ax : Nat) (new old : Noun) :
    BoundedBy q new → BoundedBy q old →
      ∀ {m : Noun}, edit ax new old = some m → BoundedBy q m := by
  induction ax, new, old using Nock.Noun.edit.induct with
  | case1 x y => intro _ _ m h; simp [edit] at h
  | case2 new x => intro hnew _ m h; simp only [edit] at h; obtain rfl := Option.some.inj h; exact hnew
  | case3 a new old sibAxis sib hsib paired ih =>
      intro hnew hold m h
      have hsibB : BoundedBy q sib := slot_boundedBy q _ _ hold hsib
      have hpair : ∀ b : Bool, BoundedBy q
          (if b = true then new.cell sib else sib.cell new) := by
        intro b; cases b <;> exact ⟨by assumption, by assumption⟩
      simp only [edit] at h
      rw [show slot (if ((a + 2) % 2 == 0) = true then a + 2 + 1 else a + 2 - 1) old = some sib
            from hsib] at h
      exact ih (hpair _) hold h
  | case4 a new old sibAxis hnone =>
      intro _ _ m h
      simp only [edit] at h
      rw [show slot (if ((a + 2) % 2 == 0) = true then a + 2 + 1 else a + 2 - 1) old = none
            from hnone] at h
      simp at h

theorem edit_bounded (ax : Nat) (new old : Noun) :
    Bounded new → Bounded old → ∀ {m : Noun}, edit ax new old = some m → Bounded m :=
  edit_boundedBy p ax new old

/-- Increment modulo a positive `q` always produces an atom `< q`. -/
theorem lusFBy_bounded {q : ℕ} (hq : 0 < q) {x m : Noun}
    (h : lusFBy q x = some m) : BoundedBy q m := by
  cases x with
  | atom n => simp only [lusFBy] at h; obtain rfl := Option.some.inj h; exact Nat.mod_lt _ hq
  | cell l r => simp [lusFBy] at h

theorem lusF_bounded {x m : Noun} (h : lusF x = some m) : Bounded m :=
  lusFBy_bounded p_pos h

theorem wut_boundedBy {q : ℕ} (hq : 1 < q) (x : Noun) : BoundedBy q (wut x) := by
  cases x with
  | cell _ _ =>
      simp only [wut, BoundedBy_atom]
      omega
  | atom _ => exact hq

theorem wut_bounded (x : Noun) : Bounded (wut x) := wut_boundedBy one_lt_p x

theorem tis_boundedBy {q : ℕ} (hq : 1 < q) (a b : Noun) : BoundedBy q (tis a b) := by
  unfold tis; split
  · simp only [BoundedBy_atom]
    omega
  · exact hq

theorem tis_bounded (a b : Noun) : Bounded (tis a b) := tis_boundedBy one_lt_p a b

/-! ## Main agreement lemma (the no-overflow simulation)

`agree` is proved by induction on `fuel`.  Its conclusion bundles the three facts that must
be carried through the recursion simultaneously:
* `evalN … = some r`  — the Nat reference reproduces the guarded result;
* `evalF … = some r`  — the field-valued evaluator reproduces it too; and
* `Bounded r`          — the result is again a field noun (needed to feed nested calls).

The ONLY place the three evaluators differ is OP_4 (`+`): there `evalGBy q` succeeds exactly when
`n + 1 < q`, and under that guard the Nat increment (`n+1`) and the modular increment
(`(n+1) mod q`) coincide — this is where no-overflow discharges the divergence. -/
theorem agreeBy (q : ℕ) (hq : 1 < q) :
    ∀ (fuel : Nat) (s f r : Noun), BoundedBy q s → BoundedBy q f →
      evalGBy q fuel s f = some r →
        evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r := by
  intro fuel
  induction fuel with
  | zero => intro s f r _ _ hG; simp [evalGBy] at hG
  | succ fuel ih =>
    intro s f r hs hf hG
    match f with
    | .atom a => simp [evalGBy] at hG
    | .cell (.cell b c) d =>
        -- autocons
        obtain ⟨hfbc, hfd⟩ := hf
        simp only [evalGBy] at hG
        cases hbc : evalGBy q fuel s (.cell b c) with
        | none => rw [hbc] at hG; simp at hG
        | some l =>
          cases hd : evalGBy q fuel s d with
          | none => rw [hbc, hd] at hG; simp at hG
          | some r' =>
            rw [hbc, hd] at hG
            simp only [Option.some.injEq] at hG
            obtain ⟨hNbc, hFbc, hBl⟩ := ih s (.cell b c) l hs hfbc hbc
            obtain ⟨hNd, hFd, hBr⟩ := ih s d r' hs hfd hd
            subst hG
            refine ⟨?_, ?_, ⟨hBl, hBr⟩⟩
            · simp only [evalN, hNbc, hNd]
            · simp only [evalFBy, hFbc, hFd]
    | .cell (.atom op) tail =>
        obtain ⟨-, hft⟩ := hf
        match op with
        | 0 =>
            simp only [evalGBy] at hG
            match tail with
            | .atom ax =>
                refine ⟨?_, ?_, slot_boundedBy q ax s hs hG⟩
                · simpa only [evalN] using hG
                · simpa only [evalFBy] using hG
            | .cell _ _ => simp at hG
        | 1 =>
            simp only [evalGBy] at hG
            obtain rfl := Option.some.inj hG
            exact ⟨by simp only [evalN], by simp only [evalFBy], hft⟩
        | 2 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  cases hc : evalGBy q fuel s c with
                  | none => rw [hb, hc] at hG; simp at hG
                  | some sc =>
                    rw [hb, hc] at hG
                    obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                    obtain ⟨hNc, hFc, hBc⟩ := ih s c sc hs hfc hc
                    obtain ⟨hN2, hF2, hBr⟩ := ih sb sc r hBb hBc hG
                    exact ⟨by simp only [evalN, hNb, hNc, hN2],
                           by simp only [evalFBy, hFb, hFc, hF2], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 3 =>
            simp only [evalGBy] at hG
            cases ht : evalGBy q fuel s tail with
            | none => rw [ht] at hG; simp at hG
            | some v =>
              rw [ht] at hG
              simp only [Option.map_some, Option.some.injEq] at hG
              obtain ⟨hN, hF, _⟩ := ih s tail v hs hft ht
              subst hG
              exact ⟨by simp only [evalN, hN, Option.map_some],
                     by simp only [evalFBy, hF, Option.map_some], wut_boundedBy hq v⟩
        | 4 =>
            simp only [evalGBy] at hG
            cases ht : evalGBy q fuel s tail with
            | none => rw [ht] at hG; simp at hG
            | some v =>
              rw [ht] at hG
              obtain ⟨hN, hF, hBv⟩ := ih s tail v hs hft ht
              -- `v` must be an atom `< q`; the guard forces `n + 1 < q`
              cases v with
              | cell _ _ => simp [lusGBy] at hG
              | atom n =>
                simp only [Option.bind_some, lusGBy] at hG
                split at hG
                · rename_i hlt
                  obtain rfl := Option.some.inj hG
                  refine ⟨?_, ?_, ?_⟩
                  · simp only [evalN, hN, Option.bind_some, Noun.lus]
                  · -- modular increment: `(n+1) mod q = n+1` since `n+1 < q`
                    simp only [evalFBy, hF, Option.bind_some, lusFBy, Nat.mod_eq_of_lt hlt]
                  · exact hlt
                · simp at hG
        | 5 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  cases hc : evalGBy q fuel s c with
                  | none => rw [hb, hc] at hG; simp at hG
                  | some sc =>
                    rw [hb, hc] at hG
                    simp only [Option.some.injEq] at hG
                    obtain ⟨hNb, hFb, _⟩ := ih s b sb hs hfb hb
                    obtain ⟨hNc, hFc, _⟩ := ih s c sc hs hfc hc
                    subst hG
                    exact ⟨by simp only [evalN, hNb, hNc],
                           by simp only [evalFBy, hFb, hFc], tis_boundedBy hq sb sc⟩
            | .atom _ => simp [evalGBy] at hG
        | 6 =>
            match tail with
            | .cell b (.cell c d) =>
                obtain ⟨hfb, hfc, hfd⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some vb =>
                  obtain ⟨hNb, hFb, _⟩ := ih s b vb hs hfb hb
                  rw [hb] at hG
                  match vb, hNb, hFb, hG with
                  | .atom 0, hNb, hFb, hG =>
                      obtain ⟨hNc, hFc, hBr⟩ := ih s c r hs hfc hG
                      exact ⟨by simp only [evalN, hNb, hNc],
                             by simp only [evalFBy, hFb, hFc], hBr⟩
                  | .atom 1, hNb, hFb, hG =>
                      obtain ⟨hNd, hFd, hBr⟩ := ih s d r hs hfd hG
                      exact ⟨by simp only [evalN, hNb, hNd],
                             by simp only [evalFBy, hFb, hFd], hBr⟩
                  | .atom (n+2), _, _, hG => simp at hG
                  | .cell _ _, _, _, hG => simp at hG
            | .cell b (.atom _) => simp [evalGBy] at hG
            | .atom _ => simp [evalGBy] at hG
        | 7 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  rw [hb] at hG
                  obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                  obtain ⟨hN7, hF7, hBr⟩ := ih sb c r hBb hfc hG
                  exact ⟨by simp only [evalN, hNb, hN7],
                         by simp only [evalFBy, hFb, hF7], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 8 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hb : evalGBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  rw [hb] at hG
                  obtain ⟨hNb, hFb, hBb⟩ := ih s b sb hs hfb hb
                  obtain ⟨hN8, hF8, hBr⟩ := ih (.cell sb s) c r ⟨hBb, hs⟩ hfc hG
                  exact ⟨by simp only [evalN, hNb, hN8],
                         by simp only [evalFBy, hFb, hF8], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | 9 =>
            match tail with
            | .cell (.atom ax) c =>
                obtain ⟨-, hfc⟩ := hft
                simp only [evalGBy] at hG
                cases hc : evalGBy q fuel s c with
                | none => rw [hc] at hG; simp at hG
                | some core =>
                  rw [hc] at hG
                  dsimp only at hG
                  obtain ⟨hNc, hFc, hBcore⟩ := ih s c core hs hfc hc
                  cases harm : slot ax core with
                  | none => rw [harm] at hG; simp at hG
                  | some arm =>
                    rw [harm] at hG
                    dsimp only at hG
                    have hBarm : BoundedBy q arm := slot_boundedBy q ax core hBcore harm
                    obtain ⟨hN9, hF9, hBr⟩ := ih core arm r hBcore hBarm hG
                    exact ⟨by simp only [evalN, hNc, harm, hN9],
                           by simp only [evalFBy, hFc, harm, hF9], hBr⟩
            | .cell (.cell _ _) _ => simp [evalGBy] at hG
            | .atom _ => simp [evalGBy] at hG
        | 10 =>
            match tail with
            | .cell (.cell (.atom ax) c) d =>
                obtain ⟨⟨-, hfc⟩, hfd⟩ := hft
                simp only [evalGBy] at hG
                cases hc : evalGBy q fuel s c with
                | none => rw [hc] at hG; simp at hG
                | some new =>
                  cases hd : evalGBy q fuel s d with
                  | none => rw [hc, hd] at hG; simp at hG
                  | some old =>
                    rw [hc, hd] at hG
                    obtain ⟨hNc, hFc, hBnew⟩ := ih s c new hs hfc hc
                    obtain ⟨hNd, hFd, hBold⟩ := ih s d old hs hfd hd
                    refine ⟨?_, ?_, edit_boundedBy q ax new old hBnew hBold hG⟩
                    · simp only [evalN, hNc, hNd]; exact hG
                    · simp only [evalFBy, hFc, hFd]; exact hG
            | .cell (.cell (.cell _ _) _) _ => simp [evalGBy] at hG
            | .cell (.atom _) _ => simp [evalGBy] at hG
            | .atom _ => simp [evalGBy] at hG
        | 11 =>
            match tail with
            | .cell (.cell hd clue) body =>
                obtain ⟨⟨-, hfclue⟩, hfbody⟩ := hft
                simp only [evalGBy] at hG
                cases hcl : evalGBy q fuel s clue with
                | none => rw [hcl] at hG; simp at hG
                | some vc =>
                  rw [hcl] at hG
                  obtain ⟨hNcl, hFcl, _⟩ := ih s clue vc hs hfclue hcl
                  obtain ⟨hNb, hFb, hBr⟩ := ih s body r hs hfbody hG
                  exact ⟨by simp only [evalN, hNcl, hNb],
                         by simp only [evalFBy, hFcl, hFb], hBr⟩
            | .cell (.atom hint) body =>
                obtain ⟨-, hfbody⟩ := hft
                simp only [evalGBy] at hG
                obtain ⟨hNb, hFb, hBr⟩ := ih s body r hs hfbody hG
                exact ⟨by simp only [evalN, hNb],
                       by simp only [evalFBy, hFb], hBr⟩
            | .atom _ => simp [evalGBy] at hG
        | (n+12) => simp [evalGBy] at hG

theorem agree :
    ∀ (fuel : Nat) (s f r : Noun), Bounded s → Bounded f →
      evalG fuel s f = some r →
        evalN fuel s f = some r ∧ evalF fuel s f = some r ∧ Bounded r :=
  agreeBy p one_lt_p

/-! ## The guarded evaluator refines `evalN`: the guard only removes behaviours -/

theorem evalGBy_le_evalN {q : ℕ} (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (h : evalGBy q fuel s f = some r) :
    evalN fuel s f = some r :=
  (agreeBy q hq fuel s f r hs hf h).1

theorem evalG_le_evalN {fuel : Nat} {s f r : Noun}
    (hs : Bounded s) (hf : Bounded f) (h : evalG fuel s f = some r) :
    evalN fuel s f = some r :=
  (agree fuel s f r hs hf h).1

/-! ## The no-overflow agreement theorem (B1) -/

/-- **Parameterized no-overflow agreement.**  For `q`-bounded inputs, a successful guarded run
contains no modular wrap at `q`, so the Nat and modulo-`q` evaluators return the same `q`-bounded
noun. -/
theorem noOverflow_agreeBy {q : ℕ} (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (hno : evalGBy q fuel s f = some r) :
    evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r :=
  agreeBy q hq fuel s f r hs hf hno

theorem noOverflow_agree {fuel : Nat} {s f r : Noun}
    (hs : Bounded s) (hf : Bounded f) (hno : evalG fuel s f = some r) :
    evalN fuel s f = some r ∧ evalF fuel s f = some r ∧ Bounded r :=
  agree fuel s f r hs hf hno

/-! ## The genuine `ZMod p` embedding (`Nat`-nouns ↪ `𝔽_p`-nouns)

`evalF` above models a field noun by its canonical representative `< p` (a `Noun`).  Here we
make the embedding into genuine Mathlib field elements explicit: a field noun is a `FNoun`
whose leaves are elements of `𝔽_p = ZMod p`, and `emb` sends a `Nat`-noun
to its field image `n ↦ (n : ZMod p)` structurally (the map the paper's `𝒟𝒯(𝔽)` uses).

The two facts that make the bounded fragment faithful:
* `natCast_inj_of_lt` / `emb_inj_on_bounded` — on field nouns (`Bounded`), `emb` is injective,
  so the structural Nock equality used by `evalF`'s OP_5 IS the field equality `=` of the paper: distinct atoms `< p` stay distinct in `𝔽_p`.
* `lusF_eq_zmod` — `evalF`'s OP_4 increment `(n+1) mod p` is exactly `((n : ZMod p) + 1).val`,
  the canonical value of the paper's field increment `+(n) = (1+n) mod p`.

The parameterized `ZMod q` helpers below take their modulus assumptions explicitly and do not use
`goldilocks_prime`. -/

instance : NeZero p := ⟨by norm_num [Field.p]⟩

/-- Field nouns: proper binary trees with leaves in `𝔽_p = ZMod p`. -/
inductive FNoun where
  | atom : ZMod p → FNoun
  | cell : FNoun → FNoun → FNoun
deriving DecidableEq

/-- The embedding of `Nat`-nouns into field nouns: `n ↦ (n : ZMod p)`, structural on cells
    (the paper's leaf map into `𝒟𝒯(𝔽)`, the paper). -/
def emb : Noun → FNoun
  | .atom n   => .atom (n : ZMod p)
  | .cell l r => .cell (emb l) (emb r)

/-- The `Nat` cast into `ZMod q` is injective on canonical representatives `[0,q)`.
    Primality is not needed for this representative-level fact. -/
theorem zmod_natCast_inj_of_lt {q m n : ℕ} [NeZero q] (hm : m < q) (hn : n < q)
    (h : (m : ZMod q) = (n : ZMod q)) : m = n := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] at this

/-- For every supplied prime `q` (including a varying prime `p_n`), the canonical cast
    `ℕ → ZMod q` is injective on `[0,q)`.  The prime is an explicit typeclass input; this theorem
    does not use `Field.goldilocks_prime`. -/
theorem zmod_prime_natCast_injOn_Iio (q : ℕ) [Fact (Nat.Prime q)] :
    Set.InjOn (fun k : ℕ => (k : ZMod q)) (Set.Iio q) := by
  intro m hm n hn h
  exact CharP.natCast_injOn_Iio (ZMod q) q hm hn h

theorem natCast_inj_of_lt {m n : ℕ} (hm : m < p) (hn : n < p)
    (h : (m : ZMod p) = (n : ZMod p)) : m = n :=
  zmod_natCast_inj_of_lt hm hn h

/-- **`emb` is injective on field nouns.**  Hence the structural Nock equality (`tis`, OP_5)
    used by `evalF` coincides with field equality on `Bounded` inputs: the
    no-overflow condition is exactly what rules out distinct atoms colliding in `𝔽_p`. -/
theorem emb_inj_on_bounded : ∀ {a b : Noun}, Bounded a → Bounded b → emb a = emb b → a = b := by
  intro a
  induction a with
  | atom m =>
      intro b hm hb h
      cases b with
      | atom n => simp only [emb, FNoun.atom.injEq] at h; rw [natCast_inj_of_lt hm hb h]
      | cell _ _ => simp [emb] at h
  | cell la ra ihl ihr =>
      intro b ha hb h
      cases b with
      | atom _ => simp [emb] at h
      | cell lb rb =>
          simp only [emb, FNoun.cell.injEq] at h
          obtain ⟨hl, hr⟩ := h
          rw [ihl ha.1 hb.1 hl, ihr ha.2 hb.2 hr]

/-- **Field increment ↔ `ZMod p`.**  The canonical representative produced by `evalF`'s OP_4
    (`(n+1) mod p`) is precisely `((n : ZMod p) + 1).val`, i.e. the value of the paper's field
    increment `+(n) = (1 + n) mod p`. -/
theorem lusF_eq_zmod (n : ℕ) : lusF (.atom n) = some (.atom (((n : ZMod p) + 1).val)) := by
  simp only [lusF, lusFBy, Option.some.injEq, Noun.atom.injEq]
  rw [← Nat.cast_one (R := ZMod p), ← Nat.cast_add, ZMod.val_natCast]

/-- The atom map underlying `emb`, recorded as a `ZMod p` element. -/
theorem emb_atom (n : ℕ) : emb (.atom n) = .atom (n : ZMod p) := rfl

/-! ## Non-vacuity of the no-overflow side condition

Ordinary Nock computations whose atoms stay below `p` satisfy the hypothesis of
`noOverflow_agree`; the three evaluators then return the same result.  (Field wraparound only
occurs for atoms reaching `2^64 − 2^32 + 1`, far beyond anything a `#eval` sanity check hits.) -/
section Witnesses
open Noun

-- `*[42 [4 0 1]] = 43`: increment stays `< p`, so the guarded run succeeds …
#eval evalG 100 (.atom 42) (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))          -- some 43
-- … and both the Nat reference and the field evaluator agree with it.
#eval evalN 100 (.atom 42) (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))          -- some 43
#eval evalF 100 (.atom 42) (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))          -- some 43
-- Equality (OP_5) on distinct small atoms: `=[1 2] = 1` in all three.
#eval evalG 100 (.cell (.atom 1) (.atom 2))
        (.cell (.atom 5) (.cell (.cell (.atom 0) (.atom 2)) (.cell (.atom 0) (.atom 3))))

/-- A concrete non-vacuity witness that `noOverflow_agree` is not vacuously satisfied: a
    field-noun program runs overflow-free (`evalG … = some …`) and there the Nat reference and
    the field evaluator provably coincide.  (We use OP_1 here so the guarded run reduces by
    `rfl` without unfolding the 64-bit prime; the `#eval`s above exercise the increment path.) -/
example :
    evalN 1 (.atom 0) (.cell (.atom 1) (.atom 5)) = some (.atom 5) ∧
    evalF 1 (.atom 0) (.cell (.atom 1) (.atom 5)) = some (.atom 5) := by
  have hs : Bounded (Noun.atom 0) := by norm_num [Bounded, Field.p]
  have hf : Bounded (Noun.cell (.atom 1) (.atom 5)) := by norm_num [Bounded, Field.p]
  have hG : evalG 1 (.atom 0) (.cell (.atom 1) (.atom 5)) = some (.atom 5) := rfl
  obtain ⟨hN, hF, _⟩ := noOverflow_agree hs hf hG
  exact ⟨hN, hF⟩

end Witnesses

end Nock.FieldEmbedding
