/-
  Nock/Reference.lean

  A standard, *executable* big-step reference semantics for Nock — plain Urbit Nock
  (opcodes 0..11), over `Nat` atoms.

  It is *fuel-indexed* (`evalN`) so that it is total and usable in proofs; `none` means
  "crashed or ran out of fuel".  Nock is Turing-complete, so no total fuel-free version
  exists.

  Paper opcodes are OP_0..OP_10 + `cons`.  Standard Nock adds 11
  (hints), which we include here for fidelity to the real language; the paper's VM omits
  10 (write) from `NockVMROM` and does not model 11.  Where a reduction rule below is the
  observable-equivalent of a longer macro-expansion (notably 6 and 9), that is noted.
-/

import Nock.Tree

namespace Nock
namespace Noun

/-- `?` : `atom 0` for a cell, `atom 1` for an atom. -/
def wut : Noun → Noun
  | .cell _ _ => .atom 0
  | .atom _   => .atom 1

/-- `+` : increment an atom; crash (`none`) on a cell. -/
def lus : Noun → Option Noun
  | .atom n   => some (.atom (n + 1))
  | .cell _ _ => none

/-- `=` : `atom 0` if equal, `atom 1` otherwise. -/
def tis (a b : Noun) : Noun :=
  if a = b then .atom 0 else .atom 1

/-- `/` (slot / tree address): `/[a n]`.
    `/[1 n] = n`, `/[2 n] = head`, `/[3 n] = tail`,
    `/[2k n] = /[2 /[k n]]`, `/[2k+1 n] = /[3 /[k n]]`.
    Total `def` (axis strictly decreases: `a/2 < a` for `a ≥ 2`); the well-founded
    packaging deferred by the design note is completed here so the recursion has usable
    equation lemmas (Sprint 4a).  The body is unchanged from the original `partial def`. -/
def slot : Nat → Noun → Option Noun
  | 0, _ => none
  | 1, n => some n
  | (a+2), n =>
    match slot ((a+2) / 2) n with
    | some (.cell l r) => some (if (a+2) % 2 == 0 then l else r)
    | _ => none
  termination_by a => a
  decreasing_by omega

/-- `#` (edit): `#[a new old]` replaces the subtree at axis `a` of `old` with `new`.
    `#[1 new _] = new`,
    `#[2k new old] = #[k [new /[2k+1 old]] old]`,
    `#[2k+1 new old] = #[k [/[2k old] new] old]`.
    Total `def` for the same reason as `slot` (Sprint 4a); body unchanged. -/
def edit : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | 1, new, _ => some new
  | (a+2), new, old =>
    let sibAxis := if (a+2) % 2 == 0 then (a+2) + 1 else (a+2) - 1
    match slot sibAxis old with
    | some sib =>
      let paired := if (a+2) % 2 == 0 then Noun.cell new sib else Noun.cell sib new
      edit ((a+2) / 2) paired old
    | none => none
  termination_by a => a
  decreasing_by omega

end Noun

open Noun

/-- `*[subject formula]`, fuel-indexed.  `evalN 0 _ _ = none`. -/
def evalN : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      -- autocons: the head of the formula is itself a formula ⇒ distribute (Nock's [b c] rule)
      match evalN fuel subj (.cell b c), evalN fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with               -- *[a 0 b] = /[b a]
           | .atom ax => slot ax subj
           | _ => none
    | 1 => some tail                      -- *[a 1 b] = b
    | 2 => match tail with               -- *[a 2 b c] = *[*[a b] *[a c]]
           | .cell b c =>
             match evalN fuel subj b, evalN fuel subj c with
             | some sb, some sc => evalN fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalN fuel subj tail).map wut               -- *[a 3 b] = ?*[a b]
    | 4 => (evalN fuel subj tail).bind lus              -- *[a 4 b] = +*[a b]
    | 5 => match tail with               -- *[a 5 b c] = =[*[a b] *[a c]]
           | .cell b c =>
             match evalN fuel subj b, evalN fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with               -- *[a 6 b c d]  (if b then c else d)
           | .cell b (.cell c d) =>
             match evalN fuel subj b with
             | some (.atom 0) => evalN fuel subj c
             | some (.atom 1) => evalN fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with               -- *[a 7 b c] = *[*[a b] c]
           | .cell b c =>
             match evalN fuel subj b with
             | some sb => evalN fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with               -- *[a 8 b c] = *[[*[a b] a] c]
           | .cell b c =>
             match evalN fuel subj b with
             | some sb => evalN fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with               -- *[a 9 b c] = *[*[a c] 2 [0 1] 0 b]
           | .cell (.atom ax) c =>       -- ≡ fetch arm at axis b of core *[a c], run core against it
             match evalN fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalN fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with              -- *[a 10 [b c] d] = #[b *[a c] *[a d]]
            | .cell (.cell (.atom ax) c) d =>
              match evalN fuel subj c, evalN fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | 11 => match tail with              -- *[a 11 [b c] d] (dynamic) / *[a 11 b c] (static) — hints
            | .cell (.cell _ clue) body =>
              match evalN fuel subj clue with
              | some _ => evalN fuel subj body
              | none => none
            | .cell (.atom _) body => evalN fuel subj body
            | _ => none
    | _ => none                          -- unknown opcode ⇒ crash

/-- Convenience wrapper with a large fuel budget, for `#eval` sanity checks. -/
def eval (subj formula : Noun) : Option Noun := evalN 100000 subj formula

section Sanity
open Noun

-- `*[[1 2] [0 1]] = [1 2]`  (slot 1 = identity)
#eval eval (.cell (.atom 1) (.atom 2)) (.cell (.atom 0) (.atom 1))
-- `*[42 [4 0 1]] = 43`  (increment)
#eval eval (.atom 42) (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))
-- `*[[1 2] [0 2]] = 1`  (head) and `*[[1 2] [0 3]] = 2`  (tail)
#eval eval (.cell (.atom 1) (.atom 2)) (.cell (.atom 0) (.atom 2))
#eval eval (.cell (.atom 1) (.atom 2)) (.cell (.atom 0) (.atom 3))
end Sanity

end Nock
