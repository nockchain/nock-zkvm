/-
  Nock/PaperReference.lean

  The **paper-faithful** big-step reference evaluator `evalPaper`: exactly the paper's
  opcode set OP₀..OP₁₀ + `cons`, evaluated over `Nat` atoms.  It is
  `evalN` (Nock/Reference.lean) with the OP₁₁ (hints) clause REMOVED — an OP₁₁ head is an
  unknown opcode and therefore crashes (`none`), matching the paper's computable domain
  `opHeadOk` (`op < 11`, Nock/Verb.lean:205) and the small-step paper machine `runProgram`.

  ── WHY A SEPARATE ORACLE ──────────────────────────────────────────────────────────────
  `evalN` implements OP₁₁ for fidelity to real Urbit Nock, but the paper's small-step verb
  machine (`runProgram`) treats an OP₁₁ head as out-of-domain and crashes.  Pairing the
  machine with `evalN` therefore makes the completeness direction FALSE on OP₁₁ (evalN
  succeeds, the machine crashes).  `evalPaper` is the matching oracle: it crashes on OP₁₁
  exactly where `runProgram` does, so the two are bidirectionally adequate on the whole
  OP₀..OP₁₀ fragment with NO side hypothesis.  (The OP₁₁ extension lives in
  Nock/PureAgreement.lean, paired with the extended machine `runHint`.)

  `evalPaper` refines `evalN`: `evalPaper_le_evalN` shows every `evalPaper` success is an
  `evalN` success with the same value (they differ only where `evalN` would fire OP₁₁).
-/

import Nock.Reference

namespace Nock

open Noun

/-- `*[subject formula]`, fuel-indexed, **paper fragment only** (OP₀..OP₁₀ + `cons`).
    Identical to `evalN` except an OP₁₁ head (`op = 11`) is an unknown opcode and crashes,
    matching the paper's `opHeadOk` (`op < 11`) and the small-step machine `runProgram`. -/
def evalPaper : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalPaper fuel subj (.cell b c), evalPaper fuel subj d with
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
             match evalPaper fuel subj b, evalPaper fuel subj c with
             | some sb, some sc => evalPaper fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalPaper fuel subj tail).map wut
    | 4 => (evalPaper fuel subj tail).bind lus
    | 5 => match tail with
           | .cell b c =>
             match evalPaper fuel subj b, evalPaper fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalPaper fuel subj b with
             | some (.atom 0) => evalPaper fuel subj c
             | some (.atom 1) => evalPaper fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalPaper fuel subj b with
             | some sb => evalPaper fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalPaper fuel subj b with
             | some sb => evalPaper fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalPaper fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalPaper fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalPaper fuel subj c, evalPaper fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | _ => none                          -- op ≥ 11 (incl. OP₁₁ hints) ⇒ crash (paper fragment)

/-- Convenience wrapper with a large fuel budget, for `#eval` sanity checks. -/
def evalPaperTop (subj formula : Noun) : Option Noun := evalPaper 100000 subj formula

/-- **Fuel monotonicity (single step)** for `evalPaper` (same shape as `evalN_succ`). -/
theorem evalPaper_succ {n : Nat} {s form r : Noun}
    (h : evalPaper n s form = some r) : evalPaper (n + 1) s form = some r := by
  induction n, s, form using evalPaper.induct generalizing r with
  | case11 fuel subj tail ih =>
      simp only [evalPaper, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subj tail ih =>
      simp only [evalPaper, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ =>
      simp_all [evalPaper]

/-- **Fuel monotonicity** for `evalPaper`. -/
theorem evalPaper_mono {n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalPaper n s form = some r) : evalPaper m s form = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalPaper_succ ih

/-- **`evalPaper` refines `evalN`.**  Every paper-fragment evaluation is a standard Nock
    evaluation with the same result: `evalPaper` and `evalN` differ only where `evalN`
    fires OP₁₁ (which `evalPaper` crashes on).  Proof: functional induction; every clause
    is identical except OP₁₁, where `evalPaper` returns `none` so the hypothesis is absurd. -/
theorem evalPaper_le_evalN {n : Nat} {s form r : Noun}
    (h : evalPaper n s form = some r) : evalN n s form = some r := by
  induction n, s, form using evalPaper.induct generalizing r <;>
    simp_all only [evalPaper, evalN, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] <;>
    grind

end Nock
