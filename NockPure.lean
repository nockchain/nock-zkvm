/-
  NockPure.lean — root of the standalone, VM-independent "Pure Nock" deliverable.

  ────────────────────────────────────────────────────────────────────────────────────
  SCOPE.  This library packages the formalization of the Nock *language* (nouns, the
  paper's small-step verb/trace interpreter, and the executable big-step reference), and
  the AGREEMENT between them, as a self-contained artifact whose closure contains NO part
  of the §5 zkVM stack: no `NockVM`, `NockVMROM`, `Thm54`, `AIR`, `RAP`, `ComputeTable`,
  or `MemoryTable` module.  (The import closure of `NockPure` can be checked with
  `lake env lean --deps NockPure.lean`.)

  TWO TIERS OF ADEQUACY (see `Nock.PureAgreement`):

    Tier A (paper-faithful, OP₀..OP₁₀):  `runProgram`      ⟺  `evalPaper`
    Tier B (extension, ours, OP₀..OP₁₁): `runHintProgram`  ⟺  `evalN`

  Proven UNCONDITIONALLY (axioms ⊆ {propext, Classical.choice, Quot.sound}, `sorry`-free):
    • `Verb.runProgram_adequate_complete` — **TIER A ADEQUACY, `runProgram` ⟺ `evalPaper`, with
                                             NO hypotheses** (both directions proven)
    • `Verb.runHint_adequate_complete`    — **TIER B ADEQUACY, `runHintProgram` ⟺ `evalN`, with
                                             NO hypotheses** (both directions proven)
    • `Verb.paperSound_holds` / `Verb.paperComplete_holds` — Tier A soundness / completeness bridges
    • `Verb.runHintProgram_sound` / `Verb.hintComplete_holds` — Tier B soundness / completeness
    • `Verb.runProgram_sound`      — Tier A soundness (`runProgram` ⇒ `evalN`)
    • `evalPaper_le_evalN`         — the paper fragment refines the reference
    • `Verb.paper_hint_separation` — the exact OP₁₁ Tier A / Tier B boundary

  BOTH tiers are now CLOSED in both directions — there are NO remaining open ports.  Completeness
  is powered by a denotation-keyed cost measure (`Verb.vcost`/`pcost` for Tier A, `vcostN`/`ncost`
  for Tier B), sidestepping the "no verb-local measure" obstruction (which only rules out a
  *syntactic* measure: a `1`-redex or an OP₆/OP₁₁ macro can grow the verb, but not the remaining
  evaluation the cost counts).  Tier B is OUR extension; the paper deliberately stops at OP₁₀.
  ────────────────────────────────────────────────────────────────────────────────────
-/

-- The language: nouns, big-step reference, paper verb/trace interpreter, opcode set.
import Nock.Tree
import Nock.Reference
import Nock.Verb
import Nock.Trace
import Nock.Semantics

-- The paper-faithful oracle (OP₀..OP₁₀) and the agreement layer.
import Nock.PaperReference
import Nock.Agreement
import Nock.PureAgreement
import Nock.PureComplete
import Nock.PureCompleteHint

-- VM-independent supporting theory (Dyck words, noun validation).
import Nock.Dyck
import Nock.NounValidation

import NockPure.PurePaperNames
import NockPure.RedTeam
