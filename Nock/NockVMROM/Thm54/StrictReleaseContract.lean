/-
  Nock/NockVMROM/Thm54/StrictReleaseContract.lean

  Packet 0 of the Theorem 5.4 north star: the strict release contract.

  This module pins the release-grade *object threading* discipline for the eventual paper theorem
  without asserting any S1--S8 acceptance result.

  * **Same-object threading.** `StrictThreadedObjects` carries exactly one `ExactExecution`, and the
    encoded request/response IO lists are *equal to the ones derived from that single execution*
    (`req_eq_derived` / `resp_eq_derived`).  The compute chip, memory forest, and IO record set can
    therefore never silently diverge.

  * **No self-manufactured witnesses.** The fields are data (`cfg`, `exec`, `reqRecs`, `respRecs`)
    plus two *equations*.  There is no proof field that fabricates a witness; the threading facts are
    definitional consequences of the shared execution.

  `StrictReleaseContract` is a predicate over the *loose* components (config, execution, and two IO
  lists supplied independently).  This is what gives the contract teeth: a tampered IO list that is
  not the derived one is rejected (`strictReleaseContract_rejects_tampered_reqRecs`), while genuine
  threaded objects always satisfy it (`strictThreadedObjects_satisfy_contract`).

  The strict *language* fixes the paper's modular field-noun semantics; see `Nock/PaperReferenceMod`.
  `CanonicalFieldNoun p` records that every atom leaf is a canonical residue `< p`, so the atom range
  is the field characteristic, never an independently selectable public bound.
-/

import Nock.NockVMROM.Thm54.Language
import Nock.PaperReferenceMod

namespace Nock.NockVMROM.Thm54

open scoped Classical

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Canonical field nouns -/

/-- A noun is a **canonical field noun modulo `p`** when every atom leaf is a canonical residue
`< p`.  The atom range is the field characteristic; there is no independent public `q`. -/
def CanonicalFieldNoun (p : ℕ) (n : Noun) : Prop :=
  FieldEmbedding.BoundedBy p n

@[simp] theorem canonicalFieldNoun_atom {p n : ℕ} :
    CanonicalFieldNoun p (.atom n) ↔ n < p := Iff.rfl

@[simp] theorem canonicalFieldNoun_cell {p : ℕ} {l r : Noun} :
    CanonicalFieldNoun p (.cell l r) ↔ CanonicalFieldNoun p l ∧ CanonicalFieldNoun p r := Iff.rfl

/-! ## Threaded objects -/

/-- The single-execution object bundle threaded through every strict clause.

The two `*_eq_derived` fields are the compiled statement of same-object IO threading: the encoded
request/response lists are *the ones produced by this execution*, so no clause can quietly use a
different IO record set. -/
structure StrictThreadedObjects (F K : Type) [Field F] [Field K] [Algebra F K] where
  /-- The shared exact configuration. -/
  cfg : ExactConfig F K
  /-- The single authoritative execution feeding compute, memory, and IO. -/
  exec : ExactExecution cfg
  /-- The encoded compute request IO. -/
  reqRecs : List (Fin 9 → K)
  /-- The encoded memory response IO. -/
  respRecs : List (Fin 9 → K)
  /-- Requests are exactly those derived from the shared execution. -/
  req_eq_derived : reqRecs = exec.derivedRequestIO
  /-- Responses are exactly those derived from the shared execution. -/
  resp_eq_derived : respRecs = exec.derivedResponseIO

/-! ## The release contract as a loose predicate -/

/-- The strict release contract over independently supplied components.

Stating it over loose `reqRecs`/`respRecs` (rather than only over a `StrictThreadedObjects`) is what
gives it teeth: an IO list that is not the derived one violates the last two conjuncts. -/
def StrictReleaseContract (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (reqRecs respRecs : List (Fin 9 → K)) : Prop :=
  0 < cfg.compRows ∧ 0 < cfg.memRows ∧ exec.memoryForest ≠ [] ∧
    reqRecs = exec.derivedRequestIO ∧ respRecs = exec.derivedResponseIO

/-- **Genuine threaded objects satisfy the contract.**  Non-vacuity: the contract is inhabited by
every well-formed `StrictThreadedObjects`, using only structural positivity, forest-nonemptiness,
and the two threading equations. -/
theorem strictThreadedObjects_satisfy_contract (P : StrictThreadedObjects F K) :
    StrictReleaseContract P.cfg P.exec P.reqRecs P.respRecs :=
  ⟨P.cfg.compRows_pos, P.cfg.memRows_pos, P.exec.memoryForest_nonempty,
    P.req_eq_derived, P.resp_eq_derived⟩

/-- **The contract rejects a tampered request list.**  Whenever the derived request IO is nonempty,
supplying the empty list as `reqRecs` (a threading forgery) fails the contract.  This shows the
last two conjuncts are not vacuous filler. -/
theorem strictReleaseContract_rejects_tampered_reqRecs
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (respRecs : List (Fin 9 → K))
    (hne : exec.derivedRequestIO ≠ []) :
    ¬ StrictReleaseContract cfg exec [] respRecs := by
  rintro ⟨_, _, _, hreq, _⟩
  exact hne hreq.symm

/-- **The contract rejects a tampered response list.** -/
theorem strictReleaseContract_rejects_tampered_respRecs
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (reqRecs : List (Fin 9 → K))
    (hne : exec.derivedResponseIO ≠ []) :
    ¬ StrictReleaseContract cfg exec reqRecs [] := by
  rintro ⟨_, _, _, _, hresp⟩
  exact hne hresp.symm

/-- **The contract forces both IO lists to agree with the shared execution.**  Extracted threading
equalities, for downstream clauses that must reuse the same records. -/
theorem StrictReleaseContract.io_threaded
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {reqRecs respRecs : List (Fin 9 → K)}
    (h : StrictReleaseContract cfg exec reqRecs respRecs) :
    reqRecs = exec.derivedRequestIO ∧ respRecs = exec.derivedResponseIO :=
  ⟨h.2.2.2.1, h.2.2.2.2⟩

end

end Nock.NockVMROM.Thm54
