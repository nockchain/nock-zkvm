/-
  Nock/RedTeam/Batch19Thm54ReleaseContract.lean

  These receipts do not assert any S1--S8 acceptance theorem.  They lock four facts the strict
  program depends on:

  1. **Modular OP4, not unbounded increment.**  The strict paper evaluator `evalPaperMod q` wraps the
     top atom `q-1` to `0`, exactly `+(n) = (1+n) mod q`, and therefore differs
     from the unbounded `evalPaper` at the top atom.
  2. **Fragment refinement.**  `evalPaperMod q` refines the full modular evaluator `evalFBy q`
     (re-exported), and crashes on OP11, matching the paper's `op < 11` domain.
  3. **Atom range is the characteristic.**  A canonical field noun forbids the atom `= q`; the range
     is `[0,q)`, never an independently selectable public bound.
  4. **Contract teeth.**  The strict release contract rejects a tampered IO list that is not the one
     derived from the shared execution, and is satisfied by every genuine threaded object.

  It also records the one-hot-size accounting: the mechanized one-hot uses 11 selectors
  (`s0..s9` + `cons`), while the paper's headline `opcode_onehot_size = 10` counts the ten ROM
  opcodes; `cons` is the structural, non-opcode selector.
-/

import Nock.PaperReferenceMod
import Nock.NockVMROM.Thm54.StrictReleaseContract
import Nock.NockVM

namespace Nock.RedTeam.Batch19

open Nock Nock.Noun
open Nock.NockVMROM.Thm54

/-! ## 1. Modular OP4 wraps at the top atom -/

/-- The strict modular evaluator wraps: `*[0 [4 [1 2]]] = (2+1) mod 3 = 0`. -/
theorem b19_evalPaperMod_wraps_at_top :
    evalPaperMod 3 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2))) = some (.atom 0) := by
  decide

/-- The unbounded paper-fragment evaluator does not wrap: `*[0 [4 [1 2]]] = 2+1 = 3`. -/
theorem b19_evalPaper_no_wrap_at_top :
    evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2))) = some (.atom 3) := by
  decide

/-- **Modular OP4 differs from the unbounded increment at the top atom.** -/
theorem b19_evalPaperMod_ne_evalPaper_at_top :
    evalPaperMod 3 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2)))
      ≠ evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 2))) := by
  rw [b19_evalPaperMod_wraps_at_top, b19_evalPaper_no_wrap_at_top]
  decide

/-! ## 2. Fragment refinement and OP11 exclusion -/

/-- **`evalPaperMod q` refines `evalFBy q`** (re-export of the module theorem). -/
theorem b19_evalPaperMod_le_evalFBy {q n : ℕ} {s form r : Noun}
    (h : evalPaperMod q n s form = some r) :
    FieldEmbedding.evalFBy q n s form = some r :=
  evalPaperMod_le_evalFBy h

/-- **`evalPaperMod` crashes on an OP11 head** (paper fragment `op < 11`). -/
theorem b19_evalPaperMod_crashes_on_op11 (q : ℕ) (subj : Noun) :
    evalPaperMod q 3 subj
        (.cell (.atom 11) (.cell (.atom 99) (.cell (.atom 1) (.atom 5)))) = none := by
  rfl

/-- **The full modular evaluator does not crash on that same OP11 term.**  So the fragment boundary
is real: `evalFBy` follows the hint into `[1 5]` and returns `some (atom 5)`. -/
theorem b19_evalFBy_succeeds_on_op11 (q : ℕ) (subj : Noun) :
    FieldEmbedding.evalFBy q 3 subj
        (.cell (.atom 11) (.cell (.atom 99) (.cell (.atom 1) (.atom 5)))) = some (.atom 5) := by
  rfl

/-! ## 3. The atom range is the characteristic -/

/-- **The top residue `q` is not a canonical field noun.**  Atoms range over `[0,q)`, so `q` is
excluded; there is no independent public bound admitting it. -/
theorem b19_canonical_excludes_char (q : ℕ) : ¬ CanonicalFieldNoun q (.atom q) := by
  simp [CanonicalFieldNoun]

/-- **The residue just below `q` is canonical** (non-vacuity of `CanonicalFieldNoun`). -/
theorem b19_canonical_admits_below_char (q : ℕ) (hq : 0 < q) :
    CanonicalFieldNoun q (.atom (q - 1)) := by
  simp only [canonicalFieldNoun_atom]
  omega

/-! ## 4. Contract teeth -/

/-- **Genuine threaded objects satisfy the release contract** (re-export). -/
theorem b19_contract_satisfied {F K : Type} [Field F] [Field K] [Algebra F K]
    (P : StrictThreadedObjects F K) :
    StrictReleaseContract P.cfg P.exec P.reqRecs P.respRecs :=
  strictThreadedObjects_satisfy_contract P

/-- **The contract rejects a tampered request list** (re-export). -/
theorem b19_contract_rejects_tampered_reqRecs
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (respRecs : List (Fin 9 → K)) (hne : exec.derivedRequestIO ≠ []) :
    ¬ StrictReleaseContract cfg exec [] respRecs :=
  strictReleaseContract_rejects_tampered_reqRecs cfg exec respRecs hne

/-! ## One-hot size accounting -/

/-- **One-hot accounting.**  The paper's headline one-hot size is `10` (the ROM opcodes
`OP0..OP9`), while the mechanized selector family `sfin : Fin 11` has one extra selector, `cons`,
which is structural rather than an eleventh opcode.  `Fintype.card State = 11 = 10 + 1`. -/
theorem b19_onehot_accounting :
    Nock.NockVM.opcode_onehot_size = 10
      ∧ Fintype.card Nock.ComputeTable.State = Nock.NockVM.opcode_onehot_size + 1 := by
  refine ⟨rfl, ?_⟩
  decide

end Nock.RedTeam.Batch19

#print axioms Nock.RedTeam.Batch19.b19_evalPaperMod_ne_evalPaper_at_top
#print axioms Nock.RedTeam.Batch19.b19_evalPaperMod_le_evalFBy
#print axioms Nock.RedTeam.Batch19.b19_evalPaperMod_crashes_on_op11
#print axioms Nock.RedTeam.Batch19.b19_canonical_excludes_char
#print axioms Nock.RedTeam.Batch19.b19_contract_rejects_tampered_reqRecs
#print axioms Nock.RedTeam.Batch19.b19_onehot_accounting
