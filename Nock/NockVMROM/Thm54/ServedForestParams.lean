import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.Op3Statement

/-!
## Why this is the whole per-opcode surface (verified against the proofs)

Every parent-touching obligation in the ~3300-line reassembly reads `parentFormulaS` / `parentHeadS`
through an **opcode-invariant channel**, never through the concrete leaf value:

* the **pole / size** channel — `pole memInputsS parentRecordS = (-1)^parentFormulaS.leaves`
  (`MultiRootServedFixture.pole_parentRecordS`), and `parentFormulaS.leaves = 3` for *any* head atom;
* the **`enc_cons`** homomorphism (`aDecomposeOuter_accepts`, gated only on `z ≠ 0`);
* the **`enc_atom`** fingerprint (`aHeadHalt_accepts`, generic in the atom);
* **boundedness** `BoundedBy 97 _` (generic once the head atom is `< 97`);
* **timestamp-based distinctness** (`encRec_ne_of_ts_ne` on `4/16/64`), so **no `enc` injectivity is
  needed anywhere**.

Consequently the per-opcode interface is exactly the bundle below: the head noun and its atom bound,
the cons-shape of the parent formula, and the gate-output bounds. `parentFormula_leaves` (proved from
the interface alone) witnesses the head-independence of the pole/size channel — it is `3` regardless
of the head atom, which is the load-bearing fact the scoping report relies on.

## Scope note

The remaining work is the mechanical port noted in `ServedForestModule`.
-/

namespace Nock.NockVMROM.Thm54.ServedForest

open Nock Nock.Noun
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.Op3Statement

noncomputable section

/-- The shared served child (`subjectS`, `resultS`, `formulaS`, `headS`, `tailS`) is fixed across
opcodes; only the parent head atom, the parent formula shape, and the gate output vary. The seed
hypotheses (`servedSeed ≠ 0`, `1 < orderOf servedSeed`) are global to the served fixture and are not
re-parameterized here. -/
structure ServedForestParams where
  /-- The parent opcode head (e.g. `.atom 4` for OP₄, `.atom 3` for OP₃). -/
  parentHead : Noun
  /-- Its atom literal. -/
  headAtom : ℕ
  /-- The head is that atom. -/
  hhead : parentHead = Noun.atom headAtom
  /-- The atom is in range (drives `enc_atom` boundedness). -/
  hheadlt : headAtom < 97
  /-- The parent formula. -/
  parentFormula : Noun
  /-- The parent formula is a cell over the shared served tail `formulaS` (drives `enc_cons`, the
  axis-3 service slot, and `parentFormulaS.leaves = 3`). -/
  hcons : parentFormula = Noun.cell parentHead formulaS
  /-- Boundedness of the head (interface hypothesis, `MultiRootServedFixture.bounded_parentHeadS`). -/
  hheadBounded : FieldEmbedding.BoundedBy 97 parentHead
  /-- Boundedness of the parent formula
  (`MultiRootServedFixture.bounded_parentFormulaS`). -/
  hformulaBounded : FieldEmbedding.BoundedBy 97 parentFormula
  /-- The produced result of the parent gate (`parentResultS` for OP₄, `op3ParentResultS` for OP₃). -/
  parentResult : Noun
  /-- Gate-output boundedness (`MultiRootServedFixture.bounded_parentResultS`). -/
  hresultBounded : FieldEmbedding.BoundedBy 97 parentResult
  /-- Gate-output leaf bound (the `SizeWindow`/census bound). -/
  hresultLeaves : parentResult.leaves ≤ 3

variable (P : ServedForestParams)

/-- **The pole/size channel is head-independent.** The parent formula has `3` leaves regardless of
the head atom, which is exactly why `pole_parentRecordS = (-1)^3 = -1` and the census timestamps are
opcode-invariant. Proved from the interface alone. -/
theorem parentFormula_leaves : P.parentFormula.leaves = 3 := by
  rw [P.hcons, P.hhead]
  simp [Noun.leaves, formulaS, headS, tailS]

end

/-! ## The OP₄ instantiation (regression baseline)

Every field is discharged from the existing `NonterminalServedRow` / `MultiRootServedFixture`
lemmas — no new proof obligation. -/

noncomputable def op4Params : ServedForestParams where
  parentHead := parentHeadS
  headAtom := 4
  hhead := rfl
  hheadlt := by norm_num
  parentFormula := parentFormulaS
  hcons := parentFormulaS_cons
  hheadBounded := bounded_parentHeadS
  hformulaBounded := bounded_parentFormulaS
  parentResult := parentResultS
  hresultBounded := bounded_parentResultS
  hresultLeaves := by simp [parentResultS, Noun.leaves]

/-! ## The OP₃ instantiation (the target opcode)

Discharged from the already-built `Op3Statement` compute seam; only the head atom literal and the
`wut` gate output differ from OP₄. -/

noncomputable def op3Params : ServedForestParams where
  parentHead := op3ParentHeadS
  headAtom := 3
  hhead := rfl
  hheadlt := by norm_num
  parentFormula := op3ParentFormulaS
  hcons := op3ParentFormulaS_cons
  hheadBounded := by simp [op3ParentHeadS]
  hformulaBounded := by
    simp [op3ParentFormulaS, op3ParentHeadS, formulaS, headS, tailS, FieldEmbedding.BoundedBy]
  parentResult := op3ParentResultS
  hresultBounded := by rw [op3ParentResultS_atom]; simp [FieldEmbedding.BoundedBy]
  hresultLeaves := by rw [op3ParentResultS_atom]; simp [Noun.leaves]

/-- Both opcodes agree on the head-independent pole/size channel: `3` leaves either way. -/
theorem op4Params_leaves : op4Params.parentFormula.leaves = 3 :=
  parentFormula_leaves op4Params

theorem op3Params_leaves : op3Params.parentFormula.leaves = 3 :=
  parentFormula_leaves op3Params

end Nock.NockVMROM.Thm54.ServedForest

#print axioms Nock.NockVMROM.Thm54.ServedForest.op4Params
#print axioms Nock.NockVMROM.Thm54.ServedForest.op3Params
#print axioms Nock.NockVMROM.Thm54.ServedForest.parentFormula_leaves
