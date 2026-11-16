/-
  Nock/NockVMROM/Thm54/TraceGen/ConsGen.lean

  The trace generator, run on the fresh ROM program
  `*[0 [[1 5] [1 6]]] = [5 6]` over `F = ZMod 97`, reproduces the already-verified
  `ConsConfig.exec` three-row compute tree — the `.cons` autocons root over its two `OP_1` children.

  This is the branching analogue of `Op1Gen`: the generator's DFS emission now recurses on the two
  autocons branches, the exponent pass threads its record-count accumulator ACROSS the two siblings
  (so the left child is stamped at line `1` and the right at line `2`, the paper's BFS order), and the
  render pass fills the `.cons` row's six subformula columns and its single live record.  Two things
  are proved, both `#print axioms`-clean:

  * `renderConsRow_eq` / `renderOp1LRow_eq` / `renderOp1RRow_eq` — each rendered row collapses (via
    `Encode.encC_eq`) to the verified `ConsConfig` row at its assigned exponents.

  * `genTrace_cons_computeRows` — `genTrace 97 4 8 4 (n+2) (.atom 0) [[1 5] [1 6]]` succeeds and the
    row projection of its committed compute node tree is exactly `ConsConfig.exec.computeTree`.

  * `gen_cons_evalFBy` — the capstone evaluator agrees with the generated nouns:
    `*[0 [[1 5] [1 6]]] = [5 6]`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.TraceGen.ConsConfig
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.ConsConfig
open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

/-! ## The rendered rows are the hand-built `ConsConfig` rows -/

/-- The rendered `.cons` root is the verified `ConsConfig.consRow`.  At exponents
    `(lnPrev, ln, rec₀) = (0, 1, 1)` the fingerprint columns collapse to `enc`, `ln_prev = α⁰ = 1`,
    `ln = α¹ = α`, and the single record's timestamp is `α¹ = α`. -/
theorem renderConsRow_eq :
    renderConsRow seedZ alphaA
        { state := .cons, lnPrevExponent := 0, lnExponent := 1, recordExponent := fun _ => 1 }
        (genSkelCons subjectNoun leftFormula rightFormula leftResult rightResult)
      = ConsConfig.consRow := by
  simp only [renderConsRow, genSkelCons, formulaHead, formulaTail, ConsConfig.consRow, compInputs,
    consPub, consDec, ConsConfig.recCons, formulaNoun, resultNoun, enc, encC_eq, pow_zero, pow_one]

/-- The rendered left `OP_1` child is the verified `ConsConfig.op1LRow` at exponents `(1, 2, 2)`. -/
theorem renderOp1LRow_eq :
    renderOp1Row seedZ alphaA
        { state := .s1, lnPrevExponent := 1, lnExponent := 2, recordExponent := fun _ => 2 }
        (genSkelOp1 subjectNoun leftFormula leftResult (.atom 1))
      = ConsConfig.op1LRow := by
  simp only [renderOp1Row, genSkelOp1, formulaHead, leftFormula, op1Head, ConsConfig.op1LRow,
    compInputs, op1LPub, op1PubOf, op1DecOf, ConsConfig.recL, enc, encC_eq, pow_one, pow_two]

/-- The rendered right `OP_1` child is the verified `ConsConfig.op1RRow` at exponents `(2, 3, 3)`. -/
theorem renderOp1RRow_eq :
    renderOp1Row seedZ alphaA
        { state := .s1, lnPrevExponent := 2, lnExponent := 3, recordExponent := fun _ => 3 }
        (genSkelOp1 subjectNoun rightFormula rightResult (.atom 1))
      = ConsConfig.op1RRow := by
  simp only [renderOp1Row, genSkelOp1, formulaHead, rightFormula, op1Head, ConsConfig.op1RRow,
    compInputs, op1RPub, op1PubOf, op1DecOf, ConsConfig.recR, enc, encC_eq, pow_succ, pow_two,
    pow_one]

/-! ## The generator reproduces the branching compute tree -/

/-- **PR-3 gate.**  The generator reproduces the verified branching compute tree: for any fuel `n+2`,
    `genTrace 97 4 8 4 (n+2) (.atom 0) [[1 5] [1 6]]` succeeds, and the row projection of its
    committed compute node tree is exactly `ConsConfig.exec.computeTree` — the `.cons` root over the
    two `OP_1` children, stamped in the paper's BFS line order. -/
theorem genTrace_cons_computeRows (n : ℕ) :
    ∃ G : GenTrace ConsConfig.F ConsConfig.F,
      genTrace 97 4 seedZ alphaA (n + 2) subjectNoun formulaNoun = .ok G ∧
        mapNTree GenComputeRow.row G.computeNodes = exec.computeTree := by
  refine ⟨_, rfl, ?_⟩
  show mapNTree GenComputeRow.row
      (renderRows seedZ alphaA (bfsAssign
        (.node (skelNode (genSkelCons subjectNoun leftFormula rightFormula leftResult rightResult)
            [⟨formulaNoun, rightFormula, 3, 0⟩])
          [.node (skelNode (genSkelOp1 subjectNoun leftFormula leftResult (.atom 1))
              [⟨leftFormula, leftResult, 3, 0⟩]) [],
           .node (skelNode (genSkelOp1 subjectNoun rightFormula rightResult (.atom 1))
              [⟨rightFormula, rightResult, 3, 0⟩]) []])))
      = exec.computeTree
  rw [bfsAssign_eq_assignExponents_two_leaves]
  have hcons : (genSkelCons subjectNoun leftFormula rightFormula leftResult rightResult).state
      = ComputeTable.State.cons := rfl
  have hop1 : (genSkelOp1 subjectNoun leftFormula leftResult (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hop1' : (genSkelOp1 subjectNoun rightFormula rightResult (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, stampOfAcc, renderRows,
    renderNode, skelNode, hcons, hop1, hop1', Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, List.sum_cons, mapNTree, ConsConfig.exec, ConsConfig.computeTree,
    Nat.zero_add, Nat.add_zero]
  rw [renderConsRow_eq, renderOp1LRow_eq, renderOp1RRow_eq]

/-- The generator's committed evaluation noun for the cons program is exactly `[5 6]`. -/
theorem gen_cons_result (n : ℕ) :
    (genTrace 97 4 seedZ alphaA (n + 2) subjectNoun formulaNoun).map GenTrace.result
      = .ok resultNoun := rfl

/-- **The generated skeleton is semantically faithful to `evalFBy`.**  The capstone evaluator agrees
    with the generator's committed nouns: `*[0 [[1 5] [1 6]]] = [5 6]`. -/
theorem gen_cons_evalFBy :
    FieldEmbedding.evalFBy 97 2 subjectNoun formulaNoun = some resultNoun := rfl

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genTrace_cons_computeRows
