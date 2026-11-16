/-
  Nock/NockVMROM/Thm54/TraceGen/Op1Gen.lean

  The trace generator, run on the fresh ROM program
  `*[0 [1 5]] = 5` over `F = ZMod 97`, reproduces the already-verified `Op1Config.exec` compute row.

  Two things are proved, both `#print axioms`-clean:

  * `genTrace_op1_computeRows` — `genTrace 97 3 8 4 (n+1) (.atom 0) [1 5]` reduces to `.ok G`, and
    the row projection of the generated compute node tree is *exactly* the verified execution's
    compute tree `Op1Config.exec.computeTree`.  So the generator's DFS/exponent/render passes emit
    the hand-built OP1 vertical slice, through `encC` (`= enc`, `Encode.encC_eq`).

  * `gen_op1_evalFBy` — the capstone evaluator `evalFBy` agrees with the generated skeleton's
    semantic nouns: `evalFBy 97 1 G.subject G.formula = some G.result`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.TraceGen.Op1Config
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.Op1Config
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

/-- **The rendered `OP_1` row is the hand-built `Op1Config.computeRow`.**  `renderRows`, run on the
    `OP_1` skeleton at exponents `(lnPrev, ln, rec₀) = (0, 1, 1)`, reproduces the verified row: the
    `encC` fingerprint columns collapse to the `enc` columns (`Encode.encC_eq`), `ln_prev = α⁰ = 1`,
    `ln = α¹ = α`, and the single record's timestamp is `α¹ = α`. -/
theorem renderOp1Row_eq (z α : Op1Config.F) :
    renderOp1Row z α (stampOfAcc ComputeTable.State.s1 0)
        (genSkelOp1 subjectNoun formulaNoun resultNoun (Noun.atom 1))
      = computeRow z α := by
  simp only [renderOp1Row, genSkelOp1, stampOfAcc, formulaHead, formulaNoun,
    Nock.Framework.recordCount, computeRow, computeInputs, computePub, computeDec,
    requestRecord, fp, encC_eq, pow_zero, pow_one, Nat.zero_add]

/-- **PR-1 gate.**  The generator reproduces the verified OP1 compute row: for any positive fuel,
    `genTrace 97 3 8 4 (n+1) (.atom 0) [1 5]` succeeds, and the row projection of its committed
    compute node tree is exactly `Op1Config.exec.computeTree`. -/
theorem genTrace_op1_computeRows (n : ℕ) :
    ∃ G : GenTrace Op1Config.F Op1Config.F,
      genTrace 97 3 (seedZ) (alphaA) (n + 1) subjectNoun formulaNoun = .ok G ∧
        mapNTree GenComputeRow.row G.computeNodes = (exec seedZ alphaA).computeTree := by
  refine ⟨_, rfl, ?_⟩
  show mapNTree GenComputeRow.row
      (renderRows seedZ alphaA (bfsAssign
        (.node (skelNode (genSkelOp1 subjectNoun formulaNoun resultNoun (.atom 1)) [⟨formulaNoun, resultNoun, 3, 0⟩]) [])))
      = (exec seedZ alphaA).computeTree
  rw [bfsAssign_node_nil_eq_assignExponents]
  have hstate : (genSkelOp1 subjectNoun formulaNoun resultNoun (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, renderRows, renderNode, skelNode, hstate,
    List.map_nil, mapNTree, exec]
  rw [renderOp1Row_eq]

/-- The generator's committed evaluation noun for the OP1 program is exactly `result = 5`. -/
theorem gen_op1_result (n : ℕ) :
    (genTrace 97 3 (seedZ) (alphaA) (n + 1) subjectNoun formulaNoun).map GenTrace.result
      = .ok resultNoun := rfl

/-- **The generated skeleton is semantically faithful to `evalFBy`.**  The capstone evaluator
    agrees with the generator's committed nouns: `*[0 [1 5]] = 5`, and that `5` is
    precisely the noun the generator commits (`gen_op1_result`). -/
theorem gen_op1_evalFBy :
    FieldEmbedding.evalFBy 97 1 subjectNoun formulaNoun = some resultNoun := rfl

/-- Consequently, for any successfully generated `G`, `evalFBy` agrees with its committed nouns. -/
theorem gen_op1_evalFBy_of_ok (n : ℕ) (G : GenTrace Op1Config.F Op1Config.F)
    (h : genTrace 97 3 (seedZ) (alphaA) (n + 1) subjectNoun formulaNoun = .ok G) :
    FieldEmbedding.evalFBy 97 1 G.subject G.formula = some G.result := by
  rw [← Except.ok.inj h]
  exact gen_op1_evalFBy

end Nock.NockVMROM.Thm54.TraceGen
