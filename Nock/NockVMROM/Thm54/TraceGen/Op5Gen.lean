/-
  Nock/NockVMROM/Thm54/TraceGen/Op5Gen.lean

  Phase 3, the OP5 (equality `=`) vertical slice — LAYER 1 (generator side only).  The trace
  generator's compute-side emission for the equality program

      `*[0 [5 [1 3] [1 4]]] = 1`

  where `b = [1 3]`, `c = [1 4]`, so the two operands are `sf1 = *[0 [1 3]] = 3` and
  `sf2 = *[0 [1 4]] = 4`, and the row result is the equality gate `result = =[sf1 sf2] =
  Noun.tis 3 4 = 1` — the two operands are DISTINCT, so `tis` returns atom `1`.

  OP5 is the equality row: state `.s5`, fan-out `2` (`fanoutComp.s5 = 2`), TWO live memory records
  (`recordCount.s5 = 2`) — the formula-open `[5 [b c]] @3` record and the `formula_tail@2` record
  `[b c] @2` (same record shape as OP2/OP7).  The two subformula slots are the operands `*[a b]`
  (slot `0`, result `sf1`) and `*[a c]` (slot `1`, result `sf2`), BOTH evaluated against the SAME
  row subject `a` (unlike OP7's threaded second subject), per `evalN` (`evalN subj b`/`evalN subj
  c`).  The tail decomposition is active (`decActive.s5.f_th = decActive.s5.f_tt = true`,
  `SemanticStrategy.lean:47`), so `f_th ↦ b`, `f_tt ↦ c`.  The distinctive OP5 datum is the
  `equalityOperand` comparison gate `result = Noun.tis sf1 sf2` (`SemanticTrace.lean:141`), which
  DISCRIMINATES: atom `0` when the two operands are equal, atom `1` when distinct.
  Because `requiredServedLookups.s5 = 0` the served side is vacuous and the memory forest stays
  single-root (`kMem = 1`), like OP1/OP2/OP7.

  What lands here (all additive, kernel-clean, generic over any `[Field K]`):

  * `genComputeSkeleton_op5` — the generator's new `OP_5` DFS arm classifies `[5 [b c]]` on the row
    subject `a`, recurses on `b` and `c` BOTH against `a` for the two operands `sf1 = *[a b]`,
    `sf2 = *[a c]`, produces the equality gate `Noun.tis sf1 sf2`, and emits the `.s5` root over its
    two `OP_1` children with the two records.
  * `gen_op5ComputeNodes_eq` — the full DFS → exponent → render pipeline collapses to the
    locally-defined carrier `computeNodesOp5` (root rendered by the new `.s5` `renderNode` dispatch
    and `stampOfAcc` branch; the two children by `renderOp1Row`).
  * `gen_op5Trace_is_generated` — running the generator end-to-end yields exactly `computeNodesOp5`.
  * Non-vacuity: the 2-call fan-out, the active tail decomposition, the two records, the two
    operands sharing the row subject `a`, and — the point of OP5 — the equality gate genuinely
    DISCRIMINATES (an equal-operands fixture producing `0`, the distinct-operands fixture producing
    `1`), all inhabited by concrete terms and confirmed against `evalN`.

  DEFERRED, and why (reported precisely, not faked):

  * The **served-memory forest** `genOp5MemForest` is NOT built here.  A *meaningful* generated
    forest equality (the pattern of `Op1GenData.gen_memForest_eq` / `ConsGenMem.gen_consMemForest_eq`)
    is stated against an independently *committed* served-memory fixture whose cells and LogUp
    accumulator are *validated* by the honest commitment's `BindMemoryRow` / `MemoryNodesOK` proofs.
    There is no committed OP5 served-memory fixture: it is exactly the `.s5` served
    `ExactServedMemoryTrace` that is the deferred heavy CORE.  `Op2Gen.lean`/`Op7Gen.lean` deferred
    their forests for the same reason.  The OP5 served side is `requiredServedLookups.s5 = 0`
    (VACUOUS) and single-root (`kMem = 1`), so this forest is a reconstruction of the committed
    records, deferred to Layer 2.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

/-! ## A. The OP5 fixture nouns (`*[0 [5 [1 3] [1 4]]] = 1`) -/

/-- The row subject `a = 0`. -/
def op5Subject : Noun := .atom 0
/-- The first operand formula `b = [1 3]` (an `OP_1` constant): `*[a b] = 3`. -/
def op5ChildFormulaB : Noun := .cell (.atom 1) (.atom 3)
/-- The first operand evaluation `sf1 = *[0 [1 3]] = 3`. -/
def op5Sf1 : Noun := .atom 3
/-- The second operand formula `c = [1 4]` (an `OP_1` constant): `*[a c] = 4`. -/
def op5ChildFormulaC : Noun := .cell (.atom 1) (.atom 4)
/-- The second operand evaluation `sf2 = *[0 [1 4]] = 4`. -/
def op5Sf2 : Noun := .atom 4
/-- The formula tail `[b c]`. -/
def op5ParentTail : Noun := .cell op5ChildFormulaB op5ChildFormulaC
/-- The OP5 formula `[5 [b c]]`. -/
def op5ParentFormula : Noun := .cell (.atom 5) op5ParentTail
/-- The produced result `=[sf1 sf2] = Noun.tis 3 4 = 1`. -/
def op5Result : Noun := Noun.tis op5Sf1 op5Sf2

/-- The equality gate on the fixture's distinct operands really is atom `1`. -/
theorem op5Result_is_one : op5Result = Noun.atom 1 := rfl

/-- An equal-operands OP5 formula `[5 [1 3] [1 3]]`, used to witness that the equality gate
    DISCRIMINATES: `*[0 [5 [1 3] [1 3]]] = =[3 3] = 0`. -/
def op5FormulaEqual : Noun := .cell (.atom 5) (.cell op5ChildFormulaB op5ChildFormulaB)

/-! ## B. The generator's `OP_5` DFS arm fires on the equality formula `[5 [b c]]` -/

/-- **The `OP_5` DFS arm of `genComputeSkeleton` classifies the equality `[5 [b c]]`** on the row
    subject `a`: it recurses on `b` and `c` BOTH against `a` (the two operands `*[a b] → sf1`,
    `*[a c] → sf2`), produces the equality gate `Noun.tis sf1 sf2`, and emits the `.s5` root over
    the two `OP_1` children with the two committed records (formula-open `[5 [b c]] @3`,
    formula-tail `[b c] @2`).  Mirrors `genComputeSkeleton_op7` at
    fan-out 2 but with BOTH children's subjects the row subject `a` (not threaded) and the row
    result the equality gate (per `evalN`, `Reference.lean:99-104`). -/
theorem genComputeSkeleton_op5 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) op5Subject op5ParentFormula
      = .ok (.node (skelNode
            (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail op5ChildFormulaB
              op5ChildFormulaC op5Sf1 op5Sf2 op5Result)
            [⟨op5ParentFormula, op5ParentTail, 3, 0⟩, ⟨op5ParentTail, op5ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op5Subject op5ChildFormulaB op5Sf1 (.atom 1))
                [⟨op5ChildFormulaB, op5Sf1, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op5Subject op5ChildFormulaC op5Sf2 (.atom 1))
                [⟨op5ChildFormulaC, op5Sf2, 3, 0⟩]) []],
          op5Result) := by
  show genComputeSkeleton ((n + 1) + 1) op5Subject op5ParentFormula = _
  simp only [genComputeSkeleton, op5ParentFormula, op5ParentTail, op5ChildFormulaB,
    op5ChildFormulaC, op5Subject, op5Sf1, op5Sf2, op5Result]

/-! ## C. The compute render tree collapses to the locally-defined carrier `computeNodesOp5` -/

/-- The locally-defined `.s5`-over-two-`.s1` compute node carrier.  The root is rendered by the new
    `.s5` `renderNode` dispatch at `stampOfAcc.s5 0` (records at consecutive lines `1`,`2`); the two
    `OP_1` children are rendered by `renderOp1Row` at the BFS accumulators `2`,`3`. -/
def computeNodesOp5 (z α : K) : NTree (ComputeNode K) :=
  .node
    { skel := genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail op5ChildFormulaB
        op5ChildFormulaC op5Sf1 op5Sf2 op5Result
      stamp := stampOfAcc .s5 0
      row := renderOp5Row z α (stampOfAcc .s5 0)
        (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail op5ChildFormulaB
          op5ChildFormulaC op5Sf1 op5Sf2 op5Result) }
    [.node
        { skel := genSkelOp1 op5Subject op5ChildFormulaB op5Sf1 (.atom 1)
          stamp := stampOfAcc .s1 2
          row := renderOp1Row z α (stampOfAcc .s1 2)
            (genSkelOp1 op5Subject op5ChildFormulaB op5Sf1 (.atom 1)) } [],
     .node
        { skel := genSkelOp1 op5Subject op5ChildFormulaC op5Sf2 (.atom 1)
          stamp := stampOfAcc .s1 3
          row := renderOp1Row z α (stampOfAcc .s1 3)
            (genSkelOp1 op5Subject op5ChildFormulaC op5Sf2 (.atom 1)) } []]

/-- **The generator's emitted `OP_5` compute tree, rendered, is exactly `computeNodesOp5`.**  The
    DFS pass emits the `.s5` root over the two `OP_1` children; the exponent pass stamps the root at
    `stampOfAcc.s5 0` and the children at the BFS accumulators `2`,`3` (threaded by
    `subtreeRecordCount`); the render pass fires the new `.s5` `renderNode` dispatch on the root and
    reuses `renderOp1Row` on the children.  The compute-side Layer-1 analogue of
    `gen_op7ComputeNodes_eq` for OP5. -/
theorem gen_op5ComputeNodes_eq (z α : K) :
    mapNTree GenComputeRow.node
        (renderRows z α (assignExponents
          (.node (skelNode
            (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail op5ChildFormulaB
              op5ChildFormulaC op5Sf1 op5Sf2 op5Result)
            [⟨op5ParentFormula, op5ParentTail, 3, 0⟩, ⟨op5ParentTail, op5ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op5Subject op5ChildFormulaB op5Sf1 (.atom 1))
                [⟨op5ChildFormulaB, op5Sf1, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op5Subject op5ChildFormulaC op5Sf2 (.atom 1))
                [⟨op5ChildFormulaC, op5Sf2, 3, 0⟩]) []])))
      = computeNodesOp5 z α := by
  have hroot : (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail op5ChildFormulaB
      op5ChildFormulaC op5Sf1 op5Sf2 op5Result).state = ComputeTable.State.s5 := rfl
  have hc0 : (genSkelOp1 op5Subject op5ChildFormulaB op5Sf1 (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hc1 : (genSkelOp1 op5Subject op5ChildFormulaC op5Sf2 (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, renderRows,
    renderNode, skelNode, hroot, hc0, hc1, Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, mapNTree, Nat.zero_add, Nat.add_zero]
  simp only [GenComputeRow.node, computeNodesOp5]

/-- **The generator really runs end-to-end on the OP5 program.**  Running the DFS pass
    `genComputeSkeleton 2 op5Subject op5ParentFormula` and rendering its tree yields exactly the
    rendered `.s5`-over-two-`.s1` carrier — nothing is hand-substituted for the generator. -/
theorem gen_op5Trace_is_generated (z α : K) :
    (genComputeSkeleton (K := K) 2 op5Subject op5ParentFormula).map
        (fun p => mapNTree GenComputeRow.node
          (renderRows z α (assignExponents p.1)))
      = .ok (computeNodesOp5 z α) := by
  rw [genComputeSkeleton_op5 0]
  exact congrArg Except.ok (gen_op5ComputeNodes_eq z α)

/-! ## D. Non-vacuity of the fan-out-2 / equality-gate shape -/

/-- OP5 spawns exactly TWO compute children. -/
theorem op5_fanout_two : ComputeTable.fanoutComp ComputeTable.State.s5 = 2 := rfl

/-- OP5 commits exactly TWO live memory records. -/
theorem op5_recordCount_two : Nock.Framework.recordCount ComputeTable.State.s5 = 2 := rfl

/-- The OP5 tail decomposition is active (`decActive.s5.f_th = decActive.s5.f_tt = true`), the
    enabler of the `tailCons` comparison role for `.s5`. -/
theorem op5_tail_decomposed :
    SemanticStrategy.decActive ComputeTable.State.s5 .f_th = true ∧
      SemanticStrategy.decActive ComputeTable.State.s5 .f_tt = true :=
  ⟨rfl, rfl⟩

/-- The active tail decomposition slots are genuinely `f_th ↦ b`, `f_tt ↦ c`. -/
theorem op5_tail_slots :
    (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail op5ChildFormulaB
        op5ChildFormulaC op5Sf1 op5Sf2 op5Result).decomposition .f_th (by decide) = op5ChildFormulaB ∧
      (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail op5ChildFormulaB
        op5ChildFormulaC op5Sf1 op5Sf2 op5Result).decomposition .f_tt (by decide) = op5ChildFormulaC :=
  ⟨rfl, rfl⟩

/-- Both subformula slots are live operands: `(a, b, sf1) = *[a b]` and `(a, c, sf2) = *[a c]`. -/
theorem op5_subformula_slots :
    P8Census.skeletonSubformula (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 0 .formula = op5ChildFormulaB ∧
      P8Census.skeletonSubformula (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 1 .formula = op5ChildFormulaC ∧
      P8Census.skeletonSubformula (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 0 .result = op5Sf1 ∧
      P8Census.skeletonSubformula (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 1 .result = op5Sf2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Both operands share the row subject `a` — the OP5 shape distinct from OP7.**  Unlike OP7 (whose
    second child's subject is the threaded helper result), OP5 evaluates BOTH operands `*[a b]` and
    `*[a c]` against the SAME row subject `a`: `skeletonSubformula _ 0.subject =
    skeletonSubformula _ 1.subject = op5Subject` (per `evalN`, `Reference.lean:99-104`, `evalN subj
    b`/`evalN subj c`). -/
theorem op5_operands_share_subject :
    P8Census.skeletonSubformula (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 0 .subject = op5Subject ∧
      P8Census.skeletonSubformula (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 1 .subject = op5Subject :=
  ⟨rfl, rfl⟩

/-- **The equality gate discriminates (mirror `op3_wut_gate_atom`/`_cell`).**  On the fixture's
    DISTINCT operands `sf1 = 3`, `sf2 = 4` the gate `Noun.tis sf1 sf2 = atom 1`; on EQUAL operands
    `Noun.tis sf1 sf1 = atom 0`.  The produced-result relation is genuinely non-trivial, not constant. -/
theorem op5_tis_gate_distinct : Noun.tis op5Sf1 op5Sf2 = Noun.atom 1 := rfl

/-- The equality gate on EQUAL operands returns atom `0`. -/
theorem op5_tis_gate_equal : Noun.tis op5Sf1 op5Sf1 = Noun.atom 0 := rfl

/-- **The compare gate discriminates at the real Nock evaluator.**  The distinct-operands fixture
    `*[0 [5 [1 3] [1 4]]]` evaluates to atom `1`, while the equal-operands fixture
    `*[0 [5 [1 3] [1 3]]]` evaluates to atom `0` — two genuinely different results from the same
    `OP_5` gate. -/
theorem op5_compare_discriminates :
    Nock.evalN 3 op5Subject op5ParentFormula = some (Noun.atom 1) ∧
      Nock.evalN 3 op5Subject op5FormulaEqual = some (Noun.atom 0) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The generator's OP5 arm produces the discriminating result on both fixtures.**  Extracting the
    generator's returned noun (`Prod.snd`), the distinct fixture yields atom `1` and the equal
    fixture yields atom `0` — the equality gate is inhabited on both sides by the generator itself. -/
theorem gen_op5_result_discriminates :
    (genComputeSkeleton (K := K) 3 op5Subject op5ParentFormula).map Prod.snd
        = .ok (Noun.atom 1) ∧
      (genComputeSkeleton (K := K) 3 op5Subject op5FormulaEqual).map Prod.snd
        = .ok (Noun.atom 0) := by
  refine ⟨?_, ?_⟩
  · simp only [genComputeSkeleton, op5ParentFormula, op5ParentTail, op5ChildFormulaB,
      op5ChildFormulaC, op5Subject, Except.map]
    decide
  · simp only [genComputeSkeleton, op5FormulaEqual, op5ChildFormulaB, op5Subject, Except.map]
    decide

/-- The `formula_tail@2` record is genuinely committed at axis `2`: the OP5 root's
    second memory record opens the formula tail `[b c]` at axis `2` with child `b`. -/
theorem op5_formulaTail_record_axis2 :
    P8Census.skeletonMemoryAxis (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 1 = 2 := rfl

/-- **The generated skeleton is semantically faithful to `evalFBy`.**  The capstone evaluator agrees
    with the generator's committed nouns: `*[0 [5 [1 3] [1 4]]] = 1`. -/
theorem gen_op5_evalFBy :
    FieldEmbedding.evalFBy 97 3 op5Subject op5ParentFormula = some op5Result := rfl

/-- Joint non-vacuity of the OP5 Layer-1 slice: fan-out 2, two records, active tail decomposition,
    both operands sharing the row subject `a` (distinct from OP7's threaded subject), the
    `formula_tail@2` record, and — the point of OP5 — the equality gate discriminating (distinct
    operands `→ 1`, equal operands `→ 0`). -/
theorem op5_nonvacuous :
    ComputeTable.fanoutComp ComputeTable.State.s5 = 2 ∧
      Nock.Framework.recordCount ComputeTable.State.s5 = 2 ∧
      SemanticStrategy.decActive ComputeTable.State.s5 .f_th = true ∧
      P8Census.skeletonSubformula (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 0 .subject = op5Subject ∧
      P8Census.skeletonSubformula (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 1 .subject = op5Subject ∧
      P8Census.skeletonMemoryAxis (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail
        op5ChildFormulaB op5ChildFormulaC op5Sf1 op5Sf2 op5Result) 1 = 2 ∧
      Noun.tis op5Sf1 op5Sf2 = Noun.atom 1 ∧
      Noun.tis op5Sf1 op5Sf1 = Noun.atom 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


#print axioms genComputeSkeleton_op5
#print axioms gen_op5ComputeNodes_eq
#print axioms gen_op5Trace_is_generated
#print axioms op5_operands_share_subject
#print axioms op5_compare_discriminates
#print axioms gen_op5_result_discriminates
#print axioms gen_op5_evalFBy
#print axioms op5_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
