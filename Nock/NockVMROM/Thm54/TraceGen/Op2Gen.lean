/-
  Nock/NockVMROM/Thm54/TraceGen/Op2Gen.lean

  LAYER 1 (generator side only).  The trace generator's
  compute-side emission for the fan-out-3 eval program

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  with `head(n2) = [1 [0 1]]`, `tail(n2) = [1 [1 5]]`, so
  `sf1 = *[0 [1 [0 1]]] = [0 1]`, `sf2 = *[0 [1 [1 5]]] = [1 5]`, and
  `child_three = *[sf1 sf2] = *[[0 1] [1 5]] = 5` (verified against `evalN`, `Reference.lean:91-96`).

  OP2 is the max-width compute row: state `.s2`, fan-out `3` (`fanoutComp.s2 = 3`), TWO live memory
  records (`recordCount.s2 = 2`) — the formula-open `[2 [b c]] @3` and the first `formula_tail@2`
  record `[b c] @2`.  It is the first row with three live subformula slots, the first `tailCons`
  (active tail decomposition `decActive.s2.f_th = true`), and the first child whose SUBJECT is a
  computed evaluation (`sf1`).  Because `requiredServedLookups.s2 = 0` the served side is vacuous
  and the memory forest stays single-root (`kMem = 1`), like OP1.

  What lands here (all additive, kernel-clean, generic over any `[Field K]`):

  * `genComputeSkeleton_op2` — the generator's new `OP_2` DFS arm classifies `[2 [b c]]` on `0`,
    recurses on `b`, `c` (→ `sf1`/`sf2`) and then on `.cell sf1 sf2` (the computed-subject third
    child, → `result`), and emits the `.s2` root over its three `OP_1` children with the two records.
  * `gen_op2ComputeNodes_eq` — the full DFS → exponent → render pipeline collapses to the
    locally-defined carrier `computeNodesOp2` (root rendered by the new `.s2` `renderNode` dispatch
    and `stampOfAcc` branch; the three children by `renderOp1Row`).
  * `gen_op2Trace_is_generated` — running the generator end-to-end yields exactly `computeNodesOp2`.
  * Non-vacuity: the 3-call fan-out, the first `tailCons` role, and the computed-subject child are
    genuinely inhabited by concrete terms.

  DEFERRED, and why (reported precisely, not faked):

  * The **served-memory forest** `genOp2MemForest` is NOT built here.  A *meaningful* generated
    forest equality (the pattern of `Op1GenData.gen_memForest_eq` / `ConsGenMem.gen_consMemForest_eq`)
    is stated against an independently *committed* served-memory fixture — for OP1 `Op1Config`, for
    cons `ConsConfig.consMemTree` — whose cells and LogUp accumulator are *validated* by the honest
    commitment's `BindMemoryRow` / `MemoryNodesOK` proofs.  There is no committed OP2 served-memory
    fixture: it is exactly the `.s2` served `ExactServedMemoryTrace` that is the deferred heavy CORE.
    In particular the OP2-specific `mr2 = ⟨formula_tail, formula_tail_head, 2⟩` record is an **axis-2 (left) descent** on the formula tail, whose cell dyck/size
    offsets and telescoping `(ipre,icur)` accumulator cannot be validated at Layer 1 (no
    `BindMemoryRow`/`semanticCoverage`); hand-emitting them would be unverified data.  The OP3 slice
    (`Op3Gen.lean`, the Layer-1 template) shipped no memory forest for the same reason.  Note the
    OP2 served side is `requiredServedLookups.s2 = 0` (VACUOUS) and single-root (`kMem = 1`), so this
    forest is a *reconstruction* of the committed records, deferred to the Layer-2 pass.

  * `op2DataOfGenerated`, `op2Data`, `op2Residual`, `op2Statement`, and any
    `Data`/`BuildableNockExecution`/census/bind/specialization obligation — these need the `.s2`
    semantic CORE (`ExactExecutionSemanticData`), the heavy focused pass, out of scope for Layer 1.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

/-! ## A. The OP2 fixture nouns (`*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`) -/

/-- The row subject `0`. -/
def op2Subject : Noun := .atom 0
/-- The first call formula `b = head(n2) = [1 [0 1]]`. -/
def op2ChildFormula1 : Noun := .cell (.atom 1) (.cell (.atom 0) (.atom 1))
/-- The first call evaluation `sf1 = *[0 [1 [0 1]]] = [0 1]`. -/
def op2Sf1 : Noun := .cell (.atom 0) (.atom 1)
/-- The second call formula `c = tail(n2) = [1 [1 5]]`. -/
def op2ChildFormula2 : Noun := .cell (.atom 1) (.cell (.atom 1) (.atom 5))
/-- The second call evaluation `sf2 = *[0 [1 [1 5]]] = [1 5]`. -/
def op2Sf2 : Noun := .cell (.atom 1) (.atom 5)
/-- The formula tail `[b c]`. -/
def op2ParentTail : Noun := .cell op2ChildFormula1 op2ChildFormula2
/-- The OP2 formula `[2 [b c]]`. -/
def op2ParentFormula : Noun := .cell (.atom 2) op2ParentTail
/-- The produced result `*[sf1 sf2] = *[[0 1] [1 5]] = 5`. -/
def op2Result : Noun := .atom 5

/-! ## B. The generator's `OP_2` DFS arm fires on the eval formula `[2 [b c]]` -/

/-- **The `OP_2` DFS arm of `genComputeSkeleton` classifies the eval `[2 [b c]]`** on `0`: it
    recurses on `b`/`c` (the two `OP_1` constant children → `sf1`/`sf2`) and then on `.cell sf1 sf2`
    (the third child, whose SUBJECT is the computed `sf1` → `result`), and emits the `.s2` root over
    the three `OP_1` children with the two committed records (formula-open `[2 [b c]] @3`,
    formula-tail `[b c] @2`).  Mirrors `genComputeSkeleton_op4`
    generalized to fan-out 3. -/
theorem genComputeSkeleton_op2 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) op2Subject op2ParentFormula
      = .ok (.node (skelNode
            (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail op2ChildFormula1
              op2ChildFormula2 op2Sf1 op2Sf2 op2Result)
            [⟨op2ParentFormula, op2ParentTail, 3, 0⟩, ⟨op2ParentTail, op2ChildFormula1, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op2Subject op2ChildFormula1 op2Sf1 (.atom 1))
                [⟨op2ChildFormula1, op2Sf1, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op2Subject op2ChildFormula2 op2Sf2 (.atom 1))
                [⟨op2ChildFormula2, op2Sf2, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op2Sf1 op2Sf2 op2Result (.atom 1))
                [⟨op2Sf2, op2Result, 3, 0⟩]) []],
          op2Result) := by
  show genComputeSkeleton ((n + 1) + 1) op2Subject op2ParentFormula = _
  simp only [genComputeSkeleton, op2ParentFormula, op2ParentTail, op2ChildFormula1,
    op2ChildFormula2, op2Subject, op2Sf1, op2Sf2, op2Result]

/-! ## C. The compute render tree collapses to the locally-defined carrier `computeNodesOp2` -/

/-- The locally-defined `.s2`-over-three-`.s1` compute node carrier.  The root is rendered by the
    new `.s2` `renderNode` dispatch at `stampOfAcc.s2 0` (records at consecutive lines `1`,`2`); the
    three `OP_1` children are rendered by `renderOp1Row` at the BFS accumulators `2`,`3`,`4`. -/
def computeNodesOp2 (z α : K) : NTree (ComputeNode K) :=
  .node
    { skel := genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail op2ChildFormula1
        op2ChildFormula2 op2Sf1 op2Sf2 op2Result
      stamp := stampOfAcc .s2 0
      row := renderOp2Row z α (stampOfAcc .s2 0)
        (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail op2ChildFormula1
          op2ChildFormula2 op2Sf1 op2Sf2 op2Result) }
    [.node
        { skel := genSkelOp1 op2Subject op2ChildFormula1 op2Sf1 (.atom 1)
          stamp := stampOfAcc .s1 2
          row := renderOp1Row z α (stampOfAcc .s1 2)
            (genSkelOp1 op2Subject op2ChildFormula1 op2Sf1 (.atom 1)) } [],
     .node
        { skel := genSkelOp1 op2Subject op2ChildFormula2 op2Sf2 (.atom 1)
          stamp := stampOfAcc .s1 3
          row := renderOp1Row z α (stampOfAcc .s1 3)
            (genSkelOp1 op2Subject op2ChildFormula2 op2Sf2 (.atom 1)) } [],
     .node
        { skel := genSkelOp1 op2Sf1 op2Sf2 op2Result (.atom 1)
          stamp := stampOfAcc .s1 4
          row := renderOp1Row z α (stampOfAcc .s1 4)
            (genSkelOp1 op2Sf1 op2Sf2 op2Result (.atom 1)) } []]

/-- **The generator's emitted `OP_2` compute tree, rendered, is exactly `computeNodesOp2`.**  The
    DFS pass emits the `.s2` root over the three `OP_1` children; the exponent pass stamps the root
    at `stampOfAcc.s2 0` and the children at the BFS accumulators `2`,`3`,`4` (threaded by
    `subtreeRecordCount`); the render pass fires the new `.s2` `renderNode` dispatch on the root and
    reuses `renderOp1Row` on the children.  The compute-side Layer-1 analogue of `gen_op3ComputeNodes_eq`
    for OP2. -/
theorem gen_op2ComputeNodes_eq (z α : K) :
    mapNTree GenComputeRow.node
        (renderRows z α (assignExponents
          (.node (skelNode
            (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail op2ChildFormula1
              op2ChildFormula2 op2Sf1 op2Sf2 op2Result)
            [⟨op2ParentFormula, op2ParentTail, 3, 0⟩, ⟨op2ParentTail, op2ChildFormula1, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op2Subject op2ChildFormula1 op2Sf1 (.atom 1))
                [⟨op2ChildFormula1, op2Sf1, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op2Subject op2ChildFormula2 op2Sf2 (.atom 1))
                [⟨op2ChildFormula2, op2Sf2, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op2Sf1 op2Sf2 op2Result (.atom 1))
                [⟨op2Sf2, op2Result, 3, 0⟩]) []])))
      = computeNodesOp2 z α := by
  have hroot : (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail op2ChildFormula1
      op2ChildFormula2 op2Sf1 op2Sf2 op2Result).state = ComputeTable.State.s2 := rfl
  have hc0 : (genSkelOp1 op2Subject op2ChildFormula1 op2Sf1 (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hc1 : (genSkelOp1 op2Subject op2ChildFormula2 op2Sf2 (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hc2 : (genSkelOp1 op2Sf1 op2Sf2 op2Result (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, renderRows,
    renderNode, skelNode, hroot, hc0, hc1, hc2, Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, mapNTree, Nat.zero_add, Nat.add_zero]
  simp only [GenComputeRow.node, computeNodesOp2]

/-- **The generator really runs end-to-end on the OP2 program.**  Running the DFS pass
    `genComputeSkeleton 2 op2Subject op2ParentFormula` and rendering its tree yields exactly the
    rendered `.s2`-over-three-`.s1` carrier — nothing is hand-substituted for the generator. -/
theorem gen_op2Trace_is_generated (z α : K) :
    (genComputeSkeleton (K := K) 2 op2Subject op2ParentFormula).map
        (fun p => mapNTree GenComputeRow.node
          (renderRows z α (assignExponents p.1)))
      = .ok (computeNodesOp2 z α) := by
  rw [genComputeSkeleton_op2 0]
  exact congrArg Except.ok (gen_op2ComputeNodes_eq z α)

/-! ## D. Non-vacuity of the fan-out-3 / `tailCons` / computed-subject shape -/

/-- OP2 is the max-width compute row: fan-out exactly `3`. -/
theorem op2_fanout_three : ComputeTable.fanoutComp ComputeTable.State.s2 = 3 := rfl

/-- OP2 commits exactly TWO live memory records. -/
theorem op2_recordCount_two : Nock.Framework.recordCount ComputeTable.State.s2 = 2 := rfl

/-- **The first `tailCons`:** OP2 is the first compute skeleton whose tail decomposition is active
    (`decActive.s2.f_th = decActive.s2.f_tt = true`), the enabler of the `tailCons`
    comparison role. -/
theorem op2_tail_decomposed :
    SemanticStrategy.decActive ComputeTable.State.s2 .f_th = true ∧
      SemanticStrategy.decActive ComputeTable.State.s2 .f_tt = true :=
  ⟨rfl, rfl⟩

/-- The active tail decomposition slots are genuinely `f_th ↦ b`, `f_tt ↦ c`. -/
theorem op2_tail_slots :
    (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail op2ChildFormula1
        op2ChildFormula2 op2Sf1 op2Sf2 op2Result).decomposition .f_th (by decide) = op2ChildFormula1 ∧
      (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail op2ChildFormula1
        op2ChildFormula2 op2Sf1 op2Sf2 op2Result).decomposition .f_tt (by decide) = op2ChildFormula2 :=
  ⟨rfl, rfl⟩

/-- The three subformula slots are all live: children `(0, b, sf1)`, `(0, c, sf2)`, and
    `(sf1, sf2, result)`. -/
theorem op2_subformula_slots :
    P8Census.skeletonSubformula (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail
        op2ChildFormula1 op2ChildFormula2 op2Sf1 op2Sf2 op2Result) 0 .formula = op2ChildFormula1 ∧
      P8Census.skeletonSubformula (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail
        op2ChildFormula1 op2ChildFormula2 op2Sf1 op2Sf2 op2Result) 1 .formula = op2ChildFormula2 ∧
      P8Census.skeletonSubformula (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail
        op2ChildFormula1 op2ChildFormula2 op2Sf1 op2Sf2 op2Result) 2 .result = op2Result :=
  ⟨rfl, rfl, rfl⟩

/-- **The computed-subject child:** the third subformula slot's SUBJECT is the computed evaluation
    `sf1 = [0 1]`, NOT the row subject `0` — the first time a `subformula i.subject` is drawn from a
    prior evaluation rather than the program AST. -/
theorem op2_computed_subject_child :
    P8Census.skeletonSubformula (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail
        op2ChildFormula1 op2ChildFormula2 op2Sf1 op2Sf2 op2Result) 2 .subject = op2Sf1 ∧
      op2Sf1 ≠ op2Subject :=
  ⟨rfl, by decide⟩

/-- The `formula_tail@2` record is genuinely committed at axis `2`: the OP2 root's
    second memory record opens the formula tail `[b c]` at axis `2` with child `b`. -/
theorem op2_formulaTail_record_axis2 :
    P8Census.skeletonMemoryAxis (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail
        op2ChildFormula1 op2ChildFormula2 op2Sf1 op2Sf2 op2Result) 1 = 2 := rfl

/-- **The generated skeleton is semantically faithful to `evalFBy`.**  The capstone evaluator agrees
    with the generator's committed nouns: `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`. -/
theorem gen_op2_evalFBy :
    FieldEmbedding.evalFBy 97 3 op2Subject op2ParentFormula = some op2Result := rfl

/-- Joint non-vacuity of the OP2 Layer-1 slice: fan-out 3, two records, active tail decomposition
    (the `tailCons` enabler), the computed-subject third child, and the `formula_tail@2` record. -/
theorem op2_nonvacuous :
    ComputeTable.fanoutComp ComputeTable.State.s2 = 3 ∧
      Nock.Framework.recordCount ComputeTable.State.s2 = 2 ∧
      SemanticStrategy.decActive ComputeTable.State.s2 .f_th = true ∧
      P8Census.skeletonSubformula (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail
        op2ChildFormula1 op2ChildFormula2 op2Sf1 op2Sf2 op2Result) 2 .subject = op2Sf1 ∧
      op2Sf1 ≠ op2Subject ∧
      P8Census.skeletonMemoryAxis (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail
        op2ChildFormula1 op2ChildFormula2 op2Sf1 op2Sf2 op2Result) 1 = 2 :=
  ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩


#print axioms genComputeSkeleton_op2
#print axioms gen_op2ComputeNodes_eq
#print axioms gen_op2Trace_is_generated
#print axioms op2_computed_subject_child
#print axioms gen_op2_evalFBy
#print axioms op2_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
