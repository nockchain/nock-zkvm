/-
  Nock/NockVMROM/Thm54/TraceGen/Op7Gen.lean

  LAYER 1 (generator side only).  The trace generator's
  compute-side emission for the compose program

      `*[0 [7 [[1 3] [1 5]]]] = 5`

  where `b = [1 3]`, `c = [1 5]`, so the helper `sb = *[0 [1 3]] = 3` and the consumer
  `result = *[sb c] = *[3 [1 5]] = 5` (verified against `evalN`, `Reference.lean:112-117`, and
  `evalFBy`, `FieldEmbedding.lean:138-143`).

  OP7 is the first row with genuine **subject threading**: state `.s7`, fan-out `2`
  (`fanoutComp.s7 = 2`), TWO live memory records (`recordCount.s7 = 2`) — the formula-open
  `[7 [b c]] @3` record and the `formula_tail@2` record `[b c] @2` (same record shape as OP2).  The
  two subformula slots are the helper `*[a b]` (slot `0`, result `sb = sf_evaluation_2`) and the
  consumer `*[sb c]` (slot `1`), whose **subject is the computed helper `sb`, NOT the row subject
  `a`** — the follow-on subject is child two's result, per `evalN` (`evalN sb c` with `sb = *[a b]`).
  The tail decomposition is active (`decActive.s7.f_th = decActive.s7.f_tt = true`), so
  `f_th ↦ b`, `f_tt ↦ c`.  Because `requiredServedLookups.s7 = 0` the served side is vacuous and
  the memory forest stays single-root (`kMem = 1`), like OP1/OP2.

  **OP7 role-index resolution (per `evalN`, authoritative).**  The design doc flags a naming
  discrepancy: the paper names `sf_evaluation_1` for child-one's subject, but `evalN`
  (`Reference.lean:115`, `evalN sb c` with `sb = *[a b]`) makes the follow-on subject the *helper
  result*, which is child-two's output.  This slice follows `evalN`: the threaded subject of the
  consumer child is `op7Sb` (the helper `*[a b]` result), confirmed by `op7_threaded_subject`
  (`skeletonSubformula _ 1.subject = op7Sb = skeletonSubformula _ 0.result`) and by
  `op7_threading_matches_evalN` (`evalN _ op7Subject b = some op7Sb` and `evalN _ op7Sb c =
  some op7Result`).

  What lands here (all additive, kernel-clean, generic over any `[Field K]`):

  * `genComputeSkeleton_op7` — the generator's new `OP_7` DFS arm classifies `[7 [b c]]` on the row
    subject `a`, recurses on `b` against `a` for the helper `sb = *[a b]`, then on `c` against the
    **computed helper `sb`** (the threaded subject) for `result = *[sb c]`, and emits the `.s7` root
    over its two `OP_1` children with the two records.
  * `gen_op7ComputeNodes_eq` — the full DFS → exponent → render pipeline collapses to the
    locally-defined carrier `computeNodesOp7` (root rendered by the new `.s7` `renderNode` dispatch
    and `stampOfAcc` branch; the two children by `renderOp1Row`).
  * `gen_op7Trace_is_generated` — running the generator end-to-end yields exactly `computeNodesOp7`.
  * Non-vacuity: the 2-call fan-out, the active tail decomposition, the two records, and — the point
    of OP7 — the threaded consumer subject (child-one subject = child-two result ≠ row subject),
    all inhabited by concrete terms and confirmed against `evalN`.

  DEFERRED, and why (reported precisely, not faked):

  * The **served-memory forest** `genOp7MemForest` is NOT built here.  A *meaningful* generated
    forest equality (the pattern of `Op1GenData.gen_memForest_eq` / `ConsGenMem.gen_consMemForest_eq`)
    is stated against an independently *committed* served-memory fixture whose cells and LogUp
    accumulator are *validated* by the honest commitment's `BindMemoryRow` / `MemoryNodesOK` proofs.
    There is no committed OP7 served-memory fixture: it is exactly the `.s7` served
    `ExactServedMemoryTrace` that is the deferred heavy CORE.  In particular the OP7-specific
    `mr2 = ⟨formula_tail, formula_tail_head, 2⟩` record is an axis-2 (left)
    descent on the formula tail, whose cell dyck/size offsets and telescoping `(ipre,icur)`
    accumulator cannot be validated at Layer 1 (no `BindMemoryRow`/`semanticCoverage`); hand-emitting
    them would be unverified data.  `Op2Gen.lean`/`Op3Gen.lean` deferred their forests for the same
    reason.  The OP7 served side is `requiredServedLookups.s7 = 0` (VACUOUS) and single-root
    (`kMem = 1`), so this forest is a reconstruction of the committed records, deferred to Layer 2.

  * `op7DataOfGenerated`, `op7Data`, `op7Statement`, `BuildableNockExecution`, and any
    census/bind/specialization obligation — these need the `.s7` semantic CORE
    (`ExactExecutionSemanticData`), which must witness `e = *[sb c]` with the threaded subject
    `sb = *[a b]`.  That is the heavy focused Layer-2 pass, out of scope here.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

/-! ## A. The OP7 fixture nouns (`*[0 [7 [[1 3] [1 5]]]] = 5`) -/

/-- The row subject `a = 0`. -/
def op7Subject : Noun := .atom 0
/-- The helper formula `b = [1 3]` (an `OP_1` constant): `*[a b] = 3`. -/
def op7ChildFormulaB : Noun := .cell (.atom 1) (.atom 3)
/-- The helper evaluation `sb = *[0 [1 3]] = 3` (`= sf_evaluation_2`, the threaded subject). -/
def op7Sb : Noun := .atom 3
/-- The consumer formula `c = [1 5]` (an `OP_1` constant): `*[sb c] = 5`. -/
def op7ChildFormulaC : Noun := .cell (.atom 1) (.atom 5)
/-- The formula tail `[b c]`. -/
def op7ParentTail : Noun := .cell op7ChildFormulaB op7ChildFormulaC
/-- The OP7 formula `[7 [b c]]`. -/
def op7ParentFormula : Noun := .cell (.atom 7) op7ParentTail
/-- The produced result `*[sb c] = *[3 [1 5]] = 5` (`= sf_evaluation_1`, the row result). -/
def op7Result : Noun := .atom 5

/-! ## B. The generator's `OP_7` DFS arm fires on the compose formula `[7 [b c]]` -/

/-- **The `OP_7` DFS arm of `genComputeSkeleton` classifies the compose `[7 [b c]]`** on the row
    subject `a`: it recurses on `b` against `a` (the helper `*[a b]` → `sb`) and then on `c`
    against the **computed helper `sb`** (the threaded subject → the consumer `*[sb c]` → `result`),
    and emits the `.s7` root over the two `OP_1` children with the two committed records
    (formula-open `[7 [b c]] @3`, formula-tail `[b c] @2`).
    Mirrors `genComputeSkeleton_op2` at fan-out 2 with the second child's SUBJECT threaded to the
    first child's RESULT (per `evalN`, `Reference.lean:112-117`). -/
theorem genComputeSkeleton_op7 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) op7Subject op7ParentFormula
      = .ok (.node (skelNode
            (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
              op7ChildFormulaC op7Sb op7Result)
            [⟨op7ParentFormula, op7ParentTail, 3, 0⟩, ⟨op7ParentTail, op7ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op7Subject op7ChildFormulaB op7Sb (.atom 1))
                [⟨op7ChildFormulaB, op7Sb, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op7Sb op7ChildFormulaC op7Result (.atom 1))
                [⟨op7ChildFormulaC, op7Result, 3, 0⟩]) []],
          op7Result) := by
  show genComputeSkeleton ((n + 1) + 1) op7Subject op7ParentFormula = _
  simp only [genComputeSkeleton, op7ParentFormula, op7ParentTail, op7ChildFormulaB,
    op7ChildFormulaC, op7Subject, op7Sb, op7Result]

/-! ## C. The compute render tree collapses to the locally-defined carrier `computeNodesOp7` -/

/-- The locally-defined `.s7`-over-two-`.s1` compute node carrier.  The root is rendered by the new
    `.s7` `renderNode` dispatch at `stampOfAcc.s7 0` (records at consecutive lines `1`,`2`); the two
    `OP_1` children are rendered by `renderOp1Row` at the BFS accumulators `2`,`3`. -/
def computeNodesOp7 (z α : K) : NTree (ComputeNode K) :=
  .node
    { skel := genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
        op7ChildFormulaC op7Sb op7Result
      stamp := stampOfAcc .s7 0
      row := renderOp7Row z α (stampOfAcc .s7 0)
        (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
          op7ChildFormulaC op7Sb op7Result) }
    [.node
        { skel := genSkelOp1 op7Subject op7ChildFormulaB op7Sb (.atom 1)
          stamp := stampOfAcc .s1 2
          row := renderOp1Row z α (stampOfAcc .s1 2)
            (genSkelOp1 op7Subject op7ChildFormulaB op7Sb (.atom 1)) } [],
     .node
        { skel := genSkelOp1 op7Sb op7ChildFormulaC op7Result (.atom 1)
          stamp := stampOfAcc .s1 3
          row := renderOp1Row z α (stampOfAcc .s1 3)
            (genSkelOp1 op7Sb op7ChildFormulaC op7Result (.atom 1)) } []]

/-- **The generator's emitted `OP_7` compute tree, rendered, is exactly `computeNodesOp7`.**  The
    DFS pass emits the `.s7` root over the two `OP_1` children; the exponent pass stamps the root at
    `stampOfAcc.s7 0` and the children at the BFS accumulators `2`,`3` (threaded by
    `subtreeRecordCount`); the render pass fires the new `.s7` `renderNode` dispatch on the root and
    reuses `renderOp1Row` on the children.  The compute-side Layer-1 analogue of
    `gen_op2ComputeNodes_eq` for OP7. -/
theorem gen_op7ComputeNodes_eq (z α : K) :
    mapNTree GenComputeRow.node
        (renderRows z α (assignExponents
          (.node (skelNode
            (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
              op7ChildFormulaC op7Sb op7Result)
            [⟨op7ParentFormula, op7ParentTail, 3, 0⟩, ⟨op7ParentTail, op7ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op7Subject op7ChildFormulaB op7Sb (.atom 1))
                [⟨op7ChildFormulaB, op7Sb, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op7Sb op7ChildFormulaC op7Result (.atom 1))
                [⟨op7ChildFormulaC, op7Result, 3, 0⟩]) []])))
      = computeNodesOp7 z α := by
  have hroot : (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
      op7ChildFormulaC op7Sb op7Result).state = ComputeTable.State.s7 := rfl
  have hc0 : (genSkelOp1 op7Subject op7ChildFormulaB op7Sb (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hc1 : (genSkelOp1 op7Sb op7ChildFormulaC op7Result (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, renderRows,
    renderNode, skelNode, hroot, hc0, hc1, Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, mapNTree, Nat.zero_add, Nat.add_zero]
  simp only [GenComputeRow.node, computeNodesOp7]

/-- **The generator really runs end-to-end on the OP7 program.**  Running the DFS pass
    `genComputeSkeleton 2 op7Subject op7ParentFormula` and rendering its tree yields exactly the
    rendered `.s7`-over-two-`.s1` carrier — nothing is hand-substituted for the generator. -/
theorem gen_op7Trace_is_generated (z α : K) :
    (genComputeSkeleton (K := K) 2 op7Subject op7ParentFormula).map
        (fun p => mapNTree GenComputeRow.node
          (renderRows z α (assignExponents p.1)))
      = .ok (computeNodesOp7 z α) := by
  rw [genComputeSkeleton_op7 0]
  exact congrArg Except.ok (gen_op7ComputeNodes_eq z α)

/-! ## D. Non-vacuity of the fan-out-2 / subject-threading shape -/

/-- OP7 spawns exactly TWO compute children. -/
theorem op7_fanout_two : ComputeTable.fanoutComp ComputeTable.State.s7 = 2 := rfl

/-- OP7 commits exactly TWO live memory records. -/
theorem op7_recordCount_two : Nock.Framework.recordCount ComputeTable.State.s7 = 2 := rfl

/-- The OP7 tail decomposition is active (`decActive.s7.f_th = decActive.s7.f_tt = true`), the
    enabler of the `tailCons` comparison role for `.s7`. -/
theorem op7_tail_decomposed :
    SemanticStrategy.decActive ComputeTable.State.s7 .f_th = true ∧
      SemanticStrategy.decActive ComputeTable.State.s7 .f_tt = true :=
  ⟨rfl, rfl⟩

/-- The active tail decomposition slots are genuinely `f_th ↦ b`, `f_tt ↦ c`. -/
theorem op7_tail_slots :
    (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
        op7ChildFormulaC op7Sb op7Result).decomposition .f_th (by decide) = op7ChildFormulaB ∧
      (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
        op7ChildFormulaC op7Sb op7Result).decomposition .f_tt (by decide) = op7ChildFormulaC :=
  ⟨rfl, rfl⟩

/-- Both subformula slots are live: AIR `sf1` is the consumer `(sb, c, result)` and
    AIR `sf2` is the helper `(a, b, sb)`. -/
theorem op7_subformula_slots :
    P8Census.skeletonSubformula (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 0 .formula = op7ChildFormulaC ∧
      P8Census.skeletonSubformula (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 1 .formula = op7ChildFormulaB ∧
      P8Census.skeletonSubformula (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 0 .result = op7Result :=
  ⟨rfl, rfl, rfl⟩

/-- **The subject-threading witness — the point of OP7.**  AIR slot `1` (helper) is evaluated
    against the ROW subject `a`, and AIR slot `0` (consumer) is evaluated against the
    **computed helper result `sb`**: `skeletonSubformula _ 0.subject = op7Sb = skeletonSubformula _
    1.result`, and `op7Sb ≠ op7Subject`.  The follow-on subject is `sf_evaluation_2` (the helper's
    result), NOT the row subject. -/
theorem op7_threaded_subject :
    P8Census.skeletonSubformula (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 1 .subject = op7Subject ∧
      P8Census.skeletonSubformula (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 0 .subject = op7Sb ∧
      P8Census.skeletonSubformula (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 1 .result = op7Sb ∧
      op7Sb ≠ op7Subject :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- **The role index resolved per `evalN` (authoritative).**  The generator's threaded subject
    `op7Sb` is exactly `evalN`'s helper result `*[a b]`, and the row result is `*[sb c]` evaluated
    with `sb` as the subject: `evalN _ op7Subject op7ChildFormulaB = some op7Sb` and
    `evalN _ op7Sb op7ChildFormulaC = some op7Result`.  This pins the paper
    `sf_evaluation_1`-vs-`sf_evaluation_2` naming flag to `sf_evaluation_2` (child-two's result) as
    the follow-on subject (`Reference.lean:112-117`). -/
theorem op7_threading_matches_evalN :
    Nock.evalN 2 op7Subject op7ChildFormulaB = some op7Sb ∧
      Nock.evalN 2 op7Sb op7ChildFormulaC = some op7Result :=
  ⟨rfl, rfl⟩

/-- The `formula_tail@2` record is genuinely committed at axis `2`: the OP7
    root's second memory record opens the formula tail `[b c]` at axis `2` with child `b`. -/
theorem op7_formulaTail_record_axis2 :
    P8Census.skeletonMemoryAxis (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 1 = 2 := rfl

/-- **The generated skeleton is semantically faithful to `evalFBy`.**  The capstone evaluator agrees
    with the generator's committed nouns: `*[0 [7 [[1 3] [1 5]]]] = 5`. -/
theorem gen_op7_evalFBy :
    FieldEmbedding.evalFBy 97 3 op7Subject op7ParentFormula = some op7Result := rfl

/-- Joint non-vacuity of the OP7 Layer-1 slice: fan-out 2, two records, active tail decomposition,
    the threaded consumer subject (child-one subject = child-two result ≠ row subject, per `evalN`),
    and the `formula_tail@2` record. -/
theorem op7_nonvacuous :
    ComputeTable.fanoutComp ComputeTable.State.s7 = 2 ∧
      Nock.Framework.recordCount ComputeTable.State.s7 = 2 ∧
      SemanticStrategy.decActive ComputeTable.State.s7 .f_th = true ∧
      P8Census.skeletonSubformula (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 0 .subject = op7Sb ∧
      P8Census.skeletonSubformula (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 1 .result = op7Sb ∧
      op7Sb ≠ op7Subject ∧
      Nock.evalN 2 op7Subject op7ChildFormulaB = some op7Sb ∧
      P8Census.skeletonMemoryAxis (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail
        op7ChildFormulaB op7ChildFormulaC op7Sb op7Result) 1 = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl⟩


#print axioms genComputeSkeleton_op7
#print axioms gen_op7ComputeNodes_eq
#print axioms gen_op7Trace_is_generated
#print axioms op7_threaded_subject
#print axioms op7_threading_matches_evalN
#print axioms gen_op7_evalFBy
#print axioms op7_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
