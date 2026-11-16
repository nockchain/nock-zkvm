/-
  Nock/NockVMROM/Thm54/TraceGen/Op6Gen.lean

  LAYER 1 (generator side only).  The trace
  generator's compute-side emission for the fan-out-2 branch program

      `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`

  Here the condition formula is `b = [1 0]`, the two branches are `c = [1 5]` and `d = [1 6]`, so
  the condition evaluates `*[0 [1 0]] = 0`, which selects the **then** branch `c`: the taken
  compute `*[0 [1 5]] = 5 = result`.  The **else** branch `d = [1 6]` is present only structurally
  (the `f_ttt` decomposition column and the third `[c d] @2` record's cons check) and is NOT
  evaluated.  All committed nouns are verified against `evalN` (`Reference.lean:105-111`) and
  `evalFBy`.

  OP6 is the genuine branch: state `.s6`, fan-out `2` (`fanoutComp.s6 = 2`), THREE live memory
  records (`recordCount.s6 = 3`) — the formula-open `[6 [b [c d]]] @3`, the formula-tail
  `[b [c d]] @2` exposing the condition formula `b`, and the branch-pair `[c d] @2` exposing the
  head branch `c` (structurally reading BOTH branches even though only one is evaluated).  It is the
  **only** state whose tail-tail decomposition is active (`decActive.s6.f_tth =.f_ttt = true`),
  the **first** generator arm that consults a computed VALUE (the condition) to fix the tree shape,
  and the **first** row whose size window is NON-VACUOUS.

  What lands here (all additive, kernel-clean, generic over any `[Field K]`):

  * `genComputeSkeleton_op6` — the generator's new `OP_6` DFS arm classifies `[6 [b [c d]]]` on `0`,
    recurses on `b` (→ the condition `cond = 0`), BRANCHES on that value to select the taken branch
    `c`, recurses on `c` against the shared subject (→ `result = 5`), and emits the `.s6` root over
    its two `OP_1` children (condition, taken) with the THREE records; the untaken `d` is present
    only in the `f_ttt` decomposition column and the `[c d] @2` record.
  * `gen_op6ComputeNodes_eq` — the DFS → exponent → render pipeline collapses to the locally-defined
    carrier `computeNodesOp6` (root rendered by the new `.s6` `renderNode` dispatch and `stampOfAcc`
    branch with THREE records; the two children by `renderOp1Row`).
  * `gen_op6Trace_is_generated` — running the generator end-to-end yields exactly `computeNodesOp6`.
  * `genComputeSkeleton_op6_else` + `op6_value_driven_selection` — the SAME two branches with a
    condition that evaluates to `1` instead of `0` make the generator commit the ELSE branch `d`
    (not `c`) as the taken child: the value-driven branch is real, resolved by consulting the
    `evalN`/DFS condition value at emission time.
  * Non-vacuity: fan-out 2, three records, the unique active `f_tth`/`f_ttt` decomposition, the
    taken child = the value-selected branch, the untaken branch present only structurally, and the
    NON-VACUOUS 1-leaf condition size window.

  DEFERRED, and why (reported precisely, not faked):

  * The **served-memory forest** is NOT built here.  As for OP2 (`Op2Gen.lean`) a *meaningful*
    generated forest equality is stated against an independently *committed* served-memory fixture
    whose cells and LogUp accumulator are validated by the honest commitment's
    `BindMemoryRow`/`MemoryNodesOK` proofs.  OP6's `mr2`/`mr3` are axis-2 (left) descents on
    `formula_tail` and on the branch pair `[c d]`, whose cell dyck/size
    offsets and telescoping `(ipre,icur)` accumulator cannot be validated at Layer 1; hand-emitting
    them would be unverified data.  Deferred to the Layer-2 pass.

  * `op6DataOfGenerated`, `op6Data`, `op6Statement`, and any `BuildableNockExecution`/semantic-CORE
    (`ExactExecutionSemanticData`) obligation — these carry the branch's actual value semantics
    (the taken child is exactly the branch selected by `sf_evaluation_2 ∈ {0,1}`, EC.6.1/EC.6.2) and
    are the deferred heavy Layer-2 pass (design spec §OP6.4, §OP6.6, §OP6.8).  This file commits
    ONLY the generator output as pure data, its equality to a local carrier, and the value-driven
    selection at the DFS level; it does NOT claim the AIR branch-selection constraint or the CORE.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.HonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

/-! ## A. The OP6 fixture nouns (`*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`, condition `0` → then-branch) -/

/-- The row subject `0`. -/
def op6Subject : Noun := .atom 0
/-- The condition formula `b = [1 0]` (an `OP_1` constant returning `0`). -/
def op6CondFormula : Noun := .cell (.atom 1) (.atom 0)
/-- The condition's evaluation `cond = *[0 [1 0]] = 0` — the 1-leaf branch selector. -/
def op6CondResult : Noun := .atom 0
/-- The then-branch formula `c = [1 5]` (an `OP_1` constant returning `5`). -/
def op6BranchC : Noun := .cell (.atom 1) (.atom 5)
/-- The else-branch formula `d = [1 6]` (an `OP_1` constant returning `6`; present but untaken). -/
def op6BranchD : Noun := .cell (.atom 1) (.atom 6)
/-- The branch pair `[c d]` (`f_tt`). -/
def op6BranchPair : Noun := .cell op6BranchC op6BranchD
/-- The formula tail `[b [c d]]` (`f_t`). -/
def op6ParentTail : Noun := .cell op6CondFormula op6BranchPair
/-- The OP6 formula `[6 [b [c d]]]`. -/
def op6ParentFormula : Noun := .cell (.atom 6) op6ParentTail
/-- The branch result `*[0 c] = *[0 [1 5]] = 5`. -/
def op6Result : Noun := .atom 5

/-- The taken branch is a genuine value-driven selection: the condition `*[0 [1 0]]` evaluates to
    `0`, which per `evalN` (`Reference.lean:108`) selects the THEN branch `c = [1 5]`, whose
    evaluation is `5`. -/
theorem op6_then_evalN :
    FieldEmbedding.evalFBy 97 3 op6Subject op6CondFormula = some op6CondResult ∧
      FieldEmbedding.evalFBy 97 3 op6Subject op6BranchC = some op6Result := by
  constructor <;>
    simp [FieldEmbedding.evalFBy, op6Subject, op6CondFormula, op6CondResult, op6BranchC, op6Result]

/-! ## B. The generator's `OP_6` DFS arm fires on the branch formula `[6 [b [c d]]]` -/

/-- **The `OP_6` DFS arm of `genComputeSkeleton` classifies the branch `[6 [b [c d]]]`** on `0`: it
    recurses on `b` (the `OP_1` condition → `cond = 0`), BRANCHES on that computed value, recurses on `c` against the shared subject `0`
    (the `OP_1` then-branch → `result = 5`), and emits the `.s6` root over its two `OP_1` children
    (condition, then-branch) with the THREE committed records (formula-open `[6 [b [c d]]] @3`,
    formula-tail `[b [c d]] @2`, branch-pair `[c d] @2`).  This
    is the first generator dispatch that consults an `evalN` VALUE to fix the tree shape; the
    untaken `d` is present only in the `f_ttt` decomposition column and the `[c d] @2` record. -/
theorem genComputeSkeleton_op6 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) op6Subject op6ParentFormula
      = .ok (.node (skelNode
            (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula
              op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
            [⟨op6ParentFormula, op6ParentTail, 3, 0⟩, ⟨op6ParentTail, op6CondFormula, 2, 0⟩,
             ⟨op6BranchPair, op6BranchC, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op6Subject op6CondFormula op6CondResult (.atom 1))
                [⟨op6CondFormula, op6CondResult, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op6Subject op6BranchC op6Result (.atom 1))
                [⟨op6BranchC, op6Result, 3, 0⟩]) []],
          op6Result) := by
  show genComputeSkeleton ((n + 1) + 1) op6Subject op6ParentFormula = _
  simp only [genComputeSkeleton, op6ParentFormula, op6ParentTail, op6BranchPair, op6CondFormula,
    op6BranchC, op6BranchD, op6Subject, op6CondResult, op6Result]

/-! ## C. The compute render tree collapses to the locally-defined carrier `computeNodesOp6` -/

/-- The locally-defined `.s6`-over-two-`.s1` compute node carrier.  The root is rendered by the new
    `.s6` `renderNode` dispatch at `stampOfAcc.s6 0` (THREE records at consecutive lines
    `1`,`2`,`3`); the two `OP_1` children — the condition (emitted first, DFS evaluation order) and
    the then-branch — are rendered by `renderOp1Row` at the BFS accumulators `3`,`4` (threaded by
    `subtreeRecordCount`, root record count `recordCount.s6 = 3`). -/
def computeNodesOp6 (z α : K) : NTree (ComputeNode K) :=
  .node
    { skel := genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula
        op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result
      stamp := stampOfAcc .s6 0
      row := renderOp6Row z α (stampOfAcc .s6 0)
        (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula
          op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result) }
    [.node
        { skel := genSkelOp1 op6Subject op6CondFormula op6CondResult (.atom 1)
          stamp := stampOfAcc .s1 3
          row := renderOp1Row z α (stampOfAcc .s1 3)
            (genSkelOp1 op6Subject op6CondFormula op6CondResult (.atom 1)) } [],
     .node
        { skel := genSkelOp1 op6Subject op6BranchC op6Result (.atom 1)
          stamp := stampOfAcc .s1 4
          row := renderOp1Row z α (stampOfAcc .s1 4)
            (genSkelOp1 op6Subject op6BranchC op6Result (.atom 1)) } []]

/-- **The generator's emitted `OP_6` compute tree, rendered, is exactly `computeNodesOp6`.**  The
    DFS pass emits the `.s6` root over the two `OP_1` children; the exponent pass stamps the root at
    `stampOfAcc.s6 0` and the children at the BFS accumulators `3`,`4` (threaded by
    `subtreeRecordCount`, root record count `recordCount.s6 = 3`); the render pass fires the new
    `.s6` `renderNode` dispatch on the root (THREE records, all four decomposition columns) and
    reuses `renderOp1Row` on the children. -/
theorem gen_op6ComputeNodes_eq (z α : K) :
    mapNTree GenComputeRow.node
        (renderRows z α (assignExponents
          (.node (skelNode
            (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula
              op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
            [⟨op6ParentFormula, op6ParentTail, 3, 0⟩, ⟨op6ParentTail, op6CondFormula, 2, 0⟩,
             ⟨op6BranchPair, op6BranchC, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op6Subject op6CondFormula op6CondResult (.atom 1))
                [⟨op6CondFormula, op6CondResult, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op6Subject op6BranchC op6Result (.atom 1))
                [⟨op6BranchC, op6Result, 3, 0⟩]) []])))
      = computeNodesOp6 z α := by
  have hroot : (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula
      op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result).state
      = ComputeTable.State.s6 := rfl
  have hc0 : (genSkelOp1 op6Subject op6CondFormula op6CondResult (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hc1 : (genSkelOp1 op6Subject op6BranchC op6Result (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, renderRows,
    renderNode, skelNode, hroot, hc0, hc1, Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, mapNTree, Nat.zero_add, Nat.add_zero]
  simp only [GenComputeRow.node, computeNodesOp6]

/-- **The generator really runs end-to-end on the OP6 program.**  Running the DFS pass
    `genComputeSkeleton 2 op6Subject op6ParentFormula` and rendering its tree yields exactly the
    rendered `.s6`-over-two-`.s1` carrier — nothing is hand-substituted for the generator, and the
    branch was resolved by consulting the condition value during the DFS. -/
theorem gen_op6Trace_is_generated (z α : K) :
    (genComputeSkeleton (K := K) 2 op6Subject op6ParentFormula).map
        (fun p => mapNTree GenComputeRow.node
          (renderRows z α (assignExponents p.1)))
      = .ok (computeNodesOp6 z α) := by
  rw [genComputeSkeleton_op6 0]
  exact congrArg Except.ok (gen_op6ComputeNodes_eq z α)

/-! ## D. The value-driven branch is real: the SAME branches with condition `1` select the ELSE
    branch `d` -/

/-- The else-fixture condition formula `b' = [1 1]` (an `OP_1` constant returning `1`). -/
def op6ElseCondFormula : Noun := .cell (.atom 1) (.atom 1)
/-- The else-fixture condition's evaluation `cond' = *[0 [1 1]] = 1` — selects the ELSE branch. -/
def op6ElseCondResult : Noun := .atom 1
/-- The else-branch result `*[0 d] = *[0 [1 6]] = 6`. -/
def op6ElseResult : Noun := .atom 6
/-- The else-fixture formula tail `[b' [c d]]` — the SAME branch pair `[c d]`, different condition. -/
def op6ElseParentTail : Noun := .cell op6ElseCondFormula op6BranchPair
/-- The else-fixture OP6 formula `[6 [b' [c d]]]`. -/
def op6ElseParentFormula : Noun := .cell (.atom 6) op6ElseParentTail

/-- **The `OP_6` DFS arm on the ELSE fixture selects the ELSE branch `d`.**  With the SAME two
    branches `c = [1 5]`, `d = [1 6]` but a condition `b' = [1 1]` that evaluates to `1`, the
    generator BRANCHES the other way: it recurses on `d` (not `c`), commits `d` as
    the taken child (subformula slot `0`'s formula), and yields `result = 6`.  The tree shape is
    fixed by the computed condition value, not by syntax. -/
theorem genComputeSkeleton_op6_else (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) op6Subject op6ElseParentFormula
      = .ok (.node (skelNode
            (genSkelOp6 op6Subject op6ElseParentFormula (.atom 6) op6ElseParentTail op6ElseCondFormula
              op6BranchPair op6BranchC op6BranchD op6ElseCondResult op6BranchD op6ElseResult)
            [⟨op6ElseParentFormula, op6ElseParentTail, 3, 0⟩,
             ⟨op6ElseParentTail, op6ElseCondFormula, 2, 0⟩, ⟨op6BranchPair, op6BranchC, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op6Subject op6ElseCondFormula op6ElseCondResult (.atom 1))
                [⟨op6ElseCondFormula, op6ElseCondResult, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op6Subject op6BranchD op6ElseResult (.atom 1))
                [⟨op6BranchD, op6ElseResult, 3, 0⟩]) []],
          op6ElseResult) := by
  show genComputeSkeleton ((n + 1) + 1) op6Subject op6ElseParentFormula = _
  simp only [genComputeSkeleton, op6ElseParentFormula, op6ElseParentTail, op6BranchPair,
    op6ElseCondFormula, op6BranchC, op6BranchD, op6Subject, op6ElseCondResult, op6ElseResult]

/-- **The branch selection is genuinely value-driven.**  The taken child's committed formula
    (subformula slot `0`, per the AIR/size-window convention `AIR.evalRExprs_s6_sound`) is the THEN
    branch `c` when the condition evaluates to `0`, and the ELSE branch `d` when it evaluates to `1`
    — and `c ≠ d`.  The generator consulted the `evalN` condition value to fix which branch becomes
    a compute child. -/
theorem op6_value_driven_selection :
    P8Census.skeletonSubformula (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail
        op6CondFormula op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
        0 .formula = op6BranchC ∧
      P8Census.skeletonSubformula (genSkelOp6 op6Subject op6ElseParentFormula (.atom 6)
        op6ElseParentTail op6ElseCondFormula op6BranchPair op6BranchC op6BranchD op6ElseCondResult
        op6BranchD op6ElseResult) 0 .formula = op6BranchD ∧
      op6BranchC ≠ op6BranchD :=
  ⟨rfl, rfl, by decide⟩

/-! ## E. Non-vacuity of the fan-out-2 / three-record / branch shape / size window -/

/-- OP6 is a fan-out-`2` compute row. -/
theorem op6_fanout_two : ComputeTable.fanoutComp ComputeTable.State.s6 = 2 := rfl

/-- OP6 commits exactly THREE live memory records. -/
theorem op6_recordCount_three : Nock.Framework.recordCount ComputeTable.State.s6 = 3 := rfl

/-- **The unique tail-tail decomposition:** OP6 is the ONLY state whose tail-tail decomposition is
    active (`decActive.s6.f_tth = decActive.s6.f_ttt = true`, `SemanticStrategy.lean:53`) — both
    branch formulas `c`/`d` are present as decomposition columns. -/
theorem op6_branch_pair_decomposed :
    SemanticStrategy.decActive ComputeTable.State.s6 .f_tth = true ∧
      SemanticStrategy.decActive ComputeTable.State.s6 .f_ttt = true :=
  ⟨rfl, rfl⟩

/-- Both branch formulas are genuinely present as decomposition columns `f_tth ↦ c`, `f_ttt ↦ d`,
    even though only `c` is evaluated. -/
theorem op6_branch_columns :
    (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula op6BranchPair
        op6BranchC op6BranchD op6CondResult op6BranchC op6Result).decomposition .f_tth (by decide)
        = op6BranchC ∧
      (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula op6BranchPair
        op6BranchC op6BranchD op6CondResult op6BranchC op6Result).decomposition .f_ttt (by decide)
        = op6BranchD :=
  ⟨rfl, rfl⟩

/-- **The taken child = the value-selected branch, and the untaken branch is present only
    structurally.**  Subformula slot `0` (the taken child) has formula `c` (the branch the condition
    `0` selects) and slot `1` (the condition) has formula `b`; the ELSE branch `d` appears as NO
    subformula child — it lives ONLY in the `f_ttt` decomposition column (`op6_branch_columns`) and
    the `[c d] @2` record.  This is exactly "both branches structurally present, only one
    evaluated". -/
theorem op6_taken_and_untaken :
    P8Census.skeletonSubformula (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail
        op6CondFormula op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
        0 .formula = op6BranchC ∧
      P8Census.skeletonSubformula (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail
        op6CondFormula op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
        1 .formula = op6CondFormula ∧
      op6BranchC ≠ op6BranchD :=
  ⟨rfl, rfl, by decide⟩

/-- **The branch-pair `[c d] @2` record is genuinely committed at axis `2`**: the
    OP6 root's THIRD memory record opens the branch pair `[c d]` at axis `2` to expose its head `c`,
    structurally reading both branches. -/
theorem op6_branchPair_record_axis2 :
    P8Census.skeletonMemoryAxis (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail
        op6CondFormula op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result) 2
      = 2 ∧
      (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula op6BranchPair
        op6BranchC op6BranchD op6CondResult op6BranchC op6Result).memoryRecord 2 (by decide)
        = ⟨op6BranchPair, op6BranchC, 2⟩ :=
  ⟨rfl, rfl⟩

/-- **The condition result is the size-window noun, and OP6 is the FIRST non-vacuous size window.**
    `requiredSizeWindowNouns.s6 = [skeletonSubformula s 1.result]` = `[cond]` — the condition's
    evaluation, the 1-leaf atom `0` — whereas the OP_1 leaf (like OP1/cons/OP2) has an EMPTY size
    window.  This is the first place `SizeWindowCounting` fires. -/
theorem op6_sizeWindow_nonvacuous :
    SizeWindowCounting.requiredSizeWindowNouns
        (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula op6BranchPair
          op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
      = [op6CondResult] ∧
      op6CondResult = Noun.atom 0 ∧
      SizeWindowCounting.requiredSizeWindowNouns
        (genSkelOp1 op6Subject op6CondFormula op6CondResult (.atom 1)) = [] :=
  ⟨rfl, rfl, rfl⟩

/-- **The generated skeleton is semantically faithful to `evalFBy`.**  The capstone evaluator agrees
    with the generator's committed nouns on BOTH the then-fixture and the else-fixture:
    `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5` and `*[0 [6 [[1 1] [[1 5] [1 6]]]]] = 6`. -/
theorem gen_op6_evalFBy :
    FieldEmbedding.evalFBy 97 3 op6Subject op6ParentFormula = some op6Result ∧
      FieldEmbedding.evalFBy 97 3 op6Subject op6ElseParentFormula = some op6ElseResult := by
  constructor <;>
    simp [FieldEmbedding.evalFBy, op6Subject, op6ParentFormula, op6ParentTail, op6ElseParentFormula,
      op6ElseParentTail, op6BranchPair, op6CondFormula, op6ElseCondFormula, op6BranchC, op6BranchD,
      op6Result, op6ElseResult]

/-- Joint non-vacuity of the OP6 Layer-1 slice: fan-out 2, three records, the unique active
    `f_tth`/`f_ttt` decomposition, the value-selected taken child (`c`, with the untaken `d ≠ c`
    present only structurally), the branch-pair `[c d] @2` record, and the NON-VACUOUS 1-leaf
    condition size window. -/
theorem op6_nonvacuous :
    ComputeTable.fanoutComp ComputeTable.State.s6 = 2 ∧
      Nock.Framework.recordCount ComputeTable.State.s6 = 3 ∧
      SemanticStrategy.decActive ComputeTable.State.s6 .f_tth = true ∧
      SemanticStrategy.decActive ComputeTable.State.s6 .f_ttt = true ∧
      P8Census.skeletonSubformula (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail
        op6CondFormula op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
        0 .formula = op6BranchC ∧
      op6BranchC ≠ op6BranchD ∧
      P8Census.skeletonMemoryAxis (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail
        op6CondFormula op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result) 2
        = 2 ∧
      SizeWindowCounting.requiredSizeWindowNouns
        (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula op6BranchPair
          op6BranchC op6BranchD op6CondResult op6BranchC op6Result) = [op6CondResult] :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl⟩


#print axioms genComputeSkeleton_op6
#print axioms gen_op6ComputeNodes_eq
#print axioms gen_op6Trace_is_generated
#print axioms genComputeSkeleton_op6_else
#print axioms op6_value_driven_selection
#print axioms op6_taken_and_untaken
#print axioms op6_sizeWindow_nonvacuous
#print axioms gen_op6_evalFBy
#print axioms op6_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
