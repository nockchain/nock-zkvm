/-
  Nock/NockVMROM/Thm54/TraceGen/Op8Gen.lean

  LAYER 1 (generator side only).  The trace
  generator's compute-side emission for the push program

      `*[0 [8 [[1 3] [1 5]]]] = 5`

  where `b = [1 3]`, `c = [1 5]`, so the helper `sb = *[0 [1 3]] = 3`, the pushed subject is the
  autocons `[sb a] = [3 0]`, and the consumer `result = *[[sb a] c] = *[[3 0] [1 5]] = 5` (verified
  against `evalN`, `Reference.lean:118-123`, and `evalFBy`, `FieldEmbedding.lean:138-143`).

  OP8 is OP7 (compose) plus one **autocons on the threaded subject**: state `.s8`, fan-out `2`
  (`fanoutComp.s8 = 2`), TWO live memory records (`recordCount.s8 = 2`) — the formula-open
  `[8 [b c]] @3` record and the `formula_tail@2` record `[b c] @2` (same record shape as OP7).  The
  two subformula slots are the helper `*[a b]` (slot `0`, result `sb = sf_evaluation_2`) and the
  consumer `*[[sb a] c]` (slot `1`), whose **subject is the autocons `[sb a]` — the computed helper
  `sb` PAIRED WITH the original row subject `a` (the "push"), NOT the row subject alone (OP7) and NOT
  the bare helper**.  The tail decomposition is active (`decActive.s8.f_th = decActive.s8.f_tt =
  true`), so `f_th ↦ b`, `f_tt ↦ c`.  Because `requiredServedLookups.s8 = 0` the served side is
  vacuous and the memory forest stays single-root (`kMem = 1`), like OP1/OP2/OP7.

  **OP8 vs OP7 (per `evalN`, authoritative).**  OP7 threads the bare helper result `sb` as the
  follow-on subject and carries an `sf_evaluation_1`-vs-`sf_evaluation_2` naming flag.  OP8 has NO such flag: `evalN` (`Reference.lean:121`, `evalN (.cell sb subj) c`)
  makes the follow-on subject the autocons `[sb a]` unambiguously.  The push is
  confirmed by `op8_pushed_subject` (`skeletonSubformula _ 1.subject = op8PushedSubject =
.cell op8Sb op8Subject`) and by `op8_subject_matches_evalN` (`evalN _ op8Subject op8ChildFormulaB
  = some op8Sb` and `evalN _ (.cell op8Sb op8Subject) op8ChildFormulaC = some op8Result`).  The
  constructed subject cons is the Layer-1 face of the compute-AIR cons check EC.8.1
  (the paper, `sf1_s = cons(sf2_e, s)`), inhabited here by `op8_ec81_cons_present`.

  What lands here (all additive, kernel-clean, generic over any `[Field K]`):

  * `genComputeSkeleton_op8` — the generator's new `OP_8` DFS arm classifies `[8 [b c]]` on the row
    subject `a`, recurses on `b` against `a` for the helper `sb = *[a b]`, then on `c` against the
    **autocons `[sb a]`** (the pushed subject) for `result = *[[sb a] c]`, and emits the `.s8` root
    over its two `OP_1` children with the two records.
  * `gen_op8ComputeNodes_eq` — the full DFS → exponent → render pipeline collapses to the
    locally-defined carrier `computeNodesOp8` (root rendered by the new `.s8` `renderNode` dispatch
    and `stampOfAcc` branch; the two children by `renderOp1Row`).
  * `gen_op8Trace_is_generated` — running the generator end-to-end yields exactly `computeNodesOp8`.
  * Non-vacuity: the 2-call fan-out, the active tail decomposition, the two records, and — the point
    of OP8 — the pushed autocons subject (child-one subject = `[sb a]` = cons(child-two result, row
    subject)), all inhabited by concrete terms and confirmed against `evalN`.

  DEFERRED, and why (reported precisely, not faked):

  * The **served-memory forest** `genOp8MemForest` is NOT built here, for exactly the reason the OP7
    slice deferred `genOp7MemForest`: a *meaningful* generated forest equality (the pattern of
    `Op1GenData.gen_memForest_eq` / `ConsGenMem.gen_consMemForest_eq`) is stated against an
    independently *committed* served-memory fixture whose cells and LogUp accumulator are *validated*
    by the honest commitment's `BindMemoryRow` / `MemoryNodesOK` proofs.  There is no committed OP8
    served-memory fixture: it is exactly the `.s8` served `ExactServedMemoryTrace` that is the
    deferred heavy CORE.  The OP8 served side is `requiredServedLookups.s8 = 0` (VACUOUS) and
    single-root (`kMem = 1`).  `Op2Gen.lean`/`Op3Gen.lean`/`Op7Gen.lean` deferred their forests for
    the same reason.

  * `op8DataOfGenerated`, `op8Data`, `op8Statement`, `BuildableNockExecution`, and any
    census/bind/specialization obligation — these need the `.s8` semantic CORE
    (`ExactExecutionSemanticData`), which must witness `e = *[[sb a] c]` with the pushed subject
    `[sb a]` (`sb = *[a b]`) AND the EC.8.1 cons well-formedness of the constructed subject.  That is
    the heavy focused Layer-2 pass, out of scope here.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

/-! ## A. The OP8 fixture nouns (`*[0 [8 [[1 3] [1 5]]]] = 5`) -/

/-- The row subject `a = 0`. -/
def op8Subject : Noun := .atom 0
/-- The helper formula `b = [1 3]` (an `OP_1` constant): `*[a b] = 3`. -/
def op8ChildFormulaB : Noun := .cell (.atom 1) (.atom 3)
/-- The helper evaluation `sb = *[0 [1 3]] = 3` (`= sf_evaluation_2`). -/
def op8Sb : Noun := .atom 3
/-- The consumer formula `c = [1 5]` (an `OP_1` constant): `*[[sb a] c] = 5`. -/
def op8ChildFormulaC : Noun := .cell (.atom 1) (.atom 5)
/-- The **pushed subject** `[sb a] = [3 0]` — the autocons of the helper result with the original
    subject. -/
def op8PushedSubject : Noun := .cell op8Sb op8Subject
/-- The formula tail `[b c]`. -/
def op8ParentTail : Noun := .cell op8ChildFormulaB op8ChildFormulaC
/-- The OP8 formula `[8 [b c]]`. -/
def op8ParentFormula : Noun := .cell (.atom 8) op8ParentTail
/-- The produced result `*[[sb a] c] = *[[3 0] [1 5]] = 5` (`= sf_evaluation_1`, the row result). -/
def op8Result : Noun := .atom 5

/-! ## B. The generator's `OP_8` DFS arm fires on the push formula `[8 [b c]]` -/

/-- **The `OP_8` DFS arm of `genComputeSkeleton` classifies the push `[8 [b c]]`** on the row
    subject `a`: it recurses on `b` against `a` (the helper `*[a b]` → `sb`) and then on `c` against
    the **autocons `[sb a]`** (the pushed subject → the consumer `*[[sb a] c]` → `result`), and
    emits the `.s8` root over the two `OP_1` children with the two committed records (formula-open
    `[8 [b c]] @3`, formula-tail `[b c] @2`).  Mirrors
    `genComputeSkeleton_op7` at fan-out 2 with the second child's SUBJECT the autocons of the first
    child's RESULT with the row subject (per `evalN`, `Reference.lean:118-123`). -/
theorem genComputeSkeleton_op8 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) op8Subject op8ParentFormula
      = .ok (.node (skelNode
            (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
              op8ChildFormulaC op8Sb op8Result)
            [⟨op8ParentFormula, op8ParentTail, 3, 0⟩, ⟨op8ParentTail, op8ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op8Subject op8ChildFormulaB op8Sb (.atom 1))
                [⟨op8ChildFormulaB, op8Sb, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op8PushedSubject op8ChildFormulaC op8Result (.atom 1))
                [⟨op8ChildFormulaC, op8Result, 3, 0⟩]) []],
          op8Result) := by
  show genComputeSkeleton ((n + 1) + 1) op8Subject op8ParentFormula = _
  simp only [genComputeSkeleton, op8ParentFormula, op8ParentTail, op8ChildFormulaB,
    op8ChildFormulaC, op8Subject, op8Sb, op8Result, op8PushedSubject]

/-! ## C. The compute render tree collapses to the locally-defined carrier `computeNodesOp8` -/

/-- The locally-defined `.s8`-over-two-`.s1` compute node carrier.  The root is rendered by the new
    `.s8` `renderNode` dispatch at `stampOfAcc.s8 0` (records at consecutive lines `1`,`2`); the two
    `OP_1` children are rendered by `renderOp1Row` at the BFS accumulators `2`,`3`.  The consumer
    child's subject is the pushed autocons `op8PushedSubject = [sb a]`. -/
def computeNodesOp8 (z α : K) : NTree (ComputeNode K) :=
  .node
    { skel := genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
        op8ChildFormulaC op8Sb op8Result
      stamp := stampOfAcc .s8 0
      row := renderOp8Row z α (stampOfAcc .s8 0)
        (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
          op8ChildFormulaC op8Sb op8Result) }
    [.node
        { skel := genSkelOp1 op8Subject op8ChildFormulaB op8Sb (.atom 1)
          stamp := stampOfAcc .s1 2
          row := renderOp1Row z α (stampOfAcc .s1 2)
            (genSkelOp1 op8Subject op8ChildFormulaB op8Sb (.atom 1)) } [],
     .node
        { skel := genSkelOp1 op8PushedSubject op8ChildFormulaC op8Result (.atom 1)
          stamp := stampOfAcc .s1 3
          row := renderOp1Row z α (stampOfAcc .s1 3)
            (genSkelOp1 op8PushedSubject op8ChildFormulaC op8Result (.atom 1)) } []]

/-- **The generator's emitted `OP_8` compute tree, rendered, is exactly `computeNodesOp8`.**  The
    DFS pass emits the `.s8` root over the two `OP_1` children; the exponent pass stamps the root at
    `stampOfAcc.s8 0` and the children at the BFS accumulators `2`,`3` (threaded by
    `subtreeRecordCount`); the render pass fires the new `.s8` `renderNode` dispatch on the root and
    reuses `renderOp1Row` on the children.  The compute-side Layer-1 analogue of
    `gen_op7ComputeNodes_eq` for OP8. -/
theorem gen_op8ComputeNodes_eq (z α : K) :
    mapNTree GenComputeRow.node
        (renderRows z α (assignExponents
          (.node (skelNode
            (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
              op8ChildFormulaC op8Sb op8Result)
            [⟨op8ParentFormula, op8ParentTail, 3, 0⟩, ⟨op8ParentTail, op8ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op8Subject op8ChildFormulaB op8Sb (.atom 1))
                [⟨op8ChildFormulaB, op8Sb, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op8PushedSubject op8ChildFormulaC op8Result (.atom 1))
                [⟨op8ChildFormulaC, op8Result, 3, 0⟩]) []])))
      = computeNodesOp8 z α := by
  have hroot : (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
      op8ChildFormulaC op8Sb op8Result).state = ComputeTable.State.s8 := rfl
  have hc0 : (genSkelOp1 op8Subject op8ChildFormulaB op8Sb (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hc1 : (genSkelOp1 op8PushedSubject op8ChildFormulaC op8Result (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, renderRows,
    renderNode, skelNode, hroot, hc0, hc1, Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, mapNTree, Nat.zero_add, Nat.add_zero]
  simp only [GenComputeRow.node, computeNodesOp8]

/-- **The generator really runs end-to-end on the OP8 program.**  Running the DFS pass
    `genComputeSkeleton 2 op8Subject op8ParentFormula` and rendering its tree yields exactly the
    rendered `.s8`-over-two-`.s1` carrier — nothing is hand-substituted for the generator. -/
theorem gen_op8Trace_is_generated (z α : K) :
    (genComputeSkeleton (K := K) 2 op8Subject op8ParentFormula).map
        (fun p => mapNTree GenComputeRow.node
          (renderRows z α (assignExponents p.1)))
      = .ok (computeNodesOp8 z α) := by
  rw [genComputeSkeleton_op8 0]
  exact congrArg Except.ok (gen_op8ComputeNodes_eq z α)

/-! ## D. Non-vacuity of the fan-out-2 / autocons-push shape -/

/-- OP8 spawns exactly TWO compute children. -/
theorem op8_fanout_two : ComputeTable.fanoutComp ComputeTable.State.s8 = 2 := rfl

/-- OP8 commits exactly TWO live memory records. -/
theorem op8_recordCount_two : Nock.Framework.recordCount ComputeTable.State.s8 = 2 := rfl

/-- The OP8 tail decomposition is active (`decActive.s8.f_th = decActive.s8.f_tt = true`), the
    enabler of the `tailCons` comparison role for `.s8`. -/
theorem op8_tail_decomposed :
    SemanticStrategy.decActive ComputeTable.State.s8 .f_th = true ∧
      SemanticStrategy.decActive ComputeTable.State.s8 .f_tt = true :=
  ⟨rfl, rfl⟩

/-- The active tail decomposition slots are genuinely `f_th ↦ b`, `f_tt ↦ c`. -/
theorem op8_tail_slots :
    (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
        op8ChildFormulaC op8Sb op8Result).decomposition .f_th (by decide) = op8ChildFormulaB ∧
      (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
        op8ChildFormulaC op8Sb op8Result).decomposition .f_tt (by decide) = op8ChildFormulaC :=
  ⟨rfl, rfl⟩

/-- Both subformula slots are live: AIR `sf1` is the consumer `([sb a], c, result)` and
    AIR `sf2` is the helper `(a, b, sb)`. -/
theorem op8_subformula_slots :
    P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 0 .formula = op8ChildFormulaC ∧
      P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 1 .formula = op8ChildFormulaB ∧
      P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 0 .result = op8Result :=
  ⟨rfl, rfl, rfl⟩

/-- **The autocons-push witness — the point of OP8.**  AIR slot `1` (helper) is evaluated
    against the ROW subject `a`, and AIR slot `0` (consumer) is evaluated against the
    **autocons `[sb a]`**: the computed helper result `sb` PAIRED WITH the original row subject `a`.
    `skeletonSubformula _ 0.subject = op8PushedSubject =.cell op8Sb op8Subject`, `op8Sb =
    skeletonSubformula _ 1.result`, and the pushed subject is neither the row subject nor the bare
    helper (`op8PushedSubject ≠ op8Subject` and `op8PushedSubject ≠ op8Sb`). -/
theorem op8_pushed_subject :
    P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 1 .subject = op8Subject ∧
      P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 0 .subject = op8PushedSubject ∧
      P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 1 .result = op8Sb ∧
      op8PushedSubject = .cell op8Sb op8Subject ∧
      op8PushedSubject ≠ op8Subject ∧
      op8PushedSubject ≠ op8Sb :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

/-- **The EC.8.1 cons role, Layer-1 face.**  The compute-AIR cons well-formedness check EC.8.1 reifies as `sf1_s = cons(sf2_e, s)` — the consumer subject is the cons of
    the helper result with the row subject.  At Layer 1 this is the structural identity
    `skeletonSubformula _ 0.subject = cons(skeletonSubformula _ 1.result, subject)`. -/
theorem op8_ec81_cons_present :
    P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 0 .subject
      = .cell (P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8)
          op8ParentTail op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 1 .result)
        op8Subject :=
  rfl

/-- **The push matches `evalN` (authoritative), with NO role-index flag (unlike OP7).**  The
    generator's pushed subject `op8PushedSubject = [sb a]` is exactly the follow-on subject `evalN`
    constructs: `evalN _ op8Subject op8ChildFormulaB = some op8Sb` (the helper `*[a b]`) and
    `evalN _ (.cell op8Sb op8Subject) op8ChildFormulaC = some op8Result` (the consumer `*[[sb a] c]`
    with the autocons `[sb a]` as subject) (`Reference.lean:118-123`, `evalN (.cell sb subj) c`). -/
theorem op8_subject_matches_evalN :
    Nock.evalN 2 op8Subject op8ChildFormulaB = some op8Sb ∧
      Nock.evalN 2 (.cell op8Sb op8Subject) op8ChildFormulaC = some op8Result :=
  ⟨rfl, rfl⟩

/-- The `formula_tail@2` record is genuinely committed at axis `2`: the OP8
    root's second memory record opens the formula tail `[b c]` at axis `2` with child `b`. -/
theorem op8_formulaTail_record_axis2 :
    P8Census.skeletonMemoryAxis (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 1 = 2 := rfl

/-- **The generated skeleton is semantically faithful to `evalFBy`.**  The capstone evaluator agrees
    with the generator's committed nouns: `*[0 [8 [[1 3] [1 5]]]] = 5`. -/
theorem gen_op8_evalFBy :
    FieldEmbedding.evalFBy 97 3 op8Subject op8ParentFormula = some op8Result := rfl

/-- Joint non-vacuity of the OP8 Layer-1 slice: fan-out 2, two records, active tail decomposition,
    the pushed autocons subject (child-one subject = `[sb a]` = cons(child-two result, row subject),
    per `evalN`), and the `formula_tail@2` record. -/
theorem op8_nonvacuous :
    ComputeTable.fanoutComp ComputeTable.State.s8 = 2 ∧
      Nock.Framework.recordCount ComputeTable.State.s8 = 2 ∧
      SemanticStrategy.decActive ComputeTable.State.s8 .f_th = true ∧
      P8Census.skeletonSubformula (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 0 .subject = op8PushedSubject ∧
      op8PushedSubject = .cell op8Sb op8Subject ∧
      op8PushedSubject ≠ op8Subject ∧
      Nock.evalN 2 (.cell op8Sb op8Subject) op8ChildFormulaC = some op8Result ∧
      P8Census.skeletonMemoryAxis (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail
        op8ChildFormulaB op8ChildFormulaC op8Sb op8Result) 1 = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl⟩


#print axioms genComputeSkeleton_op8
#print axioms gen_op8ComputeNodes_eq
#print axioms gen_op8Trace_is_generated
#print axioms op8_pushed_subject
#print axioms op8_ec81_cons_present
#print axioms op8_subject_matches_evalN
#print axioms gen_op8_evalFBy
#print axioms op8_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
