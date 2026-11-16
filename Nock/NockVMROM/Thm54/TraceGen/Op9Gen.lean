/-
  Nock/NockVMROM/Thm54/TraceGen/Op9Gen.lean

  LAYER 1 (generator side only).  The trace generator's
  compute-side emission AND the served-memory forest for the fan-out-2 invoke program

      `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`

  Here the axis atom is `b = 2`, the core formula `c = [1 [[1 7] [1 9]]]`, so
  `core = *[0 c] = [[1 7] [1 9]]` (a two-armed core), `arm = /[2 core] = [1 7]`, and the invoke
  `*[core arm] = *[[[1 7] [1 9]] [1 7]] = 7 = result` (verified against `evalN`,
  `Reference.lean:124-132`, and `evalFBy 97 3`).

  OP9 is the invoke row: state `.s9`, fan-out `2` (`fanoutComp.s9 = 2`), THREE live memory records
  (`recordCount.s9 = 3`) — the formula-open `[9 [b c]] @3`, the formula-tail `[b c] @2`, and the
  **served arm fetch** `⟨core, arm, b⟩` whose root is the computed core
  `sf_evaluation_1` (a mutated subject) and whose axis is the atom `b`.  Because
  `requiredServedLookups.s9 = 1` the served side is NON-VACUOUS for the first time, and because the
  arm-fetch record's root `core` is NOT a subtree of the program formula it seeds a SECOND served
  forest root, so the served forest is the first with `kMem = 2`.

  What lands here (all additive, kernel-clean, generic over any `[Field K]`):

  * `genComputeSkeleton_op9` — the generator's new `OP_9` DFS arm classifies `[9 [b c]]` on `0`,
    recurses on `c` (→ the core `sf1`), fetches the arm `slot b core` (the first generator dispatch
    that consults `Noun.slot` during emission), and recurses on `.cell core arm` against the computed
    core (→ `result`), emitting the `.s9` root over its two `OP_1` children with the THREE records.
  * `gen_op9ComputeNodes_eq` — the DFS → exponent → render pipeline collapses to the locally-defined
    carrier `computeNodesOp9` (root rendered by the new `.s9` `renderNode` dispatch and `stampOfAcc`
    branch; the two children by `renderOp1Row`).
  * `gen_op9Trace_is_generated` — running the generator end-to-end yields exactly `computeNodesOp9`.
  * `genOp9MemForest` / `gen_op9MemForest_eq` — the `kMem = 2` multi-root served memory forest
    (compute-core root + arm-read root) emitted as pure `encC` data and collapsing to the
    locally-defined node carrier `memForestOp9`, mirroring `Op0Gen.genOp0MemForest` /
    `gen_op0MemForest_eq`.
  * Non-vacuity: the 2-call fan-out, the three records with the arm-fetch record rooted at the
    computed core `sf1` at the (arbitrary) axis `b`, the two served forest roots, and the arm-read
    served record present with its axis, are all inhabited by concrete terms.

  DEFERRED, and why (reported precisely, not faked): the semantic CORE
  (`ExactExecutionSemanticData` / `ExactServedMemoryTrace` with the non-vacuous `semanticCoverage`
  matching the arm `Service`, the arbitrary-axis `ServiceWalk`, and the two-root timestamp
  aggregation), the `axisGates`/`AxisAtomComparisonCertificate` census bundle, and any
  `Data`/`BuildableNockExecution` transport — these are the deferred Layer-2 pass (design spec §3.6,
  §3.8).  This file commits ONLY the generator output as pure data and its equality to a local
  carrier; it does NOT claim the served forest satisfies `semanticCoverage`/`BindMemoryRow`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

/-! ## A. The OP9 fixture nouns (`*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`) -/

/-- The row subject `0`. -/
def op9Subject : Noun := .atom 0
/-- The axis atom `b = 2` (`formula_tail_head`); the arm is fetched at this axis. -/
def op9AxisAtom : Noun := .atom 2
/-- The computed core `core = *[0 c] = [[1 7] [1 9]]` (`sf_evaluation_1`). -/
def op9CoreNoun : Noun :=
  .cell (.cell (.atom 1) (.atom 7)) (.cell (.atom 1) (.atom 9))
/-- The core formula `c = tail(n2) = [1 [[1 7] [1 9]]]` (an `OP_1` constant returning the core). -/
def op9CoreFormula : Noun := .cell (.atom 1) op9CoreNoun
/-- The fetched arm `arm = /[2 core] = [1 7]` (an `OP_1` constant returning `7`). -/
def op9Arm : Noun := .cell (.atom 1) (.atom 7)
/-- The invoke result `*[core arm] = *[core [1 7]] = 7`. -/
def op9Result : Noun := .atom 7
/-- The formula tail `[b c]`. -/
def op9ParentTail : Noun := .cell op9AxisAtom op9CoreFormula
/-- The OP9 formula `[9 [b c]]`. -/
def op9ParentFormula : Noun := .cell (.atom 9) op9ParentTail

/-- The arm fetch is a genuine slot read: `/[2 core] = [1 7] = arm`. -/
theorem op9_slot : Nock.Noun.slot 2 op9CoreNoun = some op9Arm := by
  simp [op9CoreNoun, op9Arm, Nock.Noun.slot]

/-! ## B. The generator's `OP_9` DFS arm fires on the invoke formula `[9 [b c]]` -/

/-- **The `OP_9` DFS arm of `genComputeSkeleton` classifies the invoke `[9 [b c]]`** on `0`: it
    recurses on `c` (the `OP_1` core formula → `core = sf1`), fetches the arm `slot 2 core = [1 7]`
    (the first generator dispatch that consults `Noun.slot` during emission), and recurses on
    `.cell core arm` against the computed core (the `OP_1` arm formula → `result = 7`), emitting the
    `.s9` root over the two `OP_1` children with the THREE committed records (formula-open
    `[9 [b c]] @3`, formula-tail `[b c] @2`, arm fetch `[core arm] @2`).  Mirrors `genComputeSkeleton_op7` with the served
    third record. -/
theorem genComputeSkeleton_op9 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) op9Subject op9ParentFormula
      = .ok (.node (skelNode
            (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail op9AxisAtom
              op9CoreFormula op9CoreNoun op9Arm op9Result 2)
            [⟨op9ParentFormula, op9ParentTail, 3, 0⟩, ⟨op9ParentTail, op9AxisAtom, 2, 0⟩,
             ⟨op9CoreNoun, op9Arm, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op9Subject op9CoreFormula op9CoreNoun (.atom 1))
                [⟨op9CoreFormula, op9CoreNoun, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op9CoreNoun op9Arm op9Result (.atom 1))
                [⟨op9Arm, op9Result, 3, 0⟩]) []],
          op9Result) := by
  show genComputeSkeleton ((n + 1) + 1) op9Subject op9ParentFormula = _
  -- Keep `op9CoreNoun` FOLDED so the emitted core matches `op9_slot`'s LHS `slot 2 op9CoreNoun`.
  simp only [genComputeSkeleton, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula,
    op9Subject, op9Arm, op9Result, op9_slot]

/-! ## C. The compute render tree collapses to the locally-defined carrier `computeNodesOp9` -/

/-- The locally-defined `.s9`-over-two-`.s1` compute node carrier.  The root is rendered by the new
    `.s9` `renderNode` dispatch at `stampOfAcc.s9 0` (records at consecutive lines `1`,`2`,`3`); the
    two `OP_1` children are rendered by `renderOp1Row` at the BFS accumulators `3`,`4` (threaded by
    `subtreeRecordCount`, root record count `3`). -/
def computeNodesOp9 (z α : K) : NTree (ComputeNode K) :=
  .node
    { skel := genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail op9AxisAtom
        op9CoreFormula op9CoreNoun op9Arm op9Result 2
      stamp := stampOfAcc .s9 0
      row := renderOp9Row z α (stampOfAcc .s9 0)
        (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail op9AxisAtom
          op9CoreFormula op9CoreNoun op9Arm op9Result 2) }
    [.node
        { skel := genSkelOp1 op9Subject op9CoreFormula op9CoreNoun (.atom 1)
          stamp := stampOfAcc .s1 3
          row := renderOp1Row z α (stampOfAcc .s1 3)
            (genSkelOp1 op9Subject op9CoreFormula op9CoreNoun (.atom 1)) } [],
     .node
        { skel := genSkelOp1 op9CoreNoun op9Arm op9Result (.atom 1)
          stamp := stampOfAcc .s1 4
          row := renderOp1Row z α (stampOfAcc .s1 4)
            (genSkelOp1 op9CoreNoun op9Arm op9Result (.atom 1)) } []]

/-- **The generator's emitted `OP_9` compute tree, rendered, is exactly `computeNodesOp9`.**  The
    DFS pass emits the `.s9` root over the two `OP_1` children; the exponent pass stamps the root at
    `stampOfAcc.s9 0` and the children at the BFS accumulators `3`,`4` (threaded by
    `subtreeRecordCount`, root record count `recordCount.s9 = 3`); the render pass fires the new
    `.s9` `renderNode` dispatch on the root and reuses `renderOp1Row` on the children. -/
theorem gen_op9ComputeNodes_eq (z α : K) :
    mapNTree GenComputeRow.node
        (renderRows z α (assignExponents
          (.node (skelNode
            (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail op9AxisAtom
              op9CoreFormula op9CoreNoun op9Arm op9Result 2)
            [⟨op9ParentFormula, op9ParentTail, 3, 0⟩, ⟨op9ParentTail, op9AxisAtom, 2, 0⟩,
             ⟨op9CoreNoun, op9Arm, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op9Subject op9CoreFormula op9CoreNoun (.atom 1))
                [⟨op9CoreFormula, op9CoreNoun, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op9CoreNoun op9Arm op9Result (.atom 1))
                [⟨op9Arm, op9Result, 3, 0⟩]) []])))
      = computeNodesOp9 z α := by
  have hroot : (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail op9AxisAtom
      op9CoreFormula op9CoreNoun op9Arm op9Result 2).state = ComputeTable.State.s9 := rfl
  have hc0 : (genSkelOp1 op9Subject op9CoreFormula op9CoreNoun (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hc1 : (genSkelOp1 op9CoreNoun op9Arm op9Result (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, renderRows,
    renderNode, skelNode, hroot, hc0, hc1, Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, mapNTree, Nat.zero_add, Nat.add_zero]
  simp only [GenComputeRow.node, computeNodesOp9]

/-- **The generator really runs end-to-end on the OP9 program.**  Running the DFS pass
    `genComputeSkeleton 2 op9Subject op9ParentFormula` and rendering its tree yields exactly the
    rendered `.s9`-over-two-`.s1` carrier — nothing is hand-substituted for the generator. -/
theorem gen_op9Trace_is_generated (z α : K) :
    (genComputeSkeleton (K := K) 2 op9Subject op9ParentFormula).map
        (fun p => mapNTree GenComputeRow.node
          (renderRows z α (assignExponents p.1)))
      = .ok (computeNodesOp9 z α) := by
  rw [genComputeSkeleton_op9 0]
  exact congrArg Except.ok (gen_op9ComputeNodes_eq z α)

/-! ## D. Non-vacuity of the fan-out-2 / three-record / served-arm shape -/

/-- OP9 is a fan-out-`2` compute row. -/
theorem op9_fanout_two : ComputeTable.fanoutComp ComputeTable.State.s9 = 2 := rfl

/-- OP9 commits exactly THREE live memory records. -/
theorem op9_recordCount_three : Nock.Framework.recordCount ComputeTable.State.s9 = 3 := rfl

/-- OP9's tail decomposition is active (`decActive.s9.f_th = decActive.s9.f_tt = true`), the
    enabler of the `tailCons` comparison role. -/
theorem op9_tail_decomposed :
    SemanticStrategy.decActive ComputeTable.State.s9 .f_th = true ∧
      SemanticStrategy.decActive ComputeTable.State.s9 .f_tt = true :=
  ⟨rfl, rfl⟩

/-- **The computed-core child:** the second subformula slot's SUBJECT is the computed core
    `[[1 7] [1 9]]`, NOT the row subject `0` — the invoke's subject is a mutated subject. -/
theorem op9_computed_core_child :
    P8Census.skeletonSubformula (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail
        op9AxisAtom op9CoreFormula op9CoreNoun op9Arm op9Result 2) 1 .subject = op9CoreNoun ∧
      op9CoreNoun ≠ op9Subject :=
  ⟨rfl, by decide⟩

/-- The second subformula slot's FORMULA is the served arm `[1 7]`. -/
theorem op9_invoke_formula_is_arm :
    P8Census.skeletonSubformula (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail
        op9AxisAtom op9CoreFormula op9CoreNoun op9Arm op9Result 2) 1 .formula = op9Arm :=
  rfl

/-- **The served arm-fetch record is genuinely committed at axis `b = 2`**: the
    OP9 root's third memory record opens the computed core `sf1` at the (arbitrary) axis `2`. -/
theorem op9_armRecord_axis_two :
    P8Census.skeletonMemoryAxis (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail
        op9AxisAtom op9CoreFormula op9CoreNoun op9Arm op9Result 2) 2 = 2 := rfl

/-- **The served arm-fetch record's root is the computed core `sf_evaluation_1`**: the third record's root equals the first subformula slot's
    result (the core eval), the first time a compute record's root is a subformula evaluation rather
    than a subtree of the formula. -/
theorem op9_armRecord_root_is_sf1 :
    (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail op9AxisAtom op9CoreFormula
        op9CoreNoun op9Arm op9Result 2).memoryRecord 2 (by decide) =
      ⟨op9CoreNoun, op9Arm, 2⟩ ∧
      P8Census.skeletonSubformula (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail
        op9AxisAtom op9CoreFormula op9CoreNoun op9Arm op9Result 2) 0 .result = op9CoreNoun :=
  ⟨rfl, rfl⟩

/-- **The generated skeleton is semantically faithful to `evalFBy`.**  The capstone evaluator agrees
    with the generator's committed nouns: `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`. -/
theorem gen_op9_evalFBy :
    FieldEmbedding.evalFBy 97 3 op9Subject op9ParentFormula = some op9Result := by
  simp [FieldEmbedding.evalFBy, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom,
    op9CoreFormula, op9CoreNoun, op9Arm, op9Result, Nock.Noun.slot]

/-- Joint non-vacuity of the OP9 Layer-1 compute slice: fan-out 2, three records, active tail
    decomposition, the computed-core invoke subject, and the served arm-fetch record rooted at the
    computed core `sf1` at axis `2`. -/
theorem op9_compute_nonvacuous :
    ComputeTable.fanoutComp ComputeTable.State.s9 = 2 ∧
      Nock.Framework.recordCount ComputeTable.State.s9 = 3 ∧
      SemanticStrategy.decActive ComputeTable.State.s9 .f_th = true ∧
      P8Census.skeletonSubformula (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail
        op9AxisAtom op9CoreFormula op9CoreNoun op9Arm op9Result 2) 1 .subject = op9CoreNoun ∧
      op9CoreNoun ≠ op9Subject ∧
      P8Census.skeletonMemoryAxis (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail
        op9AxisAtom op9CoreFormula op9CoreNoun op9Arm op9Result 2) 2 = 2 :=
  ⟨rfl, rfl, rfl, rfl, by decide, rfl⟩

/-! ## E. The `kMem = 2` multi-root served memory forest

    The invoke's served forest is the first with TWO serviced roots, because the arm-fetch record
    `mr3 = ⟨core, arm, b⟩` is rooted at the COMPUTED core `sf_evaluation_1` — a mutated subject that
    is not a subtree of the program formula — so it seeds a second forest root beside the syntactic
    formula root.

    * **Root `A`** (rooted at the formula `[9 [b c]]`) serves the two syntactic records through a
      nested `read`/`verify` descent: `mr1 = ⟨formula, formula_tail, 3⟩` (open the whole formula at
      axis `3`) and `mr2 = ⟨formula_tail, b, 2⟩` (open the tail at axis `2` to expose the arm axis
      `b`).
    * **Root `B`** (rooted at the computed core `core`) serves the ARM FETCH `mr3 = ⟨core, arm, b⟩`
      as a genuine **arbitrary-axis** read at axis `b = 2` — the non-vacuous served lookup.

    The forest is emitted as pure data through a single encoder-parametrized builder `op9ForestData`;
    the generator instantiates it at the computable `encC z`, the local carrier at the idealized
    `GlobalCarryRecognizer.enc z`, and `gen_op9MemForest_eq` collapses one to the other via `encC_eq`.
    This mirrors `Op0Gen.genOp0MemForest` / `gen_op0MemForest_eq` (the OP0 Layer-1 shape: forest +
    equality + non-vacuity, NO `Data`/transport). -/

/-- The core tail `coreTail = /[3 core] = [1 9]` (the sibling of the fetched arm inside `core`). -/
def op9CoreTail : Noun := .cell (.atom 1) (.atom 9)

/-- A `read_root` memory-row skeleton at an ARBITRARY axis `ax` (the generic `memReadSkel` bakes in
    axis `3`; the OP9 arm read and formula-tail read are at axis `2`). -/
def memReadSkelAx (root child : Noun) (ax : ℕ) : MemoryRowSkeleton where
  state := .read_root
  parent := root
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then root else .atom 0
  memoryRecord := fun _ => ⟨root, child, ax⟩

/-- A `verify_child` memory-row skeleton at an ARBITRARY axis `ax`. -/
def memVerifySkelAx (root child : Noun) (ax : ℕ) : MemoryRowSkeleton where
  state := .verify_child
  parent := child
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => child
  memoryRecord := fun _ => ⟨root, child, ax⟩

/-- Package a served pub with its skeleton and Nat record exponent into a `GenMemoryRow` (the OP9
    analogue of `Op0Gen.gMemRow`, generic over any `[Field K]`). -/
def gMemRow9 (sk : MemoryRowSkeleton) (e : ℕ) (z : K) (pub : MemoryTable.Pub K) : GenMemoryRow K where
  skel := sk
  stamp := { state := sk.state, recordExponent := e }
  row := (sk.state, (memInputs z, pub))

/-- A `read_root` served pub: root fingerprint in `pt`/`lc`, the served record `⟨root, child, ax⟩`
    at timestamp `ts` in `mem`. -/
def op9ReadPub (E : Noun → ComputeTable.FP K) (root child : Noun) (ax : ℕ) (ts : K) :
    MemoryTable.Pub K where
  st := .read_root
  pt := ⟨E root, 0, 0⟩
  lc := ⟨E root, 0, 0⟩
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := ⟨E root, E child, (ax : K), ts⟩
  ipre := 0
  icur := 0

/-- A `decompose` served pub: parent fingerprint in `pt`, its two children `head`/`tail` in
    `lc`/`rc`; no live record. -/
def op9DecPub (E : Noun → ComputeTable.FP K) (root head tail : Noun) : MemoryTable.Pub K where
  st := .decompose
  pt := ⟨E root, 0, 0⟩
  lc := ⟨E head, 0, 0⟩
  rc := ⟨E tail, 0, 0⟩
  lcSt := .halt
  rcSt := .read_root
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0

/-- A `verify_child` served pub: child fingerprint in `pt`/`lc`, re-asserting the served record
    `⟨root, child, ax⟩` at timestamp `ts`. -/
def op9VerifyPub (E : Noun → ComputeTable.FP K) (root child : Noun) (ax : ℕ) (ts : K) :
    MemoryTable.Pub K where
  st := .verify_child
  pt := ⟨E child, 0, 0⟩
  lc := ⟨E child, 0, 0⟩
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := ⟨E root, E child, (ax : K), ts⟩
  ipre := 0
  icur := 0

/-- A terminal `halt` served pub for the atom `a`. -/
def op9HaltPub (E : Noun → ComputeTable.FP K) (a : ℕ) : MemoryTable.Pub K where
  st := .halt
  pt := ⟨E (.atom a), 0, 0⟩
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0

/-- **The encoder-parametrized `kMem = 2` served forest.**  Root `A` (six rows) serves the two
    syntactic records `mr1 = ⟨formula, formula_tail, 3⟩` and `mr2 = ⟨formula_tail, b, 2⟩` through a
    nested `read`/`verify` descent (the head atom `9` halted); root `B` (three rows) serves the
    served arm fetch `mr3 = ⟨core, arm, 2⟩` on the COMPUTED core.  Record timestamps `α¹, α², α³`
    match the three compute-record exponents (`stampOfAcc.s9`).  Instantiating `E := encC z` gives
    the generated forest; `E := enc z` gives the carrier. -/
def op9ForestData (E : Noun → ComputeTable.FP K) (α z : K) :
    List (NTree (GenMemoryRow K)) :=
  [ .node (gMemRow9 (memReadSkelAx op9ParentFormula op9ParentTail 3) 1 z
            (op9ReadPub E op9ParentFormula op9ParentTail 3 (α ^ 1)))
      [.node (gMemRow9 (memDecomposeSkel op9ParentFormula (.atom 9) op9ParentTail) 0 z
                (op9DecPub E op9ParentFormula (.atom 9) op9ParentTail))
        [.node (gMemRow9 (memHaltSkel 9) 0 z (op9HaltPub E 9)) [],
         .node (gMemRow9 (memReadSkelAx op9ParentTail op9AxisAtom 2) 2 z
                  (op9ReadPub E op9ParentTail op9AxisAtom 2 (α ^ 2)))
          [.node (gMemRow9 (memVerifySkelAx op9ParentFormula op9ParentTail 3) 1 z
                    (op9VerifyPub E op9ParentFormula op9ParentTail 3 (α ^ 1)))
            [.node (gMemRow9 (memDecomposeSkel op9ParentTail op9AxisAtom op9CoreFormula) 0 z
                      (op9DecPub E op9ParentTail op9AxisAtom op9CoreFormula))
              [.node (gMemRow9 (memVerifySkelAx op9ParentTail op9AxisAtom 2) 2 z
                        (op9VerifyPub E op9ParentTail op9AxisAtom 2 (α ^ 2))) []]]]]],
    .node (gMemRow9 (memReadSkelAx op9CoreNoun op9Arm 2) 3 z
            (op9ReadPub E op9CoreNoun op9Arm 2 (α ^ 3)))
      [.node (gMemRow9 (memDecomposeSkel op9CoreNoun op9Arm op9CoreTail) 0 z
                (op9DecPub E op9CoreNoun op9Arm op9CoreTail))
        [.node (gMemRow9 (memVerifySkelAx op9CoreNoun op9Arm 2) 3 z
                  (op9VerifyPub E op9CoreNoun op9Arm 2 (α ^ 3))) []]] ]

/-- **`genOp9MemForest`.**  The generated `kMem = 2` served memory forest of the invoke program,
    emitted as pure data with the computable `encC z` fingerprints. -/
def genOp9MemForest (z α : K) : List (NTree (GenMemoryRow K)) :=
  op9ForestData (encC z) α z

/-- The locally-defined served-forest node carrier: the same two-root topology emitted with the
    idealized `GlobalCarryRecognizer.enc z` fingerprints and projected to `MemoryNode`s. -/
noncomputable def memForestOp9 (z α : K) : List (NTree (HonestCommitment.MemoryNode K)) :=
  (op9ForestData (fun n => GlobalCarryRecognizer.enc z n) α z).map (mapNTree GenMemoryRow.node)

/-- **The generated served forest's `.node` projection is exactly `memForestOp9`.**  Every served
    cell/record fingerprint collapses `encC → enc` (`Encode.encC_eq`); the `kMem = 2` two-root
    topology, the nested `read`/`verify` descent of root `A`, and the arbitrary-axis arm read of
    root `B` are reproduced verbatim. -/
theorem gen_op9MemForest_eq (z α : K) :
    (genOp9MemForest z α).map (mapNTree GenMemoryRow.node) = memForestOp9 z α := by
  unfold genOp9MemForest memForestOp9
  rw [show (encC z : Noun → ComputeTable.FP K)
        = (fun n => GlobalCarryRecognizer.enc z n) from funext (fun n => encC_eq z n)]

/-! ## F. Non-vacuity of the `kMem = 2` served coverage -/

/-- **The served forest has TWO serviced roots** — the first with `kMem = 2`. -/
theorem genOp9MemForest_two_roots (z α : K) : (genOp9MemForest z α).length = 2 := rfl

/-- **The second root serves the arm fetch on the computed core.**  Root `B`'s `read_root` label
    carries exactly the arm-fetch record `⟨enc core, enc arm, b, α³⟩` at the ARBITRARY axis `b = 2`
    — the non-vacuous served lookup rooted at the mutated core `sf_evaluation_1`. -/
theorem genOp9MemForest_arm_record (z α : K) :
    ((genOp9MemForest z α)[1]?).map (fun t => t.label.row.2.2.mem)
      = some ⟨encC z op9CoreNoun, encC z op9Arm, (2 : K), α ^ 3⟩ := rfl

/-- The second root's served read is a genuine `read_root` state whose skeleton opens the computed
    core `core` at the arm axis `b = 2`. -/
theorem genOp9MemForest_arm_read_state (z α : K) :
    ((genOp9MemForest z α)[1]?).map (fun t => (t.label.skel.state, t.label.skel.parent))
      = some (MemoryTable.MState.read_root, op9CoreNoun) := rfl

/-- **The arm-read record's root is the computed core, not a formula subtree.**  Root `B`'s served
    record root fingerprint is `enc core` (the computed core `sf_evaluation_1`), and `core` is not
    the formula `[9 [b c]]` — this is what forces the SECOND forest root. -/
theorem genOp9MemForest_arm_root_is_core (z : K) :
    op9CoreNoun ≠ op9ParentFormula := by decide

/-- Joint non-vacuity of the OP9 served side: two serviced roots, the arm fetch served at the
    arbitrary axis `b = 2` on the computed core, whose root differs from the formula. -/
theorem op9_served_nonvacuous (z α : K) :
    (genOp9MemForest z α).length = 2 ∧
      ((genOp9MemForest z α)[1]?).map (fun t => t.label.row.2.2.mem)
        = some ⟨encC z op9CoreNoun, encC z op9Arm, (2 : K), α ^ 3⟩ ∧
      op9CoreNoun ≠ op9ParentFormula :=
  ⟨rfl, rfl, by decide⟩


#print axioms genComputeSkeleton_op9
#print axioms gen_op9ComputeNodes_eq
#print axioms gen_op9Trace_is_generated
#print axioms op9_computed_core_child
#print axioms op9_armRecord_root_is_sf1
#print axioms gen_op9_evalFBy
#print axioms op9_compute_nonvacuous
#print axioms gen_op9MemForest_eq
#print axioms genOp9MemForest_two_roots
#print axioms genOp9MemForest_arm_record
#print axioms genOp9MemForest_arm_read_state
#print axioms op9_served_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
