/-
  Nock/NockVMROM/Thm54/TraceGen/Op3Gen.lean

  The trace generator's compute-side emission for the
  nonterminal cell-test program `*[subjectS [3 [0 2]]]`.  Structurally OP3 mirrors
  OP4 exactly (state `.s3`: one recursive call `*[a b]` plus one size window) EXCEPT the
  produced-result gate is the *total* cell-test `?` (`Nock.Noun.wut`: `0` on a cell, `1` on an atom)
  in place of OP4's `incMod` (increment).

  The recursive call is reused verbatim from the OP0 slice: `*[subjectS [0 2]] = /[2 subjectS] =
  resultS`, the already-proven served child `servedNode`.  Nothing about the
  served OP0 child is re-derived; only the `.s3` parent is fresh.

  What lands here (all additive, kernel-clean):

  * `genComputeSkeleton_op3` — the generator's new `OP_3` DFS arm classifies `[3 [0 2]]` on
    `subjectS`, recurses through the `OP_0` axis read, and emits the `.s3` parent skeleton over the
    served `.s0` child with produced result `? resultS`.
  * `gen_op3ComputeNodes_eq` — the full DFS → exponent → render pipeline collapses (via `encC = enc`
    and the reused `renderOp0Row_eq`) to the concrete `.s3`-over-`.s0` compute node tree
    `computeNodesOp3`, exercising the new `.s3` `renderNode` dispatch and `stampOfAcc` branch.
  * Non-vacuity: the `.s3` size window is genuinely inhabited by `resultS`, and the `wut` gate
    genuinely discriminates — `? resultS = 1` (atom) versus `? subjectS = 0` (cell).

  STATUS of the Layer-2 released statement (updated; the hard compute site is now DONE):

  * The genuinely-new `.s3`/`wut` PARENT COMPUTE ROW is built and proven kernel-clean in
    `Nock/NockVMROM/Thm54/Op3Statement.lean`: `op3ParentRowS`, its accepted `Vcomp`
    (`op3ParentS_accepts` — the `.s3` `evalV` block discharged through `enc_wut_eq`, using the
    `wut` produced-result gate and `servedSeed = -1`), its two-row `RVT` compute tree
    (`op3ComputeTreeS_rvt`), its full `ComputeRowSemanticData` (`op3ParentRowData`), its
    `LocalOpcodeCertificate.s3` (`op3ParentCertificate_nonempty`), and its derived Nock semantics
    (`op3ParentS_semantics`: a real ROM `?`-step + a bounded `evalFBy` producing `?(resultS)`).
    All decls are `⊆ {propext, Classical.choice, Quot.sound}`.

  * That holds for the COMPUTE side (above) but NOT the MEMORY side.  The
    served-memory forest's root `A` in `MultiRootServedFixture.lean` is rooted at
    `encS parentFormulaS` and threads `parentRecordS = ⟨encS parentFormulaS, encS formulaS, 3, α⟩`
    (the parent row's `mr1`, an active `rawRequests` entry) through its nine rows, census
    distinctness, the NMR bridge, and every downstream reassembly (`execS`, `semanticDataS`,
    `servedMemoryTraceS`, `dataM`, `residualM`, `statementM`).  Because the head atom changes
    (`.atom 4 →.atom 3`), `encS parentFormulaS` changes, so root `A` and the whole
    `MultiRootServedFixture` (2255 L) + `MultiRootHonestCommitment` (1105 L) reassembly must be
    re-derived for `.s3` before an `op3Execution : BuildableNockExecution` and `op3Statement` can be
    assembled.  This is a ~3300-line CLONE (timestamp-based distinctness ports verbatim; the
    noun-encoding-dependent `norm_num`/acceptance/realization proofs recompute), not a shallow
    parameter swap — so per the task's escape clause the memory-forest clone is deferred, and the
    coherent green partial delivered is the compute-side core in `Op3Statement.lean`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.Op0Gen
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
import Nock.NockVMROM.Thm54.SizeWindowCounting

namespace Nock.NockVMROM.Thm54.TraceGen

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment

noncomputable section

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## A. The `.s3` parent nouns (cell-test over the reused OP0 child) -/

/-- The `OP_3` head atom. -/
def op3ParentHeadS : Noun := .atom 3

/-- The `OP_3` cell-test formula `[3 [0 2]]`: cell-test of the axis read reused from the OP0 slice. -/
def op3ParentFormulaS : Noun := .cell op3ParentHeadS formulaS

/-- The produced result of `*[subjectS [3 [0 2]]] = ?*[subjectS [0 2]] = ? resultS`.  Since
    `resultS = /[2 subjectS] =.atom 7` is an atom, the cell-test yields `.atom 1`. -/
def op3ParentResultS : Noun := Nock.Noun.wut resultS

/-! ## B. The generator's `OP_3` DFS arm fires on the cell-test formula `[3 [0 2]]` -/

/-- **The `OP_3` DFS arm of `genComputeSkeleton` classifies the cell-test `[3 [0 2]]`** on
    `subjectS`: it recurses on the axis read `[0 2]` (the `OP_0` arm), cell-tests the call's result
    `resultS = /[2 subjectS]` to `op3ParentResultS = ? resultS`, and emits the `.s3` parent skeleton
    over the served `.s0` child.  Mirrors `genComputeSkeleton_op4` with
    `wut` (total) in place of `Noun.lus` (partial). -/
theorem genComputeSkeleton_op3 (n : ℕ) :
    genComputeSkeleton (K := K97cubic) (n + 2) subjectS op3ParentFormulaS
      = .ok (.node (skelNode
            (genSkelOp3 subjectS op3ParentFormulaS (.atom 3) formulaS subjectS formulaS resultS
              op3ParentResultS)
            [⟨op3ParentFormulaS, formulaS, 3, 0⟩])
            [.node (skelNode (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2)
                [⟨formulaS, tailS, 3, 0⟩, ⟨subjectS, resultS, 2, 0⟩]) []],
          op3ParentResultS) := by
  show genComputeSkeleton ((n + 1) + 1) subjectS op3ParentFormulaS = _
  simp only [genComputeSkeleton, op3ParentFormulaS, op3ParentHeadS, formulaS, headS, tailS,
    slot_subjectS, op3ParentResultS]

/-! ## C. The compute render tree collapses to a concrete `.s3`-over-`.s0` node tree -/

/-- The committed `.s3` parent compute node, rendered from its generated skeleton at the root
    exponents (`stampOfAcc.s3 0`).  Its evaluation column encodes `op3ParentResultS = ? resultS`,
    its single subformula slot carries the reused OP0 call's `(subjectS, formulaS, resultS)`, and its
    one live record opens `[3 [0 2]]` at axis `3` (child the tail `[0 2]`). -/
def op3ParentNode : ComputeNode K97cubic where
  skel := genSkelOp3 subjectS op3ParentFormulaS (.atom 3) formulaS subjectS formulaS resultS
    op3ParentResultS
  stamp := stampOfAcc .s3 0
  row := renderOp3Row servedSeed fixtureAlpha (stampOfAcc .s3 0)
    (genSkelOp3 subjectS op3ParentFormulaS (.atom 3) formulaS subjectS formulaS resultS
      op3ParentResultS)

/-- The generated `OP_3[OP_0]` compute node tree: the `.s3` cell-test parent over the reused,
    already-proven `.s0` served child `servedNode`. -/
def computeNodesOp3 : NTree (ComputeNode K97cubic) :=
  .node op3ParentNode [.node servedNode []]

/-- **The generator's emitted `OP_3[OP_0]` compute tree, rendered, is exactly `computeNodesOp3`.**
    The DFS pass (`genComputeSkeleton_op3`) emits the `.s3` parent over the `.s0` child; the exponent
    pass stamps the root at `stampOfAcc.s3 0` and the child at `stampOfAcc.s0 1`; the render pass
    fires the new `.s3` `renderNode` dispatch on the parent and reuses `renderOp0Row_eq` for the
    child (collapsing it to the committed `servedRow`).  The compute-side analogue of
    `gen_op0ComputeNodes_eq` for OP3. -/
theorem gen_op3ComputeNodes_eq :
    mapNTree GenComputeRow.node
        (renderRows servedSeed fixtureAlpha (assignExponents
          (.node (skelNode
            (genSkelOp3 subjectS op3ParentFormulaS (.atom 3) formulaS subjectS formulaS resultS
              op3ParentResultS)
            [⟨op3ParentFormulaS, formulaS, 3, 0⟩])
            [.node (skelNode (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2)
                [⟨formulaS, tailS, 3, 0⟩, ⟨subjectS, resultS, 2, 0⟩]) []])))
      = computeNodesOp3 := by
  have hparent : (genSkelOp3 subjectS op3ParentFormulaS (.atom 3) formulaS subjectS formulaS resultS
      op3ParentResultS).state = ComputeTable.State.s3 := rfl
  have hserved : (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2).state
      = ComputeTable.State.s0 := rfl
  simp only [assignExponents, assignTree, assignList, renderRows,
    renderNode, skelNode, hparent, hserved, Nock.Framework.recordCount, List.map_nil,
    List.map_cons, mapNTree, Nat.zero_add]
  simp only [GenComputeRow.node, computeNodesOp3, op3ParentNode, servedNode]
  rw [renderOp0Row_eq]
  rfl

/-- **The generator really runs end-to-end on the OP3 program.**  Running the DFS pass
    `genComputeSkeleton 2 subjectS op3ParentFormulaS` and rendering its tree yields exactly the
    rendered `.s3`-over-`.s0` compute tree — nothing is hand-substituted for the generator. -/
theorem gen_op3Trace_is_generated :
    (genComputeSkeleton (K := K97cubic) 2 subjectS op3ParentFormulaS).map
        (fun p => mapNTree GenComputeRow.node
          (renderRows servedSeed fixtureAlpha (assignExponents p.1)))
      = .ok computeNodesOp3 := by
  rw [genComputeSkeleton_op3 0]
  exact congrArg Except.ok gen_op3ComputeNodes_eq

/-! ## D. Non-vacuity of the `.s3` size window and the `wut` produced-result gate -/

/-- The `OP_3` cell-test requires exactly one size window. -/
theorem op3_requiredSizeWindows : SemanticTrace.requiredSizeWindows ComputeTable.State.s3 = 1 := rfl

/-- The `OP_3` parent's required size window is genuinely inhabited: exactly one bounded power
    window, the call's result `resultS`. -/
theorem op3_sizeWindow_inhabited :
    SizeWindowCounting.requiredSizeWindowNouns
        (genSkelOp3 subjectS op3ParentFormulaS (.atom 3) formulaS subjectS formulaS resultS
          op3ParentResultS)
      = [resultS] := rfl

/-- The `OP_3` produced-result gate: `? resultS = op3ParentResultS`. -/
theorem op3_wut_gate : Nock.Noun.wut resultS = op3ParentResultS := rfl

/-- The `wut` gate on the concrete atom result `resultS =.atom 7`: an atom cell-tests to `1`. -/
theorem op3_wut_gate_atom : Nock.Noun.wut resultS = Noun.atom 1 := rfl

/-- The `wut` gate genuinely discriminates: the cell `subjectS = [7 9]` cell-tests to `0`, whereas
    the atom `resultS` cell-tests to `1` — the produced-result relation is non-trivial, not constant. -/
theorem op3_wut_gate_cell : Nock.Noun.wut subjectS = Noun.atom 0 := rfl

/-- Joint non-vacuity of the OP3 slice: the DFS arm fires on `[3 [0 2]]`, the `.s3` size window is
    inhabited by `resultS`, and the `wut` gate discriminates cell (`0`) from atom (`1`). -/
theorem op3_nonvacuous :
    SemanticTrace.requiredSizeWindows ComputeTable.State.s3 = 1 ∧
      SizeWindowCounting.requiredSizeWindowNouns
        (genSkelOp3 subjectS op3ParentFormulaS (.atom 3) formulaS subjectS formulaS resultS
          op3ParentResultS) = [resultS] ∧
      Nock.Noun.wut resultS = op3ParentResultS ∧
      Nock.Noun.wut resultS = Noun.atom 1 ∧
      Nock.Noun.wut subjectS = Noun.atom 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end


#print axioms genComputeSkeleton_op3
#print axioms gen_op3ComputeNodes_eq
#print axioms gen_op3Trace_is_generated
#print axioms op3_sizeWindow_inhabited
#print axioms op3_wut_gate
#print axioms op3_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
