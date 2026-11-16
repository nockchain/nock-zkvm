
import Nock.NockVMROM.Thm54.TraceGen.Demo
import Nock.NockVMROM.Thm54.TraceGen.Encode
import Nock.NockVMROM.Thm54.TraceGen.GenMem

/-!
# A computable replica of the memory-forest builder

`genMemForestFromTree` (`GenMem.lean`) is `noncomputable` for exactly two reasons, both of which
come from `MemoryTable` and neither of which is about the field arithmetic:

* `MemoryTable.pwScaleExp K := Nat.size (ringChar K) - 1`, and `ringChar K` is chosen by
  `Classical.choose`, so it has no code;
* `MemoryTable.nockAxisOf`, which recovers an axis from its field cast with `Classical.epsilon`
  (used by `formRReadPw` / `formRReadCounts` in the read-row public values).

This file copies the nine builder definitions (`GenMem.lean:781-1180`, text unchanged apart from the
renaming `tw_*`) and replaces those two classical constants by explicit computable data:
`ScaleExp.e K` for `pwScaleExp K`, and the axis `ax` itself for `nockAxisOf (ax : K)`.
`Gen.lean` and `GenMem.lean` are not touched, and `implemented_by` is not used: the executable calls
the replica directly.
-/

namespace TraceDemo.Compute

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

/-- A computable stand-in for `Nat.size (ringChar K) - 1`. -/
class ScaleExp (K : Type) where
  e : ℕ

instance : ScaleExp (ZMod 97) := ⟨Nat.size 97 - 1⟩

variable {K : Type} [Field K] [ScaleExp K]

/-- `MemoryTable.formRC` with `pwScaleExp K` replaced by `ScaleExp.e K`. -/
def tw_formRC (lmb : K) (ax : ℕ) : K :=
  let n := ScaleExp.e K
  lmb ^ n +
    ((List.range n).map (fun j =>
      (if MemoryTable.formRCertBit ax j then (1 : K) else 0) * lmb ^ (n - (j + 1)))).sum

/-- `MemoryTable.formRReadPw` at a record whose stored axis is `(ax : K)`, `nockAxisOf` replaced by `ax`. -/
def tw_formRReadPw (lmb : K) (ax : ℕ) (ts : K) : K :=
  lmb ^ ScaleExp.e K * MemoryTable.formRT lmb ax * ts

def tw_formRReadCounts (lmb : K) (ax : ℕ) (ts : K) : K :=
  MemoryTable.formRT lmb ax * tw_formRC lmb ax * ts

def tw_annotatedVerifyPub (E : Noun → ComputeTable.FP K) (root child : Noun)
    (ax : ℕ) (ts : K) (lcCell : MemoryTable.Cell K)
    (ipre icur : K) (lmb : K) : MemoryTable.Pub K where
  st := .verify_child
  pt := ⟨E child,
         lcCell.indicator + lmb ^ ScaleExp.e K * ts,
         lcCell.counts + lmb ^ ScaleExp.e K * ts⟩
  lc := lcCell
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := ⟨E root, E child, (ax : K), ts⟩
  ipre := ipre
  icur := icur
  ver := false
  lambda? := some lmb

/-- Annotated read pub: indicator/counts propagated from given lc cell.
    `ipre`/`icur` are the LogUp accumulator pair.  Honest `ver = true`
    (the paper; generator: `ver := (state = read_root)`).
    **A-bearing**: the record stores the Nock axis nat-cast and `cprime?` is
    unset.  The leftover subtracts the Form R read weights `formRReadPw`/`formRReadCounts` of
    that record, i.e. `λ^{n−1}·T·ts` and `T·C'·ts` with `(T, C') = (formRT λ a, formRC λ a)`,
    `a = nockAxisOf (ax : K)` — exactly the `read_root` `eqBlk` on the executed row
    `MemoryRowTemplate.encodeRow` of this row at the same `λ`. -/
def tw_annotatedReadPub (E : Noun → ComputeTable.FP K) (root child : Noun)
    (ax : ℕ) (ts : K) (lcCell : MemoryTable.Cell K)
    (ipre icur : K) (lmb : K) : MemoryTable.Pub K where
  st := .read_root
  pt := ⟨E root,
         lcCell.indicator - tw_formRReadPw lmb ax ts,
         lcCell.counts - tw_formRReadCounts lmb ax ts⟩
  lc := lcCell
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := ⟨E root, E child, (ax : K), ts⟩
  ipre := ipre
  icur := icur
  ver := true
  lambda? := some lmb


def tw_genAnnotatedVerify (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    : NTree (GenMemoryRow K) × MemoryTable.Cell K :=
  (.node (gMemRow9 (memVerifySkelAx root child ax) recordExp z
      (tw_annotatedVerifyPub E root child ax ts (genAnnotatedNounWalk E z lmb child).2 0 0 lmb))
    [(genAnnotatedNounWalk E z lmb child).1],
   (tw_annotatedVerifyPub E root child ax ts (genAnnotatedNounWalk E z lmb child).2 0 0 lmb).pt)

/-- Annotated axis descent: builds the decomposition chain with correct indicator/counts.
    Returns the list of children to place under the parent and the pt cell of the root. -/
def tw_genAnnotatedDescent (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ)
    : List (NTree (GenMemoryRow K)) × MemoryTable.Cell K :=
  if remainingAxis < 2 then
    let (vt, vc) := tw_genAnnotatedVerify E z lmb root child recAxis ts recordExp
    ([vt], vc)
  else
    let hd := formulaHead currentNoun
    let tl := formulaTail currentNoun
    if axisTopBit remainingAxis then
      let (headWalk, lcCell) := genAnnotatedNounWalk E z lmb hd
      let (tailTrees, tailCell) :=
        tw_genAnnotatedDescent E z lmb root child recAxis ts recordExp tl
          (axisRest remainingAxis)
      let pub := annotatedDecPub E currentNoun hd tl lcCell tailCell
          (nounWalkRootState hd) (descentRootState (axisRest remainingAxis)) 0 0 lmb
      ([.node (gMemRow9 (memDecomposeSkel currentNoun hd tl) 0 z pub)
          ([headWalk] ++ tailTrees)], pub.pt)
    else
      let (headTrees, headCell) :=
        tw_genAnnotatedDescent E z lmb root child recAxis ts recordExp hd
          (axisRest remainingAxis)
      let (tailWalk, rcCell) := genAnnotatedNounWalk E z lmb tl
      let pub := annotatedDecPub E currentNoun hd tl headCell rcCell
          (descentRootState (axisRest remainingAxis)) (nounWalkRootState tl) 0 0 lmb
      ([.node (gMemRow9 (memDecomposeSkel currentNoun hd tl) 0 z pub)
          (headTrees ++ [tailWalk])], pub.pt)
termination_by remainingAxis
decreasing_by
  all_goals
    apply axisRest_lt
    omega

/-- Annotated record tree: builds the complete served tree for a single record with correct
    indicator/counts at every node. -/
def tw_genAnnotatedRecordTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) : NTree (GenMemoryRow K) :=
  let ts := α ^ recordExp
  let (descentChildren, descentCell) :=
    tw_genAnnotatedDescent E z lmb root child axis ts recordExp root axis
  let pub := tw_annotatedReadPub E root child axis ts descentCell 0 0 lmb
  .node (gMemRow9 (memReadSkelAx root child axis) recordExp z pub) descentChildren

/-! ## N. Annotated chained descent

The annotated continuation-based descent generalizes `genAxisDescentCont` by threading
indicator/counts through the continuation as well. -/

/-- Annotated axis descent with custom continuation: places `cont` at the terminal instead
    of a verify subtree, using `contCell` as the continuation root's pt cell.
    `contState` is the `MState` of the continuation's root node. -/
def tw_genAnnotatedDescentCont (E : Noun → ComputeTable.FP K) (z lmb : K)
    (cont : List (NTree (GenMemoryRow K)))
    (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (currentNoun : Noun) (remainingAxis : ℕ)
    : List (NTree (GenMemoryRow K)) × MemoryTable.Cell K :=
  if remainingAxis < 2 then (cont, contCell)
  else
    let hd := formulaHead currentNoun
    let tl := formulaTail currentNoun
    if axisTopBit remainingAxis then
      let (headWalk, lcCell) := genAnnotatedNounWalk E z lmb hd
      let (tailTrees, tailCell) :=
        tw_genAnnotatedDescentCont E z lmb cont contCell contState tl
          (axisRest remainingAxis)
      let pub := annotatedDecPub E currentNoun hd tl lcCell tailCell
          (nounWalkRootState hd)
          (descentContRootState contState (axisRest remainingAxis)) 0 0 lmb
      ([.node (gMemRow9 (memDecomposeSkel currentNoun hd tl) 0 z pub)
          ([headWalk] ++ tailTrees)], pub.pt)
    else
      let (headTrees, headCell) :=
        tw_genAnnotatedDescentCont E z lmb cont contCell contState hd
          (axisRest remainingAxis)
      let (tailWalk, rcCell) := genAnnotatedNounWalk E z lmb tl
      let pub := annotatedDecPub E currentNoun hd tl headCell rcCell
          (descentContRootState contState (axisRest remainingAxis))
          (nounWalkRootState tl) 0 0 lmb
      ([.node (gMemRow9 (memDecomposeSkel currentNoun hd tl) 0 z pub)
          (headTrees ++ [tailWalk])], pub.pt)
termination_by remainingAxis
decreasing_by
  all_goals
    apply axisRest_lt
    omega

/-- Annotated chained inner: builds the continuation for a chain with correct indicators.
    Returns the tree children and the root cell of the continuation. -/
def tw_genAnnotatedChainedInner (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (prev : MemRecordReq)
    : List MemRecordReq → List (NTree (GenMemoryRow K)) × MemoryTable.Cell K
  | [] =>
    let (vt, vc) := tw_genAnnotatedVerify E z lmb prev.root prev.child prev.axis
                      (α ^ prev.recordExp) prev.recordExp
    ([vt], vc)
  | r :: more =>
    let tsPrev := α ^ prev.recordExp
    let tsR := α ^ r.recordExp
    let (innerCont, innerCell) := tw_genAnnotatedChainedInner E z α lmb r more
    let innerRootState := chainedInnerRootState more
    let (descent2, descent2Cell) :=
      tw_genAnnotatedDescentCont E z lmb innerCont innerCell innerRootState r.root r.axis
    let verifyPub := tw_annotatedVerifyPub E prev.root prev.child prev.axis tsPrev descent2Cell 0 0 lmb
    let verifyNode : NTree (GenMemoryRow K) := .node
      (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis) prev.recordExp z verifyPub)
      descent2
    let readLcCell := verifyPub.pt
    let readPub := tw_annotatedReadPub E r.root r.child r.axis tsR readLcCell 0 0 lmb
    ([.node (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z readPub)
        [verifyNode]], readPub.pt)

/-- Annotated chained tree: builds a chained memory tree with correct indicator/counts. -/
def tw_genAnnotatedChainedTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) : Option (NTree (GenMemoryRow K)) :=
  match reqs with
  | [] => none
  | [r] => some (tw_genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)
  | r :: rest =>
    let ts := α ^ r.recordExp
    let (innerCont, innerCell) := tw_genAnnotatedChainedInner E z α lmb r rest
    let innerRootState := chainedInnerRootState rest
    let (descent, descentCell) :=
      tw_genAnnotatedDescentCont E z lmb innerCont innerCell innerRootState r.root r.axis
    let pub := tw_annotatedReadPub E r.root r.child r.axis ts descentCell 0 0 lmb
    some (.node (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z pub) descent)

/-! ## O. Annotated forest builder -/

/-- Build an annotated independent forest from a list of record requests. -/
def genAnnotatedForest (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) : List (NTree (GenMemoryRow K)) :=
  reqs.map fun r => tw_genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp


def tw_genRowMemForest (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) : List (NTree (GenMemoryRow K)) :=
  match reqs with
  | [] => []
  | [r] => [tw_genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp]
  | [r1, r2] =>
    if r1.child = r2.root then
      match tw_genAnnotatedChainedTree E z α lmb [r1, r2] with
      | some t => [t]
      | none => [tw_genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                 tw_genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
    else
      [tw_genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
       tw_genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
  | [r1, r2, r3] =>
    let first2 :=
      if r1.child = r2.root then
        match tw_genAnnotatedChainedTree E z α lmb [r1, r2] with
        | some t => [t]
        | none => [tw_genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                   tw_genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
      else
        [tw_genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
         tw_genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
    first2 ++ [tw_genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp]
  | rs => rs.map fun r => tw_genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp

/-! ## S. Compute tree → full memory forest -/

mutual
def tw_genMemForestFromTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    : NTree (GenComputeRow K) → List (NTree (GenMemoryRow K))
  | .node g cs =>
    tw_genRowMemForest E z α lmb (extractNodeReqs g) ++ tw_genMemForestFromList E z α lmb cs

def tw_genMemForestFromList (E : Noun → ComputeTable.FP K) (z α lmb : K)
    : List (NTree (GenComputeRow K)) → List (NTree (GenMemoryRow K))
  | [] => []
  | t :: ts => tw_genMemForestFromTree E z α lmb t ++ tw_genMemForestFromList E z α lmb ts
end

/-- `genTraceGeneric` (`GenMem.lean:1190`) with the memory forest built by the replica.  `αW` is not
    an argument of `genTraceGeneric` at this commit: the signature is `(_q _Λ) (z α lmb) fuel subject formula`. -/
def tw_genTraceGeneric (_q _Λ : ℕ) (z α lmb : K) (fuel : ℕ) (subject formula : Noun)
    : Except GenError (GenTrace K K) :=
  match genComputeSkeleton fuel subject formula with
  | .error e => .error e
  | .ok (ct, result) =>
    let assigned := bfsAssign ct
    .ok
      { subject := subject, formula := formula, result := result, fuel := fuel
        computeNodes := renderRows z α assigned
        memoryNodes := tw_genMemForestFromTree (encC z) z α lmb assigned }

end TraceDemo.Compute

/-! Standalone executable that runs the NockVM trace-generation pipeline on
  small Nock programs and prints the resulting field-element rows to stdout.

  Build and run:  `lake exe trace-demo`

  The generator `genTraceGeneric` is `noncomputable` (`pwScaleExp`, `nockAxisOf`), so this executable
  calls `TraceDemo.Compute.tw_genTraceGeneric`, a computable replica of the memory-forest builder
  (defined at the top of this file).  The compute rows come from the unchanged computable
  `genComputeSkeleton` / `bfsAssign` / `renderRows`.  This is a trace print, not a proof.
-/

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.Demo

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

private def sep : String := String.ofList (List.replicate 72 '-')

private def runDemo (label : String) (subject formula : Noun) : IO Unit := do
  IO.println s!"\n{sep}"
  IO.println s!"  {label}"
  IO.println sep
  IO.println s!"Subject:  {repr subject}"
  IO.println s!"Formula:  {repr formula}"

  match evalN 100 subject formula with
  | some r => IO.println s!"evalN result: {repr r}"
  | none   => IO.println "evalN: out of fuel"

  IO.println s!"enc(subject) = {repr (encC (8 : ZMod 97) subject)}"
  IO.println s!"enc(formula) = {repr (encC (8 : ZMod 97) formula)}"

  match TraceDemo.Compute.tw_genTraceGeneric 97 3 (8 : ZMod 97) (4 : ZMod 97) MemoryTable.formRDefault 100 subject formula with
  | .ok t => do
    IO.println s!"\nCompute tree size: {t.computeNodes.size}"
    IO.println s!"Memory forest trees: {t.memoryNodes.length}"
    IO.println s!"\n--- Compute tree ---"
    IO.println (toString (repr t.computeNodes))
    IO.println s!"\n--- Memory forest ---"
    let mut idx := 0
    for tree in t.memoryNodes do
      IO.println s!"  Tree {idx}: {repr tree}"
      idx := idx + 1
    IO.println s!"\n--- Service requests ---"
    let srs := genServiceReqs t.computeNodes
    idx := 0
    for sr in srs do
      IO.println s!"  [{idx}] {repr sr}"
      idx := idx + 1
  | .error _ =>
    IO.println "Trace generation failed."

def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════════╗"
  IO.println "║   NockVM Theorem 5.4 — trace print (unproved computable replica)       ║"
  IO.println "║                     Field: ZMod 97, z=8, α=4                            ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════════╝"

  runDemo "*[42 [4 0 1]] = 43   (increment)"
    (.atom 42)
    (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))

  runDemo "*[42 [3 0 1]] = 1    (cell-test on atom)"
    (.atom 42)
    (.cell (.atom 3) (.cell (.atom 0) (.atom 1)))

  runDemo "*[[1 2] [3 0 1]] = 0 (cell-test on cell)"
    (.cell (.atom 1) (.atom 2))
    (.cell (.atom 3) (.cell (.atom 0) (.atom 1)))

  runDemo "*[42 [1 [5 6]]] = [5 6] (quote)"
    (.atom 42)
    (.cell (.atom 1) (.cell (.atom 5) (.atom 6)))

  IO.println s!"\n{sep}"
  IO.println "Done."
