/-
  Nock/NockVMROM/Thm54/TraceGen/GenBroadProgram.lean

  **A second generator-route program, chosen to maximise `ComputeTable.State` coverage.**

  Every generic theorem of the `genComputeSkeleton → genSemanticData → genData` chain is
  instantiated at exactly one program, Tier A's, whose eight rows take
  four of the eleven states — `s6, s2, s1×5, s9`.

  The program here is
  ```
      *[[5 7]  [ [7 [1 5] [0 1]]                    -- OP_7, threaded subject
                 [ [8 [1 3] [0 3]]                  -- OP_8, pushed subject
                   [ [5 [1 1] [1 2]]                -- OP_5, DISTINCT operands
                     [ [4 [1 1]]                    -- OP_4
                       [3 [1 [1 2]]] ] ] ] ] ]      -- OP_3, CELL call result
        = [5 [[5 7] [1 [2 0]]]]
  ```
  — four autocons rows carrying five opcode arms.  Seventeen compute rows, states

      cons, s7, cons, s0, s1, s8, cons, s0, s1, s5, cons, s1, s1, s4, s3, s1, s1

  in AIR order, i.e. **`{cons, s0, s1, s3, s4, s5, s7, s8}`** — the seven states the generic chain
  had never reached, plus `s1`.  Together with Tier A's `{s1, s2, s6, s9}` that is all eleven.

  Three shapes are deliberate, and each makes a hypothesis of `genSemanticData` bite that has never
  bitten:

  * the OP5 operands are `1` and `2`, so `RowSeedGood`'s `.s5` clause `op5ResultsAgree` is on the
    **right** disjunct (unequal operands) rather than the trivial left one, and
    `ComputeCoinsGeneric`'s `rlc5Holds` obligation is live at the row;
  * the OP3 recursive call returns the **cell** `[1 2]`, so `op3CallSizeOk` is on the `.cell` branch
    (`z ^ 2 ≠ z`) rather than the `.atom` branch, which is `True`;
  * the four autocons heads are cells, so the `.cons` clause
    `(encC z (formulaHead …)).dyck ≠ 0` is a genuine polynomial condition on the seed.

  The `.s7` and `.s8` rows additionally exercise `airReorder`'s child swap at two states beyond
  Tier A's `.s6` (`airNeedsSwap`, `GenAirOrder.lean:52`).  Their `.s0` children are not the first
  `.s0` rows the generator emits — `Op0Gen.lean:367` and `Batch226` have those — but they are the
  first inside a program that also has a `cons` row.

  `Gen.lean` is not edited: the tree below is the tree the DFS arm emits, and
  `genComputeSkeleton_bp` proves it.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrder
import Nock.NockVMROM.Thm54.TraceGen.GenProgramKit
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.CensusExtraClosure

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open ComputeTable

variable {K : Type} [Field K]

/-! ## Program nouns -/

/-- Row subject `[5 7]` — a cell, so `OP_0` axis reads have somewhere to land. -/
def bpSubject : Noun := .cell (.atom 5) (.atom 7)

/-! ### `OP_7` arm: `[7 [1 5] [0 1]]` — helper `5`, then `*[5 [0 1]] = 5` -/

def bp7B : Noun := .cell (.atom 1) (.atom 5)
def bp7C : Noun := .cell (.atom 0) (.atom 1)
def bp7Tail : Noun := .cell bp7B bp7C
def bp7 : Noun := .cell (.atom 7) bp7Tail
/-- `*[[5 7] [1 5]] = 5`, the threaded subject of the `OP_7` second child. -/
def bp7Sb : Noun := .atom 5

/-! ### `OP_8` arm: `[8 [1 3] [0 3]]` — push `3`, then `/[3 [3 [5 7]]] = [5 7]` -/

def bp8B : Noun := .cell (.atom 1) (.atom 3)
def bp8C : Noun := .cell (.atom 0) (.atom 3)
def bp8Tail : Noun := .cell bp8B bp8C
def bp8 : Noun := .cell (.atom 8) bp8Tail
/-- `*[[5 7] [1 3]] = 3`. -/
def bp8Sb : Noun := .atom 3
/-- The pushed subject `[3 [5 7]]`. -/
def bp8Pushed : Noun := .cell bp8Sb bpSubject

/-! ### `OP_5` arm: `[5 [1 1] [1 2]]` — operands `1` and `2`, so `=` yields `1` -/

def bp5B : Noun := .cell (.atom 1) (.atom 1)
def bp5C : Noun := .cell (.atom 1) (.atom 2)
def bp5Tail : Noun := .cell bp5B bp5C
def bp5 : Noun := .cell (.atom 5) bp5Tail
def bp5Sf1 : Noun := .atom 1
def bp5Sf2 : Noun := .atom 2

/-! ### `OP_4` arm: `[4 [1 1]]` — increment of `1` -/

def bp4Tail : Noun := .cell (.atom 1) (.atom 1)
def bp4 : Noun := .cell (.atom 4) bp4Tail

/-! ### `OP_3` arm: `[3 [1 [1 2]]]` — cell-test of the CELL `[1 2]` -/

def bp3Call : Noun := .cell (.atom 1) (.atom 2)
def bp3Tail : Noun := .cell (.atom 1) bp3Call
def bp3 : Noun := .cell (.atom 3) bp3Tail

/-! ### The autocons spine -/

def bpR3 : Noun := .cell bp4 bp3
def bpR2 : Noun := .cell bp5 bpR3
def bpR1 : Noun := .cell bp8 bpR2
/-- The whole program formula. -/
def bpFormula : Noun := .cell bp7 bpR1

/-! ### Results, innermost outwards -/

def bpR3Result : Noun := .cell (.atom 2) (.atom 0)
def bpR2Result : Noun := .cell (.atom 1) bpR3Result
def bpR1Result : Noun := .cell bpSubject bpR2Result
/-- `*[[5 7] bpFormula] = [5 [[5 7] [1 [2 0]]]]`. -/
def bpResult : Noun := .cell (.atom 5) bpR1Result

/-! ## Slot facts the generator consults during emission -/

theorem bp7_slot : Noun.slot 1 bp7Sb = some bp7Sb := by
  simp [bp7Sb, Noun.slot]

theorem bp8_slot : Noun.slot 3 bp8Pushed = some bpSubject := by
  simp [bp8Pushed, bp8Sb, bpSubject, Noun.slot]

/-! ## The emitted subtrees, in the generator's own shapes -/

/-- `OP_1` leaf: `*[s [1 t]] = t`. -/
def bpOp1Tree (subject tail : Noun) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 subject (.cell (.atom 1) tail) tail (.atom 1))
    [⟨.cell (.atom 1) tail, tail, 3, 0⟩]) []

/-- The `OP_7` second child: `OP_0` at axis `1` against the helper `5`. -/
def bp7CTree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp0 bp7Sb bp7C (.atom 0) (.atom 1) bp7Sb 1)
    [⟨bp7C, .atom 1, 3, 0⟩, ⟨bp7Sb, bp7Sb, 1, 0⟩]) []

def bp7Tree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp7 bpSubject bp7 (.atom 7) bp7Tail bp7B bp7C bp7Sb bp7Sb)
    [⟨bp7, bp7Tail, 3, 0⟩, ⟨bp7Tail, bp7B, 2, 0⟩])
    [bpOp1Tree bpSubject (.atom 5), bp7CTree]

/-- The `OP_8` second child: `OP_0` at axis `3` against the pushed subject `[3 [5 7]]`. -/
def bp8CTree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp0 bp8Pushed bp8C (.atom 0) (.atom 3) bpSubject 3)
    [⟨bp8C, .atom 3, 3, 0⟩, ⟨bp8Pushed, bpSubject, 3, 0⟩]) []

def bp8Tree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp8 bpSubject bp8 (.atom 8) bp8Tail bp8B bp8C bp8Sb bpSubject)
    [⟨bp8, bp8Tail, 3, 0⟩, ⟨bp8Tail, bp8B, 2, 0⟩])
    [bpOp1Tree bpSubject (.atom 3), bp8CTree]

def bp5Tree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp5 bpSubject bp5 (.atom 5) bp5Tail bp5B bp5C bp5Sf1 bp5Sf2 (.atom 1))
    [⟨bp5, bp5Tail, 3, 0⟩, ⟨bp5Tail, bp5B, 2, 0⟩])
    [bpOp1Tree bpSubject (.atom 1), bpOp1Tree bpSubject (.atom 2)]

def bp4Tree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp4 bpSubject bp4 (.atom 4) bp4Tail bpSubject bp4Tail
      (.atom 1) (.atom 2))
    [⟨bp4, bp4Tail, 3, 0⟩])
    [bpOp1Tree bpSubject (.atom 1)]

def bp3Tree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp3 bpSubject bp3 (.atom 3) bp3Tail bpSubject bp3Tail
      bp3Call (.atom 0))
    [⟨bp3, bp3Tail, 3, 0⟩])
    [bpOp1Tree bpSubject bp3Call]

def bpR3Tree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelCons bpSubject bp4 bp3 (.atom 2) (.atom 0))
    [⟨bpR3, bp3, 3, 0⟩])
    [bp4Tree, bp3Tree]

def bpR2Tree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelCons bpSubject bp5 bpR3 (.atom 1) bpR3Result)
    [⟨bpR2, bpR3, 3, 0⟩])
    [bp5Tree, bpR3Tree]

def bpR1Tree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelCons bpSubject bp8 bpR2 bpSubject bpR2Result)
    [⟨bpR1, bpR2, 3, 0⟩])
    [bp8Tree, bpR2Tree]

/-- The seventeen-row tree the DFS emission arm produces. -/
def bpTree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelCons bpSubject bp7 bpR1 (.atom 5) bpR1Result)
    [⟨bpFormula, bpR1, 3, 0⟩])
    [bp7Tree, bpR1Tree]

/-! ## Generator emission, arm by arm

Composed from `GenProgramKit`: each subtree's acceptance is the kit lemma for its arm applied to
its children's acceptances.  Nothing here reduces the whole tree by `whnf`. -/

theorem bp_lus : Noun.lus (.atom 1) = some (.atom 2) := rfl

theorem bp_wut : Noun.wut bp3Call = .atom 0 := rfl

theorem bp_tis : Noun.tis (.atom 1) (.atom 2) = .atom 1 := by
  simp [Noun.tis]

/-- `*[[5 7] [1 t]] = t` at every `OP_1` leaf of the program. -/
theorem bp_gen_op1 (n : ℕ) (subject tail : Noun) :
    genComputeSkeleton (K := K) (n + 1) subject (.cell (.atom 1) tail)
      = .ok (bpOp1Tree subject tail, tail) :=
  gen_quote n subject tail

theorem bp_gen_7C (n : ℕ) :
    genComputeSkeleton (K := K) (n + 1) bp7Sb bp7C = .ok (bp7CTree, bp7Sb) :=
  gen_op0 n bp7_slot

theorem bp_gen_7 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) bpSubject bp7 = .ok (bp7Tree, bp7Sb) :=
  gen_op7 (n + 1) (bp_gen_op1 n bpSubject (.atom 5)) (bp_gen_7C n)

theorem bp_gen_8C (n : ℕ) :
    genComputeSkeleton (K := K) (n + 1) bp8Pushed bp8C = .ok (bp8CTree, bpSubject) :=
  gen_op0 n bp8_slot

theorem bp_gen_8 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) bpSubject bp8 = .ok (bp8Tree, bpSubject) :=
  gen_op8 (n + 1) (bp_gen_op1 n bpSubject (.atom 3)) (bp_gen_8C n)

theorem bp_gen_5 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) bpSubject bp5 = .ok (bp5Tree, .atom 1) := by
  have h := gen_op5 (K := K) (n + 1)
    (bp_gen_op1 n bpSubject (.atom 1)) (bp_gen_op1 n bpSubject (.atom 2))
  rw [bp_tis] at h
  exact h

theorem bp_gen_4 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) bpSubject bp4 = .ok (bp4Tree, .atom 2) :=
  gen_op4 (n + 1) (bp_gen_op1 n bpSubject (.atom 1)) bp_lus

theorem bp_gen_3 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 2) bpSubject bp3 = .ok (bp3Tree, .atom 0) := by
  have h := gen_op3 (K := K) (n + 1) (bp_gen_op1 n bpSubject bp3Call)
  rw [bp_wut] at h
  exact h

theorem bp_gen_R3 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 3) bpSubject bpR3 = .ok (bpR3Tree, bpR3Result) :=
  gen_cons (n + 2) (bp_gen_4 n) (bp_gen_3 n)

theorem bp_gen_R2 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 4) bpSubject bpR2 = .ok (bpR2Tree, bpR2Result) :=
  gen_cons (n + 3) (bp_gen_5 (n + 1)) (bp_gen_R3 n)

theorem bp_gen_R1 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 5) bpSubject bpR1 = .ok (bpR1Tree, bpR1Result) :=
  gen_cons (n + 4) (bp_gen_8 (n + 2)) (bp_gen_R2 n)

/-- **The program is accepted**, and the emitted tree is `bpTree`.  Fuel `n + 6` covers the
four-deep autocons spine. -/
theorem genComputeSkeleton_bp (n : ℕ) :
    genComputeSkeleton (K := K) (n + 6) bpSubject bpFormula = .ok (bpTree, bpResult) :=
  gen_cons (n + 5) (bp_gen_7 (n + 3)) (bp_gen_R1 n)

/-! ## The AIR-ordered tree

`airNeedsSwap` is `true` at `.s6`, `.s7` and `.s8` (`GenAirOrder.lean:52`).  This program has an
`.s7` row and an `.s8` row, so `airReorder` swaps two pairs of children — at two states Tier A's
single `.s6` swap does not reach. -/

def bp7TreeAir : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp7 bpSubject bp7 (.atom 7) bp7Tail bp7B bp7C bp7Sb bp7Sb)
    [⟨bp7, bp7Tail, 3, 0⟩, ⟨bp7Tail, bp7B, 2, 0⟩])
    [bp7CTree, bpOp1Tree bpSubject (.atom 5)]

def bp8TreeAir : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp8 bpSubject bp8 (.atom 8) bp8Tail bp8B bp8C bp8Sb bpSubject)
    [⟨bp8, bp8Tail, 3, 0⟩, ⟨bp8Tail, bp8B, 2, 0⟩])
    [bp8CTree, bpOp1Tree bpSubject (.atom 3)]

def bpR1TreeAir : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelCons bpSubject bp8 bpR2 bpSubject bpR2Result)
    [⟨bpR1, bpR2, 3, 0⟩])
    [bp8TreeAir, bpR2Tree]

def bpTreeAir : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelCons bpSubject bp7 bpR1 (.atom 5) bpR1Result)
    [⟨bpFormula, bpR1, 3, 0⟩])
    [bp7TreeAir, bpR1TreeAir]

theorem airReorder_bpTree : airReorder (bpTree (K := K)) = bpTreeAir := by
  simp [airReorder, bpTree, bpTreeAir, bpR1Tree, bpR1TreeAir, bp7Tree, bp7TreeAir,
    bp8Tree, bp8TreeAir, bpR2Tree, bpR3Tree, bp5Tree, bp4Tree, bp3Tree, bp7CTree,
    bp8CTree, bpOp1Tree, skelNode, genSkelCons, genSkelOp7, genSkelOp8, genSkelOp5,
    genSkelOp4, genSkelOp3, genSkelOp1, genSkelOp0, airNeedsSwap, swapPair]

/-! ## The BFS row list

`TraceConfined` and every row-indexed measurement are discharged from this list, exactly as
`dot_air_bfsRows` discharges Tier A's (`Batch164.dot_traceConfined`). -/

theorem bpTreeAir_children :
    (bpTreeAir (K := K)).children = [bp7TreeAir, bpR1TreeAir] := rfl
theorem bp7TreeAir_children :
    (bp7TreeAir (K := K)).children = [bp7CTree, bpOp1Tree bpSubject (.atom 5)] := rfl
theorem bpR1TreeAir_children :
    (bpR1TreeAir (K := K)).children = [bp8TreeAir, bpR2Tree] := rfl
theorem bp8TreeAir_children :
    (bp8TreeAir (K := K)).children = [bp8CTree, bpOp1Tree bpSubject (.atom 3)] := rfl
theorem bpR2Tree_children :
    (bpR2Tree (K := K)).children = [bp5Tree, bpR3Tree] := rfl
theorem bp5Tree_children :
    (bp5Tree (K := K)).children
      = [bpOp1Tree bpSubject (.atom 1), bpOp1Tree bpSubject (.atom 2)] := rfl
theorem bpR3Tree_children :
    (bpR3Tree (K := K)).children = [bp4Tree, bp3Tree] := rfl
theorem bp4Tree_children :
    (bp4Tree (K := K)).children = [bpOp1Tree bpSubject (.atom 1)] := rfl
theorem bp3Tree_children :
    (bp3Tree (K := K)).children = [bpOp1Tree bpSubject bp3Call] := rfl
theorem bp7CTree_children : (bp7CTree (K := K)).children = [] := rfl
theorem bp8CTree_children : (bp8CTree (K := K)).children = [] := rfl
theorem bpOp1Tree_children (subject tail : Noun) :
    (bpOp1Tree (K := K) subject tail).children = [] := rfl

/-- The seventeen nodes in BFS order. -/
theorem bp_air_bfsForest :
    bfsForest [bpTreeAir (K := K)] =
      [bpTreeAir, bp7TreeAir, bpR1TreeAir,
       bp7CTree, bpOp1Tree bpSubject (.atom 5), bp8TreeAir, bpR2Tree,
       bp8CTree, bpOp1Tree bpSubject (.atom 3), bp5Tree, bpR3Tree,
       bpOp1Tree bpSubject (.atom 1), bpOp1Tree bpSubject (.atom 2), bp4Tree, bp3Tree,
       bpOp1Tree bpSubject (.atom 1), bpOp1Tree bpSubject bp3Call] := by
  have hne {α : Type} {a : α} {l : List α} : a :: l ≠ [] := List.cons_ne_nil _ _
  repeat
    rw [bfsForest_cons_eq _ hne]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
      List.cons_append, bpTreeAir_children, bp7TreeAir_children, bpR1TreeAir_children,
      bp8TreeAir_children, bpR2Tree_children, bp5Tree_children, bpR3Tree_children,
      bp4Tree_children, bp3Tree_children, bp7CTree_children, bp8CTree_children,
      bpOp1Tree_children]
  rw [bfsForest_nil]

theorem bp_air_bfsRows :
    bfsRows (bpTreeAir (K := K)) =
      [(bpTreeAir (K := K)).label, bp7TreeAir.label, bpR1TreeAir.label,
       bp7CTree.label, (bpOp1Tree bpSubject (.atom 5)).label, bp8TreeAir.label,
       bpR2Tree.label, bp8CTree.label, (bpOp1Tree bpSubject (.atom 3)).label,
       bp5Tree.label, bpR3Tree.label, (bpOp1Tree bpSubject (.atom 1)).label,
       (bpOp1Tree bpSubject (.atom 2)).label, bp4Tree.label, bp3Tree.label,
       (bpOp1Tree bpSubject (.atom 1)).label, (bpOp1Tree bpSubject bp3Call).label] := by
  simp [bfsRows, bp_air_bfsForest]

theorem bp_air_rowsLen : (bfsRows (bpTreeAir (K := K))).length = 17 := by
  rw [bp_air_bfsRows]; rfl

/-! ### The DFS row list

`SeedGood` is stated on the tree the generator emits, i.e. before `airReorder`, so the DFS row list
is needed as well.  It differs from the AIR list only by the `.s7`/`.s8` child swaps. -/

theorem bpTree_children : (bpTree (K := K)).children = [bp7Tree, bpR1Tree] := rfl
theorem bp7Tree_children :
    (bp7Tree (K := K)).children = [bpOp1Tree bpSubject (.atom 5), bp7CTree] := rfl
theorem bpR1Tree_children : (bpR1Tree (K := K)).children = [bp8Tree, bpR2Tree] := rfl
theorem bp8Tree_children :
    (bp8Tree (K := K)).children = [bpOp1Tree bpSubject (.atom 3), bp8CTree] := rfl

theorem bp_bfsForest :
    bfsForest [bpTree (K := K)] =
      [bpTree, bp7Tree, bpR1Tree,
       bpOp1Tree bpSubject (.atom 5), bp7CTree, bp8Tree, bpR2Tree,
       bpOp1Tree bpSubject (.atom 3), bp8CTree, bp5Tree, bpR3Tree,
       bpOp1Tree bpSubject (.atom 1), bpOp1Tree bpSubject (.atom 2), bp4Tree, bp3Tree,
       bpOp1Tree bpSubject (.atom 1), bpOp1Tree bpSubject bp3Call] := by
  have hne {α : Type} {a : α} {l : List α} : a :: l ≠ [] := List.cons_ne_nil _ _
  repeat
    rw [bfsForest_cons_eq _ hne]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
      List.cons_append, bpTree_children, bp7Tree_children, bpR1Tree_children,
      bp8Tree_children, bpR2Tree_children, bp5Tree_children, bpR3Tree_children,
      bp4Tree_children, bp3Tree_children, bp7CTree_children, bp8CTree_children,
      bpOp1Tree_children]
  rw [bfsForest_nil]

theorem bp_bfsRows :
    bfsRows (bpTree (K := K)) =
      [(bpTree (K := K)).label, bp7Tree.label, bpR1Tree.label,
       (bpOp1Tree bpSubject (.atom 5)).label, bp7CTree.label, bp8Tree.label,
       bpR2Tree.label, (bpOp1Tree bpSubject (.atom 3)).label, bp8CTree.label,
       bp5Tree.label, bpR3Tree.label, (bpOp1Tree bpSubject (.atom 1)).label,
       (bpOp1Tree bpSubject (.atom 2)).label, bp4Tree.label, bp3Tree.label,
       (bpOp1Tree bpSubject (.atom 1)).label, (bpOp1Tree bpSubject bp3Call).label] := by
  simp [bfsRows, bp_bfsForest]

theorem bp_compRowsLen : (bfsForest [bpTree (K := K)]).length = 17 := by
  rw [bp_bfsForest]; rfl

/-! ## The state census — eight of the eleven states, in AIR order -/

/-- The seventeen row states. -/
abbrev bpStates : List ComputeTable.State :=
  [.cons, .s7, .cons, .s0, .s1, .s8, .cons, .s0, .s1, .s5, .cons, .s1, .s1, .s4, .s3, .s1, .s1]

theorem bp_air_states :
    (bfsRows (bpTreeAir (K := K))).map (fun g => g.skel.state) = bpStates := by
  rw [bp_air_bfsRows]; rfl

/-- **Eight distinct states**: `{cons, s0, s1, s3, s4, s5, s7, s8}`.  Tier A's four are
`{s1, s2, s6, s9}`, so the two programs together cover all eleven. -/
theorem bp_air_states_dedup :
    bpStates.eraseDups = [.cons, .s7, .s0, .s1, .s8, .s5, .s4, .s3] := by decide

theorem bp_air_states_nodup_length : bpStates.eraseDups.length = 8 := by decide

/-! ## The Λ-confinement measurement

The window is `22`, and it is the root row's **formula**: the program text has 22 leaves.
Coincidentally the same number as Tier A's, for the same reason. -/

theorem bpFormula_leaves : bpFormula.leaves = 22 := by
  simp [bpFormula, bp7, bp8, bp5, bp4, bp3, bpR1, bpR2, bpR3, bp7Tail, bp8Tail,
    bp5Tail, bp4Tail, bp3Tail, bp7B, bp7C, bp8B, bp8C, bp5B, bp5C, bp3Call, Noun.leaves]

/-- **The program is Λ-confined at 22**, measured row by row off `bp_air_bfsRows`. -/
theorem bp_traceConfined : TraceConfined 22 (bpTreeAir (K := K)) := by
  intro g hg
  rw [bp_air_bfsRows] at hg
  fin_cases hg <;>
    exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- And it **fails at 21**, at the root row's formula: 22 is this program's exact window, so the
premise is a real constraint on `Λ` here as well. -/
theorem bp_not_traceConfined_21 : ¬ TraceConfined 21 (bpTreeAir (K := K)) := by
  intro h
  have hr := h (bpTreeAir (K := K)).label (by rw [bp_air_bfsRows]; simp)
  exact absurd (show (22 : ℕ) ≤ 21 from hr.2.1) (by decide)

/-! ## Program-level side conditions of `GenGenericBounded` / `GenGenericAxisRange` -/

theorem bp_subject_bounded {q : ℕ} (hq : 8 < q) :
    FieldEmbedding.BoundedBy q bpSubject := by
  simp only [bpSubject, FieldEmbedding.BoundedBy]
  omega

theorem bp_formula_bounded {q : ℕ} (hq : 8 < q) :
    FieldEmbedding.BoundedBy q bpFormula := by
  simp only [bpFormula, bp7, bp8, bp5, bp4, bp3, bpR1, bpR2, bpR3, bp7Tail, bp8Tail,
    bp5Tail, bp4Tail, bp3Tail, bp7B, bp7C, bp8B, bp8C, bp5B, bp5C, bp3Call,
    FieldEmbedding.BoundedBy]
  omega

/-- The `q`-guarded run does not overflow: `OP_4` increments `1` to `2`, and `2 < q`. -/
theorem bp_evalGBy {q : ℕ} (hq : 8 < q) :
    FieldEmbedding.evalGBy q 6 bpSubject bpFormula = some bpResult := by
  have h2 : (1 : ℕ) + 1 < q := by omega
  simp [FieldEmbedding.evalGBy, FieldEmbedding.lusGBy, bpFormula, bp7, bp8, bp5, bp4, bp3,
    bpR1, bpR2, bpR3, bp7Tail, bp8Tail, bp5Tail, bp4Tail, bp3Tail, bp7B, bp7C, bp8B, bp8C,
    bp5B, bp5C, bp3Call, bpSubject, bpResult, bpR1Result, bpR2Result, bpR3Result,
    Noun.slot, Noun.tis, Noun.wut, h2]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bp
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_air_bfsRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_air_states
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_air_states_dedup
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_not_traceConfined_21
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_evalGBy
#print axioms Nock.NockVMROM.Thm54.TraceGen.airReorder_bpTree
