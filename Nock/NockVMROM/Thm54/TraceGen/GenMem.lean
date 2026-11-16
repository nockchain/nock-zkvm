/-
  Nock/NockVMROM/Thm54/TraceGen/GenMem.lean

  Phase 3b: the computable memory forest builder.

  Given a memory record `(root, child, axis, recordExp)`, `genRecordTree` constructs the
  served memory NTree by descending the root noun along the Nock axis path — decomposing each
  cell into head/tail, halting atom siblings, and placing the `read_root`/`verify_child` pair
  that carries the served record at the endpoints.  `genIndependentForest` packages a list
  of independent records into a forest (one tree per record, no interleaving).

  The builder reuses the OP9 zero-indicator pub constructors (`op9ReadPub`, `op9DecPub`,
  `op9VerifyPub`, `op9HaltPub`) and the generic row wrapper `gMemRow9`.  Agreement with the
  manually-built OP9 Root B tree is proved by definitional reduction.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op9Gen
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]
variable {lmb : K}

-- Every
-- builder takes it explicitly; generic theorems are stated at every `λ`.
variable {lmb : K}

/-! ## A. Atomic building blocks -/

/-- Halt nodes for a noun: a single halt leaf for atoms, empty list for cells.
    Cells cannot halt directly (halt requires the parent to be an atom). -/
def genHaltNodes (E : Noun → ComputeTable.FP K) (z : K) :
    Noun → List (NTree (GenMemoryRow K))
  | .atom a => [.node (gMemRow9 (memHaltSkel a) 0 z (op9HaltPub E a)) []]
  | .cell _ _ => []

/-- The verify subtree for a record: a `verify_child` node with halt children for the
    child noun (halt if atom, no children if cell). -/
def genVerifySubtree (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) : NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memVerifySkelAx root child ax) recordExp z
    (op9VerifyPub E root child ax ts)) (genHaltNodes E z child)

/-! ## B. Axis descent builder

The axis descent follows the paper route `axisPath`: bits below
the leading one, **most significant (topmost) first**, matching `Noun.slot`.
Axis `2` = head, axis `3` = tail; deeper axes take that same head/tail step at the
root, then continue on the residual axis.  The sibling of the on-path child is a
noun-walk (annotated) or a halt (zero-indicator). -/

/-- Topmost bit of a Nock axis `a ≥ 2`: `true` = tail, `false` = head.
    Equal to `(axisPath a).head!`. -/
def axisTopBit (a : ℕ) : Bool :=
  if 3 * 2 ^ (a.log2 - 1) ≤ a then true else false

/-- Residual axis after consuming `axisTopBit a`.  For `a ≥ 2` this is strictly
    smaller than `a`, so descent is well-founded. -/
def axisRest (a : ℕ) : ℕ :=
  let k := a.log2
  if 3 * 2 ^ (k - 1) ≤ a then a - 2 ^ k else a - 2 ^ (k - 1)

theorem two_pow_log2_le (n : ℕ) (h : 0 < n) : 2 ^ n.log2 ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.log2_def]
    split
    · rename_i h2
      have hhalf : n / 2 < n := Nat.div_lt_self h (by decide)
      have hpos : 0 < n / 2 := Nat.div_pos h2 (by decide)
      have ih' := ih (n / 2) hhalf hpos
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ (n / 2).log2) 2]
      have hmul : 2 * 2 ^ (n / 2).log2 ≤ 2 * (n / 2) :=
        Nat.mul_le_mul_left 2 ih'
      exact Nat.le_trans hmul (Nat.mul_div_le n 2)
    · simp
      omega

theorem log2_ge_one {a : ℕ} (h : 2 ≤ a) : 1 ≤ a.log2 := by
  rw [Nat.log2_def]
  split
  · omega
  · omega

theorem log2_one : (1 : ℕ).log2 = 0 := by
  rw [Nat.log2_def]
  simp

theorem log2_two : (2 : ℕ).log2 = 1 := by
  rw [Nat.log2_def]
  simp [log2_one]

theorem log2_three : (3 : ℕ).log2 = 1 := by
  rw [Nat.log2_def]
  simp [log2_one]

theorem axisRest_lt {a : ℕ} (h : 2 ≤ a) : axisRest a < a := by
  dsimp [axisRest]
  have hpos : 0 < a := by omega
  split_ifs
  · exact Nat.sub_lt hpos (Nat.two_pow_pos _)
  · exact Nat.sub_lt hpos (Nat.two_pow_pos _)

/-- Count of `axisTopBit = false` steps from `a` down to `1`.  Form R's extra
    `+ rc.indicator` on the head (not-top) decompose path accumulates this many
    copies of the continuation indicator. -/
def axisZeroBits (a : ℕ) : ℕ :=
  if h : a < 2 then 0
  else (if axisTopBit a then 0 else 1) + axisZeroBits (axisRest a)
decreasing_by
  exact axisRest_lt (Nat.le_of_not_lt h)

@[simp] theorem axisZeroBits_lt_two {a : ℕ} (ha : a < 2) : axisZeroBits a = 0 := by
  simp [axisZeroBits, ha]

@[simp] theorem axisZeroBits_one : axisZeroBits 1 = 0 :=
  axisZeroBits_lt_two (by decide)

theorem axisZeroBits_top {a : ℕ} (h : 2 ≤ a) (hb : axisTopBit a = true) :
    axisZeroBits a = axisZeroBits (axisRest a) := by
  conv_lhs => rw [axisZeroBits]
  rw [dif_neg (Nat.not_lt.mpr h), if_pos hb, zero_add]

theorem axisZeroBits_not_top {a : ℕ} (h : 2 ≤ a) (hb : axisTopBit a = false) :
    axisZeroBits a = axisZeroBits (axisRest a) + 1 := by
  conv_lhs => rw [axisZeroBits]
  rw [dif_neg (Nat.not_lt.mpr h), if_neg (by simp [hb]), add_comm]

@[simp] theorem axisTopBit_two : axisTopBit 2 = false := by
  unfold axisTopBit
  rw [log2_two]
  simp

@[simp] theorem axisTopBit_three : axisTopBit 3 = true := by
  unfold axisTopBit
  rw [log2_three]
  simp

@[simp] theorem axisRest_two : axisRest 2 = 1 := by
  unfold axisRest
  rw [log2_two]
  simp

@[simp] theorem axisRest_three : axisRest 3 = 1 := by
  unfold axisRest
  rw [log2_three]
  simp

@[simp] theorem axisZeroBits_two : axisZeroBits 2 = 1 := by
  rw [axisZeroBits_not_top (by decide) axisTopBit_two, axisRest_two, axisZeroBits_one]

@[simp] theorem axisZeroBits_three : axisZeroBits 3 = 0 := by
  rw [axisZeroBits_top (by decide) axisTopBit_three, axisRest_three, axisZeroBits_one]

/-- Count of `axisTopBit = true` steps.  Form R adds `rc.indicator` on the tail
    (top) decompose path, so this many copies of the continuation indicator
    accumulate in `counts`. -/
def axisOneBits (a : ℕ) : ℕ :=
  if h : a < 2 then 0
  else (if axisTopBit a then 1 else 0) + axisOneBits (axisRest a)
decreasing_by
  exact axisRest_lt (Nat.le_of_not_lt h)

@[simp] theorem axisOneBits_lt_two {a : ℕ} (ha : a < 2) : axisOneBits a = 0 := by
  simp [axisOneBits, ha]

@[simp] theorem axisOneBits_one : axisOneBits 1 = 0 :=
  axisOneBits_lt_two (by decide)

theorem axisOneBits_top {a : ℕ} (h : 2 ≤ a) (hb : axisTopBit a = true) :
    axisOneBits a = axisOneBits (axisRest a) + 1 := by
  conv_lhs => rw [axisOneBits]
  rw [dif_neg (Nat.not_lt.mpr h), if_pos hb, add_comm]

theorem axisOneBits_not_top {a : ℕ} (h : 2 ≤ a) (hb : axisTopBit a = false) :
    axisOneBits a = axisOneBits (axisRest a) := by
  conv_lhs => rw [axisOneBits]
  rw [dif_neg (Nat.not_lt.mpr h), if_neg (by simp [hb]), zero_add]

@[simp] theorem axisOneBits_two : axisOneBits 2 = 0 := by
  rw [axisOneBits_not_top (by decide) axisTopBit_two, axisRest_two, axisOneBits_one]

@[simp] theorem axisOneBits_three : axisOneBits 3 = 1 := by
  rw [axisOneBits_top (by decide) axisTopBit_three, axisRest_three, axisOneBits_one]

theorem log2_four : (4 : ℕ).log2 = 2 := by
  rw [Nat.log2_def]
  simp [log2_two]

theorem log2_five : (5 : ℕ).log2 = 2 := by
  rw [Nat.log2_def]
  simp [log2_two]

theorem log2_six : (6 : ℕ).log2 = 2 := by
  rw [Nat.log2_def]
  simp [log2_three]

theorem log2_seven : (7 : ℕ).log2 = 2 := by
  rw [Nat.log2_def]
  simp [log2_three]

@[simp] theorem axisTopBit_four : axisTopBit 4 = false := by
  unfold axisTopBit
  rw [log2_four]
  simp

@[simp] theorem axisRest_four : axisRest 4 = 2 := by
  unfold axisRest
  rw [log2_four]
  simp

theorem log2_eight : (8 : ℕ).log2 = 3 := by
  rw [Nat.log2_def]
  simp [log2_four]

@[simp] theorem axisTopBit_eight : axisTopBit 8 = false := by
  unfold axisTopBit
  rw [log2_eight]
  simp

@[simp] theorem axisRest_eight : axisRest 8 = 4 := by
  unfold axisRest
  rw [log2_eight]
  simp

@[simp] theorem axisTopBit_five : axisTopBit 5 = false := by
  unfold axisTopBit
  rw [log2_five]
  simp

@[simp] theorem axisRest_five : axisRest 5 = 3 := by
  unfold axisRest
  rw [log2_five]
  simp

@[simp] theorem axisTopBit_six : axisTopBit 6 = true := by
  unfold axisTopBit
  rw [log2_six]
  simp

@[simp] theorem axisRest_six : axisRest 6 = 2 := by
  unfold axisRest
  rw [log2_six]
  simp

@[simp] theorem axisTopBit_seven : axisTopBit 7 = true := by
  unfold axisTopBit
  rw [log2_seven]
  simp

@[simp] theorem axisRest_seven : axisRest 7 = 3 := by
  unfold axisRest
  rw [log2_seven]
  simp

theorem log2_nine : (9 : ℕ).log2 = 3 := by
  rw [Nat.log2_def]
  simp [log2_four]

theorem log2_ten : (10 : ℕ).log2 = 3 := by
  rw [Nat.log2_def]
  simp [log2_five]

theorem log2_eleven : (11 : ℕ).log2 = 3 := by
  rw [Nat.log2_def]
  simp [log2_five]

theorem log2_twelve : (12 : ℕ).log2 = 3 := by
  rw [Nat.log2_def]
  simp [log2_six]

theorem log2_thirteen : (13 : ℕ).log2 = 3 := by
  rw [Nat.log2_def]
  simp [log2_six]

@[simp] theorem axisTopBit_nine : axisTopBit 9 = false := by
  unfold axisTopBit
  rw [log2_nine]
  simp

@[simp] theorem axisRest_nine : axisRest 9 = 5 := by
  unfold axisRest
  rw [log2_nine]
  simp

@[simp] theorem axisTopBit_ten : axisTopBit 10 = false := by
  unfold axisTopBit
  rw [log2_ten]
  simp

@[simp] theorem axisRest_ten : axisRest 10 = 6 := by
  unfold axisRest
  rw [log2_ten]
  simp

@[simp] theorem axisTopBit_eleven : axisTopBit 11 = false := by
  unfold axisTopBit
  rw [log2_eleven]
  simp

@[simp] theorem axisRest_eleven : axisRest 11 = 7 := by
  unfold axisRest
  rw [log2_eleven]
  simp

@[simp] theorem axisTopBit_twelve : axisTopBit 12 = true := by
  unfold axisTopBit
  rw [log2_twelve]
  simp

@[simp] theorem axisRest_twelve : axisRest 12 = 4 := by
  unfold axisRest
  rw [log2_twelve]
  simp

@[simp] theorem axisTopBit_thirteen : axisTopBit 13 = true := by
  unfold axisTopBit
  rw [log2_thirteen]
  simp

@[simp] theorem axisRest_thirteen : axisRest 13 = 5 := by
  unfold axisRest
  rw [log2_thirteen]
  simp

@[simp] theorem axisTopBit_fourteen : axisTopBit 14 = true := by
  unfold axisTopBit
  have h : (14 : ℕ).log2 = 3 := by
    rw [Nat.log2_def]; simp [log2_seven]
  rw [h]
  simp

@[simp] theorem axisRest_fourteen : axisRest 14 = 6 := by
  unfold axisRest
  have h : (14 : ℕ).log2 = 3 := by
    rw [Nat.log2_def]; simp [log2_seven]
  rw [h]
  simp

@[simp] theorem axisTopBit_fifteen : axisTopBit 15 = true := by
  unfold axisTopBit
  have h : (15 : ℕ).log2 = 3 := by
    rw [Nat.log2_def]; simp [log2_seven]
  rw [h]
  simp

@[simp] theorem axisRest_fifteen : axisRest 15 = 7 := by
  unfold axisRest
  have h : (15 : ℕ).log2 = 3 := by
    rw [Nat.log2_def]; simp [log2_seven]
  rw [h]
  simp

@[simp] theorem axisTopBit_thirty : axisTopBit 30 = true := by
  unfold axisTopBit
  have h : (30 : ℕ).log2 = 4 := by
    rw [Nat.log2_def]
    have h15 : (15 : ℕ).log2 = 3 := by
      rw [Nat.log2_def]; simp [log2_seven]
    simp [h15]
  rw [h]
  simp

@[simp] theorem axisRest_thirty : axisRest 30 = 14 := by
  unfold axisRest
  have h : (30 : ℕ).log2 = 4 := by
    rw [Nat.log2_def]
    have h15 : (15 : ℕ).log2 = 3 := by
      rw [Nat.log2_def]; simp [log2_seven]
    simp [h15]
  rw [h]
  simp

@[simp] theorem axisTopBit_thirtyone : axisTopBit 31 = true := by
  unfold axisTopBit
  have h : (31 : ℕ).log2 = 4 := by
    rw [Nat.log2_def]
    have h15 : (15 : ℕ).log2 = 3 := by
      rw [Nat.log2_def]; simp [log2_seven]
    simp [h15]
  rw [h]
  simp

@[simp] theorem axisRest_thirtyone : axisRest 31 = 15 := by
  unfold axisRest
  have h : (31 : ℕ).log2 = 4 := by
    rw [Nat.log2_def]
    have h15 : (15 : ℕ).log2 = 3 := by
      rw [Nat.log2_def]; simp [log2_seven]
    simp [h15]
  rw [h]
  simp

/-- Build the axis descent from `currentNoun` toward the served child along `remainingAxis`.
    Returns the list of NTree children to attach under the parent (read_root or decompose). -/
def genAxisDescent (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) : List (NTree (GenMemoryRow K)) :=
  if remainingAxis < 2 then
    [genVerifySubtree E z root child recAxis ts recordExp]
  else
    let hd := formulaHead currentNoun
    let tl := formulaTail currentNoun
    let rest := axisRest remainingAxis
    let decRow := gMemRow9 (memDecomposeSkel currentNoun hd tl) 0 z
                    (op9DecPub E currentNoun hd tl)
    if axisTopBit remainingAxis then
      [.node decRow
        (genHaltNodes E z hd
         ++ genAxisDescent E z root child recAxis ts recordExp tl rest)]
    else
      [.node decRow
        (genAxisDescent E z root child recAxis ts recordExp hd rest
         ++ genHaltNodes E z tl)]
termination_by remainingAxis
decreasing_by
  all_goals
    apply axisRest_lt
    omega

/-- Build the complete served tree for a single memory record `(root, child, axis)` at
    timestamp `α ^ recordExp`.  The tree starts with a `read_root` node and descends along
    the axis path, ending with a `verify_child` node that pairs with the read. -/
def genRecordTree (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) : NTree (GenMemoryRow K) :=
  .node (gMemRow9 (memReadSkelAx root child axis) recordExp z
          (op9ReadPub E root child axis (α ^ recordExp)))
    (genAxisDescent E z root child axis (α ^ recordExp) recordExp root axis)

/-! ## C. The independent-record forest builder -/

/-- A memory record request: the root/child/axis triple plus the natural-number exponent
    for the timestamp `α ^ recordExp`. -/
structure MemRecordReq where
  root : Noun
  child : Noun
  axis : ℕ
  recordExp : ℕ

/-- Build the served forest from a list of independent records: one tree per record,
    no interleaving of read/verify pairs across records. -/
def genIndependentForest (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) : List (NTree (GenMemoryRow K)) :=
  reqs.map fun r => genRecordTree E z α r.root r.child r.axis r.recordExp

/-! ## D. Agreement with the manually-built OP9 Root B tree

The OP9 arm-fetch record is `(core, arm, 2, 3)` — axis `2` means one decompose step to
the head, then verify.  The builder descends `op9CoreNoun = [[1 7] [1 9]]` along axis `2`:
decomposes the core to `op9Arm = [1 7]` (head) and `op9CoreTail = [1 9]` (tail), continues
on the head (axis `2 / 2 = 1 < 2`), and places the verify node.  Since both children are
cells (not atoms), no halt nodes are emitted.  The result is the three-row tree
`read_root → decompose → verify_child` that matches Root B of `op9ForestData`. -/

/-- The generic builder reproduces OP9 Root B (the arm-fetch tree) exactly. -/
theorem genRecordTree_eq_op9RootB (E : Noun → ComputeTable.FP K) (z α : K) :
    genRecordTree E z α op9CoreNoun op9Arm 2 3
      = .node (gMemRow9 (memReadSkelAx op9CoreNoun op9Arm 2) 3 z
                (op9ReadPub E op9CoreNoun op9Arm 2 (α ^ 3)))
          [.node (gMemRow9 (memDecomposeSkel op9CoreNoun op9Arm op9CoreTail) 0 z
                    (op9DecPub E op9CoreNoun op9Arm op9CoreTail))
            [.node (gMemRow9 (memVerifySkelAx op9CoreNoun op9Arm 2) 3 z
                      (op9VerifyPub E op9CoreNoun op9Arm 2 (α ^ 3))) []]] := by
  unfold genRecordTree
  unfold genAxisDescent
  simp only [show ¬(2 < 2) from by omega, ite_false, formulaHead, formulaTail, op9CoreNoun,
    show axisTopBit 2 = false from axisTopBit_two, axisRest_two,
    Bool.false_eq_true, ↓reduceIte]
  unfold genAxisDescent
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genVerifySubtree, genHaltNodes, op9Arm, op9CoreTail, List.append_nil]

/-! ## E. Axis-3 (tail direction) agreement test

The OP9 formula-tail record is `(formula, formula_tail, 3, 1)` — axis `3` means one decompose
step to the tail.  The builder descends `op9ParentFormula = [9 [b c]]` along axis `3`:
decomposes to head `.atom 9` and tail `[b c] = op9ParentTail`, goes right (tail direction),
and halts the atom head `9`.  The result is a four-row tree
`read_root → decompose → (halt(9), verify_child)` that exercises the tail direction and
atom-halt sibling. -/

/-- The builder produces the correct tail-direction tree for the OP9 formula-open record. -/
theorem genRecordTree_axis3 (E : Noun → ComputeTable.FP K) (z α : K) :
    genRecordTree E z α op9ParentFormula op9ParentTail 3 1
      = .node (gMemRow9 (memReadSkelAx op9ParentFormula op9ParentTail 3) 1 z
                (op9ReadPub E op9ParentFormula op9ParentTail 3 (α ^ 1)))
          [.node (gMemRow9 (memDecomposeSkel op9ParentFormula (.atom 9) op9ParentTail) 0 z
                    (op9DecPub E op9ParentFormula (.atom 9) op9ParentTail))
            [.node (gMemRow9 (memHaltSkel 9) 0 z (op9HaltPub E 9)) [],
             .node (gMemRow9 (memVerifySkelAx op9ParentFormula op9ParentTail 3) 1 z
                      (op9VerifyPub E op9ParentFormula op9ParentTail 3 (α ^ 1))) []]] := by
  unfold genRecordTree
  unfold genAxisDescent
  simp only [show ¬((3 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    op9ParentFormula, show axisTopBit 3 = true from axisTopBit_three, axisRest_three,
    ↓reduceIte]
  unfold genAxisDescent
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genVerifySubtree, genHaltNodes, op9ParentTail, List.cons_append, List.nil_append]

/-! ## F. Independent forest builder agreement

The `genIndependentForest` builder with the single OP9 arm-fetch request produces the same
tree as the manually-built OP9 Root B. -/

/-- The independent forest with the OP9 arm-fetch record produces OP9 Root B. -/
theorem genIndependentForest_op9ArmFetch (E : Noun → ComputeTable.FP K) (z α : K) :
    genIndependentForest E z α
      [⟨op9CoreNoun, op9Arm, 2, 3⟩]
      = [genRecordTree E z α op9CoreNoun op9Arm 2 3] := by
  simp [genIndependentForest]

/-! ## G. Pipeline bridge: service requests → memory forest

The compute tree's `genServiceReqs` produces `ServiceReq K` objects with field-valued
timestamps.  The forest builder needs `MemRecordReq` with natural-number exponents.  The
bridge function `genForestFromServiceReqs` takes requests paired with their exponents. -/

/-- Convert a service request to a memory record request given the natural exponent. -/
def ServiceReq.toMemRecordReq (r : ServiceReq K) (recordExp : ℕ) : MemRecordReq :=
  { root := r.root, child := r.child, axis := r.axis, recordExp := recordExp }

/-- Build the served forest from service requests paired with their natural exponents.
    Each `(request, exponent)` pair generates one independent record tree. -/
def genForestFromServiceReqs (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List (ServiceReq K × ℕ)) : List (NTree (GenMemoryRow K)) :=
  reqs.map fun (r, e) => genRecordTree E z α r.root r.child r.axis e

/-- The pipeline bridge produces one tree per request. -/
theorem genForestFromServiceReqs_length (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List (ServiceReq K × ℕ)) :
    (genForestFromServiceReqs E z α reqs).length = reqs.length := by
  simp [genForestFromServiceReqs]

/-- The pipeline bridge produces the same tree as `genRecordTree` for each request. -/
theorem genForestFromServiceReqs_singleton (E : Noun → ComputeTable.FP K) (z α : K)
    (r : ServiceReq K) (e : ℕ) :
    genForestFromServiceReqs E z α [(r, e)]
      = [genRecordTree E z α r.root r.child r.axis e] := by
  simp [genForestFromServiceReqs]

/-! ## H. Non-vacuity -/

/-- The builder produces a non-empty tree (not a leaf). -/
theorem genRecordTree_nonempty (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    ∃ r cs, genRecordTree E z α root child axis recordExp = .node r cs :=
  ⟨_, _, rfl⟩

/-- The independent forest has one tree per request. -/
theorem genIndependentForest_length (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) :
    (genIndependentForest E z α reqs).length = reqs.length := by
  simp [genIndependentForest]

/-! ## I. Axis descent with custom continuation

The axis descent `genAxisDescentCont` generalizes `genAxisDescent` by placing an
arbitrary continuation at the terminal position (axis < 2) instead of a verify subtree.
This is the primitive for building chained/interleaved trees where multiple read/verify
pairs share structural decomposition steps. -/

/-- Axis descent placing `cont` at the terminal instead of a verify subtree.
    When `remainingAxis < 2`, returns `cont`; otherwise decomposes, recurses in the axis
    direction, and halts the sibling (if atom). -/
def genAxisDescentCont (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K)))
    (currentNoun : Noun) (remainingAxis : ℕ) : List (NTree (GenMemoryRow K)) :=
  if remainingAxis < 2 then cont
  else
    let hd := formulaHead currentNoun
    let tl := formulaTail currentNoun
    let decRow := gMemRow9 (memDecomposeSkel currentNoun hd tl) 0 z
                    (op9DecPub E currentNoun hd tl)
    if axisTopBit remainingAxis then
      [.node decRow
        (genHaltNodes E z hd
         ++ genAxisDescentCont E z cont tl (axisRest remainingAxis))]
    else
      [.node decRow
        (genAxisDescentCont E z cont hd (axisRest remainingAxis)
         ++ genHaltNodes E z tl)]
termination_by remainingAxis
decreasing_by
  all_goals
    apply axisRest_lt
    omega

/-- `genAxisDescent` agrees with `genAxisDescentCont` using the verify subtree as continuation. -/
theorem genAxisDescent_eq_cont (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    genAxisDescent E z root child recAxis ts recordExp currentNoun remainingAxis
      = genAxisDescentCont E z
          [genVerifySubtree E z root child recAxis ts recordExp]
          currentNoun remainingAxis := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAxisDescent genAxisDescentCont
    split
    · rfl
    · rename_i hlt
      have ih' := ih (axisRest n) (axisRest_lt (by omega))
      split <;> simp only [ih']

/-! ## J. Chained multi-record tree builder

The chained pattern builds a single NTree serving multiple records that form a chain:
rec₁.child = rec₂.root, rec₂.child = rec₃.root, etc.  The tree interleaves reads and
verifies: Read₁ → descent₁ → Read₂ → Verify₁ → descent₂ →... → Verify_N.

This is the OP0 Root A pattern (two formula-open records chained on the formula
decomposition) and the OP9 Root A pattern (formula-open + formula-tail records). -/

/-- Build the inner continuation for a chained sequence: given the previous record `prev`
    and the remaining records `rest`, produce the NTree children that go at the terminal
    of `prev`'s axis descent.  For the last record, this is just the verify subtree.
    For a chain, it nests: Read(next) → [Verify(prev) → descent(next) →...]. -/
def genChainedInner (E : Noun → ComputeTable.FP K) (z α : K)
    (prev : MemRecordReq) : List MemRecordReq → List (NTree (GenMemoryRow K))
  | [] =>
    [genVerifySubtree E z prev.root prev.child prev.axis (α ^ prev.recordExp) prev.recordExp]
  | r :: more =>
    let tsPrev := α ^ prev.recordExp
    let tsR := α ^ r.recordExp
    let innerCont := genChainedInner E z α r more
    let descent2 := genAxisDescentCont E z innerCont r.root r.axis
    let verifyPrev := .node
      (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis) prev.recordExp z
        (op9VerifyPub E prev.root prev.child prev.axis tsPrev))
      descent2
    [.node (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z
              (op9ReadPub E r.root r.child r.axis tsR))
      [verifyPrev]]

/-- Build a chained memory tree from a non-empty list of records forming a chain.
    Returns `none` on empty input, the single-record tree for a singleton, and the
    full interleaved tree for chains of length ≥ 2. -/
def genChainedTree (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) : Option (NTree (GenMemoryRow K)) :=
  match reqs with
  | [] => none
  | [r] => some (genRecordTree E z α r.root r.child r.axis r.recordExp)
  | r :: rest =>
    let ts := α ^ r.recordExp
    let innerCont := genChainedInner E z α r rest
    let descent := genAxisDescentCont E z innerCont r.root r.axis
    some (.node (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z
                   (op9ReadPub E r.root r.child r.axis ts))
            descent)

/-! ## K. Chained builder agreement tests -/

/-- The chained builder on a singleton produces the same tree as `genRecordTree`. -/
theorem genChainedTree_singleton (E : Noun → ComputeTable.FP K) (z α : K) (r : MemRecordReq) :
    genChainedTree E z α [r] = some (genRecordTree E z α r.root r.child r.axis r.recordExp) :=
  rfl

/-- The chained builder on an empty list produces `none`. -/
theorem genChainedTree_empty (E : Noun → ComputeTable.FP K) (z α : K) :
    genChainedTree E z α [] = none := rfl

/-- `genChainedTree` always returns `some` for non-empty lists. -/
theorem genChainedTree_isSome (E : Noun → ComputeTable.FP K) (z α : K)
    (r : MemRecordReq) (rs : List MemRecordReq) :
    (genChainedTree E z α (r :: rs)).isSome = true := by
  cases rs <;> rfl

/-- The OP9 Root A is a chained pair: formula-open `[9 [b c]] @3` and formula-tail `[b c] @2`.
    The chained builder produces the Read→Decompose→Read→Verify→Decompose→Verify skeleton
    matching `op9ForestData` Root A, with the terminal verify including a halt child for
    `op9AxisAtom =.atom 2` (the manual OP9 forest omits this). -/
theorem genChainedTree_op9RootA (E : Noun → ComputeTable.FP K) (z α : K) :
    genChainedTree E z α
      [⟨op9ParentFormula, op9ParentTail, 3, 1⟩,
       ⟨op9ParentTail, op9AxisAtom, 2, 2⟩]
    = some
      (.node (gMemRow9 (memReadSkelAx op9ParentFormula op9ParentTail 3) 1 z
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
                          (op9VerifyPub E op9ParentTail op9AxisAtom 2 (α ^ 2)))
                  [.node (gMemRow9 (memHaltSkel 2) 0 z (op9HaltPub E 2)) []]]]]]])
    := by
  unfold genChainedTree
  unfold genChainedInner
  unfold genChainedInner
  unfold genAxisDescentCont
  unfold genAxisDescentCont
  simp only [show ¬((3 : ℕ) < 2) from by omega,
    show ¬((2 : ℕ) < 2) from by omega,
    show axisTopBit 3 = true from axisTopBit_three, axisRest_three, ↓reduceIte,
    show axisTopBit 2 = false from axisTopBit_two, axisRest_two,
    Bool.false_eq_true, formulaHead, formulaTail, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula,
    genHaltNodes]
  unfold genAxisDescentCont
  unfold genAxisDescentCont
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genVerifySubtree, genHaltNodes,
    List.cons_append, List.nil_append, List.append_nil]

/-! ## L. Annotated pub constructors (bottom-up indicator/counts)

The zero-indicator builders (`op9ReadPub`, `op9DecPub`, `op9VerifyPub`, `op9HaltPub`) produce pubs
with `indicator = 0`, `counts = 0` everywhere — suitable when the memory table is consumed with the
trivial indicator assignment.  The annotated constructors below thread the correct indicator/counts
bottom-up so that `eqBlk` holds at every node:

  * halt:           indicator = 0, counts = 0
  * decompose:      pw_P = λ·(pw_L + pw_R);
                    counts_P = counts_L + counts_R + (λ − 1)·(pw_L + pw_R) + pw_R
  * verify_child:   pw_P = pw_L + λ^{n−1}·ts;
                    counts_P = counts_L + λ^{n−1}·ts
  * read_root:      pw_P = pw_L − λ^{n−1}·T·ts;
                    counts_P = counts_L − T·C'·ts
    (`T`, `C'` of the executed row `encodeRow` of the generated a-bearing row at the configuration's `λ`)
  The generated rows are a-bearing: `read_root`/`verify_child` records hold the
  Nock axis, and `(T, C')` are written by the single encode site `MemoryRowTemplate.encodeRow`. -/

/-- Root state of a descent at `remainingAxis`: `verify_child` if at a leaf, `decompose` otherwise. -/
def descentRootState (remainingAxis : ℕ) : MemoryTable.MState :=
  if remainingAxis < 2 then .verify_child else .decompose

/-- Root state of a continuation-based descent: returns `contState` at a leaf,
    `decompose` otherwise. -/
def descentContRootState (contState : MemoryTable.MState) (remainingAxis : ℕ)
    : MemoryTable.MState :=
  if remainingAxis < 2 then contState else .decompose

/-- Root state of a chained inner continuation:
    * empty continuation → `verify_child` (the terminal verify node)
    * non-empty continuation → `read_root` (the outermost read node wrapping the rest) -/
def chainedInnerRootState : List MemRecordReq → MemoryTable.MState
  | [] => .verify_child
  | _ :: _ => .read_root

/-- Annotated decompose pub: indicator/counts computed from given lc/rc cells.
    `lcSt`/`rcSt` are the `MState` of the left/right child subtree roots.
    `ipre`/`icur` are the LogUp accumulator pair (set to 0 for the generic builder;
    opcode-specific agreement proofs thread the correct values). -/
def annotatedDecPub (E : Noun → ComputeTable.FP K) (parent _head _tail : Noun)
    (lcCell rcCell : MemoryTable.Cell K)
    (lcSt rcSt : MemoryTable.MState) (ipre icur : K)
    (lmb : K) : MemoryTable.Pub K where
  st := .decompose
  pt := ⟨E parent,
         lmb * (lcCell.indicator + rcCell.indicator),
         lcCell.counts + rcCell.counts
           + (lmb - 1) * (lcCell.indicator + rcCell.indicator) + rcCell.indicator⟩
  lc := lcCell
  rc := rcCell
  lcSt := lcSt
  rcSt := rcSt
  mem := ComputeTable.MemRec.zero
  ipre := ipre
  icur := icur
  ver := false
  lambda? := some lmb

/-- Annotated verify pub: indicator/counts propagated from given lc cell.
    `ipre`/`icur` are the LogUp accumulator pair.  Honest `ver = false`.
    **A-bearing**: the record stores the Nock
    axis nat-cast and `cprime?` is unset.  The executed row is `MemoryRowTemplate.encodeRow` of
    this row, which writes `(T, C', λ)`; the verify leftover reads only `ts`, so it is the same
    on both views. -/
noncomputable def annotatedVerifyPub (E : Noun → ComputeTable.FP K) (root child : Noun)
    (ax : ℕ) (ts : K) (lcCell : MemoryTable.Cell K)
    (ipre icur : K) (lmb : K) : MemoryTable.Pub K where
  st := .verify_child
  pt := ⟨E child,
         lcCell.indicator + lmb ^ MemoryTable.pwScaleExp K * ts,
         lcCell.counts + lmb ^ MemoryTable.pwScaleExp K * ts⟩
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
noncomputable def annotatedReadPub (E : Noun → ComputeTable.FP K) (root child : Noun)
    (ax : ℕ) (ts : K) (lcCell : MemoryTable.Cell K)
    (ipre icur : K) (lmb : K) : MemoryTable.Pub K where
  st := .read_root
  pt := ⟨E root,
         lcCell.indicator - MemoryTable.formRReadPw lmb ⟨E root, E child, (ax : K), ts⟩,
         lcCell.counts - MemoryTable.formRReadCounts lmb ⟨E root, E child, (ax : K), ts⟩⟩
  lc := lcCell
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := ⟨E root, E child, (ax : K), ts⟩
  ipre := ipre
  icur := icur
  ver := true
  lambda? := some lmb

/-! ## M. Annotated axis descent

The annotated descent mirrors `genAxisDescent` but computes indicator/counts during construction.
Each function returns the tree children **and** the pt cell of the root, which the parent uses to
set its lc/rc fields.  This avoids the post-processing problem of determining which NTree child
corresponds to lc vs rc in a decompose node. -/

/-- Root state of a paper-fan-out noun walk: halt at an atom, decompose at a cell. -/
def nounWalkRootState : Noun → MemoryTable.MState
  | .atom _ => .halt
  | .cell _ _ => .decompose

/-- Walk a noun with no live memory record, matching `fanoutMem`:
    an atom is a halt leaf; a cell is a decompose node with two child walks.
    Off-path siblings and `verify_child`'s unique child use this instead of
    `genHaltNodes`, which emits nothing for cells. -/
def genAnnotatedNounWalk (E : Noun → ComputeTable.FP K) (z lmb : K) :
    Noun → NTree (GenMemoryRow K) × MemoryTable.Cell K
  | .atom a =>
    (.node (gMemRow9 (memHaltSkel a) 0 z (op9HaltPub E a)) [], (op9HaltPub E a).pt)
  | .cell h t =>
    (.node (gMemRow9 (memDecomposeSkel (.cell h t) h t) 0 z
        (annotatedDecPub E (.cell h t) h t
          (genAnnotatedNounWalk E z lmb h).2 (genAnnotatedNounWalk E z lmb t).2
          (nounWalkRootState h) (nounWalkRootState t) 0 0 lmb))
      [(genAnnotatedNounWalk E z lmb h).1, (genAnnotatedNounWalk E z lmb t).1],
     (annotatedDecPub E (.cell h t) h t
       (genAnnotatedNounWalk E z lmb h).2 (genAnnotatedNounWalk E z lmb t).2
       (nounWalkRootState h) (nounWalkRootState t) 0 0 lmb).pt)

theorem genAnnotatedNounWalk_pt_noun (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).2.noun = E n
  | .atom a => by simp [genAnnotatedNounWalk, op9HaltPub]
  | .cell h t => by simp [genAnnotatedNounWalk, annotatedDecPub]

theorem genAnnotatedNounWalk_indicator (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).2.indicator = 0
  | .atom a => by simp [genAnnotatedNounWalk, op9HaltPub]
  | .cell h t => by
      simp [genAnnotatedNounWalk, annotatedDecPub,
        genAnnotatedNounWalk_indicator E z h, genAnnotatedNounWalk_indicator E z t]

/-- The noun walk's `counts` is `0` at every `λ` (no live record below it). -/
theorem genAnnotatedNounWalk_counts_zero (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).2.counts = 0
  | .atom a => by simp [genAnnotatedNounWalk, op9HaltPub]
  | .cell h t => by
      simp [genAnnotatedNounWalk, annotatedDecPub,
        genAnnotatedNounWalk_counts_zero E z h, genAnnotatedNounWalk_counts_zero E z t,
        genAnnotatedNounWalk_indicator E z h, genAnnotatedNounWalk_indicator E z t]

/-- Node count of a paper-fan-out noun walk: one halt per atom,
    one decompose per cell. -/
def nounWalkSize : Noun → ℕ
  | .atom _ => 1
  | .cell h t => 1 + nounWalkSize h + nounWalkSize t

theorem genAnnotatedNounWalk_size (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).1.size = nounWalkSize n
  | .atom a => by simp [genAnnotatedNounWalk, nounWalkSize, NTree.size]
  | .cell h t => by
      simp [genAnnotatedNounWalk, nounWalkSize, NTree.size]
      rw [genAnnotatedNounWalk_size E z h, genAnnotatedNounWalk_size E z t]
      omega

/-- Annotated verify subtree: a `verify_child` node whose unique child is the
    paper-fan-out walk of the served noun. -/
noncomputable def genAnnotatedVerify (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    : NTree (GenMemoryRow K) × MemoryTable.Cell K :=
  (.node (gMemRow9 (memVerifySkelAx root child ax) recordExp z
      (annotatedVerifyPub E root child ax ts (genAnnotatedNounWalk E z lmb child).2 0 0 lmb))
    [(genAnnotatedNounWalk E z lmb child).1],
   (annotatedVerifyPub E root child ax ts (genAnnotatedNounWalk E z lmb child).2 0 0 lmb).pt)

/-- Annotated axis descent: builds the decomposition chain with correct indicator/counts.
    Returns the list of children to place under the parent and the pt cell of the root. -/
noncomputable def genAnnotatedDescent (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ)
    : List (NTree (GenMemoryRow K)) × MemoryTable.Cell K :=
  if remainingAxis < 2 then
    let (vt, vc) := genAnnotatedVerify E z lmb root child recAxis ts recordExp
    ([vt], vc)
  else
    let hd := formulaHead currentNoun
    let tl := formulaTail currentNoun
    if axisTopBit remainingAxis then
      let (headWalk, lcCell) := genAnnotatedNounWalk E z lmb hd
      let (tailTrees, tailCell) :=
        genAnnotatedDescent E z lmb root child recAxis ts recordExp tl
          (axisRest remainingAxis)
      let pub := annotatedDecPub E currentNoun hd tl lcCell tailCell
          (nounWalkRootState hd) (descentRootState (axisRest remainingAxis)) 0 0 lmb
      ([.node (gMemRow9 (memDecomposeSkel currentNoun hd tl) 0 z pub)
          ([headWalk] ++ tailTrees)], pub.pt)
    else
      let (headTrees, headCell) :=
        genAnnotatedDescent E z lmb root child recAxis ts recordExp hd
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
noncomputable def genAnnotatedRecordTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) : NTree (GenMemoryRow K) :=
  let ts := α ^ recordExp
  let (descentChildren, descentCell) :=
    genAnnotatedDescent E z lmb root child axis ts recordExp root axis
  let pub := annotatedReadPub E root child axis ts descentCell 0 0 lmb
  .node (gMemRow9 (memReadSkelAx root child axis) recordExp z pub) descentChildren

/-! ## N. Annotated chained descent

The annotated continuation-based descent generalizes `genAxisDescentCont` by threading
indicator/counts through the continuation as well. -/

/-- Annotated axis descent with custom continuation: places `cont` at the terminal instead
    of a verify subtree, using `contCell` as the continuation root's pt cell.
    `contState` is the `MState` of the continuation's root node. -/
noncomputable def genAnnotatedDescentCont (E : Noun → ComputeTable.FP K) (z lmb : K)
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
        genAnnotatedDescentCont E z lmb cont contCell contState tl
          (axisRest remainingAxis)
      let pub := annotatedDecPub E currentNoun hd tl lcCell tailCell
          (nounWalkRootState hd)
          (descentContRootState contState (axisRest remainingAxis)) 0 0 lmb
      ([.node (gMemRow9 (memDecomposeSkel currentNoun hd tl) 0 z pub)
          ([headWalk] ++ tailTrees)], pub.pt)
    else
      let (headTrees, headCell) :=
        genAnnotatedDescentCont E z lmb cont contCell contState hd
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
noncomputable def genAnnotatedChainedInner (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (prev : MemRecordReq)
    : List MemRecordReq → List (NTree (GenMemoryRow K)) × MemoryTable.Cell K
  | [] =>
    let (vt, vc) := genAnnotatedVerify E z lmb prev.root prev.child prev.axis
                      (α ^ prev.recordExp) prev.recordExp
    ([vt], vc)
  | r :: more =>
    let tsPrev := α ^ prev.recordExp
    let tsR := α ^ r.recordExp
    let (innerCont, innerCell) := genAnnotatedChainedInner E z α lmb r more
    let innerRootState := chainedInnerRootState more
    let (descent2, descent2Cell) :=
      genAnnotatedDescentCont E z lmb innerCont innerCell innerRootState r.root r.axis
    let verifyPub := annotatedVerifyPub E prev.root prev.child prev.axis tsPrev descent2Cell 0 0 lmb
    let verifyNode : NTree (GenMemoryRow K) := .node
      (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis) prev.recordExp z verifyPub)
      descent2
    let readLcCell := verifyPub.pt
    let readPub := annotatedReadPub E r.root r.child r.axis tsR readLcCell 0 0 lmb
    ([.node (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z readPub)
        [verifyNode]], readPub.pt)

/-- Annotated chained tree: builds a chained memory tree with correct indicator/counts. -/
noncomputable def genAnnotatedChainedTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) : Option (NTree (GenMemoryRow K)) :=
  match reqs with
  | [] => none
  | [r] => some (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)
  | r :: rest =>
    let ts := α ^ r.recordExp
    let (innerCont, innerCell) := genAnnotatedChainedInner E z α lmb r rest
    let innerRootState := chainedInnerRootState rest
    let (descent, descentCell) :=
      genAnnotatedDescentCont E z lmb innerCont innerCell innerRootState r.root r.axis
    let pub := annotatedReadPub E r.root r.child r.axis ts descentCell 0 0 lmb
    some (.node (gMemRow9 (memReadSkelAx r.root r.child r.axis) r.recordExp z pub) descent)

/-! ## O. Annotated forest builder -/

/-- Build an annotated independent forest from a list of record requests. -/
noncomputable def genAnnotatedForest (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) : List (NTree (GenMemoryRow K)) :=
  reqs.map fun r => genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp

/-! ## P. Correctness properties of the annotated builder -/

/-- The annotated descent always produces exactly one tree (a single decompose or verify node). -/
theorem genAnnotatedDescent_length (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    (genAnnotatedDescent E z lmb root child recAxis ts recordExp currentNoun remainingAxis).1.length
      = 1 := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · simp [genAnnotatedVerify]
    · split <;> simp

/-- The annotated record tree is always non-empty (has a root). -/
theorem genAnnotatedRecordTree_nonempty (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    ∃ r cs, genAnnotatedRecordTree E z α lmb root child axis recordExp = .node r cs :=
  ⟨_, _, rfl⟩

/-- The annotated forest has one tree per request. -/
theorem genAnnotatedForest_length (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) :
    (genAnnotatedForest E z α lmb reqs).length = reqs.length := by
  simp [genAnnotatedForest]

-- `genAnnotatedDescent_indicator` (root indicator `= ts`) and the tautological
-- `genAnnotatedRecordTree_root_indicator` held only at the retired dummy `λ = 1`.  At the
-- configuration's `λ` the closed form is
-- `GenChainedLanguage.genAnnotatedDescentCont_cell` / `genAnnotatedDescent_root_cell`.

theorem genAnnotatedVerify_size (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    (genAnnotatedVerify E z lmb root child ax ts recordExp).1.size
      = 1 + nounWalkSize child := by
  simp [genAnnotatedVerify, NTree.size, genAnnotatedNounWalk_size]

/-- Axis-2 formula-tail record on a cell: read + decompose + verify(head) + walk(tail). -/
theorem genAnnotatedRecordTree_axis2_size (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e).size
      = 3 + nounWalkSize hd + nounWalkSize tl := by
  unfold genAnnotatedRecordTree genAnnotatedDescent
  simp only [show ¬((2 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    show axisTopBit 2 = false from axisTopBit_two, axisRest_two,
    Bool.false_eq_true, ↓reduceIte]
  unfold genAnnotatedDescent
  simp only [show (1 : ℕ) < 2 from by omega, ite_true, genAnnotatedVerify,
    List.cons_append, List.nil_append]
  simp [NTree.size, genAnnotatedNounWalk_size]
  ring

/-- Axis-3 formula-open record on a cell: read + decompose + walk(head) + verify(tail). -/
theorem genAnnotatedRecordTree_axis3_size (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e).size
      = 3 + nounWalkSize hd + nounWalkSize tl := by
  unfold genAnnotatedRecordTree genAnnotatedDescent
  simp only [show ¬((3 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    show axisTopBit 3 = true from axisTopBit_three, axisRest_three, ↓reduceIte]
  unfold genAnnotatedDescent
  simp only [show (1 : ℕ) < 2 from by omega, ite_true, genAnnotatedVerify,
    List.cons_append, List.nil_append]
  simp [NTree.size, genAnnotatedNounWalk_size]
  omega

/-! ## Q. Compute tree → memory forest extraction

Extract memory record requests from an assigned compute tree and build the served
memory forest.  Each compute row specifies its memory records through the `ServiceReq`
list, with the exponent assigned by `assignExponents` into `stamp.recordExponent`.
The generic builder groups records by detecting chain links (where `prev.child = next.root`)
and uses the chained builder for chainable consecutive pairs. -/

/-- Extract the natural exponent for the `i`-th record from a compute timestamp.
    `recordExponent : Fin 3 → ℕ` covers `i < 3`; out of range returns `0`. -/
def getRecordExp (stamp : ComputeTimestampRow) (i : ℕ) : ℕ :=
  if h : i < 3 then stamp.recordExponent ⟨i, h⟩ else 0

/-- Pair each service request with its record exponent from the timestamp, starting at index `i`. -/
def extractNodeReqsAux (stamp : ComputeTimestampRow) (i : ℕ) :
    List (ServiceReq K) → List MemRecordReq
  | [] => []
  | r :: rs =>
    { root := r.root, child := r.child, axis := r.axis,
      recordExp := getRecordExp stamp i } :: extractNodeReqsAux stamp (i + 1) rs

/-- Extract memory record requests from one compute row, pairing each `ServiceReq`
    with its natural-number exponent from the assigned timestamp. -/
def extractNodeReqs (g : GenComputeRow K) : List MemRecordReq :=
  extractNodeReqsAux g.stamp 0 g.requests

/-! ## R. Row-level memory forest builder with auto-chaining

Given a list of `MemRecordReq`s from one compute row, the builder detects chain
opportunities (where `req₁.child = req₂.root`) and uses the chained builder for
chainable pairs, falling back to independent trees otherwise.

For the NockVM ROM:
  * 1-record opcodes (`OP_1`, `OP_3`, `OP_4`, `cons`): one independent tree
  * 2-record opcodes (`OP_0`, `OP_2`, `OP_5`, `OP_7`, `OP_8`): chain if formula-open
    `@3` feeds into formula-tail `@2` (true for `OP_2`/`OP_5`/`OP_7`/`OP_8`; false for
    `OP_0` where the slot read has a different root)
  * 3-record opcodes (`OP_6`, `OP_9`): first two chain, third is independent -/

/-- Build the memory forest for one compute row's requests, auto-chaining where
    consecutive requests satisfy `prev.child = next.root`. -/
noncomputable def genRowMemForest (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) : List (NTree (GenMemoryRow K)) :=
  match reqs with
  | [] => []
  | [r] => [genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp]
  | [r1, r2] =>
    if r1.child = r2.root then
      match genAnnotatedChainedTree E z α lmb [r1, r2] with
      | some t => [t]
      | none => [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                 genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
    else
      [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
       genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
  | [r1, r2, r3] =>
    let first2 :=
      if r1.child = r2.root then
        match genAnnotatedChainedTree E z α lmb [r1, r2] with
        | some t => [t]
        | none => [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                   genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
      else
        [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
         genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
    first2 ++ [genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp]
  | rs => rs.map fun r => genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp

/-! ## S. Compute tree → full memory forest -/

mutual
noncomputable def genMemForestFromTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    : NTree (GenComputeRow K) → List (NTree (GenMemoryRow K))
  | .node g cs =>
    genRowMemForest E z α lmb (extractNodeReqs g) ++ genMemForestFromList E z α lmb cs

noncomputable def genMemForestFromList (E : Noun → ComputeTable.FP K) (z α lmb : K)
    : List (NTree (GenComputeRow K)) → List (NTree (GenMemoryRow K))
  | [] => []
  | t :: ts => genMemForestFromTree E z α lmb t ++ genMemForestFromList E z α lmb ts
end

/-- **`genTraceGeneric`.**  The generic trace generator.  Compute and memory both
    read BFS stamps (`bfsAssign`), so timestamps cannot diverge from
    `computeSkeletonRows` (`Walk.bfsForest`).  The memory forest is built from
    the assigned tree's record requests with auto-chaining for consecutive
    records that share a root/child link. -/
noncomputable def genTraceGeneric (_q _Λ : ℕ) (z α lmb : K) (fuel : ℕ) (subject formula : Noun)
    : Except GenError (GenTrace K K) :=
  match genComputeSkeleton fuel subject formula with
  | .error e => .error e
  | .ok (ct, result) =>
    let assigned := bfsAssign ct
    .ok
      { subject := subject, formula := formula, result := result, fuel := fuel
        computeNodes := renderRows z α assigned
        memoryNodes := genMemForestFromTree (encC z) z α lmb assigned }

/-! ## T. Wiring correctness properties -/

/-- The singleton case of `genRowMemForest` produces one tree. -/
theorem genRowMemForest_singleton (E : Noun → ComputeTable.FP K) (z α : K) (r : MemRecordReq) :
    genRowMemForest E z α lmb [r]
      = [genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp] := rfl

/-- A chainable pair produces one tree. -/
theorem genRowMemForest_chain_length (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) (hc : r1.child = r2.root) :
    (genRowMemForest E z α lmb [r1, r2]).length = 1 := by
  simp only [genRowMemForest, if_pos hc, genAnnotatedChainedTree, List.length_cons, List.length_nil]

/-- A non-chainable pair produces two trees. -/
theorem genRowMemForest_indep_length (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) (hc : r1.child ≠ r2.root) :
    (genRowMemForest E z α lmb [r1, r2]).length = 2 := by
  simp only [genRowMemForest, if_neg hc, List.length_cons, List.length_nil]

/-- The empty-request case produces no trees. -/
theorem genRowMemForest_nil (E : Noun → ComputeTable.FP K) (z α : K) :
    genRowMemForest E z α lmb [] = [] := rfl

/-- `genMemForestFromTree` on a leaf node equals `genRowMemForest` on its requests. -/
theorem genMemForestFromTree_leaf (E : Noun → ComputeTable.FP K) (z α : K) (g : GenComputeRow K) :
    genMemForestFromTree E z α lmb (.node g [])
      = genRowMemForest E z α lmb (extractNodeReqs g) := by
  unfold genMemForestFromTree genMemForestFromList
  simp

/-- `genTraceGeneric` succeeds exactly when `genComputeSkeleton` succeeds. -/
theorem genTraceGeneric_isOk_iff (q Λ : ℕ) (z α : K) (fuel : ℕ) (subject formula : Noun) :
    (genTraceGeneric q Λ z α lmb fuel subject formula).isOk
      = (genComputeSkeleton (K := K) fuel subject formula).isOk := by
  unfold genTraceGeneric
  cases genComputeSkeleton (K := K) fuel subject formula with
  | error _ => rfl
  | ok p => rfl

/-! ## The executed pub of a generated row

`encPub` is the pub component of that encode at the pub's own state; on a generated row
(`row.1 = st`) it is exactly the executed pub (`encodeRow_pub`). -/

/-- The executed (row-level) pub of a generated a-bearing pub. -/
noncomputable def encPub (lmb : K) (p : MemoryTable.Pub K) : MemoryTable.Pub K :=
  (MemoryRowTemplate.encodeRow lmb (p.st, ((⟨0, 0, 0⟩ : MemoryTable.Inputs K), p))).2.2

theorem encodeRow_pub (row : MemoryTable.MState × MemoryTable.DTmem K)
    (h : row.1 = row.2.2.st) : (MemoryRowTemplate.encodeRow lmb row).2.2 = encPub lmb row.2.2 := by
  obtain ⟨s, i, p⟩ := row
  simp only at h
  subst h
  rfl

@[simp] theorem encodeRow_fst (row : MemoryTable.MState × MemoryTable.DTmem K) :
    (MemoryRowTemplate.encodeRow lmb row).1 = row.1 := rfl

@[simp] theorem encodeRow_inputs (row : MemoryTable.MState × MemoryTable.DTmem K) :
    (MemoryRowTemplate.encodeRow lmb row).2.1 = row.2.1 := rfl

section encodeRowFields
variable (row : MemoryTable.MState × MemoryTable.DTmem K)

@[simp] theorem encodeRow_pub_st : (MemoryRowTemplate.encodeRow lmb row).2.2.st = row.2.2.st := by
  unfold MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encodeRow_pub_pt : (MemoryRowTemplate.encodeRow lmb row).2.2.pt = row.2.2.pt := by
  unfold MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encodeRow_pub_ipre :
    (MemoryRowTemplate.encodeRow lmb row).2.2.ipre = row.2.2.ipre := by
  unfold MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encodeRow_pub_icur :
    (MemoryRowTemplate.encodeRow lmb row).2.2.icur = row.2.2.icur := by
  unfold MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encodeRow_pub_ver : (MemoryRowTemplate.encodeRow lmb row).2.2.ver = row.2.2.ver := by
  unfold MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encodeRow_pub_lambda? :
    (MemoryRowTemplate.encodeRow lmb row).2.2.lambda? = some lmb := by
  unfold MemoryRowTemplate.encodeRow; split <;> rfl

@[simp] theorem encodeRow_pub_mem_ts :
    (MemoryRowTemplate.encodeRow lmb row).2.2.mem.ts = row.2.2.mem.ts := by
  unfold MemoryRowTemplate.encodeRow; split <;> rfl
theorem encodeRow_pub_mem_of_not_active (h : memoryMemRecKind row.1 ≠ .active) :
    (MemoryRowTemplate.encodeRow lmb row).2.2.mem = row.2.2.mem := by
  unfold MemoryRowTemplate.encodeRow; simp [h]

end encodeRowFields

section encPub
variable (p : MemoryTable.Pub K)

@[simp] theorem encPub_st : (encPub lmb p).st = p.st := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_pt : (encPub lmb p).pt = p.pt := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_lc : (encPub lmb p).lc = p.lc := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_rc : (encPub lmb p).rc = p.rc := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_lcSt : (encPub lmb p).lcSt = p.lcSt := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_rcSt : (encPub lmb p).rcSt = p.rcSt := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_ipre : (encPub lmb p).ipre = p.ipre := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_icur : (encPub lmb p).icur = p.icur := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_ver : (encPub lmb p).ver = p.ver := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_lambda? : (encPub lmb p).lambda? = some lmb := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_lambda : (encPub lmb p).lambda = lmb := by
  simp [MemoryTable.Pub.lambda]
@[simp] theorem encPub_mem_root : (encPub lmb p).mem.root = p.mem.root := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_mem_child : (encPub lmb p).mem.child = p.mem.child := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl
@[simp] theorem encPub_mem_ts : (encPub lmb p).mem.ts = p.mem.ts := by
  unfold encPub MemoryRowTemplate.encodeRow; split <;> rfl

theorem encPub_mem_active (h : memoryMemRecKind p.st = .active) :
    (encPub lmb p).mem = NockVM.formRRow p.mem lmb := by
  simp [encPub, MemoryRowTemplate.encodeRow, h]

theorem encPub_cprime_active (h : memoryMemRecKind p.st = .active) :
    (encPub lmb p).cprime = NockVM.formRCprime p.mem lmb := by
  simp [encPub, MemoryRowTemplate.encodeRow, h, MemoryTable.Pub.cprime]

theorem encPub_mem_padding (h : memoryMemRecKind p.st ≠ .active) :
    (encPub lmb p).mem = p.mem := by
  simp [encPub, MemoryRowTemplate.encodeRow, h]

theorem encPub_cprime?_padding (h : memoryMemRecKind p.st ≠ .active) :
    (encPub lmb p).cprime? = p.cprime? := by
  simp [encPub, MemoryRowTemplate.encodeRow, h]

/-- Off `read_root`, the executed row's `eqBlk` is the generated row's (`verify_child` reads only
`child`/`ts`, which the encode keeps; `decompose` reads `λ`). -/
theorem eqBlk_encPub_of_not_read (inp : MemoryTable.Inputs K)
    (hst : p.st ≠ .read_root) (hlam : p.st ≠ .halt → p.lambda = lmb) :
    MemoryTable.eqBlk inp (encPub lmb p) ↔ MemoryTable.eqBlk inp p := by
  unfold MemoryTable.eqBlk
  rw [encPub_st]
  cases hs : p.st with
  | read_root => exact absurd hs hst
  | decompose =>
      have hm : (encPub lmb p).mem = p.mem := encPub_mem_padding p (by simp [hs, memoryMemRecKind])
      simp only [encPub_pt, encPub_lc, encPub_rc, encPub_lambda, hm, hlam (by simp [hs])]
  | halt =>
      have hm : (encPub lmb p).mem = p.mem := encPub_mem_padding p (by simp [hs, memoryMemRecKind])
      simp only [encPub_pt, encPub_lc, encPub_rc, hm]
  | verify_child =>
      simp only [encPub_pt, encPub_lc, encPub_rc, encPub_lambda, encPub_lcSt, encPub_mem_child,
        encPub_mem_ts, hlam (by simp [hs])]

/-- At `γ = 0` (the generator's `memInputs`), the LogUp pole reads only `root.size`, which the
encode keeps; so the executed row's `interV` is the generated row's. -/
theorem interV_encPub_iff (inp : MemoryTable.Inputs K) (hγ : inp.γ = 0) :
    MemoryTable.interV inp (encPub lmb p) ↔ MemoryTable.interV inp p := by
  have hpole : MemoryTable.pole inp (encPub lmb p).mem (encPub lmb p).cprime =
      MemoryTable.pole inp p.mem p.cprime := by
    simp [MemoryTable.pole, MemoryTable.recRLC, hγ]
  unfold MemoryTable.interV
  rw [encPub_st, hpole, encPub_ipre, encPub_icur]

theorem verBool_encPub : MemoryTable.verBool (encPub lmb p) := MemoryTable.verBool_holds _

/-- At `γ = 0` the pole of the executed row is the generated row's. -/
theorem pole_encPub (inp : MemoryTable.Inputs K) (hγ : inp.γ = 0) :
    MemoryTable.pole inp (encPub lmb p).mem (encPub lmb p).cprime =
      MemoryTable.pole inp p.mem p.cprime := by
  simp [MemoryTable.pole, MemoryTable.recRLC, hγ]

theorem interDelta_encPub (inp : MemoryTable.Inputs K) (hγ : inp.γ = 0) :
    MemoryTable.interDelta inp (encPub lmb p) = MemoryTable.interDelta inp p := by
  unfold MemoryTable.interDelta
  rw [encPub_st, pole_encPub p inp hγ]

theorem wf_encPub (inp : MemoryTable.Inputs K) (hγ : inp.γ = 0) (h : MemoryTable.WF inp p) :
    MemoryTable.WF inp (encPub lmb p) :=
  ⟨fun hs => by
    rw [pole_encPub p inp hγ]
    exact h.pole_ne (by simpa using hs)⟩

end encPub

/-- **The executed `read_root` row of the annotated read pub satisfies `eqBlk`.**  Its
`(T, C')` are `encodeRow`'s, and the generated leftover subtracts exactly their Form R weights. -/
theorem annotatedReadPub_encPub_eqBlk (inp : MemoryTable.Inputs K) (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lcCell : MemoryTable.Cell K) (ipre icur : K)
    (hlc : lcCell.noun = E root) :
    MemoryTable.eqBlk inp (encPub lmb (annotatedReadPub E root child ax ts lcCell ipre icur lmb)) := by
  have hact : memoryMemRecKind (annotatedReadPub E root child ax ts lcCell ipre icur lmb).st =
      .active := rfl
  have hm := encPub_mem_active (lmb := lmb) _ hact
  have hc := encPub_cprime_active (lmb := lmb) _ hact
  unfold MemoryTable.eqBlk
  rw [encPub_st]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [annotatedReadPub, hlc]
  · simp [annotatedReadPub]
  · rw [hm, encPub_pt, encPub_lc, encPub_lambda]
    simp [annotatedReadPub, NockVM.formRRow, MemoryTable.formRReadPw]
  · rw [hm, hc, encPub_pt, encPub_lc]
    simp [annotatedReadPub, NockVM.formRRow, NockVM.formRCprime, MemoryTable.formRReadCounts]
  · rw [encPub_mem_root, encPub_pt]; simp [annotatedReadPub]
  · rw [encPub_rc]; simp [annotatedReadPub]

/-- `eqBlk` of the executed (encoded) row of a generated a-bearing pub. -/
def eqBlkE (lmb : K) (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K) : Prop :=
  MemoryTable.eqBlk inp (encPub lmb p)

/-- `Vmem` of the executed (encoded) row of a generated a-bearing pub. -/
def VmemE (lmb : K) (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K) : Prop :=
  MemoryTable.Vmem inp (encPub lmb p)

theorem eqBlkE_of_eqBlk {inp : MemoryTable.Inputs K} {p : MemoryTable.Pub K}
    (hst : p.st ≠ .read_root) (hlam : p.st ≠ .halt → p.lambda = lmb)
    (h : MemoryTable.eqBlk inp p) : eqBlkE lmb inp p :=
  (eqBlk_encPub_of_not_read p inp hst hlam).mpr h

theorem annotatedReadPub_eqBlkE (inp : MemoryTable.Inputs K) (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lcCell : MemoryTable.Cell K) (ipre icur : K)
    (hlc : lcCell.noun = E root) :
    eqBlkE lmb inp (annotatedReadPub E root child ax ts lcCell ipre icur lmb) :=
  annotatedReadPub_encPub_eqBlk inp E root child ax ts lcCell ipre icur hlc

theorem vmemE_of {inp : MemoryTable.Inputs K} {p : MemoryTable.Pub K} (hγ : inp.γ = 0)
    (he : eqBlkE lmb inp p) (hi : MemoryTable.interV inp p) : VmemE lmb inp p :=
  ⟨MemoryTable.verBool_holds _, he, (interV_encPub_iff p inp hγ).mpr hi⟩

theorem VmemE.eqBlkE {inp : MemoryTable.Inputs K} {p : MemoryTable.Pub K} (h : VmemE lmb inp p) :
    eqBlkE lmb inp p := h.2.1

theorem bindMemoryRow_encodeRow {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRowA z s row) :
    BindMemoryRow z s (MemoryRowTemplate.encodeRow lmb row) := by
  obtain ⟨houter, hseed, hst, hpt, hchild, hmem, hver⟩ := h
  have hpub : (MemoryRowTemplate.encodeRow lmb row).2.2 = encPub lmb row.2.2 :=
    encodeRow_pub row (houter.trans hst.symm)
  refine ⟨houter, hseed, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpub, encPub_st]; exact hst
  · rw [hpub, encPub_pt]; exact hpt
  · intro i
    have hi := hchild i
    rw [hpub]
    fin_cases i <;> simpa [memoryChildCell] using hi
  · by_cases ha : memoryMemRecKind s.state = .active
    · rw [dif_pos ha]
      rw [dif_pos ha] at hmem
      have ha' : memoryMemRecKind row.2.2.st = .active := by rw [hst]; exact ha
      rw [hpub, encPub_mem_active _ ha', encPub_cprime_active _ ha']
      obtain ⟨hr, hc, hax⟩ := hmem
      exact ⟨hr, hc, by simp [NockVM.formRRow, hax], by simp [NockVM.formRCprime, hax]⟩
    · rw [dif_neg ha]
      rw [dif_neg ha] at hmem
      have ha' : memoryMemRecKind row.2.2.st ≠ .active := by rw [hst]; exact ha
      rw [hpub, encPub_mem_padding _ ha']
      exact hmem
  · rw [hpub, encPub_ver]; exact hver

/-- The encode keeps the timestamp equations of a row. -/
theorem memoryTimestampSpecializesAt_encodeRow {α : K} {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp row) :
    MemoryTimestampSpecializesAt α stamp (MemoryRowTemplate.encodeRow lmb row) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hpub : (MemoryRowTemplate.encodeRow lmb row).2.2 = encPub lmb row.2.2 :=
    encodeRow_pub row (h1.trans h2.symm)
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [hpub, encPub_st]; exact h2
  · rw [hpub, encPub_mem_ts]; exact h3
  · intro hpad
    rw [hpub, encPub_mem_padding _ (by rw [h2, hpad]; decide)]
    exact h4 hpad

/-! ## The generated rows are a-bearing, at the package `λ`

Every annotated builder leaves `cprime? = none` and writes `lambda? := some λ` (the configuration's `λ`) on every non-halt row (`op9HaltPub` leaves
`lambda?` unset; a halt row reads no `λ`, and the executed row's `encodeRow λ` writes it).
`setGenAcc` copies both fields, so threading does not change them.  The executed rows are the
row encode `MemoryRowTemplate.encodeRow` of these rows, which writes `(T, C', λ)`; this
replaces the retired dummy `C' = 1, λ = 1` invariant. -/

mutual
def AllC (lmb : K) : NTree (GenMemoryRow K) → Prop
  | .node g cs =>
      (g.row.2.2.cprime? = none ∧
        (g.row.2.2.st ≠ MemoryTable.MState.halt → g.row.2.2.lambda = lmb)) ∧ AllCL lmb cs

def AllCL (lmb : K) : List (NTree (GenMemoryRow K)) → Prop
  | [] => True
  | c :: cs => AllC lmb c ∧ AllCL lmb cs
end

theorem allCL_of_forall {cs : List (NTree (GenMemoryRow K))}
    (h : ∀ c ∈ cs, AllC lmb c) : AllCL lmb cs := by
  induction cs with
  | nil => trivial
  | cons a cs ih =>
      exact ⟨h a (by simp), ih (fun c hc => h c (List.mem_cons_of_mem _ hc))⟩

theorem allC_cprime? {t : NTree (GenMemoryRow K)} (h : AllC lmb t) :
    t.label.row.2.2.cprime? = none := by
  cases t with
  | node g cs => simpa [AllC, NTree.label] using h.1.1

/-- The a-bearing row's `Pub.cprime` is the unset default. -/
theorem allC_cprime {t : NTree (GenMemoryRow K)} (h : AllC lmb t) :
    t.label.row.2.2.cprime = 1 := by
  simp [MemoryTable.Pub.cprime, allC_cprime? h]

theorem allC_lambda {t : NTree (GenMemoryRow K)} (h : AllC lmb t) :
    t.label.row.2.2.st ≠ MemoryTable.MState.halt → t.label.row.2.2.lambda = lmb := by
  cases t with
  | node g cs => simpa [AllC, NTree.label] using h.1.2

theorem allCL_mem : ∀ {cs : List (NTree (GenMemoryRow K))} {c},
    AllCL lmb cs → c ∈ cs → AllC lmb c
  | [], _, _, h => by simp at h
  | _ :: _, _, h, hc => by
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact h.1
      · exact allCL_mem h.2 hc

theorem allC_child {t c : NTree (GenMemoryRow K)} (h : AllC lmb t)
    (hc : c ∈ t.children) : AllC lmb c := by
  cases t with
  | node g cs =>
      exact allCL_mem (by simpa [AllC] using h.2) hc

theorem genAnnotatedNounWalk_allC (E : Noun → ComputeTable.FP K) (z lmb : K) :
    ∀ n, AllC lmb (genAnnotatedNounWalk E z lmb n).1
  | .atom _ => by
      unfold genAnnotatedNounWalk
      refine ⟨?_, ?_⟩
      · simp [gMemRow9, op9HaltPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
      · exact trivial
  | .cell h t => by
      unfold genAnnotatedNounWalk
      refine ⟨?_, allCL_of_forall ?_⟩
      · simp [gMemRow9, annotatedDecPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
      · intro c hc
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · exact genAnnotatedNounWalk_allC E z lmb h
        · exact genAnnotatedNounWalk_allC E z lmb t

theorem genAnnotatedVerify_allC (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    AllC lmb (genAnnotatedVerify E z lmb root child ax ts recordExp).1 := by
  unfold genAnnotatedVerify
  refine ⟨?_, allCL_of_forall ?_⟩
  · simp [gMemRow9, annotatedVerifyPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    subst hc
    exact genAnnotatedNounWalk_allC E z lmb child

theorem genAnnotatedDescent_allC (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    ∀ t ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
      currentNoun remainingAxis).1, AllC lmb t := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact genAnnotatedVerify_allC E z lmb root child recAxis ts recordExp
    · split
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine ⟨?_, allCL_of_forall ?_⟩
        · simp [gMemRow9, annotatedDecPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | hc
          · exact genAnnotatedNounWalk_allC E z lmb (formulaHead currentNoun)
          · exact ih (axisRest n) (axisRest_lt (by omega))
              (formulaTail currentNoun) c hc
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine ⟨?_, allCL_of_forall ?_⟩
        · simp [gMemRow9, annotatedDecPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with hc | rfl
          · exact ih (axisRest n) (axisRest_lt (by omega))
              (formulaHead currentNoun) c hc
          · exact genAnnotatedNounWalk_allC E z lmb (formulaTail currentNoun)

theorem genAnnotatedRecordTree_allC (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    AllC lmb (genAnnotatedRecordTree E z α lmb root child axis recordExp) := by
  unfold genAnnotatedRecordTree
  refine ⟨?_, allCL_of_forall ?_⟩
  · simp [gMemRow9, annotatedReadPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
  · intro c hc
    exact genAnnotatedDescent_allC E z lmb root child axis (α ^ recordExp) recordExp
      root axis c hc

theorem genAnnotatedDescentCont_allC (E : Noun → ComputeTable.FP K) (z lmb : K)
    (cont : List (NTree (GenMemoryRow K)))
    (contCell : MemoryTable.Cell K) (contState : MemoryTable.MState)
    (currentNoun : Noun) (remainingAxis : ℕ)
    (hcont : ∀ t ∈ cont, AllC lmb t) :
    ∀ t ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
      currentNoun remainingAxis).1, AllC lmb t := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · exact hcont
    · split
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine ⟨?_, allCL_of_forall ?_⟩
        · simp [gMemRow9, annotatedDecPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | hc
          · exact genAnnotatedNounWalk_allC E z lmb (formulaHead currentNoun)
          · exact ih (axisRest n) (axisRest_lt (by omega))
              (formulaTail currentNoun) c hc
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        refine ⟨?_, allCL_of_forall ?_⟩
        · simp [gMemRow9, annotatedDecPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with hc | rfl
          · exact ih (axisRest n) (axisRest_lt (by omega))
              (formulaHead currentNoun) c hc
          · exact genAnnotatedNounWalk_allC E z lmb (formulaTail currentNoun)

theorem genAnnotatedChainedInner_allC (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (prev : MemRecordReq) :
    ∀ reqs, ∀ t ∈ (genAnnotatedChainedInner E z α lmb prev reqs).1, AllC lmb t
  | [] => by
      intro t ht
      simp only [genAnnotatedChainedInner, List.mem_singleton] at ht
      subst ht
      exact genAnnotatedVerify_allC E z lmb prev.root prev.child prev.axis
        (α ^ prev.recordExp) prev.recordExp
  | r :: more => by
      intro t ht
      simp only [genAnnotatedChainedInner, List.mem_singleton] at ht
      subst ht
      refine ⟨?_, allCL_of_forall ?_⟩
      · simp [gMemRow9, annotatedReadPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        refine ⟨?_, allCL_of_forall ?_⟩
        · simp [gMemRow9, annotatedVerifyPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
        · intro d hd
          exact genAnnotatedDescentCont_allC E z lmb
            (genAnnotatedChainedInner E z α lmb r more).1
            (genAnnotatedChainedInner E z α lmb r more).2
            (chainedInnerRootState more) r.root r.axis
            (genAnnotatedChainedInner_allC E z α lmb r more) d hd

theorem genAnnotatedChainedTree_allC (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) (t : NTree (GenMemoryRow K))
    (h : genAnnotatedChainedTree E z α lmb reqs = some t) : AllC lmb t := by
  match reqs with
  | [] => simp [genAnnotatedChainedTree] at h
  | [r] =>
      simp only [genAnnotatedChainedTree] at h
      injection h with ht
      rw [← ht]
      exact genAnnotatedRecordTree_allC E z α lmb r.root r.child r.axis r.recordExp
  | r :: r2 :: rest =>
      simp only [genAnnotatedChainedTree] at h
      injection h with ht
      subst ht
      refine ⟨?_, allCL_of_forall ?_⟩
      · simp [gMemRow9, annotatedReadPub, MemoryTable.Pub.cprime, MemoryTable.Pub.lambda]
      · intro c hc
        exact genAnnotatedDescentCont_allC E z lmb
          (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
          (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
          (chainedInnerRootState (r2 :: rest)) r.root r.axis
          (genAnnotatedChainedInner_allC E z α lmb r (r2 :: rest)) c hc

theorem genRowMemForest_allC (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) :
    ∀ t ∈ genRowMemForest E z α lmb reqs, AllC lmb t := by
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] =>
      intro t ht
      simp only [genRowMemForest, List.mem_singleton] at ht
      subst ht
      exact genAnnotatedRecordTree_allC E z α lmb r.root r.child r.axis r.recordExp
  | [r1, r2] =>
      intro t ht
      simp only [genRowMemForest] at ht
      by_cases hch : r1.child = r2.root
      · rw [if_pos hch] at ht
        generalize hchain : genAnnotatedChainedTree E z α lmb [r1, r2] = o
        cases o
        · rw [hchain] at ht
          simp [List.mem_cons, List.mem_singleton, or_false] at ht
          rcases ht with h | h
          · exact h ▸ genAnnotatedRecordTree_allC E z α lmb r1.root r1.child r1.axis r1.recordExp
          · exact h ▸ genAnnotatedRecordTree_allC E z α lmb r2.root r2.child r2.axis r2.recordExp
        · rename_i t'
          rw [hchain] at ht
          simp [List.mem_singleton] at ht
          exact ht ▸ genAnnotatedChainedTree_allC E z α lmb [r1, r2] t' hchain
      · rw [if_neg hch] at ht
        simp [List.mem_cons, List.mem_singleton, or_false] at ht
        rcases ht with h | h
        · exact h ▸ genAnnotatedRecordTree_allC E z α lmb r1.root r1.child r1.axis r1.recordExp
        · exact h ▸ genAnnotatedRecordTree_allC E z α lmb r2.root r2.child r2.axis r2.recordExp
  | [r1, r2, r3] =>
      intro t ht
      have hpair :
          genRowMemForest E z α lmb [r1, r2, r3] =
            genRowMemForest E z α lmb [r1, r2] ++
              [genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp] := by
        simp [genRowMemForest]
      rw [hpair] at ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact genRowMemForest_allC E z α lmb [r1, r2] t ht
      · exact genAnnotatedRecordTree_allC E z α lmb r3.root r3.child r3.axis r3.recordExp
  | r1 :: r2 :: r3 :: r4 :: rest =>
      intro t ht
      simp only [genRowMemForest, List.mem_map] at ht
      obtain ⟨r, _, rfl⟩ := ht
      exact genAnnotatedRecordTree_allC E z α lmb r.root r.child r.axis r.recordExp
termination_by reqs.length

mutual
theorem genMemForestFromTree_allC (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ∀ t, ∀ u ∈ genMemForestFromTree E z α lmb t, AllC lmb u
  | .node g cs => by
      intro u hu
      simp only [genMemForestFromTree, List.mem_append] at hu
      rcases hu with hu | hu
      · exact genRowMemForest_allC E z α lmb _ u hu
      · exact genMemForestFromList_allC E z α lmb cs u hu

theorem genMemForestFromList_allC (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ∀ ts, ∀ u ∈ genMemForestFromList E z α lmb ts, AllC lmb u
  | [] => by simp [genMemForestFromList]
  | t :: ts => by
      intro u hu
      simp only [genMemForestFromList, List.mem_append] at hu
      rcases hu with hu | hu
      · exact genMemForestFromTree_allC E z α lmb t u hu
      · exact genMemForestFromList_allC E z α lmb ts u hu
end

theorem forest_bfs_cprime :
    ∀ (l : List (NTree (GenMemoryRow K))),
      (∀ t ∈ l, AllC lmb t) →
      ∀ n ∈ bfsForest l, n.label.row.2.2.cprime? = none
  | [], _, n, hn => by simp [bfsForest_nil] at hn
  | t :: rest, h, n, hn => by
      rw [bfsForest_cons_eq (t :: rest) (by simp)] at hn
      simp only [List.mem_append] at hn
      rcases hn with hn | hn
      · simp only [List.mem_cons] at hn
        rcases hn with hnt | hn
        · subst hnt
          exact allC_cprime? (h _ (List.mem_cons_self ..))
        · exact allC_cprime? (h n (List.mem_cons_of_mem _ hn))
      · have hall : ∀ c ∈ (t :: rest).flatMap NTree.children, AllC lmb c := by
          intro c hc
          simp only [List.mem_flatMap] at hc
          obtain ⟨s, hs, hc⟩ := hc
          exact allC_child (h s hs) hc
        exact forest_bfs_cprime ((t :: rest).flatMap NTree.children) hall n hn
termination_by l => totalSize l
decreasing_by
  have hsz := totalSize_flatMap_children (t :: rest)
  simp only [List.length_cons] at hsz
  omega

theorem forest_bfs_lambda :
    ∀ (l : List (NTree (GenMemoryRow K))),
      (∀ t ∈ l, AllC lmb t) →
      ∀ n ∈ bfsForest l, n.label.row.2.2.st ≠ MemoryTable.MState.halt →
        n.label.row.2.2.lambda = lmb
  | [], _, n, hn => by simp [bfsForest_nil] at hn
  | t :: rest, h, n, hn => by
      rw [bfsForest_cons_eq (t :: rest) (by simp)] at hn
      simp only [List.mem_append] at hn
      rcases hn with hn | hn
      · simp only [List.mem_cons] at hn
        rcases hn with hnt | hn
        · subst hnt
          exact allC_lambda (h _ (List.mem_cons_self ..))
        · exact allC_lambda (h n (List.mem_cons_of_mem _ hn))
      · have hall : ∀ c ∈ (t :: rest).flatMap NTree.children, AllC lmb c := by
          intro c hc
          simp only [List.mem_flatMap] at hc
          obtain ⟨s, hs, hc⟩ := hc
          exact allC_child (h s hs) hc
        exact forest_bfs_lambda ((t :: rest).flatMap NTree.children) hall n hn
termination_by l => totalSize l
decreasing_by
  have hsz := totalSize_flatMap_children (t :: rest)
  simp only [List.length_cons] at hsz
  omega


#print axioms genHaltNodes
#print axioms genVerifySubtree
#print axioms genAxisDescent
#print axioms genRecordTree
#print axioms genIndependentForest
#print axioms genForestFromServiceReqs
#print axioms genRecordTree_eq_op9RootB
#print axioms genRecordTree_axis3
#print axioms genIndependentForest_op9ArmFetch
#print axioms genForestFromServiceReqs_length
#print axioms genForestFromServiceReqs_singleton
#print axioms genRecordTree_nonempty
#print axioms genIndependentForest_length
#print axioms genAxisDescentCont
#print axioms genAxisDescent_eq_cont
#print axioms genChainedInner
#print axioms genChainedTree
#print axioms genChainedTree_singleton
#print axioms genChainedTree_empty
#print axioms genChainedTree_isSome
#print axioms genChainedTree_op9RootA
#print axioms annotatedDecPub
#print axioms annotatedVerifyPub
#print axioms annotatedReadPub
#print axioms nounWalkRootState
#print axioms genAnnotatedNounWalk
#print axioms genAnnotatedNounWalk_pt_noun
#print axioms genAnnotatedNounWalk_indicator
#print axioms nounWalkSize
#print axioms genAnnotatedNounWalk_size
#print axioms genAnnotatedNounWalk_counts_zero
#print axioms genAnnotatedVerify_size
#print axioms genAnnotatedRecordTree_axis2_size
#print axioms genAnnotatedRecordTree_axis3_size
#print axioms genAnnotatedVerify
#print axioms genAnnotatedDescent
#print axioms genAnnotatedRecordTree
#print axioms genAnnotatedDescentCont
#print axioms genAnnotatedChainedInner
#print axioms genAnnotatedChainedTree
#print axioms genAnnotatedForest
#print axioms genAnnotatedDescent_length
#print axioms genAnnotatedRecordTree_nonempty
#print axioms genAnnotatedForest_length
#print axioms getRecordExp
#print axioms extractNodeReqsAux
#print axioms extractNodeReqs
#print axioms genRowMemForest
#print axioms genMemForestFromTree
#print axioms genMemForestFromList
#print axioms genTraceGeneric
#print axioms genRowMemForest_singleton
#print axioms genRowMemForest_chain_length
#print axioms genRowMemForest_indep_length
#print axioms genRowMemForest_nil
#print axioms genMemForestFromTree_leaf
#print axioms genTraceGeneric_isOk_iff

end Nock.NockVMROM.Thm54.TraceGen
