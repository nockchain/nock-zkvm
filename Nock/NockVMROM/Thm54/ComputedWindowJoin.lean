/-
  Nock/NockVMROM/Thm54/ComputedWindowJoin.lean

`ComputedWindow.GenuineSkel` has three per-row conditions.  On the built tree
  `StrategyOfTraces.mapComputeJoinInFuel` (the join under `decodedSkeletonOf`), two of them are
  **structural** — the join computes exactly the children's inputs `KidInputs` and the row
  evaluation `RowOutput` from the same `nounHead` / `nounTail` / sibling results — except for a
  short residue, which this module names:

  * `join_kidInputs`: `KidInputs` holds at every join row of the right exec arity, given only
    the **OP9 served arm** fact (`slot ax core = arm`).
  * `join_rowOutput`: `RowOutput` holds at every join row of the right exec arity, given only the
    **OP0 served value** (`nounByFP e = slot ax subject`), the **OP4 child
    atom** (`hke` of `Batch530.ComputeJoinReady.op4`) and the **OP6 condition bit**
    (`hcondE` / `hb` of `ComputeJoinReady.op6`).

  So on the built tree the binding induction's carried hypothesis `GenuineSkel` is exactly:
  `FormulaShape` at each row (from `Vcomp` + `PairFaithful` on the formula,
  `OpcodeSemantics.cons_head_is_cell` / `numeric_formula_eq` / `realized_tail_eq_cell`, inside the
  window `ComputedWindow.honestCall_inputs_le` supplies), the exec arity (`ComputeTreeBinds.shape`),
  and the four residue facts above.  Rule 8(b): none of these is a property of arbitrary
  `(Qc, Qm)`.

-- the paper
-/
import Nock.NockVMROM.Thm54.ComputedWindow
import Nock.RedTeam.Batch530Thm54ComputeTreeBindsDeployed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.ComputedWindow

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.RedTeam.Batch530

variable {K : Type} [Field K] [DecidableEq K]

theorem label_node {α : Type*} (a : α) (cs : List (NTree α)) : (NTree.node a cs).label = a := rfl
theorem children_node {α : Type*} (a : α) (cs : List (NTree α)) :
    (NTree.node a cs).children = cs := rfl

theorem condBit_match (n : Noun) :
    (match n with
      | .atom k => k
      | _ => 0) = condBit n := by
  cases n <;> rfl

/-- **`KidInputs` on the built join.**  At a join row of the right exec arity, the children's
inputs are `KidInputs` — structurally, except OP9's arm, which must be the core's slot. -/
theorem join_kidInputs {n q : ℕ} (forest : List (NTree (MState × DTmem K)))
    (row : State × DTcomp K) (ch : List (NTree (State × DTcomp K))) (subj formula : Noun)
    (harity : ch.length = fanoutComp row.1)
    (h9 : ∀ c0 c1, row.1 = .s9 → ch = [c0, c1] →
      Noun.slot (op9Axis formula)
          (mapComputeJoinInFuel n q forest c0 subj (tl (tl formula))).label.evaluation =
        some (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)) :
    KidInputs row.1 subj formula
      ((mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula).children.map
        NTree.label) := by
  obtain ⟨st, d⟩ := row
  cases st <;>
    rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩⟩ <;>
    simp [fanoutComp] at harity
  · simp [mapComputeJoinInFuel, KidInputs]
  · simp [mapComputeJoinInFuel, KidInputs]
  · rw [mapComputeJoinInFuel_s2 forest subj formula (State.s2, d) c0 c1 c2 rfl]
    simp only [KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _
  · simp only [mapComputeJoinInFuel, KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _
  · simp only [mapComputeJoinInFuel, KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _
  · rw [mapComputeJoinInFuel_s5 forest subj formula (State.s5, d) c0 c1 rfl]
    simp only [KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _
  · rw [mapComputeJoinInFuel_s6 forest subj formula (State.s6, d) c0 c1 rfl]
    simp only [KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _
  · rw [mapComputeJoinInFuel_s7 forest subj formula (State.s7, d) c0 c1 rfl]
    simp only [KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _
  · rw [mapComputeJoinInFuel_s8 forest subj formula (State.s8, d) c0 c1 rfl]
    simp only [KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _
  · rw [mapComputeJoinInFuel_s9 forest subj formula (State.s9, d) c0 c1 rfl]
    have h := h9 c0 c1 rfl rfl
    simp only [KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _
      | (rw [mapComputeJoinInFuel_formula]; exact h)
  · rw [mapComputeJoinInFuel_cons forest subj formula (State.cons, d) c0 c1 rfl]
    simp only [KidInputs, children_node, List.map_cons, List.map_nil]
    and_intros <;> first
      | exact mapComputeJoinInFuel_subject _ _ _ _ _ _
      | exact mapComputeJoinInFuel_formula _ _ _ _ _ _

/-- **`RowOutput` on the built join.**  At a join row of the right exec arity, the row's joined
evaluation is the opcode's output from its children — structurally, except the three residue
facts: OP0's served value is the slot, OP4's child evaluation is an atom, OP6's condition is a
bit. -/
theorem join_rowOutput {n q : ℕ} (forest : List (NTree (MState × DTmem K)))
    (row : State × DTcomp K) (ch : List (NTree (State × DTcomp K))) (subj formula : Noun)
    (harity : ch.length = fanoutComp row.1)
    (h0 : row.1 = .s0 → Noun.slot (op0Axis formula) subj = some (nounByFP q forest row.2.2.1.e))
    (h4 : ∀ c0, row.1 = .s4 → ch = [c0] →
      ∃ k, (mapComputeJoinInFuel n q forest c0 subj (tl formula)).label.evaluation = .atom k)
    (h6 : ∀ c0 c1, row.1 = .s6 → ch = [c0, c1] →
      (mapComputeJoinInFuel n q forest c1 subj (hd (tl formula))).label.evaluation = .atom 0 ∨
        (mapComputeJoinInFuel n q forest c1 subj (hd (tl formula))).label.evaluation = .atom 1) :
    RowOutput row.1 subj formula
      ((mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula).children.map
        NTree.label)
      (mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula).label.evaluation := by
  obtain ⟨st, d⟩ := row
  cases st <;>
    rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩⟩ <;>
    simp [fanoutComp] at harity
  · have h := h0 rfl
    simp [mapComputeJoinInFuel, RowOutput, label_node, computeSkeletonRow, joinEvaluation]
    exact h
  · simp [mapComputeJoinInFuel, RowOutput, label_node, computeSkeletonRow, joinEvaluation, tl]
  · rw [mapComputeJoinInFuel_s2 forest subj formula (State.s2, d) c0 c1 c2 rfl]
    simp [RowOutput, children_node, label_node, computeSkeletonRow, joinEvaluation, kidSkel]
  · simp [mapComputeJoinInFuel, RowOutput, children_node, label_node, computeSkeletonRow,
      joinEvaluation, kidSkel]
  · obtain ⟨k, hk⟩ := h4 c0 rfl rfl
    rw [mapComputeJoinInFuel_s4 forest subj formula (State.s4, d) c0 rfl]
    simp only [RowOutput, children_node, label_node, List.map_cons,
      List.map_nil, computeSkeletonRow, joinEvaluation, kidSkel, List.getElem?_cons_zero,
      Option.getD_some]
    simp only [tl] at hk
    rw [hk]
    rfl
  · rw [mapComputeJoinInFuel_s5 forest subj formula (State.s5, d) c0 c1 rfl]
    simp [RowOutput, children_node, label_node, computeSkeletonRow, joinEvaluation, kidSkel]
  · rw [mapComputeJoinInFuel_s6 forest subj formula (State.s6, d) c0 c1 rfl]
    have h := h6 c0 c1 rfl rfl
    simp only [RowOutput, children_node, label_node, List.map_cons, List.map_nil,
      computeSkeletonRow, joinEvaluation, kidSkel, List.getElem?_cons_zero, Option.getD_some]
    exact ⟨h, trivial⟩
  · rw [mapComputeJoinInFuel_s7 forest subj formula (State.s7, d) c0 c1 rfl]
    simp [RowOutput, children_node, label_node, computeSkeletonRow, joinEvaluation, kidSkel]
  · rw [mapComputeJoinInFuel_s8 forest subj formula (State.s8, d) c0 c1 rfl]
    simp [RowOutput, children_node, label_node, computeSkeletonRow, joinEvaluation, kidSkel]
  · rw [mapComputeJoinInFuel_s9 forest subj formula (State.s9, d) c0 c1 rfl]
    simp [RowOutput, children_node, label_node, computeSkeletonRow, joinEvaluation, kidSkel]
  · rw [mapComputeJoinInFuel_cons forest subj formula (State.cons, d) c0 c1 rfl]
    simp [RowOutput, children_node, label_node, computeSkeletonRow, joinEvaluation, kidSkel]

/-- The join row's label is the inputs it was called with, at the exec row's state. -/
theorem join_label {n q : ℕ} (forest : List (NTree (MState × DTmem K)))
    (row : State × DTcomp K) (ch : List (NTree (State × DTcomp K))) (subj formula : Noun) :
    (mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula).label.state = row.1 ∧
      (mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula).label.subject = subj ∧
      (mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula).label.formula =
        formula :=
  ⟨rfl, mapComputeJoinInFuel_subject _ _ _ _ _ _, mapComputeJoinInFuel_formula _ _ _ _ _ _⟩

/-- **The residue, assembled.**  A built join row of the right arity whose formula has its state's
shape satisfies the row conditions of `GenuineSkel` given exactly the four residue facts; with
genuine children (the induction hypothesis) it is a genuine node. -/
theorem join_genuine_node {n q : ℕ} (forest : List (NTree (MState × DTmem K)))
    (row : State × DTcomp K) (ch : List (NTree (State × DTcomp K))) (subj formula : Noun)
    (hshape : FormulaShape row.1 formula)
    (harity : ch.length = fanoutComp row.1)
    (h0 : row.1 = .s0 → Noun.slot (op0Axis formula) subj = some (nounByFP q forest row.2.2.1.e))
    (h4 : ∀ c0, row.1 = .s4 → ch = [c0] →
      ∃ k, (mapComputeJoinInFuel n q forest c0 subj (tl formula)).label.evaluation = .atom k)
    (h6 : ∀ c0 c1, row.1 = .s6 → ch = [c0, c1] →
      (mapComputeJoinInFuel n q forest c1 subj (hd (tl formula))).label.evaluation = .atom 0 ∨
        (mapComputeJoinInFuel n q forest c1 subj (hd (tl formula))).label.evaluation = .atom 1)
    (h9 : ∀ c0 c1, row.1 = .s9 → ch = [c0, c1] →
      Noun.slot (op9Axis formula)
          (mapComputeJoinInFuel n q forest c0 subj (tl (tl formula))).label.evaluation =
        some (joinNoun q row.2.1.z forest row.2.2.1.sf2_f))
    (hkids : ∀ k ∈ (mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula).children,
      GenuineSkel k) :
    GenuineSkel (mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula) := by
  obtain ⟨hst, hsj, hf⟩ := join_label (n := n) (q := q) forest row ch subj formula
  have hin := join_kidInputs (n := n) forest row ch subj formula harity h9
  have hout := join_rowOutput (n := n) forest row ch subj formula harity h0 h4 h6
  rw [ntree_eta (mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula)]
  refine .node ?_ ?_ ?_ hkids
  · rw [hst, hf]; exact hshape
  · rw [hst, hsj, hf]; exact hin
  · rw [hst, hsj, hf]; exact hout

end Nock.NockVMROM.Thm54.ComputedWindow
