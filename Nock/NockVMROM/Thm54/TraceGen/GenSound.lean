/-
  Nock/NockVMROM/Thm54/TraceGen/GenSound.lean

  Generator-side `Vcomp` on rendered compute rows.  `bfsAssign` restamps Nat
  exponents; `GenComputeRow.row` still encodes the DFS `α^e` until `renderRows`.
  Soundness is therefore stated of `renderRows z α (bfsAssign t)`, not of
  `bfsAssign t` itself.  This module does not edit `Gen.lean`.

  The OP1 spike is field-generic over `encC`.  Stamp hypotheses `hln`/`hrec`
  are the two `stampOfAcc` equations at `.s1` (`recordCount = 1`).  Formula
  hypothesis `hform` is the Nock `OP_1` shape `[1 result]`.

  The OP0 spike is the same pipeline at `.s0` (`recordCount = 2`).  `hform`
  is the Nock `OP_0` shape `[0 axis]`, with `axis` the skeleton's second
  memory-record axis (`memBlk` reads `f_t.leaf`).  Stamp hypotheses are
  line advance by 2 and the two consecutive record exponents.

  OP3 and OP4 are the unary-nonterminal shape:
  one formula-open record `[head tail] @3`, one live `sf1` from
  `P8Census.skeletonSubformula skel 0`, `recordCount = 1`.  Stamp hyps match
  OP1.  Extra vs OP1 is `sf1` wiring plus the cell-test / increment result
  off the skeleton, not a second record.

  OP6 is the unique 3-record if/branch shape: fan-out 2, all four decomp columns live, two live sf slots
  (`sf1` = taken branch, `sf2` = condition), `recordCount = 3`.  `hform` is
  `[6 [b [c d]]]` with `b` the live `sf2` formula.  Stamp hyps are line
  advance by 3 and the three consecutive record exponents.

  Cons is the unique autocons / head-is-a-cell shape: fan-out 2, one formula-open record `[leftF rightF] @3`,
  `recordCount = 1`.  Stamp hyps match OP1.  Renderer `renderConsRow` reads
  `formulaHead`/`formulaTail` of formula and evaluation (not
  `skeletonSubformula`).  `SVhead` is `headCell` (`f_h.dyck ≠ 0`).  Extra
  vs OP3: two live sf slots and `e = FP.cons z sf1_e sf2_e`.
-/
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.GlobalCarryRecognizer

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open ComputeTable

variable {K : Type} [Field K]

/-! ## Stamp equations at `OP_1` -/

theorem stampOfAcc_s1_ln (acc : ℕ) :
    (stampOfAcc State.s1 acc).lnExponent =
      (stampOfAcc State.s1 acc).lnPrevExponent + 1 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s1_rec0 (acc : ℕ) :
    (stampOfAcc State.s1 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s1 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s1 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s1 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_1` row -/

theorem renderOp1Row_state (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp1Row z α stamp skel).1 =
      (renderOp1Row z α stamp skel).2.2.1.state :=
  rfl

theorem renderOp1Row_inputs (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp1Row z α stamp skel).2.1 = ⟨α, z, 0, 0, 0⟩ :=
  rfl

/-- Field-generic `Vcomp` for one rendered `OP_1` row.
    `hform` is the Nock constant-formula `[1 result]`; `hln`/`hrec` are the
    line/record exponents `stampOfAcc` already realises at `.s1`. -/
theorem renderOp1Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 1) skel.evaluation)
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 1)
    (hrec : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1) :
    let row := renderOp1Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp1Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · -- `pub.f = FP.cons z f_h f_t`
    rw [hform]
    change encC z (Noun.cell (Noun.atom 1) skel.evaluation) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 1) skel.evaluation)))
        (encC z skel.evaluation)
    simp only [formulaHead]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 1) skel.evaluation
  · -- `mr1 = ⟨f, f_t, 3, ln_prev * α⟩`
    refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec, pow_succ]
  · -- `SVhead` at `.s1` is `headAtom` with leaf `1`
    unfold SVhead
    have hne : ¬ (State.s1 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · -- `memBlk` at `.s1`: padded records and `ln = ln_prev * α`
    unfold memBlk
    refine ⟨rfl, rfl, ?_⟩
    rw [hln, pow_succ]
  · -- `evalV` at `.s1`: `e = f_t` and zero subformula slots
    unfold evalV sfz1 sfz2 sfz3
    refine ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- `Vcomp` for an `OP_1` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp1Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s1)
    (hform : skel.formula = Noun.cell (Noun.atom 1) skel.evaluation) :
    let row := renderOp1Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s1 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp1Row_Vcomp z α (stampOfAcc State.s1 acc) skel hz hform
    (stampOfAcc_s1_ln acc) (stampOfAcc_s1_rec0 acc)

/-! ## `renderNode` / `renderRows` at `OP_1` -/

theorem renderNode_op1_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s1) :
    (renderNode z α g).row = renderOp1Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

theorem renderNode_op1_skel (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).skel = g.skel := by
  unfold renderNode
  cases g.skel.state <;> rfl

theorem renderNode_op1_stamp (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).stamp = g.stamp := by
  unfold renderNode
  cases g.skel.state <;> rfl

/-- Rendered `OP_1` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op1_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s1)
    (hform : g.skel.formula = Noun.cell (Noun.atom 1) g.skel.evaluation)
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 1)
    (hrec : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op1_row z α g hstate]
  exact renderOp1Row_Vcomp z α g.stamp g.skel hz hform hln hrec

theorem renderNode_op1_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s1)
    (hform : g.skel.formula = Noun.cell (Noun.atom 1) g.skel.evaluation)
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s1_ln g.stamp.lnPrevExponent
  have hrec : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s1_rec0 g.stamp.lnPrevExponent
  exact renderNode_op1_Vcomp z α g hz hstate hform hln hrec

theorem renderRows_label_row (z α : K) (t : NTree (GenComputeRow K)) :
    (renderRows z α t).label.row = (renderNode z α t.label).row := by
  cases t with
  | node g cs =>
    simp [renderRows, NTree.label_node]

theorem bfsAssign_label (t : NTree (GenComputeRow K)) :
    (bfsAssign t).label = bfsLabelAt t 1 := by
  rw [bfsAssign, buildTF_label]

theorem bfsRows_leaf (g : GenComputeRow K) :
    bfsRows (.node g []) = [g] := by
  simp [bfsRows, bfsForest_singleton, NTree.children_node, bfsForest_nil]

/-- `bfsAssign` of a leaf is the same node with `stampOfAcc` at accumulator `0`. -/
theorem bfsAssign_leaf_label (g : GenComputeRow K) :
    (bfsAssign (.node g [])).label =
      { g with stamp := stampOfAcc g.skel.state 0 } := by
  rw [bfsAssign_label]
  unfold bfsLabelAt
  simp [bfsRows_leaf, accAt]


/-- Singleton `OP_1` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op1_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s1)
    (hform : g.skel.formula = Noun.cell (Noun.atom 1) g.skel.evaluation) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op1_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]

/-! ## Stamp equations at `OP_0` -/

theorem stampOfAcc_s0_ln (acc : ℕ) :
    (stampOfAcc State.s0 acc).lnExponent =
      (stampOfAcc State.s0 acc).lnPrevExponent + 2 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s0_rec0 (acc : ℕ) :
    (stampOfAcc State.s0 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s0 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s0 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s0 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s0_rec1 (acc : ℕ) :
    (stampOfAcc State.s0 acc).recordExponent (1 : Fin 3) =
      (stampOfAcc State.s0 acc).lnPrevExponent + 2 := by
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s0 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s0 acc (1 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_0` row -/

theorem renderOp0Row_state (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp0Row z α stamp skel).1 =
      (renderOp0Row z α stamp skel).2.2.1.state :=
  rfl

theorem renderOp0Row_inputs (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp0Row z α stamp skel).2.1 = ⟨α, z, 0, 0, 0⟩ :=
  rfl

/-- Field-generic `Vcomp` for one rendered `OP_0` row.
    `hform` is the Nock axis-read formula `[0 axis]`, with `axis` the second
    memory-record axis; `hln`/`hrec0`/`hrec1`
    are the two-record `stampOfAcc` schedule at `.s0`. -/
theorem renderOp0Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 0)
      (Noun.atom (P8Census.skeletonMemoryAxis skel 1)))
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 2)
    (hrec0 : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1)
    (hrec1 : stamp.recordExponent (1 : Fin 3) = stamp.lnPrevExponent + 2) :
    let row := renderOp0Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp0Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · -- `pub.f = FP.cons z f_h f_t`
    rw [hform]
    change encC z (Noun.cell (Noun.atom 0)
        (Noun.atom (P8Census.skeletonMemoryAxis skel 1))) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 0)
        (Noun.atom (P8Census.skeletonMemoryAxis skel 1)))))
        (encC z (formulaTail (Noun.cell (Noun.atom 0)
          (Noun.atom (P8Census.skeletonMemoryAxis skel 1)))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 0)
      (Noun.atom (P8Census.skeletonMemoryAxis skel 1))
  · -- `mr1 = ⟨f, f_t, 3, ln_prev * α⟩`
    refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec0, pow_succ]
  · -- `SVhead` at `.s0` is `headAtom` with leaf `0`
    unfold SVhead
    have hne : ¬ (State.s0 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · -- `memBlk` at `.s0`: slot-read `mr2`, padded `mr3`, `ln = ln_prev * α^2`,
    -- and atom-shaped formula tail
    unfold memBlk
    refine ⟨?mr2, rfl, ?ln, ?ftsize, ?ftdyck⟩
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rw [hform]
        simp only [formulaTail]
        rw [encC_eq, GlobalCarryRecognizer.enc_atom]
        simp [FP.atomFP]
      · rw [hrec1, pow_add]
    · rw [hln, pow_add]
    · rw [hform]
      simp only [formulaTail]
      rw [encC_eq, GlobalCarryRecognizer.enc_atom]
      simp [FP.atomFP]
    · rw [hform]
      simp only [formulaTail]
      rw [encC_eq, GlobalCarryRecognizer.enc_atom]
      simp [FP.atomFP]
  · -- `evalV` at `.s0`: zero subformula slots
    unfold evalV sfz1 sfz2 sfz3
    exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- `Vcomp` for an `OP_0` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp0Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s0)
    (hform : skel.formula = Noun.cell (Noun.atom 0)
      (Noun.atom (P8Census.skeletonMemoryAxis skel 1))) :
    let row := renderOp0Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s0 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp0Row_Vcomp z α (stampOfAcc State.s0 acc) skel hz hform
    (stampOfAcc_s0_ln acc) (stampOfAcc_s0_rec0 acc) (stampOfAcc_s0_rec1 acc)

/-! ## `renderNode` / `renderRows` at `OP_0` -/

theorem renderNode_op0_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s0) :
    (renderNode z α g).row = renderOp0Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_0` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op0_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s0)
    (hform : g.skel.formula = Noun.cell (Noun.atom 0)
      (Noun.atom (P8Census.skeletonMemoryAxis g.skel 1)))
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2)
    (hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1)
    (hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op0_row z α g hstate]
  exact renderOp0Row_Vcomp z α g.stamp g.skel hz hform hln hrec0 hrec1

theorem renderNode_op0_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s0)
    (hform : g.skel.formula = Noun.cell (Noun.atom 0)
      (Noun.atom (P8Census.skeletonMemoryAxis g.skel 1)))
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s0_ln g.stamp.lnPrevExponent
  have hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s0_rec0 g.stamp.lnPrevExponent
  have hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s0_rec1 g.stamp.lnPrevExponent
  exact renderNode_op0_Vcomp z α g hz hstate hform hln hrec0 hrec1

/-- Singleton `OP_0` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op0_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s0)
    (hform : g.skel.formula = Noun.cell (Noun.atom 0)
      (Noun.atom (P8Census.skeletonMemoryAxis g.skel 1))) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op0_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Stamp equations at `OP_3` -/

theorem stampOfAcc_s3_ln (acc : ℕ) :
    (stampOfAcc State.s3 acc).lnExponent =
      (stampOfAcc State.s3 acc).lnPrevExponent + 1 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s3_rec0 (acc : ℕ) :
    (stampOfAcc State.s3 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s3 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s3 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s3 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_3` row -/

theorem renderOp3Row_state (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp3Row z α stamp skel).1 =
      (renderOp3Row z α stamp skel).2.2.1.state :=
  rfl

theorem renderOp3Row_inputs (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp3Row z α stamp skel).2.1 = ⟨α, z, 0, 0, 0⟩ :=
  rfl

/-- Field-generic `Vcomp` for one rendered `OP_3` row.
    `hform` is the Nock cell-test formula `[3 arg]` with `arg` the live `sf1`
    formula; `hsf1s` wires the live subject; `heval` is the cell-test
    fingerprint `?` of the live `sf1` result.
    `hln`/`hrec` are the `stampOfAcc` schedule at `.s3`. -/
theorem renderOp3Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 3)
      (P8Census.skeletonSubformula skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (heval : encC z skel.evaluation =
      FP.atomFP z (FP.qm z (encC z (P8Census.skeletonSubformula skel 0 .result))))
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 1)
    (hrec : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1) :
    let row := renderOp3Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp3Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · -- `pub.f = FP.cons z f_h f_t`
    rw [hform]
    change encC z (Noun.cell (Noun.atom 3)
        (P8Census.skeletonSubformula skel 0 .formula)) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 3)
        (P8Census.skeletonSubformula skel 0 .formula))))
        (encC z (formulaTail (Noun.cell (Noun.atom 3)
          (P8Census.skeletonSubformula skel 0 .formula))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 3)
      (P8Census.skeletonSubformula skel 0 .formula)
  · -- `mr1 = ⟨f, f_t, 3, ln_prev * α⟩` on `formulaTail`, not a second record
    refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec, pow_succ]
  · -- `SVhead` at `.s3` is `headAtom` with leaf `3`
    unfold SVhead
    have hne : ¬ (State.s3 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · -- `memBlk` at `.s3`: padded records and `ln = ln_prev * α`
    unfold memBlk
    refine ⟨rfl, rfl, ?_⟩
    rw [hln, pow_succ]
  · -- `evalV` at `.s3`: live `sf1`, zero `sf2`/`sf3`, cell-test leaf
    unfold evalV sfz1 sfz2 sfz3
    refine ⟨?sf1s, ?sf1f, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?esize, ?edyck, ?eleaf⟩
    · rw [hsf1s]
    · rw [hform]
      simp only [formulaTail]
    · rw [heval]
      simp [FP.atomFP]
    · rw [heval]
      simp [FP.atomFP]
    · rw [heval]
      simp [FP.atomFP]

/-- `Vcomp` for an `OP_3` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp3Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s3)
    (hform : skel.formula = Noun.cell (Noun.atom 3)
      (P8Census.skeletonSubformula skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (heval : encC z skel.evaluation =
      FP.atomFP z (FP.qm z (encC z (P8Census.skeletonSubformula skel 0 .result)))) :
    let row := renderOp3Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s3 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp3Row_Vcomp z α (stampOfAcc State.s3 acc) skel hz hform hsf1s heval
    (stampOfAcc_s3_ln acc) (stampOfAcc_s3_rec0 acc)

/-! ## `renderNode` / `renderRows` at `OP_3` -/

theorem renderNode_op3_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s3) :
    (renderNode z α g).row = renderOp3Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_3` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op3_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s3)
    (hform : g.skel.formula = Noun.cell (Noun.atom 3)
      (P8Census.skeletonSubformula g.skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (heval : encC z g.skel.evaluation =
      FP.atomFP z (FP.qm z (encC z (P8Census.skeletonSubformula g.skel 0 .result))))
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 1)
    (hrec : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op3_row z α g hstate]
  exact renderOp3Row_Vcomp z α g.stamp g.skel hz hform hsf1s heval hln hrec

theorem renderNode_op3_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s3)
    (hform : g.skel.formula = Noun.cell (Noun.atom 3)
      (P8Census.skeletonSubformula g.skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (heval : encC z g.skel.evaluation =
      FP.atomFP z (FP.qm z (encC z (P8Census.skeletonSubformula g.skel 0 .result))))
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s3_ln g.stamp.lnPrevExponent
  have hrec : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s3_rec0 g.stamp.lnPrevExponent
  exact renderNode_op3_Vcomp z α g hz hstate hform hsf1s heval hln hrec

/-- Singleton `OP_3` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op3_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s3)
    (hform : g.skel.formula = Noun.cell (Noun.atom 3)
      (P8Census.skeletonSubformula g.skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (heval : encC z g.skel.evaluation =
      FP.atomFP z (FP.qm z (encC z (P8Census.skeletonSubformula g.skel 0 .result)))) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op3_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using hsf1s
  · simpa [bfsAssign_leaf_label] using heval
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Stamp equations at `OP_4` -/

theorem stampOfAcc_s4_ln (acc : ℕ) :
    (stampOfAcc State.s4 acc).lnExponent =
      (stampOfAcc State.s4 acc).lnPrevExponent + 1 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s4_rec0 (acc : ℕ) :
    (stampOfAcc State.s4 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s4 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s4 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s4 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_4` row -/

theorem renderOp4Row_state (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp4Row z α stamp skel).1 =
      (renderOp4Row z α stamp skel).2.2.1.state :=
  rfl

theorem renderOp4Row_inputs (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp4Row z α stamp skel).2.1 = ⟨α, z, 0, 0, 0⟩ :=
  rfl

/-- Field-generic `Vcomp` for one rendered `OP_4` row.
    `hform` is the Nock increment formula `[4 arg]` with `arg` the live `sf1`
    formula; `hsf1s` wires the live subject; `hsf1e` is atom shape of the live
    call result; `heval` is fingerprint increment.
    `hln`/`hrec` are the `stampOfAcc` schedule at `.s4`. -/
theorem renderOp4Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 4)
      (P8Census.skeletonSubformula skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf1e : (encC z (P8Census.skeletonSubformula skel 0 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula skel 0 .result)).dyck = 0)
    (heval : encC z skel.evaluation =
      FP.inc z (encC z (P8Census.skeletonSubformula skel 0 .result)))
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 1)
    (hrec : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1) :
    let row := renderOp4Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp4Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · -- `pub.f = FP.cons z f_h f_t`
    rw [hform]
    change encC z (Noun.cell (Noun.atom 4)
        (P8Census.skeletonSubformula skel 0 .formula)) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 4)
        (P8Census.skeletonSubformula skel 0 .formula))))
        (encC z (formulaTail (Noun.cell (Noun.atom 4)
          (P8Census.skeletonSubformula skel 0 .formula))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 4)
      (P8Census.skeletonSubformula skel 0 .formula)
  · -- `mr1 = ⟨f, f_t, 3, ln_prev * α⟩` on `formulaTail`, not a second record
    refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec, pow_succ]
  · -- `SVhead` at `.s4` is `headAtom` with leaf `4`
    unfold SVhead
    have hne : ¬ (State.s4 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · -- `memBlk` at `.s4`: padded records and `ln = ln_prev * α`
    unfold memBlk
    refine ⟨rfl, rfl, ?_⟩
    rw [hln, pow_succ]
  · -- `evalV` at `.s4`: live `sf1`, atom-shaped call result, increment
    unfold evalV sfz1 sfz2 sfz3
    refine ⟨?sf1s, ?sf1f, hsf1e.1, hsf1e.2, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?einc⟩
    · rw [hsf1s]
    · rw [hform]
      simp only [formulaTail]
    · exact heval

/-- `Vcomp` for an `OP_4` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp4Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s4)
    (hform : skel.formula = Noun.cell (Noun.atom 4)
      (P8Census.skeletonSubformula skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf1e : (encC z (P8Census.skeletonSubformula skel 0 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula skel 0 .result)).dyck = 0)
    (heval : encC z skel.evaluation =
      FP.inc z (encC z (P8Census.skeletonSubformula skel 0 .result))) :
    let row := renderOp4Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s4 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp4Row_Vcomp z α (stampOfAcc State.s4 acc) skel hz hform hsf1s hsf1e heval
    (stampOfAcc_s4_ln acc) (stampOfAcc_s4_rec0 acc)

/-! ## `renderNode` / `renderRows` at `OP_4` -/

theorem renderNode_op4_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s4) :
    (renderNode z α g).row = renderOp4Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_4` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op4_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s4)
    (hform : g.skel.formula = Noun.cell (Noun.atom 4)
      (P8Census.skeletonSubformula g.skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf1e : (encC z (P8Census.skeletonSubformula g.skel 0 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula g.skel 0 .result)).dyck = 0)
    (heval : encC z g.skel.evaluation =
      FP.inc z (encC z (P8Census.skeletonSubformula g.skel 0 .result)))
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 1)
    (hrec : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op4_row z α g hstate]
  exact renderOp4Row_Vcomp z α g.stamp g.skel hz hform hsf1s hsf1e heval hln hrec

theorem renderNode_op4_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s4)
    (hform : g.skel.formula = Noun.cell (Noun.atom 4)
      (P8Census.skeletonSubformula g.skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf1e : (encC z (P8Census.skeletonSubformula g.skel 0 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula g.skel 0 .result)).dyck = 0)
    (heval : encC z g.skel.evaluation =
      FP.inc z (encC z (P8Census.skeletonSubformula g.skel 0 .result)))
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s4_ln g.stamp.lnPrevExponent
  have hrec : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s4_rec0 g.stamp.lnPrevExponent
  exact renderNode_op4_Vcomp z α g hz hstate hform hsf1s hsf1e heval hln hrec

/-- Singleton `OP_4` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op4_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s4)
    (hform : g.skel.formula = Noun.cell (Noun.atom 4)
      (P8Census.skeletonSubformula g.skel 0 .formula))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf1e : (encC z (P8Census.skeletonSubformula g.skel 0 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula g.skel 0 .result)).dyck = 0)
    (heval : encC z g.skel.evaluation =
      FP.inc z (encC z (P8Census.skeletonSubformula g.skel 0 .result))) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op4_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using hsf1s
  · simpa [bfsAssign_leaf_label] using hsf1e
  · simpa [bfsAssign_leaf_label] using heval
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Stamp equations at `OP_6` -/

theorem stampOfAcc_s6_ln (acc : ℕ) :
    (stampOfAcc State.s6 acc).lnExponent =
      (stampOfAcc State.s6 acc).lnPrevExponent + 3 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s6_rec0 (acc : ℕ) :
    (stampOfAcc State.s6 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s6 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s6 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s6 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s6_rec1 (acc : ℕ) :
    (stampOfAcc State.s6 acc).recordExponent (1 : Fin 3) =
      (stampOfAcc State.s6 acc).lnPrevExponent + 2 := by
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s6 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s6 acc (1 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s6_rec2 (acc : ℕ) :
    (stampOfAcc State.s6 acc).recordExponent (2 : Fin 3) =
      (stampOfAcc State.s6 acc).lnPrevExponent + 3 := by
  have hi : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s6 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s6 acc (2 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_6` row -/

theorem renderOp6Row_state (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp6Row z α stamp skel).1 =
      (renderOp6Row z α stamp skel).2.2.1.state :=
  rfl

theorem renderOp6Row_inputs (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) :
    (renderOp6Row z α stamp skel).2.1 = ⟨α, z, 0, 0, 0⟩ :=
  rfl

/-- Field-generic `Vcomp` for one rendered `OP_6` row.
    `hform` is the Nock if/branch formula `[6 [b [c d]]]` with `b` the live
    `sf2` condition formula; `c`/`d` are the then/else branch formulas.
    `hsf1s`/`hsf2s` wire both live subjects; `hsf1f` selects the taken branch
    by the condition leaf; `heval` is `e = sf1_e`; `hsf2e` is the 1-leaf
    condition atom.  `hln`/`hrec0`/`hrec1`/`hrec2` are
    the three-record `stampOfAcc` schedule at `.s6`. -/
theorem renderOp6Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (c d : Noun)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 6)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (Noun.cell c d)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (hsf1f :
      ((encC z (P8Census.skeletonSubformula skel 1 .result)).leaf = 0 ∧
        P8Census.skeletonSubformula skel 0 .formula = c) ∨
      ((encC z (P8Census.skeletonSubformula skel 1 .result)).leaf = 1 ∧
        P8Census.skeletonSubformula skel 0 .formula = d))
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 0 .result)
    (hsf2e : (encC z (P8Census.skeletonSubformula skel 1 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula skel 1 .result)).dyck = 0 ∧
      ((encC z (P8Census.skeletonSubformula skel 1 .result)).leaf = 0 ∨
       (encC z (P8Census.skeletonSubformula skel 1 .result)).leaf = 1))
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 3)
    (hrec0 : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1)
    (hrec1 : stamp.recordExponent (1 : Fin 3) = stamp.lnPrevExponent + 2)
    (hrec2 : stamp.recordExponent (2 : Fin 3) = stamp.lnPrevExponent + 3) :
    let row := renderOp6Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp6Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · -- `pub.f = FP.cons z f_h f_t`
    rw [hform]
    change encC z (Noun.cell (Noun.atom 6)
        (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
          (Noun.cell c d))) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 6)
        (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
          (Noun.cell c d)))))
        (encC z (formulaTail (Noun.cell (Noun.atom 6)
          (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
            (Noun.cell c d)))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 6)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (Noun.cell c d))
  · -- `mr1 = ⟨f, f_t, 3, ln_prev * α⟩` formula-open @3
    refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec0, pow_succ]
  · -- `SVhead` at `.s6` is `headAtom` with leaf `6`
    unfold SVhead
    have hne : ¬ (State.s6 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · -- `memBlk` at `.s6`: tail-open `mr2`, branch-pair `mr3`, two `FP.cons`,
    -- and `ln = ln_prev * α^3`
    unfold memBlk
    refine ⟨?mr2, ?ftcons, ?mr3, ?fttcons, ?ln⟩
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rw [hrec1, pow_add]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, encC_eq, encC_eq]
      exact (GlobalCarryRecognizer.enc_cons hz
        (P8Census.skeletonSubformula skel 1 .formula) (Noun.cell c d)).symm
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rw [hrec2, pow_add]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, encC_eq, encC_eq]
      exact (GlobalCarryRecognizer.enc_cons hz c d).symm
    · rw [hln, pow_add]
  · -- `evalV` at `.s6`: live `sf1`/`sf2`, branch select, 1-leaf condition
    unfold evalV sfz3
    refine ⟨?sf1s, ?sf1f, ?e, ?sf2s, ?sf2f, ?sf2size, ?sf2dyck, ?sf2leaf,
      ⟨rfl, rfl, rfl⟩⟩
    · rw [hsf1s]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rcases hsf1f with ⟨hleaf0, hc⟩ | ⟨hleaf1, hd⟩
      · rw [hc, if_pos hleaf0]
      · have hne : (encC z (P8Census.skeletonSubformula skel 1 .result)).leaf ≠ 0 := by
          rw [hleaf1]
          exact one_ne_zero
        rw [hd, if_neg hne]
    · rw [heval]
    · rw [hsf2s]
    · rw [hform]
      simp only [formulaHead, formulaTail]
    · exact hsf2e.1
    · exact hsf2e.2.1
    · exact hsf2e.2.2

/-- `Vcomp` for an `OP_6` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp6Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (c d : Noun)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s6)
    (hform : skel.formula = Noun.cell (Noun.atom 6)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (Noun.cell c d)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (hsf1f :
      ((encC z (P8Census.skeletonSubformula skel 1 .result)).leaf = 0 ∧
        P8Census.skeletonSubformula skel 0 .formula = c) ∨
      ((encC z (P8Census.skeletonSubformula skel 1 .result)).leaf = 1 ∧
        P8Census.skeletonSubformula skel 0 .formula = d))
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 0 .result)
    (hsf2e : (encC z (P8Census.skeletonSubformula skel 1 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula skel 1 .result)).dyck = 0 ∧
      ((encC z (P8Census.skeletonSubformula skel 1 .result)).leaf = 0 ∨
       (encC z (P8Census.skeletonSubformula skel 1 .result)).leaf = 1)) :
    let row := renderOp6Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s6 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp6Row_Vcomp z α (stampOfAcc State.s6 acc) skel c d hz hform
    hsf1s hsf2s hsf1f heval hsf2e
    (stampOfAcc_s6_ln acc) (stampOfAcc_s6_rec0 acc)
    (stampOfAcc_s6_rec1 acc) (stampOfAcc_s6_rec2 acc)

/-! ## `renderNode` / `renderRows` at `OP_6` -/

theorem renderNode_op6_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s6) :
    (renderNode z α g).row = renderOp6Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_6` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op6_Vcomp
    (z α : K) (g : GenComputeRow K)
    (c d : Noun)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s6)
    (hform : g.skel.formula = Noun.cell (Noun.atom 6)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (Noun.cell c d)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (hsf1f :
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 0 ∧
        P8Census.skeletonSubformula g.skel 0 .formula = c) ∨
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 1 ∧
        P8Census.skeletonSubformula g.skel 0 .formula = d))
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result)
    (hsf2e : (encC z (P8Census.skeletonSubformula g.skel 1 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula g.skel 1 .result)).dyck = 0 ∧
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 0 ∨
       (encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 1))
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 3)
    (hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1)
    (hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2)
    (hrec2 : g.stamp.recordExponent (2 : Fin 3) = g.stamp.lnPrevExponent + 3) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op6_row z α g hstate]
  exact renderOp6Row_Vcomp z α g.stamp g.skel c d hz hform
    hsf1s hsf2s hsf1f heval hsf2e hln hrec0 hrec1 hrec2

theorem renderNode_op6_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (c d : Noun)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s6)
    (hform : g.skel.formula = Noun.cell (Noun.atom 6)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (Noun.cell c d)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (hsf1f :
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 0 ∧
        P8Census.skeletonSubformula g.skel 0 .formula = c) ∨
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 1 ∧
        P8Census.skeletonSubformula g.skel 0 .formula = d))
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result)
    (hsf2e : (encC z (P8Census.skeletonSubformula g.skel 1 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula g.skel 1 .result)).dyck = 0 ∧
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 0 ∨
       (encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 1))
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 3 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s6_ln g.stamp.lnPrevExponent
  have hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s6_rec0 g.stamp.lnPrevExponent
  have hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s6_rec1 g.stamp.lnPrevExponent
  have hrec2 : g.stamp.recordExponent (2 : Fin 3) = g.stamp.lnPrevExponent + 3 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s6_rec2 g.stamp.lnPrevExponent
  exact renderNode_op6_Vcomp z α g c d hz hstate hform
    hsf1s hsf2s hsf1f heval hsf2e hln hrec0 hrec1 hrec2

/-- Singleton `OP_6` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op6_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (c d : Noun)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s6)
    (hform : g.skel.formula = Noun.cell (Noun.atom 6)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (Noun.cell c d)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (hsf1f :
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 0 ∧
        P8Census.skeletonSubformula g.skel 0 .formula = c) ∨
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 1 ∧
        P8Census.skeletonSubformula g.skel 0 .formula = d))
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result)
    (hsf2e : (encC z (P8Census.skeletonSubformula g.skel 1 .result)).size = z ∧
      (encC z (P8Census.skeletonSubformula g.skel 1 .result)).dyck = 0 ∧
      ((encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 0 ∨
       (encC z (P8Census.skeletonSubformula g.skel 1 .result)).leaf = 1)) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op6_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label c d hz ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using hsf1s
  · simpa [bfsAssign_leaf_label] using hsf2s
  · simpa [bfsAssign_leaf_label] using hsf1f
  · simpa [bfsAssign_leaf_label] using heval
  · simpa [bfsAssign_leaf_label] using hsf2e
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Stamp equations at `.cons` -/

theorem stampOfAcc_cons_ln (acc : ℕ) :
    (stampOfAcc State.cons acc).lnExponent =
      (stampOfAcc State.cons acc).lnPrevExponent + 1 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_cons_rec0 (acc : ℕ) :
    (stampOfAcc State.cons acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.cons acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.cons := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.cons acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `.cons` row -/

/-- Field-generic `Vcomp` for a rendered autocons row.  `hform`/`heval` are the
    formula and evaluation cells; `hhead` is `headCell` (`f_h.dyck ≠ 0`).
    Two live sf slots come from `formulaHead`/`formulaTail`, not
    `skeletonSubformula`.  `memBlk` is the unary pad (`recordCount = 1`). -/
theorem renderConsRow_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (fL fR eL eR : Noun)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell fL fR)
    (heval : skel.evaluation = Noun.cell eL eR)
    (hhead : (encC z fL).dyck ≠ 0)
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 1)
    (hrec : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1) :
    let row := renderConsRow z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderConsRow Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · -- `pub.f = FP.cons z f_h f_t`
    rw [hform]
    change encC z (Noun.cell fL fR) =
      FP.cons z (encC z (formulaHead (Noun.cell fL fR)))
        (encC z (formulaTail (Noun.cell fL fR)))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz fL fR
  · -- `mr1 = ⟨f, f_t, 3, ln_prev * α⟩` on `formulaTail`
    refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec, pow_succ]
  · -- `SVhead` at `.cons` is `headCell` (`f_h.dyck ≠ 0`)
    unfold SVhead
    rw [if_pos (by rfl : _ = State.cons)]
    unfold headCell
    rw [hform]
    simp only [formulaHead]
    exact hhead
  · -- `memBlk` at `.cons`: padded records and `ln = ln_prev * α`
    unfold memBlk
    refine ⟨rfl, rfl, ?_⟩
    rw [hln, pow_succ]
  · -- `evalV` at `.cons`: live `sf1`/`sf2`, `e = FP.cons z sf1_e sf2_e`
    unfold evalV sfz3
    refine ⟨rfl, rfl, rfl, rfl, ?e, ⟨rfl, rfl, rfl⟩⟩
    rw [heval]
    change encC z (Noun.cell eL eR) =
      FP.cons z (encC z (formulaHead (Noun.cell eL eR)))
        (encC z (formulaTail (Noun.cell eL eR)))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz eL eR

/-- `Vcomp` for a `.cons` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderConsRow_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (fL fR eL eR : Noun)
    (hz : z ≠ 0)
    (hstate : skel.state = State.cons)
    (hform : skel.formula = Noun.cell fL fR)
    (heval : skel.evaluation = Noun.cell eL eR)
    (hhead : (encC z fL).dyck ≠ 0) :
    let row := renderConsRow z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.cons acc := by
    rw [hstate]
  rw [hstamp]
  exact renderConsRow_Vcomp z α (stampOfAcc State.cons acc) skel
    fL fR eL eR hz hform heval hhead
    (stampOfAcc_cons_ln acc) (stampOfAcc_cons_rec0 acc)

/-! ## `renderNode` / `renderRows` at `.cons` -/

theorem renderNode_cons_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.cons) :
    (renderNode z α g).row = renderConsRow z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `.cons` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_cons_Vcomp
    (z α : K) (g : GenComputeRow K)
    (fL fR eL eR : Noun)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.cons)
    (hform : g.skel.formula = Noun.cell fL fR)
    (heval : g.skel.evaluation = Noun.cell eL eR)
    (hhead : (encC z fL).dyck ≠ 0)
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 1)
    (hrec : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_cons_row z α g hstate]
  exact renderConsRow_Vcomp z α g.stamp g.skel fL fR eL eR
    hz hform heval hhead hln hrec

theorem renderNode_cons_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (fL fR eL eR : Noun)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.cons)
    (hform : g.skel.formula = Noun.cell fL fR)
    (heval : g.skel.evaluation = Noun.cell eL eR)
    (hhead : (encC z fL).dyck ≠ 0)
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_cons_ln g.stamp.lnPrevExponent
  have hrec : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_cons_rec0 g.stamp.lnPrevExponent
  exact renderNode_cons_Vcomp z α g fL fR eL eR
    hz hstate hform heval hhead hln hrec

/-- Singleton `.cons` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_cons_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (fL fR eL eR : Noun)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.cons)
    (hform : g.skel.formula = Noun.cell fL fR)
    (heval : g.skel.evaluation = Noun.cell eL eR)
    (hhead : (encC z fL).dyck ≠ 0) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_cons_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label fL fR eL eR hz ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using heval
  · simpa [bfsAssign_leaf_label] using hhead
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]

/-! ## Stamp equations at `OP_5` -/

theorem stampOfAcc_s5_ln (acc : ℕ) :
    (stampOfAcc State.s5 acc).lnExponent =
      (stampOfAcc State.s5 acc).lnPrevExponent + 2 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s5_rec0 (acc : ℕ) :
    (stampOfAcc State.s5 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s5 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s5 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s5 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s5_rec1 (acc : ℕ) :
    (stampOfAcc State.s5 acc).recordExponent (1 : Fin 3) =
      (stampOfAcc State.s5 acc).lnPrevExponent + 2 := by
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s5 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s5 acc (1 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_5` row -/

/-- Field-generic `Vcomp` for one rendered `OP_5` row.
    `hform` is the Nock equality formula `[5 [sf0 sf1]]`; both operands share the row
    subject; `heval` is the `eqOp` atom.
    `hln`/`hrec0`/`hrec1` are the two-record `stampOfAcc` schedule at `.s5`. -/
theorem renderOp5Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 5)
      (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
        (P8Census.skeletonSubformula skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (heval : encC z skel.evaluation =
      FP.atomFP z (FP.eqOp (encC z (P8Census.skeletonSubformula skel 0 .result))
        (encC z (P8Census.skeletonSubformula skel 1 .result))))
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 2)
    (hrec0 : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1)
    (hrec1 : stamp.recordExponent (1 : Fin 3) = stamp.lnPrevExponent + 2) :
    let row := renderOp5Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp5Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · rw [hform]
    change encC z (Noun.cell (Noun.atom 5)
        (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
          (P8Census.skeletonSubformula skel 1 .formula))) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 5)
        (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
          (P8Census.skeletonSubformula skel 1 .formula)))))
        (encC z (formulaTail (Noun.cell (Noun.atom 5)
          (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
            (P8Census.skeletonSubformula skel 1 .formula)))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 5)
      (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
        (P8Census.skeletonSubformula skel 1 .formula))
  · refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec0, pow_succ]
  · unfold SVhead
    have hne : ¬ (State.s5 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · unfold memBlk
    refine ⟨?mr2, ?ftcons, rfl, ?ln⟩
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rw [hrec1, pow_add]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, encC_eq, encC_eq]
      exact (GlobalCarryRecognizer.enc_cons hz
        (P8Census.skeletonSubformula skel 0 .formula)
        (P8Census.skeletonSubformula skel 1 .formula)).symm
    · rw [hln, pow_add]
  · unfold evalV sfz3
    refine ⟨?sf1s, ?sf1f, ?sf2s, ?sf2f, ⟨rfl, rfl, rfl⟩, ?esize, ?edyck, ?eleaf⟩
    · rw [hsf1s]
    · rw [hform]
      simp only [formulaHead, formulaTail]
    · rw [hsf2s]
    · rw [hform]
      simp only [formulaHead, formulaTail]
    · rw [heval]
      simp [FP.atomFP]
    · rw [heval]
      simp [FP.atomFP]
    · rw [heval]
      simp [FP.atomFP]

/-- `Vcomp` for an `OP_5` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp5Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s5)
    (hform : skel.formula = Noun.cell (Noun.atom 5)
      (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
        (P8Census.skeletonSubformula skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (heval : encC z skel.evaluation =
      FP.atomFP z (FP.eqOp (encC z (P8Census.skeletonSubformula skel 0 .result))
        (encC z (P8Census.skeletonSubformula skel 1 .result)))) :
    let row := renderOp5Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s5 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp5Row_Vcomp z α (stampOfAcc State.s5 acc) skel hz hform
    hsf1s hsf2s heval
    (stampOfAcc_s5_ln acc) (stampOfAcc_s5_rec0 acc) (stampOfAcc_s5_rec1 acc)

/-! ## `renderNode` / `renderRows` at `OP_5` -/

theorem renderNode_op5_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s5) :
    (renderNode z α g).row = renderOp5Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_5` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op5_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s5)
    (hform : g.skel.formula = Noun.cell (Noun.atom 5)
      (Noun.cell (P8Census.skeletonSubformula g.skel 0 .formula)
        (P8Census.skeletonSubformula g.skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : encC z g.skel.evaluation =
      FP.atomFP z (FP.eqOp (encC z (P8Census.skeletonSubformula g.skel 0 .result))
        (encC z (P8Census.skeletonSubformula g.skel 1 .result))))
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2)
    (hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1)
    (hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op5_row z α g hstate]
  exact renderOp5Row_Vcomp z α g.stamp g.skel hz hform hsf1s hsf2s heval
    hln hrec0 hrec1

theorem renderNode_op5_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s5)
    (hform : g.skel.formula = Noun.cell (Noun.atom 5)
      (Noun.cell (P8Census.skeletonSubformula g.skel 0 .formula)
        (P8Census.skeletonSubformula g.skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : encC z g.skel.evaluation =
      FP.atomFP z (FP.eqOp (encC z (P8Census.skeletonSubformula g.skel 0 .result))
        (encC z (P8Census.skeletonSubformula g.skel 1 .result))))
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s5_ln g.stamp.lnPrevExponent
  have hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s5_rec0 g.stamp.lnPrevExponent
  have hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s5_rec1 g.stamp.lnPrevExponent
  exact renderNode_op5_Vcomp z α g hz hstate hform hsf1s hsf2s heval
    hln hrec0 hrec1

/-- Singleton `OP_5` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op5_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s5)
    (hform : g.skel.formula = Noun.cell (Noun.atom 5)
      (Noun.cell (P8Census.skeletonSubformula g.skel 0 .formula)
        (P8Census.skeletonSubformula g.skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : encC z g.skel.evaluation =
      FP.atomFP z (FP.eqOp (encC z (P8Census.skeletonSubformula g.skel 0 .result))
        (encC z (P8Census.skeletonSubformula g.skel 1 .result)))) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op5_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using hsf1s
  · simpa [bfsAssign_leaf_label] using hsf2s
  · simpa [bfsAssign_leaf_label] using heval
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Stamp equations at `OP_2` -/

theorem stampOfAcc_s2_ln (acc : ℕ) :
    (stampOfAcc State.s2 acc).lnExponent =
      (stampOfAcc State.s2 acc).lnPrevExponent + 2 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s2_rec0 (acc : ℕ) :
    (stampOfAcc State.s2 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s2 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s2 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s2 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s2_rec1 (acc : ℕ) :
    (stampOfAcc State.s2 acc).recordExponent (1 : Fin 3) =
      (stampOfAcc State.s2 acc).lnPrevExponent + 2 := by
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s2 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s2 acc (1 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_2` row -/

/-- Field-generic `Vcomp` for one rendered `OP_2` row.
    `hform` is the Nock eval formula `[2 [sf0 sf1]]`; `hsf3s`/`hsf3f` wire the
    follow-on `*[sf0_e sf1_e]`; `heval` is `e = sf3_e`.  Stamp hyps match OP0. -/
theorem renderOp2Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 2)
      (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
        (P8Census.skeletonSubformula skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (hsf3s : P8Census.skeletonSubformula skel 2 .subject =
      P8Census.skeletonSubformula skel 0 .result)
    (hsf3f : P8Census.skeletonSubformula skel 2 .formula =
      P8Census.skeletonSubformula skel 1 .result)
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 2 .result)
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 2)
    (hrec0 : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1)
    (hrec1 : stamp.recordExponent (1 : Fin 3) = stamp.lnPrevExponent + 2) :
    let row := renderOp2Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp2Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · rw [hform]
    change encC z (Noun.cell (Noun.atom 2)
        (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
          (P8Census.skeletonSubformula skel 1 .formula))) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 2)
        (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
          (P8Census.skeletonSubformula skel 1 .formula)))))
        (encC z (formulaTail (Noun.cell (Noun.atom 2)
          (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
            (P8Census.skeletonSubformula skel 1 .formula)))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 2)
      (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
        (P8Census.skeletonSubformula skel 1 .formula))
  · refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec0, pow_succ]
  · unfold SVhead
    have hne : ¬ (State.s2 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · unfold memBlk
    refine ⟨?mr2, ?ftcons, rfl, ?ln⟩
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rw [hrec1, pow_add]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, encC_eq, encC_eq]
      exact (GlobalCarryRecognizer.enc_cons hz
        (P8Census.skeletonSubformula skel 0 .formula)
        (P8Census.skeletonSubformula skel 1 .formula)).symm
    · rw [hln, pow_add]
  · unfold evalV
    refine ⟨?sf1s, ?sf1f, ?sf2s, ?sf2f, ?sf3s, ?sf3f, ?e⟩
    · rw [hsf1s]
    · rw [hform]
      simp only [formulaHead, formulaTail]
    · rw [hsf2s]
    · rw [hform]
      simp only [formulaHead, formulaTail]
    · rw [hsf3s]
    · rw [hsf3f]
    · rw [heval]

/-- `Vcomp` for an `OP_2` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp2Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s2)
    (hform : skel.formula = Noun.cell (Noun.atom 2)
      (Noun.cell (P8Census.skeletonSubformula skel 0 .formula)
        (P8Census.skeletonSubformula skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (hsf3s : P8Census.skeletonSubformula skel 2 .subject =
      P8Census.skeletonSubformula skel 0 .result)
    (hsf3f : P8Census.skeletonSubformula skel 2 .formula =
      P8Census.skeletonSubformula skel 1 .result)
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 2 .result) :
    let row := renderOp2Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s2 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp2Row_Vcomp z α (stampOfAcc State.s2 acc) skel hz hform
    hsf1s hsf2s hsf3s hsf3f heval
    (stampOfAcc_s2_ln acc) (stampOfAcc_s2_rec0 acc) (stampOfAcc_s2_rec1 acc)

/-! ## `renderNode` / `renderRows` at `OP_2` -/

theorem renderNode_op2_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s2) :
    (renderNode z α g).row = renderOp2Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_2` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op2_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s2)
    (hform : g.skel.formula = Noun.cell (Noun.atom 2)
      (Noun.cell (P8Census.skeletonSubformula g.skel 0 .formula)
        (P8Census.skeletonSubformula g.skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (hsf3s : P8Census.skeletonSubformula g.skel 2 .subject =
      P8Census.skeletonSubformula g.skel 0 .result)
    (hsf3f : P8Census.skeletonSubformula g.skel 2 .formula =
      P8Census.skeletonSubformula g.skel 1 .result)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 2 .result)
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2)
    (hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1)
    (hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op2_row z α g hstate]
  exact renderOp2Row_Vcomp z α g.stamp g.skel hz hform
    hsf1s hsf2s hsf3s hsf3f heval hln hrec0 hrec1

theorem renderNode_op2_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s2)
    (hform : g.skel.formula = Noun.cell (Noun.atom 2)
      (Noun.cell (P8Census.skeletonSubformula g.skel 0 .formula)
        (P8Census.skeletonSubformula g.skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (hsf3s : P8Census.skeletonSubformula g.skel 2 .subject =
      P8Census.skeletonSubformula g.skel 0 .result)
    (hsf3f : P8Census.skeletonSubformula g.skel 2 .formula =
      P8Census.skeletonSubformula g.skel 1 .result)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 2 .result)
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s2_ln g.stamp.lnPrevExponent
  have hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s2_rec0 g.stamp.lnPrevExponent
  have hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s2_rec1 g.stamp.lnPrevExponent
  exact renderNode_op2_Vcomp z α g hz hstate hform
    hsf1s hsf2s hsf3s hsf3f heval hln hrec0 hrec1

/-- Singleton `OP_2` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op2_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s2)
    (hform : g.skel.formula = Noun.cell (Noun.atom 2)
      (Noun.cell (P8Census.skeletonSubformula g.skel 0 .formula)
        (P8Census.skeletonSubformula g.skel 1 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (hsf3s : P8Census.skeletonSubformula g.skel 2 .subject =
      P8Census.skeletonSubformula g.skel 0 .result)
    (hsf3f : P8Census.skeletonSubformula g.skel 2 .formula =
      P8Census.skeletonSubformula g.skel 1 .result)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 2 .result) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op2_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using hsf1s
  · simpa [bfsAssign_leaf_label] using hsf2s
  · simpa [bfsAssign_leaf_label] using hsf3s
  · simpa [bfsAssign_leaf_label] using hsf3f
  · simpa [bfsAssign_leaf_label] using heval
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Stamp equations at `OP_7` -/

theorem stampOfAcc_s7_ln (acc : ℕ) :
    (stampOfAcc State.s7 acc).lnExponent =
      (stampOfAcc State.s7 acc).lnPrevExponent + 2 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s7_rec0 (acc : ℕ) :
    (stampOfAcc State.s7 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s7 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s7 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s7 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s7_rec1 (acc : ℕ) :
    (stampOfAcc State.s7 acc).recordExponent (1 : Fin 3) =
      (stampOfAcc State.s7 acc).lnPrevExponent + 2 := by
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s7 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s7 acc (1 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_7` row -/

/-- Field-generic `Vcomp` for one rendered `OP_7` row.
    Hyps are `evalV` order: paper child-one = consumer (`sf1` ← skeleton slot 0),
    child-two = helper (`sf2` ← skeleton slot 1).  `hform` is `[7 [b c]]` with
    `b` in slot 1 and `c` in slot 0.  `memBlk` is the OP5 two-record block. -/
theorem renderOp7Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 7)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (P8Census.skeletonSubformula skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject =
      P8Census.skeletonSubformula skel 1 .result)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 0 .result)
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 2)
    (hrec0 : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1)
    (hrec1 : stamp.recordExponent (1 : Fin 3) = stamp.lnPrevExponent + 2) :
    let row := renderOp7Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp7Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · rw [hform]
    change encC z (Noun.cell (Noun.atom 7)
        (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
          (P8Census.skeletonSubformula skel 0 .formula))) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 7)
        (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
          (P8Census.skeletonSubformula skel 0 .formula)))))
        (encC z (formulaTail (Noun.cell (Noun.atom 7)
          (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
            (P8Census.skeletonSubformula skel 0 .formula)))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 7)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (P8Census.skeletonSubformula skel 0 .formula))
  · refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec0, pow_succ]
  · unfold SVhead
    have hne : ¬ (State.s7 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · unfold memBlk
    refine ⟨?mr2, ?ftcons, rfl, ?ln⟩
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rw [hrec1, pow_add]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, encC_eq, encC_eq]
      exact (GlobalCarryRecognizer.enc_cons hz
        (P8Census.skeletonSubformula skel 1 .formula)
        (P8Census.skeletonSubformula skel 0 .formula)).symm
    · rw [hln, pow_add]
  · unfold evalV sfz3
    refine ⟨?sf1s, ?sf1f, ?e, ?sf2s, ?sf2f, ⟨rfl, rfl, rfl⟩⟩
    · rw [hsf1s]
    · rw [hform]
      simp only [formulaHead, formulaTail]
    · rw [heval]
    · rw [hsf2s]
    · rw [hform]
      simp only [formulaHead, formulaTail]

/-- `Vcomp` for an `OP_7` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp7Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s7)
    (hform : skel.formula = Noun.cell (Noun.atom 7)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (P8Census.skeletonSubformula skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject =
      P8Census.skeletonSubformula skel 1 .result)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 0 .result) :
    let row := renderOp7Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s7 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp7Row_Vcomp z α (stampOfAcc State.s7 acc) skel hz hform
    hsf1s hsf2s heval
    (stampOfAcc_s7_ln acc) (stampOfAcc_s7_rec0 acc) (stampOfAcc_s7_rec1 acc)

/-! ## `renderNode` / `renderRows` at `OP_7` -/

theorem renderNode_op7_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s7) :
    (renderNode z α g).row = renderOp7Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_7` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op7_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s7)
    (hform : g.skel.formula = Noun.cell (Noun.atom 7)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject =
      P8Census.skeletonSubformula g.skel 1 .result)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result)
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2)
    (hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1)
    (hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op7_row z α g hstate]
  exact renderOp7Row_Vcomp z α g.stamp g.skel hz hform
    hsf1s hsf2s heval hln hrec0 hrec1

theorem renderNode_op7_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s7)
    (hform : g.skel.formula = Noun.cell (Noun.atom 7)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject =
      P8Census.skeletonSubformula g.skel 1 .result)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result)
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s7_ln g.stamp.lnPrevExponent
  have hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s7_rec0 g.stamp.lnPrevExponent
  have hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s7_rec1 g.stamp.lnPrevExponent
  exact renderNode_op7_Vcomp z α g hz hstate hform
    hsf1s hsf2s heval hln hrec0 hrec1

/-- Singleton `OP_7` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op7_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s7)
    (hform : g.skel.formula = Noun.cell (Noun.atom 7)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject =
      P8Census.skeletonSubformula g.skel 1 .result)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op7_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using hsf1s
  · simpa [bfsAssign_leaf_label] using hsf2s
  · simpa [bfsAssign_leaf_label] using heval
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Stamp equations at `OP_8` -/

theorem stampOfAcc_s8_ln (acc : ℕ) :
    (stampOfAcc State.s8 acc).lnExponent =
      (stampOfAcc State.s8 acc).lnPrevExponent + 2 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s8_rec0 (acc : ℕ) :
    (stampOfAcc State.s8 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s8 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s8 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s8 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s8_rec1 (acc : ℕ) :
    (stampOfAcc State.s8 acc).recordExponent (1 : Fin 3) =
      (stampOfAcc State.s8 acc).lnPrevExponent + 2 := by
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s8 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s8 acc (1 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_8` row -/

/-- Field-generic `Vcomp` for one rendered `OP_8` row.
    Same `evalV` slot order as OP7, except the consumer subject is the autocons
    `[sf2_e subject]` (`hsf1s`), discharged by `enc_cons`. -/
theorem renderOp8Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 8)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (P8Census.skeletonSubformula skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject =
      Noun.cell (P8Census.skeletonSubformula skel 1 .result) skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 0 .result)
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 2)
    (hrec0 : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1)
    (hrec1 : stamp.recordExponent (1 : Fin 3) = stamp.lnPrevExponent + 2) :
    let row := renderOp8Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp8Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · rw [hform]
    change encC z (Noun.cell (Noun.atom 8)
        (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
          (P8Census.skeletonSubformula skel 0 .formula))) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 8)
        (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
          (P8Census.skeletonSubformula skel 0 .formula)))))
        (encC z (formulaTail (Noun.cell (Noun.atom 8)
          (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
            (P8Census.skeletonSubformula skel 0 .formula)))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 8)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (P8Census.skeletonSubformula skel 0 .formula))
  · refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec0, pow_succ]
  · unfold SVhead
    have hne : ¬ (State.s8 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · unfold memBlk
    refine ⟨?mr2, ?ftcons, rfl, ?ln⟩
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rw [hrec1, pow_add]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, encC_eq, encC_eq]
      exact (GlobalCarryRecognizer.enc_cons hz
        (P8Census.skeletonSubformula skel 1 .formula)
        (P8Census.skeletonSubformula skel 0 .formula)).symm
    · rw [hln, pow_add]
  · unfold evalV sfz3
    refine ⟨?sf1s, ?sf1f, ?e, ?sf2s, ?sf2f, ⟨rfl, rfl, rfl⟩⟩
    · rw [hsf1s]
      change encC z (Noun.cell (P8Census.skeletonSubformula skel 1 .result)
          skel.subject) =
        FP.cons z (encC z (P8Census.skeletonSubformula skel 1 .result))
          (encC z skel.subject)
      rw [encC_eq, encC_eq, encC_eq]
      exact GlobalCarryRecognizer.enc_cons hz
        (P8Census.skeletonSubformula skel 1 .result) skel.subject
    · rw [hform]
      simp only [formulaHead, formulaTail]
    · rw [heval]
    · rw [hsf2s]
    · rw [hform]
      simp only [formulaHead, formulaTail]

/-- `Vcomp` for an `OP_8` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp8Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s8)
    (hform : skel.formula = Noun.cell (Noun.atom 8)
      (Noun.cell (P8Census.skeletonSubformula skel 1 .formula)
        (P8Census.skeletonSubformula skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject =
      Noun.cell (P8Census.skeletonSubformula skel 1 .result) skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject = skel.subject)
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 0 .result) :
    let row := renderOp8Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s8 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp8Row_Vcomp z α (stampOfAcc State.s8 acc) skel hz hform
    hsf1s hsf2s heval
    (stampOfAcc_s8_ln acc) (stampOfAcc_s8_rec0 acc) (stampOfAcc_s8_rec1 acc)

/-! ## `renderNode` / `renderRows` at `OP_8` -/

theorem renderNode_op8_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s8) :
    (renderNode z α g).row = renderOp8Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_8` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op8_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s8)
    (hform : g.skel.formula = Noun.cell (Noun.atom 8)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject =
      Noun.cell (P8Census.skeletonSubformula g.skel 1 .result) g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result)
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2)
    (hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1)
    (hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op8_row z α g hstate]
  exact renderOp8Row_Vcomp z α g.stamp g.skel hz hform
    hsf1s hsf2s heval hln hrec0 hrec1

theorem renderNode_op8_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s8)
    (hform : g.skel.formula = Noun.cell (Noun.atom 8)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject =
      Noun.cell (P8Census.skeletonSubformula g.skel 1 .result) g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result)
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s8_ln g.stamp.lnPrevExponent
  have hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s8_rec0 g.stamp.lnPrevExponent
  have hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s8_rec1 g.stamp.lnPrevExponent
  exact renderNode_op8_Vcomp z α g hz hstate hform
    hsf1s hsf2s heval hln hrec0 hrec1

/-- Singleton `OP_8` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op8_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s8)
    (hform : g.skel.formula = Noun.cell (Noun.atom 8)
      (Noun.cell (P8Census.skeletonSubformula g.skel 1 .formula)
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject =
      Noun.cell (P8Census.skeletonSubformula g.skel 1 .result) g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject = g.skel.subject)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 0 .result) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op8_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using hsf1s
  · simpa [bfsAssign_leaf_label] using hsf2s
  · simpa [bfsAssign_leaf_label] using heval
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Stamp equations at `OP_9` -/

theorem stampOfAcc_s9_ln (acc : ℕ) :
    (stampOfAcc State.s9 acc).lnExponent =
      (stampOfAcc State.s9 acc).lnPrevExponent + 3 := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent]
  simp [Nock.Framework.recordCount]

theorem stampOfAcc_s9_rec0 (acc : ℕ) :
    (stampOfAcc State.s9 acc).recordExponent (0 : Fin 3) =
      (stampOfAcc State.s9 acc).lnPrevExponent + 1 := by
  have hi : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s9 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s9 acc (0 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s9_rec1 (acc : ℕ) :
    (stampOfAcc State.s9 acc).recordExponent (1 : Fin 3) =
      (stampOfAcc State.s9 acc).lnPrevExponent + 2 := by
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s9 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s9 acc (1 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

theorem stampOfAcc_s9_rec2 (acc : ℕ) :
    (stampOfAcc State.s9 acc).recordExponent (2 : Fin 3) =
      (stampOfAcc State.s9 acc).lnPrevExponent + 3 := by
  have hi : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount State.s9 := by
    simp [Nock.Framework.recordCount]
  rw [stampOfAcc_recordExponent State.s9 acc (2 : Fin 3) hi,
      stampOfAcc_lnPrevExponent]
  simp

/-! ## Rendered `OP_9` row -/

/-- Field-generic `Vcomp` for one rendered `OP_9` row.
    `hform` is `[9 [atom axis, sf0]]` with `axis = skeletonMemoryAxis skel 2`.
    Core in `sf1` (`f_tt`), invoke in `sf2`, arm-fetch `mr3`.  Stamp hyps match OP6. -/
theorem renderOp9Row_Vcomp
    (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hform : skel.formula = Noun.cell (Noun.atom 9)
      (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis skel 2))
        (P8Census.skeletonSubformula skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject =
      P8Census.skeletonSubformula skel 0 .result)
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 1 .result)
    (hln : stamp.lnExponent = stamp.lnPrevExponent + 3)
    (hrec0 : stamp.recordExponent (0 : Fin 3) = stamp.lnPrevExponent + 1)
    (hrec1 : stamp.recordExponent (1 : Fin 3) = stamp.lnPrevExponent + 2)
    (hrec2 : stamp.recordExponent (2 : Fin 3) = stamp.lnPrevExponent + 3) :
    let row := renderOp9Row z α stamp skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  unfold renderOp9Row Vcomp
  refine ⟨?fcons, ?mr1, ?sv, ?mem, ?ev⟩
  · rw [hform]
    change encC z (Noun.cell (Noun.atom 9)
        (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis skel 2))
          (P8Census.skeletonSubformula skel 0 .formula))) =
      FP.cons z (encC z (formulaHead (Noun.cell (Noun.atom 9)
        (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis skel 2))
          (P8Census.skeletonSubformula skel 0 .formula)))))
        (encC z (formulaTail (Noun.cell (Noun.atom 9)
          (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis skel 2))
            (P8Census.skeletonSubformula skel 0 .formula)))))
    simp only [formulaHead, formulaTail]
    rw [encC_eq, encC_eq, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz (Noun.atom 9)
      (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis skel 2))
        (P8Census.skeletonSubformula skel 0 .formula))
  · refine MemRec.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · rw [hrec0, pow_succ]
  · unfold SVhead
    have hne : ¬ (State.s9 = State.cons) := by decide
    simp [hne]
    rw [hform]
    simp only [formulaHead]
    unfold headAtom
    rw [encC_eq, GlobalCarryRecognizer.enc_atom]
    simp [FP.atomFP, State.toNat]
  · unfold memBlk
    refine ⟨?mr2, ?ftcons, ?mr3, ?ln⟩
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rw [hrec1, pow_add]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, encC_eq, encC_eq]
      exact (GlobalCarryRecognizer.enc_cons hz
        (Noun.atom (P8Census.skeletonMemoryAxis skel 2))
        (P8Census.skeletonSubformula skel 0 .formula)).symm
    · refine MemRec.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rw [hform]
        simp only [formulaHead, formulaTail]
        rw [encC_eq, GlobalCarryRecognizer.enc_atom]
        simp [FP.atomFP]
      · rw [hrec2, pow_add]
    · rw [hln, pow_add]
  · unfold evalV sfz3
    refine ⟨?sf1s, ?sf1f, ?sf2s, ?e, ⟨rfl, rfl, rfl⟩, ?fthsize, ?fthdyck⟩
    · rw [hsf1s]
    · rw [hform]
      simp only [formulaHead, formulaTail]
    · rw [hsf2s]
    · rw [heval]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, GlobalCarryRecognizer.enc_atom]
      simp [FP.atomFP]
    · rw [hform]
      simp only [formulaHead, formulaTail]
      rw [encC_eq, GlobalCarryRecognizer.enc_atom]
      simp [FP.atomFP]

/-- `Vcomp` for an `OP_9` row whose stamp is `stampOfAcc` at its own state. -/
theorem renderOp9Row_Vcomp_of_stampOfAcc
    (z α : K) (acc : ℕ) (skel : ComputeRowSkeleton)
    (hz : z ≠ 0)
    (hstate : skel.state = State.s9)
    (hform : skel.formula = Noun.cell (Noun.atom 9)
      (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis skel 2))
        (P8Census.skeletonSubformula skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula skel 0 .subject = skel.subject)
    (hsf2s : P8Census.skeletonSubformula skel 1 .subject =
      P8Census.skeletonSubformula skel 0 .result)
    (heval : skel.evaluation = P8Census.skeletonSubformula skel 1 .result) :
    let row := renderOp9Row z α (stampOfAcc skel.state acc) skel
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hstamp : stampOfAcc skel.state acc = stampOfAcc State.s9 acc := by
    rw [hstate]
  rw [hstamp]
  exact renderOp9Row_Vcomp z α (stampOfAcc State.s9 acc) skel hz hform
    hsf1s hsf2s heval
    (stampOfAcc_s9_ln acc) (stampOfAcc_s9_rec0 acc)
    (stampOfAcc_s9_rec1 acc) (stampOfAcc_s9_rec2 acc)

/-! ## `renderNode` / `renderRows` at `OP_9` -/

theorem renderNode_op9_row (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s9) :
    (renderNode z α g).row = renderOp9Row z α g.stamp g.skel := by
  unfold renderNode
  rw [h]

/-- Rendered `OP_9` node satisfies `Vcomp`.  Stamp hypotheses come from
    `assignedStampsWellFormed` / `bfsAssign` -/
theorem renderNode_op9_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s9)
    (hform : g.skel.formula = Noun.cell (Noun.atom 9)
      (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis g.skel 2))
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject =
      P8Census.skeletonSubformula g.skel 0 .result)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 1 .result)
    (hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 3)
    (hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1)
    (hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2)
    (hrec2 : g.stamp.recordExponent (2 : Fin 3) = g.stamp.lnPrevExponent + 3) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderNode_op9_row z α g hstate]
  exact renderOp9Row_Vcomp z α g.stamp g.skel hz hform
    hsf1s hsf2s heval hln hrec0 hrec1 hrec2

theorem renderNode_op9_Vcomp_of_assigned
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s9)
    (hform : g.skel.formula = Noun.cell (Noun.atom 9)
      (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis g.skel 2))
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject =
      P8Census.skeletonSubformula g.skel 0 .result)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 1 .result)
    (hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent) :
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  have hln : g.stamp.lnExponent = g.stamp.lnPrevExponent + 3 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s9_ln g.stamp.lnPrevExponent
  have hrec0 : g.stamp.recordExponent (0 : Fin 3) = g.stamp.lnPrevExponent + 1 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s9_rec0 g.stamp.lnPrevExponent
  have hrec1 : g.stamp.recordExponent (1 : Fin 3) = g.stamp.lnPrevExponent + 2 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s9_rec1 g.stamp.lnPrevExponent
  have hrec2 : g.stamp.recordExponent (2 : Fin 3) = g.stamp.lnPrevExponent + 3 := by
    rw [hstamp, hstate]
    simpa using stampOfAcc_s9_rec2 g.stamp.lnPrevExponent
  exact renderNode_op9_Vcomp z α g hz hstate hform
    hsf1s hsf2s heval hln hrec0 hrec1 hrec2

/-- Singleton `OP_9` tree after BFS assign and render: the root row satisfies
    `Vcomp`.  `bfsAssign` on a leaf is `stampOfAcc` at accumulator `0`. -/
theorem renderRows_bfsAssign_op9_leaf_Vcomp
    (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (hstate : g.skel.state = State.s9)
    (hform : g.skel.formula = Noun.cell (Noun.atom 9)
      (Noun.cell (Noun.atom (P8Census.skeletonMemoryAxis g.skel 2))
        (P8Census.skeletonSubformula g.skel 0 .formula)))
    (hsf1s : P8Census.skeletonSubformula g.skel 0 .subject = g.skel.subject)
    (hsf2s : P8Census.skeletonSubformula g.skel 1 .subject =
      P8Census.skeletonSubformula g.skel 0 .result)
    (heval : g.skel.evaluation = P8Census.skeletonSubformula g.skel 1 .result) :
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  rw [renderRows_label_row]
  refine renderNode_op9_Vcomp_of_assigned z α
    (bfsAssign (.node g [])).label hz ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [bfsAssign_leaf_label] using hstate
  · simpa [bfsAssign_leaf_label] using hform
  · simpa [bfsAssign_leaf_label] using hsf1s
  · simpa [bfsAssign_leaf_label] using hsf2s
  · simpa [bfsAssign_leaf_label] using heval
  · simp [bfsAssign_leaf_label, stampOfAcc_lnPrevExponent]


/-! ## Non-vacuity witnesses -/

/-- Distinct atom fingerprints at a field-generic seed. -/
theorem encC_atom_ne (z : K) (a b : ℕ) (h : (a : K) ≠ (b : K)) :
    encC z (Noun.atom a) ≠ encC z (Noun.atom b) := by
  intro heq
  have hleaf := congrArg FP.leaf heq
  simp only [encC_eq, GlobalCarryRecognizer.enc_atom, FP.atomFP] at hleaf
  exact h hleaf

/-- `tis` of unequal nouns whose encodings differ is the `eqOp` atom `1`. -/
theorem encC_tis_of_enc_ne (z : K) (a b : Noun)
    (hab : a ≠ b) (hne : encC z a ≠ encC z b) :
    encC z (Noun.tis a b) =
      FP.atomFP z (FP.eqOp (encC z a) (encC z b)) := by
  unfold Noun.tis FP.eqOp
  rw [if_neg hab, if_neg hne, encC_eq, GlobalCarryRecognizer.enc_atom]
  simp

/-- OP5 fixture `*[0 [5 [1 3] [1 4]]]`: distinct operands `3` vs `4`, `tis` returns `1`. -/
def op5VcompSkel : ComputeRowSkeleton :=
  genSkelOp5 (Noun.atom 0)
    (Noun.cell (Noun.atom 5)
      (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
        (Noun.cell (Noun.atom 1) (Noun.atom 4))))
    (Noun.atom 5)
    (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
      (Noun.cell (Noun.atom 1) (Noun.atom 4)))
    (Noun.cell (Noun.atom 1) (Noun.atom 3))
    (Noun.cell (Noun.atom 1) (Noun.atom 4))
    (Noun.atom 3) (Noun.atom 4)
    (Noun.tis (Noun.atom 3) (Noun.atom 4))

/-- OP2 fixture `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`. -/
def op2VcompSkel : ComputeRowSkeleton :=
  genSkelOp2 (Noun.atom 0)
    (Noun.cell (Noun.atom 2)
      (Noun.cell (Noun.cell (Noun.atom 1) (Noun.cell (Noun.atom 0) (Noun.atom 1)))
        (Noun.cell (Noun.atom 1) (Noun.cell (Noun.atom 1) (Noun.atom 5)))))
    (Noun.atom 2)
    (Noun.cell (Noun.cell (Noun.atom 1) (Noun.cell (Noun.atom 0) (Noun.atom 1)))
      (Noun.cell (Noun.atom 1) (Noun.cell (Noun.atom 1) (Noun.atom 5))))
    (Noun.cell (Noun.atom 1) (Noun.cell (Noun.atom 0) (Noun.atom 1)))
    (Noun.cell (Noun.atom 1) (Noun.cell (Noun.atom 1) (Noun.atom 5)))
    (Noun.cell (Noun.atom 0) (Noun.atom 1))
    (Noun.cell (Noun.atom 1) (Noun.atom 5))
    (Noun.atom 5)

/-- OP7 fixture `*[0 [7 [[1 3] [1 5]]]] = 5` in `evalV` slot order
    (slot 0 = consumer, slot 1 = helper). -/
def op7EvalVSkel : ComputeRowSkeleton where
  state := .s7
  subject := Noun.atom 0
  formula := Noun.cell (Noun.atom 7)
    (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
      (Noun.cell (Noun.atom 1) (Noun.atom 5)))
  evaluation := Noun.atom 5
  decomposition := fun slot _ =>
    match slot with
    | .f_h => Noun.atom 7
    | .f_t => Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
        (Noun.cell (Noun.atom 1) (Noun.atom 5))
    | .f_th => Noun.cell (Noun.atom 1) (Noun.atom 3)
    | .f_tt => Noun.cell (Noun.atom 1) (Noun.atom 5)
    | _ => Noun.atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => Noun.atom 3
      | .formula => Noun.cell (Noun.atom 1) (Noun.atom 5)
      | .result => Noun.atom 5
    else
      match slot with
      | .subject => Noun.atom 0
      | .formula => Noun.cell (Noun.atom 1) (Noun.atom 3)
      | .result => Noun.atom 3
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then
      ⟨Noun.cell (Noun.atom 7)
        (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
          (Noun.cell (Noun.atom 1) (Noun.atom 5))),
        Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
          (Noun.cell (Noun.atom 1) (Noun.atom 5)), 3⟩
    else
      ⟨Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
        (Noun.cell (Noun.atom 1) (Noun.atom 5)),
        Noun.cell (Noun.atom 1) (Noun.atom 3), 2⟩

/-- OP8 fixture `*[0 [8 [[1 3] [1 5]]]] = 5` in `evalV` slot order
    (slot 0 = consumer with cell `sb` subject, slot 1 = helper). -/
def op8EvalVSkel : ComputeRowSkeleton where
  state := .s8
  subject := Noun.atom 0
  formula := Noun.cell (Noun.atom 8)
    (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
      (Noun.cell (Noun.atom 1) (Noun.atom 5)))
  evaluation := Noun.atom 5
  decomposition := fun slot _ =>
    match slot with
    | .f_h => Noun.atom 8
    | .f_t => Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
        (Noun.cell (Noun.atom 1) (Noun.atom 5))
    | .f_th => Noun.cell (Noun.atom 1) (Noun.atom 3)
    | .f_tt => Noun.cell (Noun.atom 1) (Noun.atom 5)
    | _ => Noun.atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => Noun.cell (Noun.atom 3) (Noun.atom 0)
      | .formula => Noun.cell (Noun.atom 1) (Noun.atom 5)
      | .result => Noun.atom 5
    else
      match slot with
      | .subject => Noun.atom 0
      | .formula => Noun.cell (Noun.atom 1) (Noun.atom 3)
      | .result => Noun.atom 3
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then
      ⟨Noun.cell (Noun.atom 8)
        (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
          (Noun.cell (Noun.atom 1) (Noun.atom 5))),
        Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
          (Noun.cell (Noun.atom 1) (Noun.atom 5)), 3⟩
    else
      ⟨Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
        (Noun.cell (Noun.atom 1) (Noun.atom 5)),
        Noun.cell (Noun.atom 1) (Noun.atom 3), 2⟩

/-- OP9 fixture `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`, arm-fetch axis `2`. -/
def op9VcompSkel : ComputeRowSkeleton :=
  genSkelOp9 (Noun.atom 0)
    (Noun.cell (Noun.atom 9)
      (Noun.cell (Noun.atom 2)
        (Noun.cell (Noun.atom 1)
          (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 7))
            (Noun.cell (Noun.atom 1) (Noun.atom 9))))))
    (Noun.atom 9)
    (Noun.cell (Noun.atom 2)
      (Noun.cell (Noun.atom 1)
        (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 7))
          (Noun.cell (Noun.atom 1) (Noun.atom 9)))))
    (Noun.atom 2)
    (Noun.cell (Noun.atom 1)
      (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 7))
        (Noun.cell (Noun.atom 1) (Noun.atom 9))))
    (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 7))
      (Noun.cell (Noun.atom 1) (Noun.atom 9)))
    (Noun.cell (Noun.atom 1) (Noun.atom 7))
    (Noun.atom 7) 2

theorem renderRows_bfsAssign_op5_leaf_Vcomp_nonvacuous
    (z α : K) (hz : z ≠ 0) :
    let g : GenComputeRow K :=
      { skel := op5VcompSkel
        stamp := stampOfAcc State.s5 0
        row := renderOp5Row z α (stampOfAcc State.s5 0) op5VcompSkel
        requests := [] }
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  refine renderRows_bfsAssign_op5_leaf_Vcomp z α
    { skel := op5VcompSkel
      stamp := stampOfAcc State.s5 0
      row := renderOp5Row z α (stampOfAcc State.s5 0) op5VcompSkel
      requests := [] } hz rfl ?hform ?hsf1s ?hsf2s ?heval
  · simp [op5VcompSkel, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [op5VcompSkel, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [op5VcompSkel, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · have h34 : (3 : K) ≠ 4 := by
      intro h
      have h0 : (4 : K) - 3 = 0 := by rw [h]; ring
      have h1 : (4 : K) - 3 = 1 := by ring
      exact one_ne_zero (h1.symm.trans h0)
    have hne : encC z (Noun.atom 3) ≠ encC z (Noun.atom 4) :=
      encC_atom_ne z 3 4 h34
    have hab : Noun.atom 3 ≠ Noun.atom 4 := by decide
    simp [op5VcompSkel, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
    exact encC_tis_of_enc_ne z (Noun.atom 3) (Noun.atom 4) hab hne

theorem renderRows_bfsAssign_op2_leaf_Vcomp_nonvacuous
    (z α : K) (hz : z ≠ 0) :
    let g : GenComputeRow K :=
      { skel := op2VcompSkel
        stamp := stampOfAcc State.s2 0
        row := renderOp2Row z α (stampOfAcc State.s2 0) op2VcompSkel
        requests := [] }
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 :=
  renderRows_bfsAssign_op2_leaf_Vcomp z α
    { skel := op2VcompSkel
      stamp := stampOfAcc State.s2 0
      row := renderOp2Row z α (stampOfAcc State.s2 0) op2VcompSkel
      requests := [] } hz rfl rfl rfl rfl rfl rfl rfl

theorem renderRows_bfsAssign_op7_leaf_Vcomp_nonvacuous
    (z α : K) (hz : z ≠ 0) :
    let g : GenComputeRow K :=
      { skel := op7EvalVSkel
        stamp := stampOfAcc State.s7 0
        row := renderOp7Row z α (stampOfAcc State.s7 0) op7EvalVSkel
        requests := [] }
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  refine renderRows_bfsAssign_op7_leaf_Vcomp z α
    { skel := op7EvalVSkel
      stamp := stampOfAcc State.s7 0
      row := renderOp7Row z α (stampOfAcc State.s7 0) op7EvalVSkel
      requests := [] } hz rfl ?hform ?hsf1s ?hsf2s ?heval
  · simp [op7EvalVSkel, P8Census.skeletonSubformula, ComputeTable.fanoutComp]
  · simp [op7EvalVSkel, P8Census.skeletonSubformula, ComputeTable.fanoutComp]
  · simp [op7EvalVSkel, P8Census.skeletonSubformula, ComputeTable.fanoutComp]
  · simp [op7EvalVSkel, P8Census.skeletonSubformula, ComputeTable.fanoutComp]

theorem renderRows_bfsAssign_op8_leaf_Vcomp_nonvacuous
    (z α : K) (hz : z ≠ 0) :
    let g : GenComputeRow K :=
      { skel := op8EvalVSkel
        stamp := stampOfAcc State.s8 0
        row := renderOp8Row z α (stampOfAcc State.s8 0) op8EvalVSkel
        requests := [] }
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  refine renderRows_bfsAssign_op8_leaf_Vcomp z α
    { skel := op8EvalVSkel
      stamp := stampOfAcc State.s8 0
      row := renderOp8Row z α (stampOfAcc State.s8 0) op8EvalVSkel
      requests := [] } hz rfl ?hform ?hsf1s ?hsf2s ?heval
  · simp [op8EvalVSkel, P8Census.skeletonSubformula, ComputeTable.fanoutComp]
  · simp [op8EvalVSkel, P8Census.skeletonSubformula, ComputeTable.fanoutComp]
  · simp [op8EvalVSkel, P8Census.skeletonSubformula, ComputeTable.fanoutComp]
  · simp [op8EvalVSkel, P8Census.skeletonSubformula, ComputeTable.fanoutComp]

theorem renderRows_bfsAssign_op9_leaf_Vcomp_nonvacuous
    (z α : K) (hz : z ≠ 0) :
    let g : GenComputeRow K :=
      { skel := op9VcompSkel
        stamp := stampOfAcc State.s9 0
        row := renderOp9Row z α (stampOfAcc State.s9 0) op9VcompSkel
        requests := [] }
    let row := (renderRows z α (bfsAssign (.node g []))).label.row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  refine renderRows_bfsAssign_op9_leaf_Vcomp z α
    { skel := op9VcompSkel
      stamp := stampOfAcc State.s9 0
      row := renderOp9Row z α (stampOfAcc State.s9 0) op9VcompSkel
      requests := [] } hz rfl ?hform ?hsf1s ?hsf2s ?heval
  · simp [op9VcompSkel, genSkelOp9, P8Census.skeletonSubformula,
      P8Census.skeletonMemoryAxis, ComputeTable.fanoutComp,
      Nock.Framework.recordCount]
  · simp [op9VcompSkel, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [op9VcompSkel, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [op9VcompSkel, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]

/-! ## Axiom receipts -/
#print axioms renderOp1Row_Vcomp
#print axioms renderOp1Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op1_Vcomp
#print axioms renderNode_op1_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op1_leaf_Vcomp
#print axioms renderOp0Row_Vcomp
#print axioms renderOp0Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op0_Vcomp
#print axioms renderNode_op0_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op0_leaf_Vcomp
#print axioms stampOfAcc_s3_ln
#print axioms stampOfAcc_s3_rec0
#print axioms renderOp3Row_Vcomp
#print axioms renderOp3Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op3_row
#print axioms renderNode_op3_Vcomp
#print axioms renderNode_op3_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op3_leaf_Vcomp
#print axioms stampOfAcc_s4_ln
#print axioms stampOfAcc_s4_rec0
#print axioms renderOp4Row_Vcomp
#print axioms renderOp4Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op4_row
#print axioms renderNode_op4_Vcomp
#print axioms renderNode_op4_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op4_leaf_Vcomp
#print axioms stampOfAcc_s6_ln
#print axioms stampOfAcc_s6_rec0
#print axioms stampOfAcc_s6_rec1
#print axioms stampOfAcc_s6_rec2
#print axioms renderOp6Row_Vcomp
#print axioms renderOp6Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op6_row
#print axioms renderNode_op6_Vcomp
#print axioms renderNode_op6_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op6_leaf_Vcomp
#print axioms stampOfAcc_cons_ln
#print axioms stampOfAcc_cons_rec0
#print axioms renderConsRow_Vcomp
#print axioms renderConsRow_Vcomp_of_stampOfAcc
#print axioms renderNode_cons_row
#print axioms renderNode_cons_Vcomp
#print axioms renderNode_cons_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_cons_leaf_Vcomp
#print axioms stampOfAcc_s5_ln
#print axioms stampOfAcc_s5_rec0
#print axioms stampOfAcc_s5_rec1
#print axioms renderOp5Row_Vcomp
#print axioms renderOp5Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op5_row
#print axioms renderNode_op5_Vcomp
#print axioms renderNode_op5_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op5_leaf_Vcomp
#print axioms stampOfAcc_s2_ln
#print axioms stampOfAcc_s2_rec0
#print axioms stampOfAcc_s2_rec1
#print axioms renderOp2Row_Vcomp
#print axioms renderOp2Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op2_row
#print axioms renderNode_op2_Vcomp
#print axioms renderNode_op2_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op2_leaf_Vcomp
#print axioms stampOfAcc_s7_ln
#print axioms stampOfAcc_s7_rec0
#print axioms stampOfAcc_s7_rec1
#print axioms renderOp7Row_Vcomp
#print axioms renderOp7Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op7_row
#print axioms renderNode_op7_Vcomp
#print axioms renderNode_op7_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op7_leaf_Vcomp
#print axioms stampOfAcc_s8_ln
#print axioms stampOfAcc_s8_rec0
#print axioms stampOfAcc_s8_rec1
#print axioms renderOp8Row_Vcomp
#print axioms renderOp8Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op8_row
#print axioms renderNode_op8_Vcomp
#print axioms renderNode_op8_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op8_leaf_Vcomp
#print axioms stampOfAcc_s9_ln
#print axioms stampOfAcc_s9_rec0
#print axioms stampOfAcc_s9_rec1
#print axioms stampOfAcc_s9_rec2
#print axioms renderOp9Row_Vcomp
#print axioms renderOp9Row_Vcomp_of_stampOfAcc
#print axioms renderNode_op9_row
#print axioms renderNode_op9_Vcomp
#print axioms renderNode_op9_Vcomp_of_assigned
#print axioms renderRows_bfsAssign_op9_leaf_Vcomp
#print axioms renderRows_bfsAssign_op5_leaf_Vcomp_nonvacuous
#print axioms renderRows_bfsAssign_op2_leaf_Vcomp_nonvacuous
#print axioms renderRows_bfsAssign_op7_leaf_Vcomp_nonvacuous
#print axioms renderRows_bfsAssign_op8_leaf_Vcomp_nonvacuous
#print axioms renderRows_bfsAssign_op9_leaf_Vcomp_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
