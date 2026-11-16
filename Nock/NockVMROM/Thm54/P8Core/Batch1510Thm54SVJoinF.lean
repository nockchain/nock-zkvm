/-
  Nock/NockVMROM/Thm54/P8Core/Batch1510Thm54SVJoinF.lean

`StrategyOfTracesR0AC2.c2Evaluation`'s OP4 arm is Nat-valued (`.atom k ↦ .atom (k + 1)`), so under
  the field semantics `HoldsF q x := ∃ fuel, evalFBy q fuel x.subject x.formula = some x.result`
  (`FieldEmbedding.evalFBy`: `Nock.evalN` with OP4 = `lusFBy q`) a decoded join value can leave
  `BoundedBy q` while `evalFBy` wraps.

  This module is the twin with the OP4 arm **mod q**: `c2EvaluationF q` is `c2Evaluation` with
  `.s4 ↦ OpcodeSemantics.incMod q (kid 0).evaluation` (`incMod q (.atom n) = .atom ((n + 1) % q)`,
  the paper, `:1531-1534`; the cell case `.atom 0` is never consumed: the accepted OP4 row
  has an atom operand).  `c2SkeletonRowF q` and `c2JoinFuelF q` are `c2SkeletonRow` /
  `c2JoinFuel` verbatim at `c2EvaluationF q`.  Every other arm is literally the Nat join's, so the
  two joins differ only through OP4 values (and whatever later reads them).

  Paper: the paper (`V_comp`), `:1864-1868` (the OP0 record), `:1879-1882` (the OP9
  record and arm), `:1531-1534` (field increment).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
import Nock.NockVMROM.Thm54.OpcodeSemantics

namespace Nock.NockVMROM.Thm54.SVJoinF

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-- **OP0's result in the field join.**  At axis `1`
the result is the subject itself (`Noun.slot 1 s = s`); the compute chip's
`z1` column serves that read with no memory lookup, so the join must not read the memory oracle
there.  Off axis `1` it is the served read `sv .verify_child (S + 2)`, as before. -/
def op0ResF (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ) (subj : Noun) : Noun :=
  if ax (S + 2) = 1 then subj else sv .verify_child (S + 2)

/-- **OP9's arm in the field join**: at axis `1` the arm is the core itself; off axis
`1` it is the served read `sv .verify_child (S + 3)`. -/
def op9ArmF (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ) (core : Noun) : Noun :=
  if ax (S + 3) = 1 then core else sv .verify_child (S + 3)

theorem op0ResF_of_ne {sv : MState → ℕ → Noun} {ax : ℕ → ℕ} {S : ℕ} (subj : Noun)
    (h : ax (S + 2) ≠ 1) : op0ResF sv ax S subj = sv .verify_child (S + 2) := if_neg h

theorem op0ResF_of_eq {sv : MState → ℕ → Noun} {ax : ℕ → ℕ} {S : ℕ} (subj : Noun)
    (h : ax (S + 2) = 1) : op0ResF sv ax S subj = subj := if_pos h

theorem op9ArmF_of_ne {sv : MState → ℕ → Noun} {ax : ℕ → ℕ} {S : ℕ} (core : Noun)
    (h : ax (S + 3) ≠ 1) : op9ArmF sv ax S core = sv .verify_child (S + 3) := if_neg h

theorem op9ArmF_of_eq {sv : MState → ℕ → Noun} {ax : ℕ → ℕ} {S : ℕ} (core : Noun)
    (h : ax (S + 3) = 1) : op9ArmF sv ax S core = core := if_pos h

/-- **The field C2 row evaluation**: `StrategyOfTracesR0AC2.c2Evaluation` with OP4 = `incMod q`. (OP0 at axis `1`: `op0ResF`). -/
def c2EvaluationF (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (st : State) (S : ℕ)
    (subj formula : Noun) (kids : List ComputeRowSkeleton) : Noun :=
  match st with
  | .cons => .cell (kidSkel kids 0).evaluation (kidSkel kids 1).evaluation
  | .s1 => nounTail formula
  | .s3 => Noun.wut (kidSkel kids 0).evaluation
  | .s4 => OpcodeSemantics.incMod q (kidSkel kids 0).evaluation
  | .s5 => Noun.tis (kidSkel kids 0).evaluation (kidSkel kids 1).evaluation
  | .s2 => (kidSkel kids 2).evaluation
  | .s6 | .s7 | .s8 => (kidSkel kids 0).evaluation
  | .s9 => (kidSkel kids 1).evaluation
  | .s0 => op0ResF sv ax S subj

/-- **The field C2 skeleton row**: `StrategyOfTracesR0AC2.c2SkeletonRow` at `c2EvaluationF q`. -/
def c2SkeletonRowF (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (st : State) (S : ℕ)
    (subj formula : Noun) (kids : List ComputeRowSkeleton) : ComputeRowSkeleton :=
  let fh := nounHead formula
  let ft := nounTail formula
  let fth := nounHead ft
  let ftt := nounTail ft
  let ftth := nounHead ftt
  let fttt := nounTail ftt
  { state := st
    subject := subj
    formula := formula
    evaluation := c2EvaluationF q sv ax st S subj formula kids
    decomposition := fun slot _ =>
      match slot with
      | .f_h => fh
      | .f_t => ft
      | .f_th => fth
      | .f_tt => ftt
      | .f_tth => ftth
      | .f_ttt => fttt
    subformula := fun i _hi slot =>
      if h : (i : ℕ) < kids.length then
        match slot with
        | .subject => (kids[(i : ℕ)]'h).subject
        | .formula => (kids[(i : ℕ)]'h).formula
        | .result => (kids[(i : ℕ)]'h).evaluation
      else
        Noun.atom 0
    memoryRecord := fun i _ =>
      match st, i.val with
      | _, 0 => ⟨formula, ft, 3⟩
      | .s0, 1 => ⟨subj, c2EvaluationF q sv ax st S subj formula kids, ax (S + 2)⟩
      | .s2, 1 | .s5, 1 | .s7, 1 | .s8, 1 | .s9, 1 => ⟨ft, fth, 2⟩
      | .s6, 1 => ⟨ft, fth, 2⟩
      | .s6, 2 => ⟨ftt, ftth, 2⟩
      | .s9, 2 => ⟨(kidSkel kids 0).evaluation, (kidSkel kids 1).formula, ax (S + 3)⟩
      | _, _ => dummyMemRec }

variable {β : Type}

/-- MIG 4.35: the children of `c2JoinFuelF` at one row, with the recursive call `f` as a parameter.
Non-recursive; split out so the kernel checks the per-opcode match outside the structural recursion (4.35 reports
deep recursion on the inlined form). The `c2JoinFuelF_eq_k_old` lemmas restate the 4.31 equations. -/
def c2JoinKidsF (q : ℕ) (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
    (f : NTree β → Noun → Noun → NTree ComputeRowSkeleton)
    (row : β) (ch : List (NTree β)) (subj formula : Noun) :
    List (NTree ComputeRowSkeleton) :=
  match st row, ch with
  | .s0, [] => []
  | .s1, [] => []
  | .cons, [c0, c1] =>
      [f c0 subj (nounHead formula),
       f c1 subj (nounTail formula)]
  | .s3, [c0] =>
      [f c0 subj (nounTail formula)]
  | .s4, [c0] =>
      [f c0 subj (nounTail formula)]
  | .s5, [c0, c1] =>
      [f c0 subj (nounHead (nounTail formula)),
       f c1 subj (nounTail (nounTail formula))]
  | .s2, [c0, c1, c2] =>
      let s0 := f c0 subj (nounHead (nounTail formula))
      let s1 := f c1 subj (nounTail (nounTail formula))
      [s0, s1, f c2 s0.label.evaluation s1.label.evaluation]
  | .s6, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftth := nounHead (nounTail (nounTail formula))
      let fttt := nounTail (nounTail (nounTail formula))
      let sCond := f c1 subj fth
      let b :=
        match sCond.label.evaluation with
        | .atom k => k
        | _ => 0
      [f c0 subj (if b = 0 then ftth else fttt), sCond]
  | .s7, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := f c1 subj fth
      [f c0 sHelp.label.evaluation ftt, sHelp]
  | .s8, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := f c1 subj fth
      [f c0 (Noun.cell sHelp.label.evaluation subj) ftt, sHelp]
  | .s9, [c0, c1] =>
      let coreF := nounTail (nounTail formula)
      let sCore := f c0 subj coreF
      let arm := op9ArmF sv ax (Sof row) sCore.label.evaluation
      [sCore, f c1 sCore.label.evaluation arm]
  | _, ch' =>
      ch'.map fun c => f c subj formula


/-- **The field C2 join at fuel**: `StrategyOfTracesR0AC2.c2JoinFuel` verbatim at
`c2SkeletonRowF q` (OP9's arm served, `sv .verify_child (S + 3)`). -/
def c2JoinFuelF (q : ℕ) (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) :
    ℕ → NTree β → Noun → Noun → NTree ComputeRowSkeleton
  | 0, .node row _, subj, formula =>
      .node (c2SkeletonRowF q sv ax (st row) (Sof row) subj formula []) []
  | n + 1, .node row ch, subj, formula =>
      let kids : List (NTree ComputeRowSkeleton) :=
        c2JoinKidsF q st Sof sv ax (fun c s fo => c2JoinFuelF q st Sof sv ax n c s fo) row ch subj formula
      .node (c2SkeletonRowF q sv ax (st row) (Sof row) subj formula (kids.map NTree.label)) kids

attribute [simp] c2JoinKidsF

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_1`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_1_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (row : β)
  (children : List (Nock.Walk.NTree β)),
  Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax 0 (Nock.Walk.NTree.node row children) x x_1 =
    Nock.Walk.NTree.node (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1 []) [] := by
  intros; rfl

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_2`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_2_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β),
  st row = Nock.ComputeTable.State.s0 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row []) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label []))
        [] := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_3`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_3_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β),
  st row = Nock.ComputeTable.State.s1 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row []) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label []))
        [] := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_4`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_4_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.cons →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead x_1),
              Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)]))
        [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead x_1),
          Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)] := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_5`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_5_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s3 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)]))
        [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)] := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_6`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_6_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s4 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)]))
        [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)] := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_7`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_7_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s5 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)),
              Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1))]))
        [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)),
          Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1))] := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_8`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_8_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 c2 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s2 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1, c2]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (have s0 :=
              Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
            have s1 :=
              Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
            [s0, s1,
              Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c2 s0.label.evaluation s1.label.evaluation])))
        (have s0 :=
          Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
        have s1 :=
          Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
        [s0, s1, Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c2 s0.label.evaluation s1.label.evaluation]) := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_9`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_9_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s6 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (let fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have ftth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
            have fttt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
            let sCond := Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x fth;
            let b :=
              match sCond.label.evaluation with
              | Nock.Noun.atom k => k
              | x => 0;
            [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x (if b = 0 then ftth else fttt), sCond])))
        (let fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have ftth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
        have fttt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
        let sCond := Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x fth;
        let b :=
          match sCond.label.evaluation with
          | Nock.Noun.atom k => k
          | x => 0;
        [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x (if b = 0 then ftth else fttt), sCond]) := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_10`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_10_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s7 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (have fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have ftt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have sHelp := Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x fth;
            [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 sHelp.label.evaluation ftt, sHelp])))
        (have fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have ftt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have sHelp := Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x fth;
        [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 sHelp.label.evaluation ftt, sHelp]) := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_11`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_11_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s8 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (have fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have ftt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have sHelp := Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x fth;
            [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 (sHelp.label.evaluation.cell x) ftt, sHelp])))
        (have fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have ftt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have sHelp := Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 x fth;
        [Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 (sHelp.label.evaluation.cell x) ftt, sHelp]) := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_12`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_12_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s9 →
    Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (have coreF :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have sCore := Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x coreF;
            have arm := Nock.NockVMROM.Thm54.SVJoinF.op9ArmF sv ax (Sof row) sCore.label.evaluation;
            [sCore, Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 sCore.label.evaluation arm])))
        (have coreF :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have sCore := Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c0 x coreF;
        have arm := Nock.NockVMROM.Thm54.SVJoinF.op9ArmF sv ax (Sof row) sCore.label.evaluation;
        [sCore, Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c1 sCore.label.evaluation arm]) := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuelF.eq_13`, verbatim, at the re-encoded def. -/
theorem c2JoinFuelF_eq_13_old : ∀ {β : Type} (q : ℕ) (st : β → Nock.ComputeTable.State) (Sof : β → ℕ)
  (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (ch : List (Nock.Walk.NTree β)),
  (st row = Nock.ComputeTable.State.s0 → ch = [] → False) →
    (st row = Nock.ComputeTable.State.s1 → ch = [] → False) →
      (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.cons → ch = [c0, c1] → False) →
        (∀ (c0 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s3 → ch = [c0] → False) →
          (∀ (c0 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s4 → ch = [c0] → False) →
            (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s5 → ch = [c0, c1] → False) →
              (∀ (c0 c1 c2 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s2 → ch = [c0, c1, c2] → False) →
                (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s6 → ch = [c0, c1] → False) →
                  (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s7 → ch = [c0, c1] → False) →
                    (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s8 → ch = [c0, c1] → False) →
                      (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s9 → ch = [c0, c1] → False) →
                        Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n.succ (Nock.Walk.NTree.node row ch) x
                            x_1 =
                          Nock.Walk.NTree.node
                            (Nock.NockVMROM.Thm54.SVJoinF.c2SkeletonRowF q sv ax (st row) (Sof row) x x_1
                              (List.map Nock.Walk.NTree.label
                                (List.map (fun c => Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c x x_1)
                                  ch)))
                            (List.map (fun c => Nock.NockVMROM.Thm54.SVJoinF.c2JoinFuelF q st Sof sv ax n c x x_1) ch) := by
  intros
  rw [c2JoinFuelF.eq_2]
  unfold c2JoinKidsF
  split <;> simp_all

/-- The field C2 join at fuel `t.size`. -/
def c2JoinF (q : ℕ) (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
    (t : NTree β) (subj formula : Noun) : NTree ComputeRowSkeleton :=
  c2JoinFuelF q st Sof sv ax t.size t subj formula

theorem c2JoinFuelF_subject (q : ℕ) (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) (fuel : ℕ) (t : NTree β) (subj formula : Noun) :
    (c2JoinFuelF q st Sof sv ax fuel t subj formula).label.subject = subj := by
  cases fuel <;> cases t <;> rfl

theorem c2JoinFuelF_formula (q : ℕ) (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) (fuel : ℕ) (t : NTree β) (subj formula : Noun) :
    (c2JoinFuelF q st Sof sv ax fuel t subj formula).label.formula = formula := by
  cases fuel <;> cases t <;> rfl

theorem c2JoinFuelF_state (q : ℕ) (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) (fuel : ℕ) (t : NTree β) (subj formula : Noun) :
    (c2JoinFuelF q st Sof sv ax fuel t subj formula).label.state = st t.label := by
  cases fuel <;> cases t <;> rfl

@[simp] theorem c2SkeletonRowF_state (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (st : State)
    (S : ℕ) (subj f : Noun) (kids : List ComputeRowSkeleton) :
    (c2SkeletonRowF q sv ax st S subj f kids).state = st := rfl

@[simp] theorem c2SkeletonRowF_subject (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
    (st : State) (S : ℕ) (subj f : Noun) (kids : List ComputeRowSkeleton) :
    (c2SkeletonRowF q sv ax st S subj f kids).subject = subj := rfl

@[simp] theorem c2SkeletonRowF_formula (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
    (st : State) (S : ℕ) (subj f : Noun) (kids : List ComputeRowSkeleton) :
    (c2SkeletonRowF q sv ax st S subj f kids).formula = f := rfl

@[simp] theorem c2SkeletonRowF_evaluation (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
    (st : State) (S : ℕ) (subj f : Noun) (kids : List ComputeRowSkeleton) :
    (c2SkeletonRowF q sv ax st S subj f kids).evaluation = c2EvaluationF q sv ax st S subj f kids := rfl

/-- Off OP4 the field evaluation IS the Nat one (the twin moves only the OP4 arm). -/
theorem c2EvaluationF_eq_of_ne_s4 (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) {st : State}
    (hst : st ≠ .s4) (S : ℕ) (subj formula : Noun) (kids : List ComputeRowSkeleton)
    (h0 : st = .s0 → ax (S + 2) ≠ 1) :
    c2EvaluationF q sv ax st S subj formula kids =
      StrategyOfTracesR0AC2.c2Evaluation sv st S formula kids := by
  cases st <;> first | rfl | exact absurd rfl hst | exact op0ResF_of_ne subj (h0 rfl)

/-- The OP4 arm of the field evaluation at an atom operand: `(k + 1) % q`. -/
theorem c2EvaluationF_s4_atom (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ)
    (subj formula : Noun)
    (kids : List ComputeRowSkeleton) {k : ℕ} (hk : (kidSkel kids 0).evaluation = .atom k) :
    c2EvaluationF q sv ax .s4 S subj formula kids = .atom ((k + 1) % q) := by
  simp [c2EvaluationF, hk, OpcodeSemantics.incMod]

end

end Nock.NockVMROM.Thm54.SVJoinF
