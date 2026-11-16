/-
  Nock/RedTeam/Batch1171Thm54C2InductionPositional.lean

  `Batch1141.Ctx.recs` quantifies over every `(u, s, f)`
  whose join node is merely a subtree of the root join; at two nodes with equal join labels and
  different trace rows (e.g. two `OP1` rows: the C2 label of an `OP1` row does not read its carrier
  `S`) that reads a trace record against another row's structural inputs, which no allowed source
  separates.  The induction only ever consumes the positional pairs: every child
  `Inp` is built by `PR.child` at the child's own index (`pr_child`).
-/
import Nock.RedTeam.Batch1090Thm54C2ReadyFuel
import Nock.RedTeam.Batch1091Thm54C2Alignment
import Nock.RedTeam.Batch1023Thm54S3PairMismatch
import Nock.RedTeam.Batch758Thm54HbindComputeCancel
import Nock.NockVMROM.Thm54.P8Core.Batch1171Thm54C2InductionPositional

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1171

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1021
open Nock.RedTeam.Batch1090
open Nock.RedTeam.Batch1091
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding

variable {K : Type} [Field K] [DecidableEq K] [Fintype K] [CharP K (ringChar K)]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}

set_option quotPrecheck false

local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-! ## §A  The per-node interface -/

/-! ## §B  Small facts -/

/-! ## §C  The generic first step at every node: the formula is a cell whose tail is bound to
`f_t` and whose head is bound to `f_h` -/

section Generic

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

end Generic

/-! ## §D  Head shape, tail bindings, kid helpers -/

section Helpers

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

end Helpers

/-! ## §E  The leaves: OP0 and OP1 -/

section Leaves

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

theorem natCast_inj_of_lt' (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0) {x y : ℕ}
    (hx : x < q) (hy : y < q) (h : (x : K) = (y : K)) : x = y :=
  C.hcast (Set.mem_Iio.2 hx) (Set.mem_Iio.2 hy) h

end Leaves

/-! ## §F  Internal nodes with structural children: OP3, OP4, cons -/

section Internal1

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

/-- The `i`-th positional child link, unpacked. -/
theorem link_at (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} (hu : InTree t u) (k : Fin 3)
    {c : NTree ((State × DTcomp K) × ℕ)} (hc : u.children[(k : ℕ)]? = some c) :
    (c.label.1.2.2.1.s, c.label.1.2.2.1.f, c.label.1.2.2.1.e) = sfTriple u.label.1.2.2.1 k :=
  (C.row u hu).link k c hc

end Internal1

/-! ## §G  Internal nodes with two records: OP5, OP2, OP7, OP8 -/

section Internal2

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

end Internal2

/-! ## §H  OP6 and OP9, and the induction -/

section Internal3

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

end Internal3

/-! ## The computed-formula children in the built order against `evalOrder` -/

section Step1

/-! ### (1) KidInputs of the join's children, built order -/

theorem kidInputs_op2 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)) (subj b c : Noun) (h : row.1.1 = .s2) :
    KidInputs .s2 subj (.cell (.atom 2) (.cell b c))
      ((J (n + 1) (.node row [c0, c1, c2]) subj (.cell (.atom 2) (.cell b c))).children.map
        NTree.label) := by
  rw [J_s2 (sv := sv) (ax := ax) _ _ row c0 c1 c2 h]
  simp [KidInputs, NTree.children, J_subject, J_formula, nounHead, nounTail, hd_cell, tl_cell]

theorem kidInputs_op9 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ)) (subj fc : Noun) (a : ℕ) (h : row.1.1 = .s9)
    (hslot : Noun.slot a (J n c0 subj fc).label.evaluation =
      some (sv .verify_child (row.2 + 3))) :
    KidInputs .s9 subj (.cell (.atom 9) (.cell (.atom a) fc))
      ((J (n + 1) (.node row [c0, c1]) subj (.cell (.atom 9) (.cell (.atom a) fc))).children.map
        NTree.label) := by
  rw [J_s9 (sv := sv) (ax := ax) _ _ row c0 c1 h]
  simp [KidInputs, NTree.children, J_subject, J_formula, nounHead, nounTail, op9Axis, hslot, hd_cell, tl_cell]

theorem kidInputs_op7 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ)) (subj b c : Noun) (h : row.1.1 = .s7) :
    KidInputs .s7 subj (.cell (.atom 7) (.cell b c))
      ((J (n + 1) (.node row [c0, c1]) subj (.cell (.atom 7) (.cell b c))).children.map
        NTree.label) := by
  rw [J_s7 (sv := sv) (ax := ax) _ _ row c0 c1 h]
  simp [KidInputs, NTree.children, J_subject, J_formula, nounHead, nounTail, hd_cell, tl_cell]

theorem kidInputs_op6 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ)) (subj b c d : Noun) (h : row.1.1 = .s6) :
    KidInputs .s6 subj (.cell (.atom 6) (.cell b (.cell c d)))
      ((J (n + 1) (.node row [c0, c1]) subj (.cell (.atom 6) (.cell b (.cell c d)))).children.map
        NTree.label) := by
  rw [J_s6 (sv := sv) (ax := ax) _ _ row c0 c1 h]
  simp only [List.map_cons, List.map_nil, NTree.children, KidInputs]
  refine ⟨J_subject _ _ _ _, ?_, J_subject _ _ _ _, ?_⟩
  · rw [J_formula]; rfl
  · rw [J_formula]
    unfold condBit
    cases (J n c1 subj b).label.evaluation <;> rfl

/-! ### (2) evalOrder at the computed-formula rows -/

theorem evalOrder_s2 {α : Type*} (l : List α) : evalOrder .s2 l = l := by
  simp [evalOrder, airNeedsSwap]

theorem evalOrder_s9 {α : Type*} (l : List α) : evalOrder .s9 l = l := by
  simp [evalOrder, airNeedsSwap]

theorem evalOrder_s7 {α : Type*} (a b : α) : evalOrder .s7 [a, b] = [b, a] := by
  simp [evalOrder, airNeedsSwap, swapPair]

/-! ### (3) The third child / the arm is an honest call once the earlier siblings are genuine -/

/-- **OP2's third child.**  Built child 2 (`sf3`), subject child 0's evaluation, formula child 1's
evaluation, is at an honest call of `G` as soon as children 0 and 1 are genuine; its inputs are
inside the window. -/
theorem honestCall_op2_third {G : NTree (GenComputeRow K)} (n : ℕ)
    (row : (State × DTcomp K) × ℕ) (c0 c1 c2 : NTree ((State × DTcomp K) × ℕ))
    (subj b c : Noun) (h : row.1.1 = .s2)
    (hcall : HonestCall G subj (.cell (.atom 2) (.cell b c)))
    (g0 : GenuineSkel (J n c0 subj b)) (g1 : GenuineSkel (J n c1 subj c)) :
    HonestCall G (J n c0 subj b).label.evaluation (J n c1 subj c).label.evaluation ∧
      (J n c0 subj b).label.evaluation.leaves ≤ programLeafBound (airReorder G) ∧
      (J n c1 subj c).label.evaluation.leaves ≤ programLeafBound (airReorder G) := by
  have hin := kidInputs_op2 (sv := sv) (ax := ax) n row c0 c1 c2 subj b c h
  have hshape : FormulaShape .s2 (.cell (.atom 2) (.cell b c)) := ⟨b, c, rfl⟩
  have hkids : (J (n + 1) (.node row [c0, c1, c2]) subj (.cell (.atom 2) (.cell b c))).children =
      [J n c0 subj b, J n c1 subj c,
        J n c2 (J n c0 subj b).label.evaluation (J n c1 subj c).label.evaluation] := by
    rw [J_s2 (sv := sv) (ax := ax) _ _ row c0 c1 c2 h]; rfl
  rw [hkids] at hin
  have hk := honestCall_kid hcall hshape hin 2
    (J n c2 (J n c0 subj b).label.evaluation (J n c1 subj c).label.evaluation)
    (by simp [evalOrder_s2])
    (by
      intro j k' hj hk'
      rw [evalOrder_s2] at hk'
      rcases j with _ | _ | j
      · simp at hk'; subst hk'; exact g0
      · simp at hk'; subst hk'; exact g1
      · omega)
  rw [J_subject, J_formula] at hk
  exact ⟨hk, (honestCall_inputs_le hk).1, (honestCall_inputs_le hk).2⟩

/-- **OP9's arm.**  Built child 1 (`sf2`), subject the core's evaluation, formula the SERVED noun
`sv.verify_child (S+3)`, is at an honest call as soon as the core is genuine and the served noun is
the noun-level slot of the core (`ServedLookup` + `axis_sound_recognizer'`, item (ii)). -/
theorem honestCall_op9_arm {G : NTree (GenComputeRow K)} (n : ℕ)
    (row : (State × DTcomp K) × ℕ) (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (subj fc : Noun) (a : ℕ) (h : row.1.1 = .s9)
    (hcall : HonestCall G subj (.cell (.atom 9) (.cell (.atom a) fc)))
    (hslot : Noun.slot a (J n c0 subj fc).label.evaluation =
      some (sv .verify_child (row.2 + 3)))
    (g0 : GenuineSkel (J n c0 subj fc)) :
    HonestCall G (J n c0 subj fc).label.evaluation (sv .verify_child (row.2 + 3)) ∧
      (J n c0 subj fc).label.evaluation.leaves ≤ programLeafBound (airReorder G) ∧
      (sv .verify_child (row.2 + 3)).leaves ≤ programLeafBound (airReorder G) := by
  have hin := kidInputs_op9 (sv := sv) (ax := ax) n row c0 c1 subj fc a h hslot
  have hshape : FormulaShape .s9 (.cell (.atom 9) (.cell (.atom a) fc)) := ⟨a, fc, rfl⟩
  have hkids : (J (n + 1) (.node row [c0, c1]) subj
      (.cell (.atom 9) (.cell (.atom a) fc))).children =
      [J n c0 subj fc, J n c1 (J n c0 subj fc).label.evaluation (sv .verify_child (row.2 + 3))] := by
    rw [J_s9 (sv := sv) (ax := ax) _ _ row c0 c1 h]; rfl
  rw [hkids] at hin
  have hk := honestCall_kid hcall hshape hin 1
    (J n c1 (J n c0 subj fc).label.evaluation (sv .verify_child (row.2 + 3)))
    (by simp [evalOrder_s9])
    (by
      intro j k' hj hk'
      rw [evalOrder_s9] at hk'
      rcases j with _ | j
      · simp at hk'; subst hk'; exact g0
      · omega)
  rw [J_subject, J_formula] at hk
  exact ⟨hk, (honestCall_inputs_le hk).1, (honestCall_inputs_le hk).2⟩

/-- **OP7, the swapped row (control).**  Built child 0 (`sf1`, the continuation) comes SECOND in
`evalOrder`; it is an honest call once built child 1 (`sf2`, the helper) is genuine. -/
theorem honestCall_op7_cons {G : NTree (GenComputeRow K)} (n : ℕ)
    (row : (State × DTcomp K) × ℕ) (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (subj b c : Noun) (h : row.1.1 = .s7)
    (hcall : HonestCall G subj (.cell (.atom 7) (.cell b c)))
    (g1 : GenuineSkel (J n c1 subj b)) :
    HonestCall G (J n c1 subj b).label.evaluation c := by
  have hin := kidInputs_op7 (sv := sv) (ax := ax) n row c0 c1 subj b c h
  have hshape : FormulaShape .s7 (.cell (.atom 7) (.cell b c)) := ⟨b, c, rfl⟩
  have hkids : (J (n + 1) (.node row [c0, c1]) subj (.cell (.atom 7) (.cell b c))).children =
      [J n c0 (J n c1 subj b).label.evaluation c, J n c1 subj b] := by
    rw [J_s7 (sv := sv) (ax := ax) _ _ row c0 c1 h]; rfl
  rw [hkids] at hin
  have hk := honestCall_kid hcall hshape hin 1 (J n c0 (J n c1 subj b).label.evaluation c)
    (by simp [evalOrder_s7])
    (by
      intro j k' hj hk'
      rw [evalOrder_s7] at hk'
      rcases j with _ | j
      · simp at hk'; subst hk'; exact g1
      · omega)
  rw [J_subject, J_formula] at hk
  exact hk

/-- **The first child in evaluation order needs nothing** (OP2's children 0/1, OP9's core). -/
theorem honestCall_op9_core {G : NTree (GenComputeRow K)} (n : ℕ)
    (row : (State × DTcomp K) × ℕ) (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (subj fc : Noun) (a : ℕ) (h : row.1.1 = .s9)
    (hcall : HonestCall G subj (.cell (.atom 9) (.cell (.atom a) fc)))
    (hslot : Noun.slot a (J n c0 subj fc).label.evaluation =
      some (sv .verify_child (row.2 + 3))) :
    HonestCall G subj fc := by
  have hin := kidInputs_op9 (sv := sv) (ax := ax) n row c0 c1 subj fc a h hslot
  have hshape : FormulaShape .s9 (.cell (.atom 9) (.cell (.atom a) fc)) := ⟨a, fc, rfl⟩
  have hkids : (J (n + 1) (.node row [c0, c1]) subj
      (.cell (.atom 9) (.cell (.atom a) fc))).children =
      [J n c0 subj fc, J n c1 (J n c0 subj fc).label.evaluation (sv .verify_child (row.2 + 3))] := by
    rw [J_s9 (sv := sv) (ax := ax) _ _ row c0 c1 h]; rfl
  rw [hkids] at hin
  have hk := honestCall_kid hcall hshape hin 0 (J n c0 subj fc) (by simp [evalOrder_s9])
    (by intro j k' hj; omega)
  rw [J_subject, J_formula] at hk
  exact hk

end Step1


section Receipt

open Nock.Noun

/-- The honest guarded run IS bounded (subject `atom 0`, result `atom 1`), but a MISALIGNED served
value `atom 30` makes the C2 join output `atom 31`, unbounded at `q = 31`; and the tree is provably
not `C2Aligned`. -/
theorem op4_misaligned_under_bounded_run (row4 row0 : (State × DTcomp (ZMod 31)) × ℕ)
    (svq : MState → ℕ → Noun) (axq : ℕ → ℕ)
    (h4 : row4.1.1 = .s4) (h0 : row0.1.1 = .s0)
    (hserve : svq .verify_child (row0.2 + 2) = .atom 30) :
    evalGBy 31 2 (.atom 0) (.cell (.atom 4) (.cell (.atom 0) (.atom 1))) = some (.atom 1) ∧
    (c2JoinFuel (fun l : (State × DTcomp (ZMod 31)) × ℕ => l.1.1) (fun l => l.2) svq axq 2
        (.node row4 [.node row0 []]) (.atom 0) (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))).label.evaluation = .atom 31 ∧
    ¬ BoundedBy 31 (.atom 31) ∧
    ¬ C2Aligned (K := ZMod 31) (sv := svq) (ax := axq) (.node row4 [.node row0 []]) (.atom 0)
        (.cell (.atom 4) (.cell (.atom 0) (.atom 1))) := by
  refine ⟨by simp [evalGBy, lusGBy, slot], ?_, by simp, ?_⟩
  · simp [c2JoinFuel, c2SkeletonRow, c2Evaluation, h4, h0, kidSkel, hserve, nounTail]
  · intro hA
    cases hA with
    | op4 _ hC =>
      cases hC with
      | op0 _ hslot => rw [hserve] at hslot; simp [slot] at hslot

end Receipt

end Nock.RedTeam.Batch1171

#print axioms Nock.RedTeam.Batch1171.good_of_inp
#print axioms Nock.RedTeam.Batch1171.root_good
#print axioms Nock.RedTeam.Batch1171.honestCall_op2_third
#print axioms Nock.RedTeam.Batch1171.honestCall_op9_arm
#print axioms Nock.RedTeam.Batch1171.op4_misaligned_under_bounded_run
