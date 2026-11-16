/-
  Nock/NockVMROM/Thm54/P8Core/Batch1091Thm54C2Alignment.lean

  The
  remaining declarations stay in `Nock/RedTeam/Batch1091Thm54C2Alignment.lean`, which imports this module. This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`. -/
import Nock.NockVMROM.Thm54.P8Core.Batch1021Thm54C2JoinAssembly
import Nock.NockVMROM.Thm54.P8Core.ComputedWindow
import Nock.NockVMROM.Thm54.StrategyOfTracesEv

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1091

open Nock
open Nock.Noun
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1021
open Nock.FieldEmbedding
variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-- OP6's branch selector as the join computes it. -/
def c6b : Noun → ℕ
  | .atom k => k
  | _ => 0

/-- **Alignment shape**: the S-carrying tree's state at every node is the opcode of the formula
passed down (the indices), OP0 / OP9 serve the noun-level axis lookup, and the children are aligned
at the subjects / formulas the join passes. -/
inductive C2Aligned : NTree ((State × DTcomp K) × ℕ) → Noun → Noun → Prop
  | op0 {row : (State × DTcomp K) × ℕ} {subj : Noun} {a : ℕ}
      (hstate : row.1.1 = .s0)
      (hslot : slot a subj = some (sv .verify_child (row.2 + 2))) :
      C2Aligned (.node row []) subj (.cell (.atom 0) (.atom a))
  | op1 {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
      (hstate : row.1.1 = .s1) :
      C2Aligned (.node row []) subj (.cell (.atom 1) tail)
  | cons {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj b c d : Noun}
      (hstate : row.1.1 = .cons)
      (hL : C2Aligned c0 subj (.cell b c))
      (hR : C2Aligned c1 subj d) :
      C2Aligned (.node row [c0, c1]) subj (.cell (.cell b c) d)
  | op3 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)} {subj tail : Noun}
      (hstate : row.1.1 = .s3) (hC : C2Aligned c0 subj tail) :
      C2Aligned (.node row [c0]) subj (.cell (.atom 3) tail)
  | op4 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)} {subj tail : Noun}
      (hstate : row.1.1 = .s4) (hC : C2Aligned c0 subj tail) :
      C2Aligned (.node row [c0]) subj (.cell (.atom 4) tail)
  | op5 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc : Noun}
      (hstate : row.1.1 = .s5)
      (hL : C2Aligned c0 subj fb) (hR : C2Aligned c1 subj fc) :
      C2Aligned (.node row [c0, c1]) subj (.cell (.atom 5) (.cell fb fc))
  | op2 {row : (State × DTcomp K) × ℕ} {c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc : Noun}
      (hstate : row.1.1 = .s2)
      (h1 : C2Aligned c0 subj fb) (h2 : C2Aligned c1 subj fc)
      (h3 : C2Aligned c2 (J c0.size c0 subj fb).label.evaluation
        (J c1.size c1 subj fc).label.evaluation) :
      C2Aligned (.node row [c0, c1, c2]) subj (.cell (.atom 2) (.cell fb fc))
  | op6 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc fd : Noun}
      (hstate : row.1.1 = .s6)
      (hC : C2Aligned c1 subj fb)
      (hT : C2Aligned c0 subj
        (if c6b (J c1.size c1 subj fb).label.evaluation = 0 then fc else fd)) :
      C2Aligned (.node row [c0, c1]) subj (.cell (.atom 6) (.cell fb (.cell fc fd)))
  | op7 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc : Noun}
      (hstate : row.1.1 = .s7)
      (hHelp : C2Aligned c1 subj fb)
      (hCons : C2Aligned c0 (J c1.size c1 subj fb).label.evaluation fc) :
      C2Aligned (.node row [c0, c1]) subj (.cell (.atom 7) (.cell fb fc))
  | op8 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc : Noun}
      (hstate : row.1.1 = .s8)
      (hHelp : C2Aligned c1 subj fb)
      (hCons : C2Aligned c0 (.cell (J c1.size c1 subj fb).label.evaluation subj) fc) :
      C2Aligned (.node row [c0, c1]) subj (.cell (.atom 8) (.cell fb fc))
  | op9 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fc : Noun} {a : ℕ}
      (hstate : row.1.1 = .s9)
      (hCore : C2Aligned c0 subj fc)
      (hslot : slot a (J c0.size c0 subj fc).label.evaluation =
        some (sv .verify_child (row.2 + 3)))
      (hInv : C2Aligned c1 (J c0.size c0 subj fc).label.evaluation
        (sv .verify_child (row.2 + 3))) :
      C2Aligned (.node row [c0, c1]) subj (.cell (.atom 9) (.cell (.atom a) fc))

@[simp] theorem c2SkeletonRow_evaluation (sv' : MState → ℕ → Noun) (ax' : ℕ → ℕ) (st : State)
    (S : ℕ) (subj f : Noun) (kids : List ComputeRowSkeleton) :
    (c2SkeletonRow sv' ax' st S subj f kids).evaluation = c2Evaluation sv' st S f kids := rfl

@[simp] theorem label_node' {α : Type*} (a : α) (l : List (NTree α)) : (NTree.node a l).label = a := rfl

theorem size_node1 (row : (State × DTcomp K) × ℕ) (c0 : NTree ((State × DTcomp K) × ℕ)) :
    (NTree.node row [c0]).size = 1 + c0.size := by
  simp [NTree.size]

theorem size_node2 (row : (State × DTcomp K) × ℕ) (c0 c1 : NTree ((State × DTcomp K) × ℕ)) :
    (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
  simp [NTree.size]; omega

theorem size_node3 (row : (State × DTcomp K) × ℕ) (c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)) :
    (NTree.node row [c0, c1, c2]).size = 1 + c0.size + c1.size + c2.size := by
  simp [NTree.size]; omega

/-- **The alignment theorem.**  On an aligned tree, every successful honest guarded run of
`(subj, formula)` is the C2 join's evaluation, at every fuel at or above the tree size. -/
theorem c2_aligned_eval (q : ℕ) {t : NTree ((State × DTcomp K) × ℕ)} {subj f : Noun}
    (hA : C2Aligned (sv := sv) (ax := ax) t subj f) :
    ∀ (fuel n : ℕ) (r : Noun), evalGBy q fuel subj f = some r → t.size ≤ n →
      (J n t subj f).label.evaluation = r := by
  induction hA with
  | @op0 row subj a hstate hslot =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [NTree.size] at hn; omega⟩
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rw [J_s0 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation]
      rw [hslot] at hG
      exact Option.some.inj hG
  | @op1 row subj tail hstate =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [NTree.size] at hn; omega⟩
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rw [J_s1 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, nounTail]
      exact Option.some.inj hG
  | @cons row c0 c1 subj b c d hstate hL hR ihL ihR =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hl : evalGBy q fu subj (.cell b c) with _ | l <;>
        rcases hr : evalGBy q fu subj d with _ | r' <;> simp [hl, hr] at hG
      rw [J_cons (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounHead, nounTail,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [ihL fu m l hl hm0, ihR fu m r' hr hm1, hG]
  | @op3 row c0 subj tail hstate hC ih =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node1] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node1] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases h0 : evalGBy q fu subj tail with _ | r0 <;> simp [h0] at hG
      rw [J_s3 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounTail,
        List.getElem?_cons_zero, Option.getD_some]
      rw [ih fu m r0 h0 hm0, hG]
  | @op4 row c0 subj tail hstate hC ih =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node1] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node1] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases h0 : evalGBy q fu subj tail with _ | r0 <;> simp [h0] at hG
      rw [J_s4 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounTail,
        List.getElem?_cons_zero, Option.getD_some]
      rw [ih fu m r0 h0 hm0]
      cases r0 with
      | atom k =>
          simp only [lusGBy] at hG
          split_ifs at hG with hk
          exact Option.some.inj hG
      | cell _ _ => simp [lusGBy] at hG
  | @op5 row c0 c1 subj fb fc hstate hL hR ihL ihR =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hl : evalGBy q fu subj fb with _ | l <;>
        rcases hr : evalGBy q fu subj fc with _ | r' <;> simp [hl, hr] at hG
      rw [J_s5 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounHead, nounTail,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [ihL fu m l hl hm0, ihR fu m r' hr hm1, hG]
  | @op2 row c0 c1 c2 subj fb fc hstate h1 h2 h3 ih1 ih2 ih3 =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node3] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node3] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node3] at hn; omega
      have hm2 : c2.size ≤ m := by rw [size_node3] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hl : evalGBy q fu subj fb with _ | sb <;>
        rcases hr : evalGBy q fu subj fc with _ | sc <;> simp [hl, hr] at hG
      have e0 : (J c0.size c0 subj fb).label.evaluation = sb := ih1 fu _ sb hl le_rfl
      have e1 : (J c1.size c1 subj fc).label.evaluation = sc := ih2 fu _ sc hr le_rfl
      have e0m : (J m c0 subj fb).label.evaluation = sb := ih1 fu m sb hl hm0
      have e1m : (J m c1 subj fc).label.evaluation = sc := ih2 fu m sc hr hm1
      have h3' := ih3 fu m r (by rw [e0, e1]; exact hG) hm2
      rw [J_s2 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounHead, nounTail,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [e0m, e1m]
      rw [e0, e1] at h3'
      exact h3'
  | @op6 row c0 c1 subj fb fc fd hstate hC hT ihC ihT =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hc : evalGBy q fu subj fb with _ | rc
      · simp [hc] at hG
      have ec : (J c1.size c1 subj fb).label.evaluation = rc := ihC fu _ rc hc le_rfl
      have ecm : (J m c1 subj fb).label.evaluation = rc := ihC fu m rc hc hm1
      rw [J_s6 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounHead, nounTail,
        List.getElem?_cons_zero, Option.getD_some]
      simp only [ecm]
      rw [ec] at ihT
      rcases rc with k | _
      · rw [hc] at hG
        rcases k with _ | _ | k
        · simp at hG
          exact ihT fu m r (by simpa [c6b] using hG) hm0
        · simp at hG
          exact ihT fu m r (by simpa [c6b] using hG) hm0
        · simp at hG
      · simp [hc] at hG
  | @op7 row c0 c1 subj fb fc hstate hHelp hCons ihHelp ihCons =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hb : evalGBy q fu subj fb with _ | sb <;> simp [hb] at hG
      have eb : (J c1.size c1 subj fb).label.evaluation = sb := ihHelp fu _ sb hb le_rfl
      have ebm : (J m c1 subj fb).label.evaluation = sb := ihHelp fu m sb hb hm1
      rw [eb] at ihCons
      rw [J_s7 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounHead, nounTail,
        List.getElem?_cons_zero, Option.getD_some]
      rw [ebm]
      exact ihCons fu m r hG hm0
  | @op8 row c0 c1 subj fb fc hstate hHelp hCons ihHelp ihCons =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hb : evalGBy q fu subj fb with _ | sb <;> simp [hb] at hG
      have eb : (J c1.size c1 subj fb).label.evaluation = sb := ihHelp fu _ sb hb le_rfl
      have ebm : (J m c1 subj fb).label.evaluation = sb := ihHelp fu m sb hb hm1
      rw [eb] at ihCons
      rw [J_s8 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounHead, nounTail,
        List.getElem?_cons_zero, Option.getD_some]
      rw [ebm]
      exact ihCons fu m r hG hm0
  | @op9 row c0 c1 subj fc a hstate hCore hslot hInv ihCore ihInv =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hcore : evalGBy q fu subj fc with _ | core <;> simp [hcore] at hG
      have ec : (J c0.size c0 subj fc).label.evaluation = core := ihCore fu _ core hcore le_rfl
      have ecm : (J m c0 subj fc).label.evaluation = core := ihCore fu m core hcore hm0
      rw [ec] at hslot ihInv
      rw [hslot] at hG
      simp only at hG
      rw [J_s9 (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, kidSkel, nounTail,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [ecm]
      exact ihInv fu m r hG hm1

theorem evalGBy_bounded {q : ℕ} (hq : 1 < q) {fuel : ℕ} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (h : evalGBy q fuel s f = some r) : BoundedBy q r :=
  (agreeBy q hq fuel s f r hs hf h).2.2

section Genuine

open Nock.NockVMROM.Thm54.ComputedWindow

@[simp] theorem c2SkeletonRow_state' (sv' : MState → ℕ → Noun) (ax' : ℕ → ℕ) (st : State) (S : ℕ)
    (subj f : Noun) (kids : List ComputeRowSkeleton) :
    (c2SkeletonRow sv' ax' st S subj f kids).state = st := rfl

@[simp] theorem c2SkeletonRow_subject' (sv' : MState → ℕ → Noun) (ax' : ℕ → ℕ) (st : State) (S : ℕ)
    (subj f : Noun) (kids : List ComputeRowSkeleton) :
    (c2SkeletonRow sv' ax' st S subj f kids).subject = subj := rfl

@[simp] theorem c2SkeletonRow_formula' (sv' : MState → ℕ → Noun) (ax' : ℕ → ℕ) (st : State) (S : ℕ)
    (subj f : Noun) (kids : List ComputeRowSkeleton) :
    (c2SkeletonRow sv' ax' st S subj f kids).formula = f := rfl

@[simp] theorem J_subject' (fuel : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) :
    (J fuel t s f).label.subject = s := J_subject fuel t s f

@[simp] theorem J_formula' (fuel : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) :
    (J fuel t s f).label.formula = f := J_formula fuel t s f

/-- **The aligned C2 join is genuine** (every row obeys its Nock step, `ComputedWindow`), given
one successful guarded honest run of the root. -/
theorem c2_aligned_genuine (q : ℕ) {t : NTree ((State × DTcomp K) × ℕ)} {subj f : Noun}
    (hA : C2Aligned (sv := sv) (ax := ax) t subj f) :
    ∀ (fuel n : ℕ) (r : Noun), evalGBy q fuel subj f = some r → t.size ≤ n →
      GenuineSkel (J n t subj f) := by
  induction hA with
  | @op0 row subj a hstate hslot =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [NTree.size] at hn; omega⟩
      rw [J_s0 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ (by simp)
      · exact ⟨a, rfl⟩
      · simp [KidInputs]
      · simp [RowOutput, c2Evaluation, op0Axis, hslot]
  | @op1 row subj tail hstate =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [NTree.size] at hn; omega⟩
      rw [J_s1 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ (by simp)
      · exact ⟨tail, rfl⟩
      · simp [KidInputs]
      · simp [RowOutput, c2Evaluation, nounTail, tl, StrategyOfTraces.nounTail]
  | @cons row c0 c1 subj b c d hstate hL hR ihL ihR =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hl : evalGBy q fu subj (.cell b c) with _ | l <;>
        rcases hr : evalGBy q fu subj d with _ | r' <;> simp [hl, hr] at hG
      rw [J_cons (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨b, c, d, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail]
      · simp [RowOutput, c2Evaluation, kidSkel, nounHead, nounTail]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl)
        · exact ihL fu m l hl hm0
        · exact ihR fu m r' hr hm1
  | @op3 row c0 subj tail hstate hC ih =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node1] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node1] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases h0 : evalGBy q fu subj tail with _ | r0 <;> simp [h0] at hG
      rw [J_s3 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨tail, rfl⟩
      · simp [KidInputs, nounTail, tl, StrategyOfTraces.nounTail]
      · simp [RowOutput, c2Evaluation, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k rfl
        exact ih fu m r0 h0 hm0
  | @op4 row c0 subj tail hstate hC ih =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node1] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node1] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases h0 : evalGBy q fu subj tail with _ | r0 <;> simp [h0] at hG
      have e0 := c2_aligned_eval (sv := sv) (ax := ax) q hC fu m r0 h0 hm0
      rw [J_s4 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨tail, rfl⟩
      · simp [KidInputs, nounTail, tl, StrategyOfTraces.nounTail]
      · simp only [label_node', List.map_cons, List.map_nil, RowOutput, c2SkeletonRow_state',
          c2SkeletonRow_evaluation, c2Evaluation, kidSkel, List.getElem?_cons_zero, Option.getD_some]
        simp only [nounTail]
        rw [e0]
        cases r0 with
        | atom k => simp [Noun.lus]
        | cell _ _ => simp [lusGBy] at hG
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k rfl
        exact ih fu m r0 h0 hm0
  | @op5 row c0 c1 subj fb fc hstate hL hR ihL ihR =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hl : evalGBy q fu subj fb with _ | l <;>
        rcases hr : evalGBy q fu subj fc with _ | r' <;> simp [hl, hr] at hG
      rw [J_s5 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail]
      · simp [RowOutput, c2Evaluation, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl)
        · exact ihL fu m l hl hm0
        · exact ihR fu m r' hr hm1
  | @op2 row c0 c1 c2 subj fb fc hstate h1 h2 h3 ih1 ih2 ih3 =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node3] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node3] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node3] at hn; omega
      have hm2 : c2.size ≤ m := by rw [size_node3] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hl : evalGBy q fu subj fb with _ | sb <;>
        rcases hr : evalGBy q fu subj fc with _ | sc <;> simp [hl, hr] at hG
      have e0 := c2_aligned_eval (sv := sv) (ax := ax) q h1 fu _ sb hl le_rfl
      have e1 := c2_aligned_eval (sv := sv) (ax := ax) q h2 fu _ sc hr le_rfl
      have e0m := c2_aligned_eval (sv := sv) (ax := ax) q h1 fu m sb hl hm0
      have e1m := c2_aligned_eval (sv := sv) (ax := ax) q h2 fu m sc hr hm1
      rw [J_s2 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail]
      · simp [RowOutput, c2Evaluation, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, nounHead, nounTail]
        rintro k (rfl | rfl | rfl)
        · exact ih1 fu m sb hl hm0
        · exact ih2 fu m sc hr hm1
        · rw [e0m, e1m]
          have := ih3 fu m r (by rw [e0, e1]; exact hG) hm2
          rwa [e0, e1] at this
  | @op6 row c0 c1 subj fb fc fd hstate hC hT ihC ihT =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hc : evalGBy q fu subj fb with _ | rc
      · simp [hc] at hG
      have ec := c2_aligned_eval (sv := sv) (ax := ax) q hC fu _ rc hc le_rfl
      have ecm := c2_aligned_eval (sv := sv) (ax := ax) q hC fu m rc hc hm1
      rw [ec] at ihT
      rw [hc] at hG
      have hbit : rc = .atom 0 ∨ rc = .atom 1 := by
        rcases rc with k | _
        · rcases k with _ | _ | k
          · exact Or.inl rfl
          · exact Or.inr rfl
          · simp at hG
        · simp at hG
      rw [J_s6 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, fd, rfl⟩
      · simp only [nounHead, nounTail] at ecm ⊢
        simp [KidInputs, hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, ecm, condBit]
        rcases hbit with rfl | rfl <;> simp
      · simp only [nounHead, nounTail] at ecm ⊢
        simp [RowOutput, c2Evaluation, kidSkel, ecm]
        exact hbit
      · simp only [List.mem_cons, List.not_mem_nil, or_false, nounHead, nounTail]
        rintro k (rfl | rfl)
        · simp only [ecm]
          rcases hbit with rfl | rfl
          · simp at hG
            exact ihT fu m r (by simpa [c6b] using hG) hm0
          · simp at hG
            exact ihT fu m r (by simpa [c6b] using hG) hm0
        · exact ihC fu m rc hc hm1
  | @op7 row c0 c1 subj fb fc hstate hHelp hCons ihHelp ihCons =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hb : evalGBy q fu subj fb with _ | sb <;> simp [hb] at hG
      have eb := c2_aligned_eval (sv := sv) (ax := ax) q hHelp fu _ sb hb le_rfl
      have ebm := c2_aligned_eval (sv := sv) (ax := ax) q hHelp fu m sb hb hm1
      rw [eb] at ihCons
      rw [J_s7 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail]
      · simp [RowOutput, c2Evaluation, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, nounHead, nounTail]
        rintro k (rfl | rfl)
        · rw [ebm]; exact ihCons fu m r hG hm0
        · exact ihHelp fu m sb hb hm1
  | @op8 row c0 c1 subj fb fc hstate hHelp hCons ihHelp ihCons =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hb : evalGBy q fu subj fb with _ | sb <;> simp [hb] at hG
      have eb := c2_aligned_eval (sv := sv) (ax := ax) q hHelp fu _ sb hb le_rfl
      have ebm := c2_aligned_eval (sv := sv) (ax := ax) q hHelp fu m sb hb hm1
      rw [eb] at ihCons
      rw [J_s8 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail]
      · simp [RowOutput, c2Evaluation, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, nounHead, nounTail]
        rintro k (rfl | rfl)
        · rw [ebm]; exact ihCons fu m r hG hm0
        · exact ihHelp fu m sb hb hm1
  | @op9 row c0 c1 subj fc a hstate hCore hslot hInv ihCore ihInv =>
      intro fuel n r hG hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      simp only [evalGBy] at hG
      rcases hcore : evalGBy q fu subj fc with _ | core <;> simp [hcore] at hG
      have ec := c2_aligned_eval (sv := sv) (ax := ax) q hCore fu _ core hcore le_rfl
      have ecm := c2_aligned_eval (sv := sv) (ax := ax) q hCore fu m core hcore hm0
      rw [ec] at hslot ihInv
      rw [hslot] at hG
      simp only at hG
      rw [J_s9 (hstate := hstate)]
      refine GenuineSkel.node ?_ ?_ ?_ ?_
      · exact ⟨a, fc, rfl⟩
      · simp only [nounTail] at ecm ⊢
        simp [KidInputs, tl, StrategyOfTraces.nounTail, ecm, op9Axis, hslot]
      · simp [RowOutput, c2Evaluation, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, nounTail]
        rintro k (rfl | rfl)
        · exact ihCore fu m core hcore hm0
        · rw [ecm]; exact ihInv fu m r hG hm1

end Genuine

section Census

open Nock.NockVMROM.Thm54.ComputedWindow

@[simp] theorem leaves_wut (n : Noun) : (Noun.wut n).leaves = 1 := by cases n <;> rfl

@[simp] theorem leaves_tis (a b : Noun) : (Noun.tis a b).leaves = 1 := by
  unfold Noun.tis; split <;> rfl

@[simp] theorem leaves_incMod (q : ℕ) (n : Noun) : (OpcodeSemantics.incMod q n).leaves = 1 := by
  cases n <;> rfl

/-- **Every comparison pair of a genuine C2 row is within `Λ`** once the row's and its kids' row
nouns are (`RowNounsLe`, from `ComputedWindow.genuine_rows_le_programLeafBound`). -/
theorem c2Row_pairs_le {Λ : ℕ} (hΛ : 1 ≤ Λ) {st : State} {S : ℕ} {s f : Noun}
    {kids : List ComputeRowSkeleton}
    (hshape : FormulaShape st f) (hin : KidInputs st s f kids)
    (hu : RowNounsLe Λ (c2SkeletonRow sv ax st S s f kids))
    (hk : ∀ k ∈ kids, RowNounsLe Λ k) :
    ∀ cu ∈ P8Census.skeletonComparisons (K := K) (c2SkeletonRow sv ax st S s f kids),
      cu.left.leaves ≤ Λ ∧ cu.right.leaves ≤ Λ := by
  intro cu hc
  cases st with
  | s0 =>
      obtain ⟨a, rfl⟩ := hshape
      simp only [KidInputs] at hin; subst hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | s1 =>
      obtain ⟨t, rfl⟩ := hshape
      simp only [KidInputs] at hin; subst hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | s2 =>
      obtain ⟨b, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, _⟩⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | s3 =>
      obtain ⟨t, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | s4 =>
      obtain ⟨t, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | s5 =>
      obtain ⟨b, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | s6 =>
      obtain ⟨b, c, d, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | s7 =>
      obtain ⟨b, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | s8 =>
      obtain ⟨b, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail, hin.2.2.1] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail, hin.2.2.1] <;> omega)
  | s9 =>
      obtain ⟨a, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)
  | cons =>
      obtain ⟨b, c, d, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRow, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRow, c2Evaluation, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2Evaluation, kidSkel, nounHead, nounTail] <;> omega)

end Census

section CensusTree

open Nock.NockVMROM.Thm54.ComputedWindow

theorem genuine_root {T : NTree ComputeRowSkeleton} (hT : GenuineSkel T) :
    FormulaShape T.label.state T.label.formula ∧
      KidInputs T.label.state T.label.subject T.label.formula (T.children.map NTree.label) := by
  cases hT with
  | node shape inputs _ _ => exact ⟨shape, inputs⟩

theorem genuine_sub {T u : NTree ComputeRowSkeleton} (hT : GenuineSkel T) (hu : InTree T u) :
    GenuineSkel u := by
  induction hu with
  | here => exact hT
  | sub hs _ ih =>
      cases hT with
      | node _ _ _ children => exact ih (children _ hs)

/-- Every node of the C2 join is a C2 row over its own children. -/
theorem J_isJ : ∀ (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun),
    ∃ (st : State) (S : ℕ), (J n t s f).label =
        c2SkeletonRow sv ax st S s f ((J n t s f).children.map NTree.label) ∧
      ∀ k ∈ (J n t s f).children, ∃ m t' s' f', k = J m t' s' f' := by
  intro n t s f
  cases n with
  | zero =>
      cases t with
      | node row ch => exact ⟨row.1.1, row.2, rfl, by simp [c2JoinFuel]⟩
  | succ n =>
      cases t with
      | node row ch =>
          refine ⟨row.1.1, row.2, rfl, ?_⟩
          simp only [c2JoinFuel, c2JoinKids, NTree.children_node]
          split <;> intro k hk <;>
            simp only [List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hk <;>
            first
            | exact hk.elim
            | (obtain ⟨c, -, h⟩ := hk; exact ⟨_, _, _, _, h.symm⟩)
            | (rcases hk with h | h | h <;> exact ⟨_, _, _, _, h⟩)
            | (rcases hk with h | h <;> exact ⟨_, _, _, _, h⟩)
            | exact ⟨_, _, _, _, hk⟩

theorem J_nodes {T : NTree ComputeRowSkeleton} (hT : ∃ m t' s' f', T = J m t' s' f')
    {u : NTree ComputeRowSkeleton} (hu : InTree T u) :
    ∃ m t' s' f', u = J m t' s' f' := by
  induction hu with
  | here => exact hT
  | sub hs _ ih =>
      obtain ⟨m, t', s', f', rfl⟩ := hT
      obtain ⟨_, _, _, hk⟩ := J_isJ (sv := sv) (ax := ax) m t' s' f'
      exact ih (hk _ hs)

/-- A C2 row's subformula field is a kid noun or `atom 0`. -/
theorem sf_le {Λ : ℕ} (hΛ : 1 ≤ Λ) {st : State} {S : ℕ} {s f : Noun}
    {kids : List ComputeRowSkeleton} (hk : ∀ k ∈ kids, RowNounsLe Λ k) (i : Fin 3)
    (slot : TripleSlot) :
    (P8Census.skeletonSubformula (c2SkeletonRow sv ax st S s f kids) i slot).leaves ≤ Λ := by
  unfold P8Census.skeletonSubformula
  split
  · simp only [c2SkeletonRow]
    split
    · rename_i h
      have hb := hk _ (List.getElem_mem h)
      cases slot <;> simp [hb.1, hb.2.1, hb.2.2]
    · simpa [Noun.leaves] using hΛ
  · simpa [Noun.leaves] using hΛ

/-- **The tree-level window**: on a genuine C2 join whose rows are within `Λ`, every combined
census pair and every size-window noun is within `Λ`. -/
theorem c2_tree_census {Λ : ℕ} (hΛ : 1 ≤ Λ) (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ))
    (subj f : Noun) (mf : List (NTree MemoryRowSkeleton))
    (hgen : GenuineSkel (J n t subj f))
    (hrows : ∀ u, InTree (J n t subj f) u → RowNounsLe Λ u.label) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
        { computeTree := J n t subj f, memoryForest := mf } Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        { computeTree := J n t subj f, memoryForest := mf } Λ := by
  -- per-node facts
  have hnode : ∀ u, InTree (J n t subj f) u →
      ∃ (st : State) (S : ℕ) (s' f' : Noun), u.label =
          c2SkeletonRow sv ax st S s' f' (u.children.map NTree.label) ∧
        FormulaShape st f' ∧ KidInputs st s' f' (u.children.map NTree.label) ∧
        RowNounsLe Λ u.label ∧ ∀ k ∈ u.children.map NTree.label, RowNounsLe Λ k := by
    intro u hu
    obtain ⟨m, t', s', f', rfl⟩ := J_nodes (sv := sv) (ax := ax) ⟨n, t, subj, f, rfl⟩ hu
    obtain ⟨st, S, hlab, -⟩ := J_isJ (sv := sv) (ax := ax) m t' s' f'
    have hg := genuine_sub hgen hu
    obtain ⟨hsh, hin⟩ := genuine_root hg
    rw [hlab] at hsh hin
    refine ⟨st, S, s', f', hlab, by simpa using hsh, by simpa using hin, hrows _ hu, ?_⟩
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hk
      exact hrows _ (InTree_trans hu (InTree.sub hc (InTree.here _)))
  have hmemRows : ∀ r ∈ computeSkeletonRows { computeTree := J n t subj f, memoryForest := mf },
      ∃ u, InTree (J n t subj f) u ∧ r = u.label := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).1 hu
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨u, hin, rfl⟩
  refine ⟨⟨⟨?_⟩, ⟨?_⟩⟩, ?_⟩
  · -- the local pair list
    intro pair hp
    simp only [BoundSemanticTrace.skeletonPairs, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    have hroot := hrows _ (InTree.here _)
    rcases hp with (rfl | rfl | rfl) | hp
    · exact ⟨hroot.1, hroot.1⟩
    · exact ⟨hroot.2.1, hroot.2.1⟩
    · exact ⟨hroot.2.2, hroot.2.2⟩
    · obtain ⟨cu, hcu, rfl⟩ := List.mem_map.1 hp
      obtain ⟨r, hr, hcu⟩ := List.mem_flatMap.1 hcu
      obtain ⟨u, hu, rfl⟩ := hmemRows r hr
      obtain ⟨st, S, s', f', hlab, hsh, hin, hu', hk⟩ := hnode u hu
      rw [hlab] at hcu hu'
      exact c2Row_pairs_le hΛ hsh hin hu' hk cu hcu
  · -- the edge pairs
    intro pair hp
    obtain ⟨u, hu, hp⟩ := List.mem_flatMap.1 hp
    have hin := (mem_bfsForest _ _).1 hu
    obtain ⟨c, hc, hin⟩ := hin
    simp only [List.mem_singleton] at hc
    subst hc
    obtain ⟨st, S, s', f', hlab, -, -, -, hk⟩ := hnode u hin
    simp only [EdgeComparisonCensus.rowEdgePairs, List.mem_flatMap, List.mem_ofFn, id] at hp
    obtain ⟨l, ⟨i, rfl⟩, hpl⟩ := hp
    split at hpl
    · simp at hpl
    · rename_i child hch
      have hchild : child ∈ u.children := List.mem_of_getElem? hch
      have hcb := hrows _ (InTree_trans hin (InTree.sub hchild (InTree.here _)))
      simp only [EdgeComparisonCensus.edgeTriple, List.mem_cons, List.not_mem_nil,
        or_false] at hpl
      rw [hlab] at hpl
      rcases hpl with rfl | rfl | rfl
      · exact ⟨hcb.1, sf_le hΛ hk i .subject⟩
      · exact ⟨hcb.2.1, sf_le hΛ hk i .formula⟩
      · exact ⟨hcb.2.2, sf_le hΛ hk i .result⟩
  · -- the size-window nouns
    intro x hx
    obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨u, hu, rfl⟩ := hmemRows r hr
    obtain ⟨st, S, s', f', hlab, -, -, -, hk⟩ := hnode u hu
    rw [hlab] at hx
    unfold SizeWindowCounting.requiredSizeWindowNouns at hx
    split at hx <;> simp only [List.mem_singleton, List.not_mem_nil] at hx
    all_goals (first | exact hx.elim | (subst hx; exact sf_le hΛ hk _ _))

/-- **(a) and (b) at any skeleton carrying an aligned C2 join**, from the
alignment, one successful honest guarded run, the honest generator run of the same claim, and the
package window `programLeafBound ≤ Λ`. -/
theorem c2_aligned_census_window {Λ q : ℕ} (hΛ1 : 1 ≤ Λ) {t : NTree ((State × DTcomp K) × ℕ)}
    {subj f : Noun} (hA : C2Aligned (sv := sv) (ax := ax) t subj f)
    {fuel : ℕ} {r : Noun} (hG : evalGBy q fuel subj f = some r)
    {gfuel : ℕ} {G : NTree (TraceGen.GenComputeRow K)} {R : Noun}
    (hgen : TraceGen.genComputeSkeleton (K := K) gfuel subj f = .ok (G, R))
    (hΛ : TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ)
    (S : SemanticSkeleton) (hS : S.computeTree = J t.size t subj f) :
    EdgeComparisonCensus.CombinedSkeletonCensus K S Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy S Λ := by
  have hg := c2_aligned_genuine (sv := sv) (ax := ax) q hA fuel t.size r hG le_rfl
  obtain ⟨-, -, hrows⟩ := genuine_rows_le_programLeafBound hgen hg (J_subject _ _ _ _)
    (J_formula _ _ _ _)
  have hrows' : ∀ u, InTree (J t.size t subj f) u → RowNounsLe Λ u.label := by
    intro u hu
    obtain ⟨a, b, c⟩ := hrows u hu
    exact ⟨a.trans hΛ, b.trans hΛ, c.trans hΛ⟩
  have h := c2_tree_census (sv := sv) (ax := ax) hΛ1 t.size t subj f S.memoryForest hg hrows'
  cases S with
  | mk ct mf =>
      simp only at hS
      subst hS
      exact h

end CensusTree

end Nock.RedTeam.Batch1091
