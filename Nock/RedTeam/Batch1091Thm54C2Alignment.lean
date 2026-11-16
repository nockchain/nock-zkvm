/-
  Nock/RedTeam/Batch1091Thm54C2Alignment.lean

* `C2Aligned` — the tree's state is the opcode head of the formula passed down (the indices),
    OP0 / OP9 serve the noun-level axis lookup (`slot a subj`, `slot a core`), children aligned at
    the join's subjects / formulas.
  * `c2_aligned_eval` — on an aligned tree every successful `evalGBy q` run of `(subj, f)` IS the
    join's evaluation, at every fuel at or above the tree size.
  * `c2_aligned_bounded` — every node's subject / formula / evaluation is `BoundedBy q` (the compute
    core of `hbound`), from one successful guarded run and bounded root inputs.

  * `op4_overflow_unbounded` — why alignment is load-bearing: at `q = 31` the C2 join's OP4 arm
    gives `atom 31` on a served `atom 30` (not `BoundedBy 31`), the field evaluator gives `atom 0`,
    and `enc z (atom 31) = enc z (atom 0)` at every seed, so no pair event separates them.

  -- the paper
-/
import Nock.RedTeam.Batch1021Thm54C2JoinAssembly
import Nock.NockVMROM.Thm54.ComputedWindow
import Nock.NockVMROM.Thm54.StrategyOfTracesEv
import Nock.NockVMROM.Thm54.P8Core.Batch1091Thm54C2Alignment

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

/-! ## `hbound`'s compute core: every node of an aligned join is `BoundedBy q` -/

def TriplesBounded (q : ℕ) (T : NTree ComputeRowSkeleton) : Prop :=
  ∀ node, InTree T node →
    BoundedBy q node.label.subject ∧ BoundedBy q node.label.formula ∧
      BoundedBy q node.label.evaluation

theorem tb_node {q : ℕ} {lab : ComputeRowSkeleton} {kids : List (NTree ComputeRowSkeleton)}
    (hroot : BoundedBy q lab.subject ∧ BoundedBy q lab.formula ∧ BoundedBy q lab.evaluation)
    (hk : ∀ k ∈ kids, TriplesBounded q k) : TriplesBounded q (.node lab kids) := by
  intro node hin
  cases hin with
  | here => exact hroot
  | sub hs h => exact hk _ hs _ h

/-- **Every node of the aligned C2 join is `BoundedBy q`** (subject, formula, evaluation): the
built skeleton's OP4 cannot overflow, because each node's evaluation IS a successful guarded
honest run (`c2_aligned_eval`).  Inputs: alignment, one successful `evalGBy q` run of the root
(§1's `hbound`, `RunBoundedBy`), bounded root subject / formula (§1's `hs`/`hf`). -/
theorem c2_aligned_bounded {q : ℕ} (hq : 1 < q) {t : NTree ((State × DTcomp K) × ℕ)}
    {subj f : Noun} (hA : C2Aligned (sv := sv) (ax := ax) t subj f) :
    ∀ (fuel n : ℕ) (r : Noun), evalGBy q fuel subj f = some r → t.size ≤ n →
      BoundedBy q subj → BoundedBy q f → TriplesBounded q (J n t subj f) := by
  induction hA with
  | @op0 row subj a hstate hslot =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op0 hstate hslot) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [NTree.size] at hn; omega⟩
      rw [J_s0 (hstate := hstate)] at hev ⊢
      exact tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ (by simp)
  | @op1 row subj tail hstate =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op1 (subj := subj) (tail := tail) hstate) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [NTree.size] at hn; omega⟩
      rw [J_s1 (hstate := hstate)] at hev ⊢
      exact tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ (by simp)
  | @cons row c0 c1 subj b c d hstate hL hR ihL ihR =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.cons hstate hL hR) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      rcases hl : evalGBy q fu subj (.cell b c) with _ | l <;>
        rcases hr' : evalGBy q fu subj d with _ | r' <;> simp [hl, hr'] at hG'
      rw [J_cons (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl)
      · exact ihL fu m l hl hm0 hs (by simpa [nounHead] using hf.1)
      · exact ihR fu m r' hr' hm1 hs (by simpa [nounTail] using hf.2)
  | @op3 row c0 subj tail hstate hC ih =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op3 hstate hC) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node1] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node1] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      rcases h0 : evalGBy q fu subj tail with _ | r0 <;> simp [h0] at hG'
      rw [J_s3 (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k rfl
      exact ih fu m r0 h0 hm0 hs (by simpa [nounTail] using hf.2)
  | @op4 row c0 subj tail hstate hC ih =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op4 hstate hC) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node1] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node1] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      rcases h0 : evalGBy q fu subj tail with _ | r0 <;> simp [h0] at hG'
      rw [J_s4 (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k rfl
      exact ih fu m r0 h0 hm0 hs (by simpa [nounTail] using hf.2)
  | @op5 row c0 c1 subj fb fc hstate hL hR ihL ihR =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op5 hstate hL hR) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      rcases hl : evalGBy q fu subj fb with _ | l <;>
        rcases hr' : evalGBy q fu subj fc with _ | r' <;> simp [hl, hr'] at hG'
      rw [J_s5 (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl)
      · exact ihL fu m l hl hm0 hs (by simpa [nounHead, nounTail] using hf.2.1)
      · exact ihR fu m r' hr' hm1 hs (by simpa [nounHead, nounTail] using hf.2.2)
  | @op2 row c0 c1 c2 subj fb fc hstate h1 h2 h3 ih1 ih2 ih3 =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op2 hstate h1 h2 h3) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node3] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node3] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node3] at hn; omega
      have hm2 : c2.size ≤ m := by rw [size_node3] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      rcases hl : evalGBy q fu subj fb with _ | sb <;>
        rcases hr' : evalGBy q fu subj fc with _ | sc <;> simp [hl, hr'] at hG'
      have hfb : BoundedBy q fb := by simpa using hf.2.1
      have hfc : BoundedBy q fc := by simpa using hf.2.2
      have e0 := c2_aligned_eval (sv := sv) (ax := ax) q h1 fu _ sb hl le_rfl
      have e1 := c2_aligned_eval (sv := sv) (ax := ax) q h2 fu _ sc hr' le_rfl
      have e0m := c2_aligned_eval (sv := sv) (ax := ax) q h1 fu m sb hl hm0
      have e1m := c2_aligned_eval (sv := sv) (ax := ax) q h2 fu m sc hr' hm1
      have hsb := evalGBy_bounded hq hs hfb hl
      have hsc := evalGBy_bounded hq hs hfc hr'
      rw [J_s2 (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl | rfl)
      · exact ih1 fu m sb hl hm0 hs (by simpa [nounHead, nounTail] using hfb)
      · exact ih2 fu m sc hr' hm1 hs (by simpa [nounHead, nounTail] using hfc)
      · simp only [nounHead, nounTail]
        rw [e0m, e1m]
        have := ih3 fu m r (by rw [e0, e1]; exact hG') hm2 (by rw [e0]; exact hsb) (by rw [e1]; exact hsc)
        rwa [e0, e1] at this
  | @op6 row c0 c1 subj fb fc fd hstate hC hT ihC ihT =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op6 hstate hC hT) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      have hfb : BoundedBy q fb := by simpa using hf.2.1
      have hfc : BoundedBy q fc := by simpa using hf.2.2.1
      have hfd : BoundedBy q fd := by simpa using hf.2.2.2
      rcases hc : evalGBy q fu subj fb with _ | rc
      · simp [hc] at hG'
      have ec := c2_aligned_eval (sv := sv) (ax := ax) q hC fu _ rc hc le_rfl
      have ecm := c2_aligned_eval (sv := sv) (ax := ax) q hC fu m rc hc hm1
      rw [J_s6 (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl)
      · simp only [nounHead, nounTail]
        simp only [ecm]
        rw [ec] at ihT
        rw [hc] at hG'
        rcases rc with k | _
        · rcases k with _ | _ | k
          · simp at hG'
            exact ihT fu m r (by simpa [c6b] using hG') hm0 hs (by simpa [c6b] using hfc)
          · simp at hG'
            exact ihT fu m r (by simpa [c6b] using hG') hm0 hs (by simpa [c6b] using hfd)
          · simp at hG'
        · simp at hG'
      · exact ihC fu m rc hc hm1 hs (by simpa [nounHead, nounTail] using hfb)
  | @op7 row c0 c1 subj fb fc hstate hHelp hCons ihHelp ihCons =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op7 hstate hHelp hCons) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      rcases hb : evalGBy q fu subj fb with _ | sb <;> simp [hb] at hG'
      have hfb : BoundedBy q fb := by simpa using hf.2.1
      have hfc : BoundedBy q fc := by simpa using hf.2.2
      have eb := c2_aligned_eval (sv := sv) (ax := ax) q hHelp fu _ sb hb le_rfl
      have ebm := c2_aligned_eval (sv := sv) (ax := ax) q hHelp fu m sb hb hm1
      have hsb := evalGBy_bounded hq hs hfb hb
      rw [J_s7 (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl)
      · simp only [nounHead, nounTail]
        rw [ebm]
        rw [eb] at ihCons
        exact ihCons fu m r hG' hm0 hsb hfc
      · exact ihHelp fu m sb hb hm1 hs (by simpa [nounHead, nounTail] using hfb)
  | @op8 row c0 c1 subj fb fc hstate hHelp hCons ihHelp ihCons =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op8 hstate hHelp hCons) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      rcases hb : evalGBy q fu subj fb with _ | sb <;> simp [hb] at hG'
      have hfb : BoundedBy q fb := by simpa using hf.2.1
      have hfc : BoundedBy q fc := by simpa using hf.2.2
      have eb := c2_aligned_eval (sv := sv) (ax := ax) q hHelp fu _ sb hb le_rfl
      have ebm := c2_aligned_eval (sv := sv) (ax := ax) q hHelp fu m sb hb hm1
      have hsb := evalGBy_bounded hq hs hfb hb
      rw [J_s8 (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl)
      · simp only [nounHead, nounTail]
        rw [ebm]
        rw [eb] at ihCons
        exact ihCons fu m r hG' hm0 ⟨hsb, hs⟩ hfc
      · exact ihHelp fu m sb hb hm1 hs (by simpa [nounHead, nounTail] using hfb)
  | @op9 row c0 c1 subj fc a hstate hCore hslot hInv ihCore ihInv =>
      intro fuel n r hG hn hs hf
      have hev := c2_aligned_eval (sv := sv) (ax := ax) q (C2Aligned.op9 hstate hCore hslot hInv) fuel n r hG hn
      have hr := evalGBy_bounded hq hs hf hG
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2] at hn; omega
      obtain ⟨fu, rfl⟩ : ∃ fu, fuel = fu + 1 := by
        cases fuel with
        | zero => simp [evalGBy] at hG
        | succ fu => exact ⟨fu, rfl⟩
      have hG' := hG
      simp only [evalGBy] at hG'
      rcases hcore : evalGBy q fu subj fc with _ | core <;> simp [hcore] at hG'
      have hfc : BoundedBy q fc := by simpa using hf.2.2
      have ec := c2_aligned_eval (sv := sv) (ax := ax) q hCore fu _ core hcore le_rfl
      have ecm := c2_aligned_eval (sv := sv) (ax := ax) q hCore fu m core hcore hm0
      have hcoreB := evalGBy_bounded hq hs hfc hcore
      rw [ec] at hslot ihInv
      have harmB := slot_boundedBy q a core hcoreB hslot
      rw [hslot] at hG'
      simp only at hG'
      rw [J_s9 (hstate := hstate)] at hev ⊢
      refine tb_node ⟨hs, hf, by simp only [label_node'] at hev; rw [hev]; exact hr⟩ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl)
      · exact ihCore fu m core hcore hm0 hs (by simpa [nounTail] using hfc)
      · simp only [nounTail]
        rw [ecm]
        exact ihInv fu m r hG' hm1 hcoreB harmB

/-! ## The aligned C2 join is `ComputedWindow.GenuineSkel` -/

section Genuine
open Nock.NockVMROM.Thm54.ComputedWindow

end Genuine



section Census
open Nock.NockVMROM.Thm54.ComputedWindow

end Census

section CensusTree
open Nock.NockVMROM.Thm54.ComputedWindow

end CensusTree

/-! ## The OP4 overflow: without alignment the C2 join leaves the field window -/

/-- At `q = 31`, `[4 [0 1]]` on the served atom `30` (an accepted FIELD evaluation: `lusFBy`
wraps to `0`) gives the C2 join the Nat evaluation `atom 31`, which is not `BoundedBy 31`, while the
honest field evaluator `evalFBy 31` returns `atom 0`.  `enc z (atom 31) = enc z (atom 0)` at every
seed in `ZMod 31`, so no pair event can separate them.  The honest guarded run fails, so §1's
`hbound` (via `C2Aligned` + `c2_aligned_eval`) is what excludes it. -/
theorem op4_overflow_unbounded (row4 row0 : (State × DTcomp (ZMod 31)) × ℕ)
    (svq : MState → ℕ → Noun) (axq : ℕ → ℕ)
    (h4 : row4.1.1 = .s4) (h0 : row0.1.1 = .s0)
    (hserve : svq .verify_child (row0.2 + 2) = .atom 30) :
    (c2JoinFuel (fun l : (State × DTcomp (ZMod 31)) × ℕ => l.1.1) (fun l => l.2) svq axq 2
        (.node row4 [.node row0 []]) (.atom 30) (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))).label.evaluation = .atom 31 ∧
      ¬ BoundedBy 31 (.atom 31) ∧
      evalFBy 31 2 (.atom 30) (.cell (.atom 4) (.cell (.atom 0) (.atom 1))) = some (.atom 0) ∧
      evalGBy 31 2 (.atom 30) (.cell (.atom 4) (.cell (.atom 0) (.atom 1))) = none ∧
      ∀ z : ZMod 31, GlobalCarryRecognizer.enc z (.atom 31) = GlobalCarryRecognizer.enc z (.atom 0) := by
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · simp [c2JoinFuel, c2SkeletonRow, c2Evaluation, h4, h0, kidSkel, hserve, nounTail]
  · simp [evalFBy, lusFBy, slot]
  · simp [evalGBy, lusGBy, slot]
  · intro z
    rw [GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_atom]
    congr 1



section AtEv

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily

variable {F K' : Type} [Field F] [Field K'] [Algebra F K']
  [Fintype F] [DecidableEq F]
  [Fintype K'] [DecidableEq K'] [CharP K' (ringChar K')] [FiniteDimensional F K']
  {hOrb : ℕ}
  (O : OptimizedStrictNockVMROMPackage F K' hOrb)


theorem census_window_Ev {Λ q : ℕ} (hΛ1 : 1 ≤ Λ)
    (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes O.basis
      O.computeChallenge O.computePublic O.orbit).rap.w → F[X])
    (Qm : Fin (namedFinalMemoryRAP O.family.problem.cfg.memRows_pos O.memoryNodes O.basis
      O.memoryChallenge O.memoryPublic O.orbit O.family.problem.cfg.kMem).rap.w → F[X])
    (hA : C2Aligned (sv := StrategyOfTracesR0AC2.c2ServedOf O Qm coinFree)
      (ax := StrategyOfTracesR0AC2.c2AxOf O Qc coinFree)
      (StrategyOfTracesR0AC2.c2TreeOfTraces O Qc coinFree)
      O.verifier.raw.claim.subject O.verifier.raw.claim.formula)
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy q fuel O.verifier.raw.claim.subject O.verifier.raw.claim.formula = some r)
    {gfuel : ℕ} {G : NTree (TraceGen.GenComputeRow K')} {R : Noun}
    (hgen : TraceGen.genComputeSkeleton (K := K') gfuel O.verifier.raw.claim.subject
      O.verifier.raw.claim.formula = .ok (G, R))
    (hΛ : TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ) :
    EdgeComparisonCensus.CombinedSkeletonCensus K' (skeletonEv O Qc Qm) Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy (skeletonEv O Qc Qm) Λ :=
  c2_aligned_census_window hΛ1 hA hG hgen hΛ (skeletonEv O Qc Qm) rfl

end AtEv

end Nock.RedTeam.Batch1091

#print axioms Nock.RedTeam.Batch1091.c2_aligned_eval
#print axioms Nock.RedTeam.Batch1091.op4_overflow_unbounded
#print axioms Nock.RedTeam.Batch1091.c2_aligned_bounded
#print axioms Nock.RedTeam.Batch1091.c2_aligned_genuine
#print axioms Nock.RedTeam.Batch1091.c2_aligned_census_window
#print axioms Nock.RedTeam.Batch1091.census_window_Ev
