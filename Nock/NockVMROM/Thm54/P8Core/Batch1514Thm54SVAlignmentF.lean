/-
  Nock/NockVMROM/Thm54/P8Core/Batch1514Thm54SVAlignmentF.lean

* `C2Aligned q` — `Batch1091.C2Aligned` transcribed at the field join `c2JoinFuelF q` (the
    dependent children's inputs are the FIELD join's evaluations).
  * **`genuineF_of_ready`** — the new theorem the standalone verifier needs in place of
    `Batch1091.c2_aligned_genuine`: an aligned, chip-ready S-carrying tree has a field-genuine C2
    join, `GenuineSkelF q (J n t subj f)` at every fuel `n ≥ t.size`.  **No honest run, no
    generator run, no window.**  The Nat proof needed `evalGBy q fuel subj f = some r` for exactly
    two facts — OP4's operand is an atom, OP6's selector is `0` or `1` — and the chip-side bundle
    already carries both (`C2ChipReady.op4`'s `hke`, `.op6`'s `hb` / `hcondE`).
  * `evalFBy_of_ready` / `holdsF_of_ready` — composed with `SVGenuineF.genuineF_evalFBy`: the field
    join's root evaluation IS the claim's field result, `evalFBy q t.size subj f = some (J …).eval`,
    hence `HoldsF q ⟨subj, f, (J …).eval⟩`.
  `c2_aligned_eval`,
    `c2_aligned_genuine` and `c2_aligned_census_window` are NOT transcribed (they rest on the
    honest run / the honest generator tree). -/
import Nock.NockVMROM.Thm54.P8Core.Batch1513Thm54SVReadyFuelF
import Nock.NockVMROM.Thm54.P8Core.Batch1511Thm54SVGenuineF
import Nock.NockVMROM.Thm54.P8Core.Batch1091Thm54C2Alignment

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVAlignmentF

open Nock
open Nock.Noun
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.SVJoinF
open Nock.NockVMROM.Thm54.SVJoinAssemblyF
open Nock.NockVMROM.Thm54.SVReadyFuelF
open Nock.NockVMROM.Thm54.SVGenuineF
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.RedTeam
open Nock.FieldEmbedding
variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
set_option hygiene false in
/-- The FIELD C2 join at the modulus `q` in scope at the use site. -/
local notation "J" => c2JoinFuelF q (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-- **Alignment shape at the field join** (`Batch1091.C2Aligned` at `c2JoinFuelF q`). -/
inductive C2Aligned (q : ℕ) : NTree ((State × DTcomp K) × ℕ) → Noun → Noun → Prop
  | op0 {row : (State × DTcomp K) × ℕ} {subj : Noun} {a : ℕ}
      (hstate : row.1.1 = .s0)
      (hslot : slot a subj = some (op0ResF sv ax row.2 subj)) :
      C2Aligned q (.node row []) subj (.cell (.atom 0) (.atom a))
  | op1 {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
      (hstate : row.1.1 = .s1) :
      C2Aligned q (.node row []) subj (.cell (.atom 1) tail)
  | cons {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj b c d : Noun}
      (hstate : row.1.1 = .cons)
      (hL : C2Aligned q c0 subj (.cell b c))
      (hR : C2Aligned q c1 subj d) :
      C2Aligned q (.node row [c0, c1]) subj (.cell (.cell b c) d)
  | op3 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)} {subj tail : Noun}
      (hstate : row.1.1 = .s3) (hC : C2Aligned q c0 subj tail) :
      C2Aligned q (.node row [c0]) subj (.cell (.atom 3) tail)
  | op4 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)} {subj tail : Noun}
      (hstate : row.1.1 = .s4) (hC : C2Aligned q c0 subj tail) :
      C2Aligned q (.node row [c0]) subj (.cell (.atom 4) tail)
  | op5 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc : Noun}
      (hstate : row.1.1 = .s5)
      (hL : C2Aligned q c0 subj fb) (hR : C2Aligned q c1 subj fc) :
      C2Aligned q (.node row [c0, c1]) subj (.cell (.atom 5) (.cell fb fc))
  | op2 {row : (State × DTcomp K) × ℕ} {c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc : Noun}
      (hstate : row.1.1 = .s2)
      (h1 : C2Aligned q c0 subj fb) (h2 : C2Aligned q c1 subj fc)
      (h3 : C2Aligned q c2 (J c0.size c0 subj fb).label.evaluation
        (J c1.size c1 subj fc).label.evaluation) :
      C2Aligned q (.node row [c0, c1, c2]) subj (.cell (.atom 2) (.cell fb fc))
  | op6 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc fd : Noun}
      (hstate : row.1.1 = .s6)
      (hC : C2Aligned q c1 subj fb)
      (hT : C2Aligned q c0 subj
        (if Batch1091.c6b (J c1.size c1 subj fb).label.evaluation = 0 then fc else fd)) :
      C2Aligned q (.node row [c0, c1]) subj (.cell (.atom 6) (.cell fb (.cell fc fd)))
  | op7 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc : Noun}
      (hstate : row.1.1 = .s7)
      (hHelp : C2Aligned q c1 subj fb)
      (hCons : C2Aligned q c0 (J c1.size c1 subj fb).label.evaluation fc) :
      C2Aligned q (.node row [c0, c1]) subj (.cell (.atom 7) (.cell fb fc))
  | op8 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fb fc : Noun}
      (hstate : row.1.1 = .s8)
      (hHelp : C2Aligned q c1 subj fb)
      (hCons : C2Aligned q c0 (.cell (J c1.size c1 subj fb).label.evaluation subj) fc) :
      C2Aligned q (.node row [c0, c1]) subj (.cell (.atom 8) (.cell fb fc))
  | op9 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fc : Noun} {a : ℕ}
      (hstate : row.1.1 = .s9)
      (hCore : C2Aligned q c0 subj fc)
      (hslot : slot a (J c0.size c0 subj fc).label.evaluation =
        some (op9ArmF sv ax row.2 (J c0.size c0 subj fc).label.evaluation))
      (hInv : C2Aligned q c1 (J c0.size c0 subj fc).label.evaluation
        (op9ArmF sv ax row.2 (J c0.size c0 subj fc).label.evaluation)) :
      C2Aligned q (.node row [c0, c1]) subj (.cell (.atom 9) (.cell (.atom a) fc))


@[simp] theorem J_subject' {q : ℕ} (fuel : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) :
    (J fuel t s f).label.subject = s := J_subject (sv := sv) (ax := ax) (q := q) fuel t s f

@[simp] theorem J_formula' {q : ℕ} (fuel : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) :
    (J fuel t s f).label.formula = f := J_formula (sv := sv) (ax := ax) (q := q) fuel t s f

/-- `J m c = J c.size c` once `c.size ≤ m` (the field join is fuel-stable). -/
theorem J_at_size {q : ℕ} (c : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) {m : ℕ}
    (hm : c.size ≤ m) : J m c s f = J c.size c s f :=
  J_eq_of_le (sv := sv) (ax := ax) (q := q) c s f le_rfl hm

theorem size_node1F (row : (State × DTcomp K) × ℕ) (c0 : NTree ((State × DTcomp K) × ℕ)) :
    (NTree.node row [c0]).size = 1 + c0.size := by
  simp [NTree.size]

theorem size_node2F (row : (State × DTcomp K) × ℕ) (c0 c1 : NTree ((State × DTcomp K) × ℕ)) :
    (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
  simp [NTree.size]; omega

theorem size_node3F (row : (State × DTcomp K) × ℕ)
    (c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)) :
    (NTree.node row [c0, c1, c2]).size = 1 + c0.size + c1.size + c2.size := by
  simp [NTree.size]; omega

/-- **Genuineness without a run.**  An aligned, chip-ready S-carrying tree has a FIELD-genuine C2
join at every fuel `n ≥ t.size`.  Replaces `Batch1091.c2_aligned_genuine`, which needed one
successful guarded honest run `evalGBy q fuel subj f = some r`. -/
theorem genuineF_of_ready {z : K} {q : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {subj f : Noun}
    (hA : C2Aligned (sv := sv) (ax := ax) q t subj f) :
    ∀ n : ℕ, t.size ≤ n → C2ChipReady (sv := sv) (ax := ax) z q t subj f →
      GenuineSkelF q (J n t subj f) := by
  induction hA with
  | @op0 row subj a hstate hslot =>
      intro n hn _
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [NTree.size] at hn; omega⟩
      rw [J_s0 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      refine GenuineSkelF.node ?_ ?_ ?_ (by simp)
      · exact ⟨a, rfl⟩
      · simp [KidInputs]
      · simp [RowOutputF, c2EvaluationF, op0Axis, hslot]
  | @op1 row subj tail hstate =>
      intro n hn _
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [NTree.size] at hn; omega⟩
      rw [J_s1 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      refine GenuineSkelF.node ?_ ?_ ?_ (by simp)
      · exact ⟨tail, rfl⟩
      · simp [KidInputs]
      · simp [RowOutputF, c2EvaluationF, nounTail, tl, StrategyOfTraces.nounTail]
  | @cons row c0 c1 subj b c d hstate hL hR ihL ihR =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2F] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2F] at hn; omega
      cases hRdy with
      | cons _ _ _ _ _ _ _ _ _ _ hL' hR' =>
      rw [J_cons (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨b, c, d, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead,
          StrategyOfTraces.nounTail]
      · simp [RowOutputF, c2EvaluationF, kidSkel, nounHead, nounTail]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl)
        · exact ihL m hm0 hL'
        · exact ihR m hm1 hR'
  | @op3 row c0 subj tail hstate hC ih =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node1F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node1F] at hn; omega
      cases hRdy with
      | op3 _ _ _ _ _ _ _ _ _ hC' =>
      rw [J_s3 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨tail, rfl⟩
      · simp [KidInputs, nounTail, tl, StrategyOfTraces.nounTail]
      · simp [RowOutputF, c2EvaluationF, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k rfl
        exact ih m hm0 hC'
  | @op4 row c0 subj tail hstate hC ih =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node1F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node1F] at hn; omega
      cases hRdy with
      | @op4 _ _ _ _ k _ _ _ _ _ _ hke _ _ hC' =>
      have hkem : (J m c0 subj tail).label.evaluation = .atom k := by
        rw [J_at_size (sv := sv) (ax := ax) (q := q) c0 subj tail hm0]; exact hke
      rw [J_s4 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨tail, rfl⟩
      · simp [KidInputs, nounTail, tl, StrategyOfTraces.nounTail]
      · simp only [Batch1091.label_node', List.map_cons, List.map_nil, RowOutputF,
          c2SkeletonRowF_state, c2SkeletonRowF_evaluation, c2EvaluationF, kidSkel,
          List.getElem?_cons_zero, Option.getD_some, nounTail]
        rw [hkem]
        simp [lusFBy, OpcodeSemantics.incMod]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k rfl
        exact ih m hm0 hC'
  | @op5 row c0 c1 subj fb fc hstate hL hR ihL ihR =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2F] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2F] at hn; omega
      cases hRdy with
      | cons h0 => rw [hstate] at h0; cases h0
      | op5 _ _ _ _ _ _ _ _ _ _ _ _ _ hL' hR' =>
      rw [J_s5 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead,
          StrategyOfTraces.nounTail]
      · simp [RowOutputF, c2EvaluationF, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl)
        · exact ihL m hm0 hL'
        · exact ihR m hm1 hR'
  | @op2 row c0 c1 c2 subj fb fc hstate h1 h2 h3 ih1 ih2 ih3 =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node3F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node3F] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node3F] at hn; omega
      have hm2 : c2.size ≤ m := by rw [size_node3F] at hn; omega
      cases hRdy with
      | op2 _ _ _ _ _ _ _ _ _ _ _ _ _ r1 r2 r3 =>
      rw [J_s2 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      simp only [nounHead, nounTail]
      rw [J_at_size (sv := sv) (ax := ax) (q := q) c0 subj fb hm0,
        J_at_size (sv := sv) (ax := ax) (q := q) c1 subj fc hm1]
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead,
          StrategyOfTraces.nounTail]
      · simp [RowOutputF, c2EvaluationF, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl | rfl)
        · rw [← J_at_size (sv := sv) (ax := ax) (q := q) c0 subj fb hm0]; exact ih1 m hm0 r1
        · rw [← J_at_size (sv := sv) (ax := ax) (q := q) c1 subj fc hm1]; exact ih2 m hm1 r2
        · exact ih3 m hm2 r3
  | @op6 row c0 c1 subj fb fc fd hstate hC hT ihC ihT =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2F] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2F] at hn; omega
      cases hRdy with
      | cons h0 => rw [hstate] at h0; cases h0
      | @op6 _ _ _ _ _ _ _ bit _ _ _ _ _ _ _ hb hcondE _ _ _ _ _ rT rC =>
      rw [J_s6 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      simp only [nounHead, nounTail]
      simp only [J_at_size (sv := sv) (ax := ax) (q := q) c1 subj fb hm1]
      rw [hcondE]
      have hif : (if Batch1091.c6b (J c1.size c1 subj fb).label.evaluation = 0 then fc else fd) =
          (if bit = 0 then fc else fd) := by
        rw [hcondE]; by_cases h : bit = 0 <;> simp [h, Batch1091.c6b]
      have hTgood := ihT m hm0 (by rw [hif]; exact rT)
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, fd, rfl⟩
      · simp [KidInputs, hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, hcondE,
          condBit]
      · simp [RowOutputF, c2EvaluationF, kidSkel, hcondE]
        rcases hb with rfl | rfl <;> simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl)
        · convert hTgood using 3
          by_cases h : bit = 0 <;> simp [h, hcondE, Batch1091.c6b]
        · rw [← J_at_size (sv := sv) (ax := ax) (q := q) c1 subj fb hm1]; exact ihC m hm1 rC
  | @op7 row c0 c1 subj fb fc hstate hHelp hCons ihHelp ihCons =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2F] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2F] at hn; omega
      cases hRdy with
      | cons h0 => rw [hstate] at h0; cases h0
      | op7 _ _ _ _ _ _ _ _ _ _ _ rH rC =>
      rw [J_s7 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      simp only [nounHead, nounTail]
      rw [J_at_size (sv := sv) (ax := ax) (q := q) c1 subj fb hm1]
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead,
          StrategyOfTraces.nounTail]
      · simp [RowOutputF, c2EvaluationF, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl)
        · exact ihCons m hm0 rC
        · rw [← J_at_size (sv := sv) (ax := ax) (q := q) c1 subj fb hm1]; exact ihHelp m hm1 rH
  | @op8 row c0 c1 subj fb fc hstate hHelp hCons ihHelp ihCons =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2F] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2F] at hn; omega
      cases hRdy with
      | cons h0 => rw [hstate] at h0; cases h0
      | op8 _ _ _ _ _ _ _ _ _ _ _ rH rC =>
      rw [J_s8 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      simp only [nounHead, nounTail]
      rw [J_at_size (sv := sv) (ax := ax) (q := q) c1 subj fb hm1]
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨fb, fc, rfl⟩
      · simp [KidInputs, nounHead, nounTail, hd, tl, StrategyOfTraces.nounHead,
          StrategyOfTraces.nounTail]
      · simp [RowOutputF, c2EvaluationF, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl)
        · exact ihCons m hm0 rC
        · rw [← J_at_size (sv := sv) (ax := ax) (q := q) c1 subj fb hm1]; exact ihHelp m hm1 rH
  | @op9 row c0 c1 subj fc a hstate hCore hslot hInv ihCore ihInv =>
      intro n hn hRdy
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by rw [size_node2F] at hn; omega⟩
      have hm0 : c0.size ≤ m := by rw [size_node2F] at hn; omega
      have hm1 : c1.size ≤ m := by rw [size_node2F] at hn; omega
      cases hRdy with
      | cons h0 => rw [hstate] at h0; cases h0
      | op9 _ _ _ _ _ _ _ _ _ _ _ _ _ rCore rInv =>
      rw [J_s9 (sv := sv) (ax := ax) (q := q) (hstate := hstate)]
      simp only [nounHead, nounTail]
      rw [J_at_size (sv := sv) (ax := ax) (q := q) c0 subj fc hm0]
      refine GenuineSkelF.node ?_ ?_ ?_ ?_
      · exact ⟨_, fc, rfl⟩
      · simp [KidInputs, tl, StrategyOfTraces.nounTail, op9Axis, hslot]
      · simp [RowOutputF, c2EvaluationF, kidSkel]
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl)
        · rw [← J_at_size (sv := sv) (ax := ax) (q := q) c0 subj fc hm0]; exact ihCore m hm0 rCore
        · exact ihInv m hm1 rInv

/-- **The field join's root evaluation is the claim's field result** (no run assumed): from
alignment and chip readiness, `evalFBy q n subj f = some (J n t subj f).label.evaluation` at the
fuel `n = (J n t subj f).size`. -/
theorem evalFBy_of_ready {z : K} {q : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {subj f : Noun}
    (hA : C2Aligned (sv := sv) (ax := ax) q t subj f)
    (hR : C2ChipReady (sv := sv) (ax := ax) z q t subj f) :
    evalFBy q (J t.size t subj f).size subj f = some (J t.size t subj f).label.evaluation := by
  have hg := genuineF_of_ready (sv := sv) (ax := ax) hA t.size le_rfl hR
  have h := genuineF_evalFBy hg
  rwa [J_subject (sv := sv) (ax := ax) (q := q), J_formula (sv := sv) (ax := ax) (q := q)] at h

/-- **`HoldsF` from alignment and chip readiness**: the claim `(subj, f, root evaluation of the
field join)` holds in the field language. -/
theorem holdsF_of_ready {z : K} {q : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {subj f : Noun}
    (hA : C2Aligned (sv := sv) (ax := ax) q t subj f)
    (hR : C2ChipReady (sv := sv) (ax := ax) z q t subj f) :
    HoldsF q ⟨subj, f, (J t.size t subj f).label.evaluation⟩ :=
  ⟨_, evalFBy_of_ready (sv := sv) (ax := ax) hA hR⟩

section Census

open Nock.NockVMROM.Thm54.ComputedWindow

/-- **Every comparison pair of a genuine C2 row is within `Λ`** once the row's and its kids' row
nouns are (`RowNounsLe`, from `ComputedWindow.genuine_rows_le_programLeafBound`). -/
theorem c2Row_pairs_le {q : ℕ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {st : State} {S : ℕ} {s f : Noun}
    {kids : List ComputeRowSkeleton}
    (hshape : FormulaShape st f) (hin : KidInputs st s f kids)
    (hu : RowNounsLe Λ (c2SkeletonRowF q sv ax st S s f kids))
    (hk : ∀ k ∈ kids, RowNounsLe Λ k) :
    ∀ cu ∈ P8Census.skeletonComparisons (K := K) (c2SkeletonRowF q sv ax st S s f kids),
      cu.left.leaves ≤ Λ ∧ cu.right.leaves ≤ Λ := by
  intro cu hc
  cases st with
  | s0 =>
      obtain ⟨a, rfl⟩ := hshape
      simp only [KidInputs] at hin; subst hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | s1 =>
      obtain ⟨t, rfl⟩ := hshape
      simp only [KidInputs] at hin; subst hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | s2 =>
      obtain ⟨b, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, _⟩⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | s3 =>
      obtain ⟨t, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | s4 =>
      obtain ⟨t, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | s5 =>
      obtain ⟨b, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | s6 =>
      obtain ⟨b, c, d, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | s7 =>
      obtain ⟨b, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | s8 =>
      obtain ⟨b, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail, hin.2.2.1] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail, hin.2.2.1] <;> omega)
  | s9 =>
      obtain ⟨a, c, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)
  | cons =>
      obtain ⟨b, c, d, rfl⟩ := hshape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _⟩⟩⟩ <;> simp only [KidInputs] at hin
      simp [P8Census.skeletonComparisons, P8Census.skeletonDec, P8Census.skeletonSubformula,
        P8Census.skeletonMemoryAxis, P8Census.skeletonUse, c2SkeletonRowF, decActive,
        hasTailDecomposition, fanoutComp, Nock.Framework.recordCount, nounHead, nounTail,
        kidSkel] at hc
      simp [RowNounsLe, c2SkeletonRowF, c2EvaluationF, kidSkel, Noun.leaves, nounHead, nounTail] at hu hk
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        (simp [Noun.leaves, c2EvaluationF, kidSkel, nounHead, nounTail] <;> omega)

end Census

section CensusTree

open Nock.NockVMROM.Thm54.ComputedWindow

/-- Every node of the C2 join is a C2 row over its own children. -/
theorem J_isJ {q : ℕ} : ∀ (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun),
    ∃ (st : State) (S : ℕ), (J n t s f).label =
        c2SkeletonRowF q sv ax st S s f ((J n t s f).children.map NTree.label) ∧
      ∀ k ∈ (J n t s f).children, ∃ m t' s' f', k = J m t' s' f' := by
  intro n t s f
  cases n with
  | zero =>
      cases t with
      | node row ch => exact ⟨row.1.1, row.2, rfl, by simp [c2JoinFuelF]⟩
  | succ n =>
      cases t with
      | node row ch =>
          refine ⟨row.1.1, row.2, rfl, ?_⟩
          simp only [c2JoinFuelF, c2JoinKidsF, NTree.children_node]
          split <;> intro k hk <;>
            simp only [List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hk <;>
            first
            | exact hk.elim
            | (obtain ⟨c, -, h⟩ := hk; exact ⟨_, _, _, _, h.symm⟩)
            | (rcases hk with h | h | h <;> exact ⟨_, _, _, _, h⟩)
            | (rcases hk with h | h <;> exact ⟨_, _, _, _, h⟩)
            | exact ⟨_, _, _, _, hk⟩

theorem J_nodes {q : ℕ} {T : NTree ComputeRowSkeleton} (hT : ∃ m t' s' f', T = J m t' s' f')
    {u : NTree ComputeRowSkeleton} (hu : InTree T u) :
    ∃ m t' s' f', u = J m t' s' f' := by
  induction hu with
  | here => exact hT
  | sub hs _ ih =>
      obtain ⟨m, t', s', f', rfl⟩ := hT
      obtain ⟨_, _, _, hk⟩ := J_isJ (sv := sv) (ax := ax) (q := q) m t' s' f'
      exact ih (hk _ hs)

/-- A C2 row's subformula field is a kid noun or `atom 0`. -/
theorem sf_le {q : ℕ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {st : State} {S : ℕ} {s f : Noun}
    {kids : List ComputeRowSkeleton} (hk : ∀ k ∈ kids, RowNounsLe Λ k) (i : Fin 3)
    (slot : TripleSlot) :
    (P8Census.skeletonSubformula (c2SkeletonRowF q sv ax st S s f kids) i slot).leaves ≤ Λ := by
  unfold P8Census.skeletonSubformula
  split
  · simp only [c2SkeletonRowF]
    split
    · rename_i h
      have hb := hk _ (List.getElem_mem h)
      cases slot <;> simp [hb.1, hb.2.1, hb.2.2]
    · simpa [Noun.leaves] using hΛ
  · simpa [Noun.leaves] using hΛ

/-- **The tree-level window**: on a genuine C2 join whose rows are within `Λ`, every combined
census pair and every size-window noun is within `Λ`. -/
theorem c2_tree_census {q : ℕ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ))
    (subj f : Noun) (mf : List (NTree MemoryRowSkeleton))
    (hgen : GenuineSkelF q (J n t subj f))
    (hrows : ∀ u, InTree (J n t subj f) u → RowNounsLe Λ u.label) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
        { computeTree := J n t subj f, memoryForest := mf } Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        { computeTree := J n t subj f, memoryForest := mf } Λ := by
  -- per-node facts
  have hnode : ∀ u, InTree (J n t subj f) u →
      ∃ (st : State) (S : ℕ) (s' f' : Noun), u.label =
          c2SkeletonRowF q sv ax st S s' f' (u.children.map NTree.label) ∧
        FormulaShape st f' ∧ KidInputs st s' f' (u.children.map NTree.label) ∧
        RowNounsLe Λ u.label ∧ ∀ k ∈ u.children.map NTree.label, RowNounsLe Λ k := by
    intro u hu
    obtain ⟨m, t', s', f', rfl⟩ := J_nodes (sv := sv) (ax := ax) (q := q) ⟨n, t, subj, f, rfl⟩ hu
    obtain ⟨st, S, hlab, -⟩ := J_isJ (sv := sv) (ax := ax) (q := q) m t' s' f'
    have hg := genuineF_sub hgen hu
    obtain ⟨hsh, hin, -⟩ := genuineF_root hg
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

end CensusTree

end Nock.NockVMROM.Thm54.SVAlignmentF
