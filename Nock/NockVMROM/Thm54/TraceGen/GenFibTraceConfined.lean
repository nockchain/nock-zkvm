/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibTraceConfined.lean

  **`TraceConfined 42 (airReorder fibTree)` as a lemma.**

  Combinator induction along the `fib_gen_*` spine.  `Λ = 42` is
  `fibFormula.leaves`, a program-text numeral.  OP8's pushed subject
  `[body, n]` is bounded by `20 + n.leaves` (also a numeral).
  Not `EvalBound`
-/
import Nock.NockVMROM.Thm54.TraceGen.GenFibKit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open ComputeTable

variable {K : Type} [Field K]

def fibΛ : ℕ := 42

theorem two_le_of_fibΛ {Λ : ℕ} (h : fibΛ ≤ Λ) : 2 ≤ Λ :=
  le_trans (by decide : 2 ≤ 42) h

theorem one_le_of_fibΛ {Λ : ℕ} (h : fibΛ ≤ Λ) : 1 ≤ Λ :=
  le_trans (by decide : 1 ≤ 42) h

theorem fibHalt_le {Λ : ℕ} (h : fibΛ ≤ Λ) : fibHalt.leaves ≤ Λ :=
  le_trans (le_of_eq fibHalt_leaves) (two_le_of_fibΛ h)

theorem fibInner_le {Λ : ℕ} (h : fibΛ ≤ Λ) : fibInner.leaves ≤ Λ :=
  le_trans (le_of_eq fibInner_leaves) (le_trans (by decide : 14 ≤ 42) h)

theorem fibInc_le {Λ : ℕ} (h : fibΛ ≤ Λ) : fibInc.leaves ≤ Λ :=
  le_trans (le_of_eq fibInc_leaves) (le_trans (by decide : 8 ≤ 42) h)

theorem fibRec_le {Λ : ℕ} (h : fibΛ ≤ Λ) : fibRec.leaves ≤ Λ :=
  le_trans (le_of_eq fibRec_leaves) (le_trans (by decide : 7 ≤ 42) h)

theorem fibRecSample_le {Λ : ℕ} (h : fibΛ ≤ Λ) : fibRecSample.leaves ≤ Λ :=
  le_trans (le_of_eq fibRecSample_leaves) (le_trans (by decide : 4 ≤ 42) h)

theorem fibBody_le {Λ : ℕ} (h : fibΛ ≤ Λ) : fibBody.leaves ≤ Λ :=
  le_trans (le_of_eq fibBody_leaves) (le_trans (by decide : 20 ≤ 42) h)

theorem fibFormula_le {Λ : ℕ} (h : fibΛ ≤ Λ) : fibFormula.leaves ≤ Λ :=
  le_trans (le_of_eq fibFormula_leaves) h

theorem fibPushed_le (n : Noun) {Λ : ℕ} (h : fibΛ ≤ Λ) (hn : n.leaves ≤ 4) :
    (fibPushed n).leaves ≤ Λ := by
  rw [fibPushed_leaves]
  have : 20 + n.leaves ≤ 24 := by omega
  exact le_trans this (le_trans (by decide : 24 ≤ 42) h)

theorem atom_le_of_fibΛ (k : ℕ) {Λ : ℕ} (h : fibΛ ≤ Λ) :
    (Noun.atom k).leaves ≤ Λ := by
  simp [atom_leaves]; exact one_le_of_fibΛ h

theorem op3_op0_le (ax : ℕ) {Λ : ℕ} (h : fibΛ ≤ Λ) :
    (op3 (op0 ax)).leaves ≤ Λ := by
  simp [op3, op0, cell_leaves, atom_leaves]
  exact le_trans (by decide : 3 ≤ 42) h

theorem op6_inner_le {Λ : ℕ} (h : fibΛ ≤ Λ) :
    (op6 (op3 (op0 7)) fibInc fibHalt).leaves ≤ Λ := by
  simpa [fibInner, op3, op6] using fibInner_le h

theorem op6_body_le {Λ : ℕ} (h : fibΛ ≤ Λ) :
    (op6 (op3 (op0 3)) fibInner fibHalt).leaves ≤ Λ := by
  simpa [fibBody, op3, op6] using fibBody_le h

/-! ## Confined spine -/

theorem confined_fib_halt {Λ n : ℕ} (s : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 1) s fibHalt = .ok (t, fibF1))
    (hs : s.leaves ≤ Λ) (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t :=
  confined_gen_op1 (by simpa [fibHalt] using h) hs (two_le_of_fibΛ hΛ)

theorem confined_fib_body_n1 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN1) fibBody =
      .ok (t, fibF1))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN1 hΛ (by simp [fibN1_leaves])
  have h0 := fib_gen_op0 (K := K) n (fib_slot3 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN1)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInner) h3 h1
  have huniq := gen_ok_unique h (by simpa [fibBody, op3, op6] using h6)
  rw [huniq.1]
  exact confined_gen_op6_one (Λ := Λ) h3 h1 h6
    (confined_gen_op3 (Λ := Λ) h0 (by simpa [op3] using h3)
      (confined_gen_op0 (Λ := Λ) (fib_slot3 fibN1) h0 hs h2)
      hs (op3_op0_le 3 hΛ) (atom_le_of_fibΛ 1 hΛ))
    (confined_fib_halt (n := n + 1) (fibPushed fibN1) h1 hs hΛ)
    hs (by simpa [fibBody, op3, op6] using fibBody_le hΛ) (atom_le_of_fibΛ 1 hΛ)

theorem confined_fib_inner_n2 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN2) fibInner =
      .ok (t, fibF1))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN2 hΛ (by simp [fibN2_leaves])
  have h0 := fib_gen_op0 (K := K) n (fib_slot7 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN2)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInc) h3 h1
  have huniq := gen_ok_unique h (by simpa [fibInner, op3, op6, fibN2, fibN1] using h6)
  rw [huniq.1]
  exact confined_gen_op6_one (Λ := Λ) h3 h1 h6
    (confined_gen_op3 (Λ := Λ) h0 (by simpa [op3] using h3)
      (confined_gen_op0 (Λ := Λ) (fib_slot7 fibN1) h0
        (by simpa [fibPushed, fibN2, fibN1, cell_leaves, fibBody_leaves] using hs) h2)
      (by simpa [fibPushed, fibN2, fibN1] using hs)
      (op3_op0_le 7 hΛ) (atom_le_of_fibΛ 1 hΛ))
    (confined_fib_halt (n := n + 1) (fibPushed fibN2) h1 hs hΛ)
    hs (by simpa [fibInner, op3, op6] using fibInner_le hΛ) (atom_le_of_fibΛ 1 hΛ)

theorem confined_fib_body_n2 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 4) (fibPushed fibN2) fibBody =
      .ok (t, fibF1))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN2 hΛ (by simp [fibN2_leaves])
  have h0 := fib_gen_op0 (K := K) (n + 1) (fib_slot3 fibN2)
  have h3 := gen_op3 (K := K) (n + 2) h0
  have hI := fib_gen_inner_n2 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 3) (d := fibHalt) h3 hI
  have huniq := gen_ok_unique h (by simpa [fibBody, op3, op6] using h6)
  rw [huniq.1]
  exact confined_gen_op6_zero (Λ := Λ) h3 hI h6
    (confined_gen_op3 (Λ := Λ) h0 (by simpa [op3] using h3)
      (confined_gen_op0 (Λ := Λ) (fib_slot3 fibN2) h0 hs h2)
      hs (op3_op0_le 3 hΛ) (atom_le_of_fibΛ 0 hΛ))
    (confined_fib_inner_n2 (Λ := Λ) hI hΛ)
    hs (by simpa [fibBody, op3, op6] using fibBody_le hΛ) (atom_le_of_fibΛ 1 hΛ)

theorem confined_fib_recSample {Λ n : ℕ} (rest : Noun)
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 2)
      (fibPushed (.cell (.atom 0) rest)) fibRecSample = .ok (t, res))
    (hΛ : fibΛ ≤ Λ) (hrest : rest.leaves ≤ 3) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs : (fibPushed (.cell (.atom 0) rest)).leaves ≤ Λ := by
    rw [fibPushed_leaves, cell_leaves, atom_leaves]
    have : 20 + (1 + rest.leaves) ≤ 24 := by omega
    exact le_trans this (le_trans (by decide : 24 ≤ 42) hΛ)
  have h2s := fib_gen_op0 (K := K) n (fib_slot2 (.cell (.atom 0) rest))
  have h7 := fib_gen_op0 (K := K) n (fib_slot7 rest)
  have hc := gen_cons (K := K) (n + 1) h2s h7
  have huniq := gen_ok_unique h (by simpa [fibRecSample, op0] using hc)
  rw [huniq.1]
  refine confined_gen_cons (Λ := Λ) h2s h7 hc ?_ ?_ hs ?_ ?_
  · exact confined_gen_op0 (Λ := Λ) (fib_slot2 (.cell (.atom 0) rest)) h2s hs h2
  · exact confined_gen_op0 (Λ := Λ) (fib_slot7 rest) h7 hs h2
  · exact fibRecSample_le hΛ
  · have : (fibBody.cell rest).leaves = 20 + rest.leaves := by
      simp [cell_leaves, fibBody_leaves]
    rw [this]
    have : 20 + rest.leaves ≤ 23 := by omega
    exact le_trans this (le_trans (by decide : 23 ≤ 42) hΛ)

theorem confined_fib_rec_n3 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 5) (fibPushed fibN3) fibRec =
      .ok (t, fibF1))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN3 hΛ (by simp [fibN3_leaves])
  have hsamp := fib_gen_recSample (K := K) (n + 2) fibN2
  have hc := fib_gen_op0 (K := K) (n + 3) (fib_slot2 fibN3)
  have hm := fib_gen_body_n2 (K := K) n
  have h2g := gen_op2 (K := K) (n + 4) hsamp hc hm
  let _ := h2g
  have h' :
      genComputeSkeleton (K := K) (n + 5) (fibPushed (.cell (.atom 0) fibN2)) fibRec =
        .ok (t, fibF1) := by
    simpa [fibN3] using h
  exact confined_gen_op2 (Λ := Λ) hsamp hc hm
    (by simpa [fibRec, op2] using h')
    (confined_fib_recSample (Λ := Λ) (n := n + 2) fibN2
      (by simpa [fibN3, fibN2] using hsamp) hΛ (by simp [fibN2_leaves]))
    (confined_gen_op0 (Λ := Λ) (fib_slot2 fibN3) hc hs h2)
    (confined_fib_body_n2 (Λ := Λ) hm hΛ)
    hs (by simpa [fibRec, op2] using fibRec_le hΛ) (atom_le_of_fibΛ 1 hΛ)

theorem confined_fib_inc_n3 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (fibPushed fibN3) fibInc =
      .ok (t, fibF2))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have hs := fibPushed_le fibN3 hΛ (by simp [fibN3_leaves])
  have hr := fib_gen_rec_n3 (K := K) n
  have h4 := gen_op4 (K := K) (n + 5) hr fib_lus_1
  have huniq := gen_ok_unique h (by simpa [fibInc, op4] using h4)
  rw [huniq.1]
  exact confined_gen_op4 (Λ := Λ) hr fib_lus_1 h4
    (confined_fib_rec_n3 (Λ := Λ) hr hΛ)
    hs (by simpa [fibInc, op4] using fibInc_le hΛ) (atom_le_of_fibΛ 2 hΛ)

theorem confined_fib_inner_n3 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 7) (fibPushed fibN3) fibInner =
      .ok (t, fibF2))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN3 hΛ (by simp [fibN3_leaves])
  have h0 := fib_gen_op0 (K := K) (n + 4) (fib_slot7 fibN2)
  have h3 := gen_op3 (K := K) (n + 5) h0
  have hi := fib_gen_inc_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 6) (d := fibHalt) h3 hi
  have huniq := gen_ok_unique h (by simpa [fibInner, op3, op6, fibN3, fibN2] using h6)
  rw [huniq.1]
  exact confined_gen_op6_zero (Λ := Λ) h3 hi h6
    (confined_gen_op3 (Λ := Λ) h0 (by simpa [op3] using h3)
      (confined_gen_op0 (Λ := Λ) (fib_slot7 fibN2) h0
        (by simpa [fibPushed, fibN3, fibN2] using hs) h2)
      (by simpa [fibPushed, fibN3, fibN2] using hs)
      (op3_op0_le 7 hΛ) (atom_le_of_fibΛ 0 hΛ))
    (confined_fib_inc_n3 (Λ := Λ) hi hΛ)
    hs (by simpa [fibInner, op3, op6] using fibInner_le hΛ) (atom_le_of_fibΛ 2 hΛ)

theorem confined_fib_body_n3 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 8) (fibPushed fibN3) fibBody =
      .ok (t, fibF2))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN3 hΛ (by simp [fibN3_leaves])
  have h0 := fib_gen_op0 (K := K) (n + 5) (fib_slot3 fibN3)
  have h3 := gen_op3 (K := K) (n + 6) h0
  have hI := fib_gen_inner_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 7) (d := fibHalt) h3 hI
  have huniq := gen_ok_unique h (by simpa [fibBody, op3, op6] using h6)
  rw [huniq.1]
  exact confined_gen_op6_zero (Λ := Λ) h3 hI h6
    (confined_gen_op3 (Λ := Λ) h0 (by simpa [op3] using h3)
      (confined_gen_op0 (Λ := Λ) (fib_slot3 fibN3) h0 hs h2)
      hs (op3_op0_le 3 hΛ) (atom_le_of_fibΛ 0 hΛ))
    (confined_fib_inner_n3 (Λ := Λ) hI hΛ)
    hs (by simpa [fibBody, op3, op6] using fibBody_le hΛ) (atom_le_of_fibΛ 2 hΛ)

theorem confined_fib_rec_n4 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 9) (fibPushed fibN4) fibRec =
      .ok (t, fibF2))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN4 hΛ (by simp [fibN4_leaves])
  have hsamp := fib_gen_recSample (K := K) (n + 6) fibN3
  have hc := fib_gen_op0 (K := K) (n + 7) (fib_slot2 fibN4)
  have hm := fib_gen_body_n3 (K := K) n
  have h2g := gen_op2 (K := K) (n + 8) hsamp hc hm
  let _ := h2g
  have h' :
      genComputeSkeleton (K := K) (n + 9) (fibPushed (.cell (.atom 0) fibN3)) fibRec =
        .ok (t, fibF2) := by
    simpa [fibN4] using h
  exact confined_gen_op2 (Λ := Λ) hsamp hc hm
    (by simpa [fibRec, op2] using h')
    (confined_fib_recSample (Λ := Λ) (n := n + 6) fibN3
      (by simpa [fibN4, fibN3] using hsamp) hΛ (by simp [fibN3_leaves]))
    (confined_gen_op0 (Λ := Λ) (fib_slot2 fibN4) hc hs h2)
    (confined_fib_body_n3 (Λ := Λ) hm hΛ)
    hs (by simpa [fibRec, op2] using fibRec_le hΛ) (atom_le_of_fibΛ 2 hΛ)

theorem confined_fib_inc_n4 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 10) (fibPushed fibN4) fibInc =
      .ok (t, fibF3))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have hs := fibPushed_le fibN4 hΛ (by simp [fibN4_leaves])
  have hr := fib_gen_rec_n4 (K := K) n
  have h4 := gen_op4 (K := K) (n + 9) hr fib_lus_2
  have huniq := gen_ok_unique h (by simpa [fibInc, op4] using h4)
  rw [huniq.1]
  exact confined_gen_op4 (Λ := Λ) hr fib_lus_2 h4
    (confined_fib_rec_n4 (Λ := Λ) hr hΛ)
    hs (by simpa [fibInc, op4] using fibInc_le hΛ) (atom_le_of_fibΛ 3 hΛ)

theorem confined_fib_inner_n4 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 11) (fibPushed fibN4) fibInner =
      .ok (t, fibF3))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN4 hΛ (by simp [fibN4_leaves])
  have h0 := fib_gen_op0 (K := K) (n + 8) (fib_slot7 fibN3)
  have h3 := gen_op3 (K := K) (n + 9) h0
  have hi := fib_gen_inc_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 10) (d := fibHalt) h3 hi
  have huniq := gen_ok_unique h (by simpa [fibInner, op3, op6, fibN4, fibN3] using h6)
  rw [huniq.1]
  exact confined_gen_op6_zero (Λ := Λ) h3 hi h6
    (confined_gen_op3 (Λ := Λ) h0 (by simpa [op3] using h3)
      (confined_gen_op0 (Λ := Λ) (fib_slot7 fibN3) h0
        (by simpa [fibPushed, fibN4, fibN3] using hs) h2)
      (by simpa [fibPushed, fibN4, fibN3] using hs)
      (op3_op0_le 7 hΛ) (atom_le_of_fibΛ 0 hΛ))
    (confined_fib_inc_n4 (Λ := Λ) hi hΛ)
    hs (by simpa [fibInner, op3, op6] using fibInner_le hΛ) (atom_le_of_fibΛ 3 hΛ)

theorem confined_fib_body_n4 {Λ n : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 12) (fibPushed fibN4) fibBody =
      .ok (t, fibF3))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_fibΛ hΛ
  have hs := fibPushed_le fibN4 hΛ (by simp [fibN4_leaves])
  have h0 := fib_gen_op0 (K := K) (n + 9) (fib_slot3 fibN4)
  have h3 := gen_op3 (K := K) (n + 10) h0
  have hI := fib_gen_inner_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 11) (d := fibHalt) h3 hI
  have huniq := gen_ok_unique h (by simpa [fibBody, op3, op6] using h6)
  rw [huniq.1]
  exact confined_gen_op6_zero (Λ := Λ) h3 hI h6
    (confined_gen_op3 (Λ := Λ) h0 (by simpa [op3] using h3)
      (confined_gen_op0 (Λ := Λ) (fib_slot3 fibN4) h0 hs h2)
      hs (op3_op0_le 3 hΛ) (atom_le_of_fibΛ 0 hΛ))
    (confined_fib_inner_n4 (Λ := Λ) hI hΛ)
    hs (by simpa [fibBody, op3, op6] using fibBody_le hΛ) (atom_le_of_fibΛ 3 hΛ)

theorem confined_fib {Λ : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) 32 fibSubject fibFormula = .ok (t, fibResult))
    (hΛ : fibΛ ≤ Λ) :
    TraceConfined Λ t := by
  have hs : fibSubject.leaves ≤ Λ :=
    le_trans (le_of_eq fibSubject_leaves) (le_trans (by decide : 4 ≤ 42) hΛ)
  have hq := gen_quote (K := K) 30 fibSubject fibBody
  have hb := fib_gen_body_n4 (K := K) 19
  have h8 := gen_op8 (K := K) 31 hq hb
  let _ := h8
  exact confined_gen_op8 (Λ := Λ) hq hb
    (by simpa [fibFormula, op8] using h)
    (confined_gen_quote (Λ := Λ) hq hs
      (by
        have : (quote fibBody).leaves = 21 := by
          simp [quote, cell_leaves, atom_leaves, fibBody_leaves]
        exact le_trans (le_of_eq this) (le_trans (by decide : 21 ≤ 42) hΛ))
      (fibBody_le hΛ))
    (confined_fib_body_n4 (Λ := Λ) hb hΛ)
    hs (fibFormula_le hΛ) (atom_le_of_fibΛ 3 hΛ)

/-- Combinator induction, not a binder. `Λ = 42` is the program-text numeral. -/
theorem fib_traceConfined :
    TraceConfined 42 (airReorder (fibTree (K := K))) :=
  traceConfined_airReorder _ (confined_fib (fibTree_eq (K := K)) (le_refl 42))

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.fib_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.confined_fib
