/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibSize.lean

  Compute-tree size of the compiled Peano-fib program
  (`n = 4`, `F = 3`) is 33.  Combinator induction along `fib_gen_*`.
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

theorem size_fib_halt {n : ℕ} (s : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 1) s fibHalt = .ok (t, fibF1)) :
    t.size = 1 :=
  gen_op1_size n s 1 (by simpa [fibHalt] using h)

theorem size_fib_body_n1 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN1) fibBody =
      .ok (t, fibF1)) :
    t.size = 4 := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot3 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN1)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInner) h3 h1
  have huniq := gen_ok_unique h (by simpa [fibBody, op3] using h6)
  have hs := gen_op6_one_size (n + 2) h3 h1 h6
  rw [huniq.1, hs, gen_op3_size (n + 1) h0 (by simpa [op3] using h3),
    gen_op0_size n (fib_slot3 fibN1) h0, size_fib_halt (fibPushed fibN1) h1]

theorem size_fib_inner_n2 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN2) fibInner =
      .ok (t, fibF1)) :
    t.size = 4 := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot7 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN2)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInc) h3 h1
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN2 = .cell (.atom 0) fibN1 from rfl, hf] at h
  have huniq := gen_ok_unique h h6
  have hs := gen_op6_one_size (n + 2) h3 h1 h6
  rw [huniq.1, hs, gen_op3_size (n + 1) h0 (by simpa [op3] using h3),
    gen_op0_size n (fib_slot7 fibN1) h0, size_fib_halt (fibPushed fibN2) h1]

theorem size_fib_body_n2 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 4) (fibPushed fibN2) fibBody =
      .ok (t, fibF1)) :
    t.size = 7 := by
  have h0 := fib_gen_op0 (K := K) (n + 1) (fib_slot3 fibN2)
  have h3 := gen_op3 (K := K) (n + 2) h0
  have hI := fib_gen_inner_n2 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 3) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  have huniq := gen_ok_unique h h6
  have hs := gen_op6_zero_size (n + 3) h3 hI h6
  rw [huniq.1, hs, gen_op3_size (n + 2) h0 (by simpa [op3] using h3),
    gen_op0_size (n + 1) (fib_slot3 fibN2) h0, size_fib_inner_n2 hI]

theorem size_fib_recSample {n : ℕ} (rest : Noun)
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 2)
      (fibPushed (.cell (.atom 0) rest)) fibRecSample = .ok (t, res)) :
    t.size = 3 := by
  have h2 := fib_gen_op0 (K := K) n (fib_slot2 (.cell (.atom 0) rest))
  have h7 := fib_gen_op0 (K := K) n (fib_slot7 rest)
  have hc := gen_cons (K := K) (n + 1) h2 h7
  have hf : fibRecSample = .cell (.cell (.atom 0) (.atom 2)) (op0 7) := by
    simp [fibRecSample, op0]
  rw [hf] at h
  have huniq := gen_ok_unique h hc
  have hs := gen_cons_size (n + 1) h2 h7 hc
  rw [huniq.1, hs, gen_op0_size n (fib_slot2 (.cell (.atom 0) rest)) h2,
    gen_op0_size n (fib_slot7 rest) h7]

theorem size_fib_rec_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 5) (fibPushed fibN3) fibRec =
      .ok (t, fibF1)) :
    t.size = 12 := by
  have hsamp := fib_gen_recSample (K := K) (n + 2) fibN2
  have hc := fib_gen_op0 (K := K) (n + 3) (fib_slot2 fibN3)
  have hm := fib_gen_body_n2 (K := K) n
  have h2g := gen_op2 (K := K) (n + 4) hsamp hc hm
  have h' :
      genComputeSkeleton (K := K) (n + 5) (fibPushed (.cell (.atom 0) fibN2)) fibRec =
        .ok (t, fibF1) := by
    simpa [fibN3] using h
  have huniq := gen_ok_unique h' (by simpa [fibRec, op2] using h2g)
  have hs := gen_op2_size (n + 4) hsamp hc hm h2g
  rw [huniq.1, hs, size_fib_recSample (n := n + 2) fibN2
      (by simpa [fibN3, fibN2] using hsamp),
    gen_op0_size (n + 3) (fib_slot2 fibN3) hc, size_fib_body_n2 hm]

theorem size_fib_inc_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (fibPushed fibN3) fibInc =
      .ok (t, fibF2)) :
    t.size = 13 := by
  have hr := fib_gen_rec_n3 (K := K) n
  have h4 := gen_op4 (K := K) (n + 5) hr fib_lus_1
  have huniq := gen_ok_unique h (by simpa [fibInc] using h4)
  have hs := gen_op4_size (n + 5) hr fib_lus_1 h4
  rw [huniq.1, hs, size_fib_rec_n3 hr]

theorem size_fib_inner_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 7) (fibPushed fibN3) fibInner =
      .ok (t, fibF2)) :
    t.size = 16 := by
  have h0 := fib_gen_op0 (K := K) (n + 4) (fib_slot7 fibN2)
  have h3 := gen_op3 (K := K) (n + 5) h0
  have hi := fib_gen_inc_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 6) (d := fibHalt) h3 hi
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN3 = .cell (.atom 0) fibN2 from rfl, hf] at h
  have huniq := gen_ok_unique h h6
  have hs := gen_op6_zero_size (n + 6) h3 hi h6
  rw [huniq.1, hs, gen_op3_size (n + 5) h0 (by simpa [op3] using h3),
    gen_op0_size (n + 4) (fib_slot7 fibN2) h0, size_fib_inc_n3 hi]

theorem size_fib_body_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 8) (fibPushed fibN3) fibBody =
      .ok (t, fibF2)) :
    t.size = 19 := by
  have h0 := fib_gen_op0 (K := K) (n + 5) (fib_slot3 fibN3)
  have h3 := gen_op3 (K := K) (n + 6) h0
  have hI := fib_gen_inner_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 7) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  have huniq := gen_ok_unique h h6
  have hs := gen_op6_zero_size (n + 7) h3 hI h6
  rw [huniq.1, hs, gen_op3_size (n + 6) h0 (by simpa [op3] using h3),
    gen_op0_size (n + 5) (fib_slot3 fibN3) h0, size_fib_inner_n3 hI]

theorem size_fib_rec_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 9) (fibPushed fibN4) fibRec =
      .ok (t, fibF2)) :
    t.size = 24 := by
  have hsamp := fib_gen_recSample (K := K) (n + 6) fibN3
  have hc := fib_gen_op0 (K := K) (n + 7) (fib_slot2 fibN4)
  have hm := fib_gen_body_n3 (K := K) n
  have h2g := gen_op2 (K := K) (n + 8) hsamp hc hm
  have h' :
      genComputeSkeleton (K := K) (n + 9) (fibPushed (.cell (.atom 0) fibN3)) fibRec =
        .ok (t, fibF2) := by
    simpa [fibN4] using h
  have huniq := gen_ok_unique h' (by simpa [fibRec, op2] using h2g)
  have hs := gen_op2_size (n + 8) hsamp hc hm h2g
  rw [huniq.1, hs, size_fib_recSample (n := n + 6) fibN3
      (by simpa [fibN4, fibN3] using hsamp),
    gen_op0_size (n + 7) (fib_slot2 fibN4) hc, size_fib_body_n3 hm]

theorem size_fib_inc_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 10) (fibPushed fibN4) fibInc =
      .ok (t, fibF3)) :
    t.size = 25 := by
  have hr := fib_gen_rec_n4 (K := K) n
  have h4 := gen_op4 (K := K) (n + 9) hr fib_lus_2
  have huniq := gen_ok_unique h (by simpa [fibInc] using h4)
  have hs := gen_op4_size (n + 9) hr fib_lus_2 h4
  rw [huniq.1, hs, size_fib_rec_n4 hr]

theorem size_fib_inner_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 11) (fibPushed fibN4) fibInner =
      .ok (t, fibF3)) :
    t.size = 28 := by
  have h0 := fib_gen_op0 (K := K) (n + 8) (fib_slot7 fibN3)
  have h3 := gen_op3 (K := K) (n + 9) h0
  have hi := fib_gen_inc_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 10) (d := fibHalt) h3 hi
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN4 = .cell (.atom 0) fibN3 from rfl, hf] at h
  have huniq := gen_ok_unique h h6
  have hs := gen_op6_zero_size (n + 10) h3 hi h6
  rw [huniq.1, hs, gen_op3_size (n + 9) h0 (by simpa [op3] using h3),
    gen_op0_size (n + 8) (fib_slot7 fibN3) h0, size_fib_inc_n4 hi]

theorem size_fib_body_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 12) (fibPushed fibN4) fibBody =
      .ok (t, fibF3)) :
    t.size = 31 := by
  have h0 := fib_gen_op0 (K := K) (n + 9) (fib_slot3 fibN4)
  have h3 := gen_op3 (K := K) (n + 10) h0
  have hI := fib_gen_inner_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 11) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  have huniq := gen_ok_unique h h6
  have hs := gen_op6_zero_size (n + 11) h3 hI h6
  rw [huniq.1, hs, gen_op3_size (n + 10) h0 (by simpa [op3] using h3),
    gen_op0_size (n + 9) (fib_slot3 fibN4) h0, size_fib_inner_n4 hI]

/-- The compiled n = 4 tree has 33 compute rows. -/
theorem fibTree_size : (fibTree (K := K)).size = 33 := by
  have hq := gen_quote (K := K) 30 fibSubject fibBody
  have hb := fib_gen_body_n4 (K := K) 19
  have h8 := gen_op8 (K := K) 31 hq hb
  have huniq := gen_ok_unique (fibTree_eq (K := K))
    (by simpa [fibFormula, op8] using h8)
  have hs := gen_op8_size 31 hq hb h8
  rw [huniq.1, hs, gen_quote_size 30 fibSubject fibBody hq, size_fib_body_n4 hb]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.fibTree_size
