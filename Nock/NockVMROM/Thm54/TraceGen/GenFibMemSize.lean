/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibMemSize.lean

  Served-memory length/size of the compiled Peano-fib
  tree, combinator induction along `fib_gen_*`.  Assigned = unassigned
  via `genMemoryForest_eq_thread`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenFibSize
import Nock.NockVMROM.Thm54.TraceGen.GenFibKit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

theorem nounWalkSize_fibHalt : nounWalkSize fibHalt = 3 := by
  simp [fibHalt, op1, nounWalkSize]

theorem nounWalkSize_op3_op0 (ax : ℕ) : nounWalkSize (op3 (op0 ax)) = 5 := by
  simp [op3, op0, nounWalkSize]

theorem nounWalkSize_fibRecSample : nounWalkSize fibRecSample = 7 := by
  simp [fibRecSample, op0, nounWalkSize]

theorem nounWalkSize_fibRec : nounWalkSize fibRec = 13 := by
  simp [fibRec, op2, fibRecSample, op0, nounWalkSize]

theorem nounWalkSize_fibInc : nounWalkSize fibInc = 15 := by
  simp [fibInc, op4, fibRec, op2, fibRecSample, op0, nounWalkSize]

theorem nounWalkSize_fibInner : nounWalkSize fibInner = 27 := by
  simp [fibInner, op6, op3, op0, fibInc, op4, fibRec, op2, fibRecSample,
    fibHalt, op1, nounWalkSize]

theorem nounWalkSize_fibBody : nounWalkSize fibBody = 39 := by
  simp [fibBody, op6, op3, op0, fibInner, fibInc, op4, fibRec, op2,
    fibRecSample, fibHalt, op1, nounWalkSize]

theorem nounWalkSize_fibN1 : nounWalkSize fibN1 = 1 := rfl
theorem nounWalkSize_fibN2 : nounWalkSize fibN2 = 3 := by
  simp [fibN2, nounWalkSize]
theorem nounWalkSize_fibN3 : nounWalkSize fibN3 = 5 := by
  simp [fibN3, fibN2, nounWalkSize]
theorem nounWalkSize_fibN4 : nounWalkSize fibN4 = 7 := by
  simp [fibN4, fibN3, fibN2, nounWalkSize]

theorem nounWalkSize_fibPushed (n : Noun) :
    nounWalkSize (fibPushed n) = 40 + nounWalkSize n := by
  simp [fibPushed, nounWalkSize, nounWalkSize_fibBody]

theorem recordTreeSize_axis7 (hd tl child : Noun) :
    recordTreeSize (.cell hd tl) child 7 =
      2 + nounWalkSize hd + descentForestSize child tl 3 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_seven)]
  simp [axisRest_seven, formulaHead, formulaTail]
  omega

theorem nounWalkSize_cond3 : nounWalkSize ((Noun.atom 3).cell (op0 3)) = 5 := by
  simp [op0, nounWalkSize]

theorem nounWalkSize_cond7 : nounWalkSize ((Noun.atom 3).cell (op0 7)) = 5 := by
  simp [op0, nounWalkSize]

theorem descentForestSize_cell0_axis3 (rest : Noun) :
    descentForestSize rest (.cell (.atom 0) rest) 3 = 3 + nounWalkSize rest := by
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three, formulaHead, formulaTail]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [nounWalkSize]
  omega

theorem recordTreeSize_pushed_axis3 (n : Noun) :
    recordTreeSize (fibPushed n) n 3 = 42 + nounWalkSize n := by
  simp [fibPushed, recordTreeSize_axis3, nounWalkSize_fibBody]

theorem recordTreeSize_pushed_axis2 (n : Noun) :
    recordTreeSize (fibPushed n) fibBody 2 = 42 + nounWalkSize n := by
  simp [fibPushed, recordTreeSize_axis2, nounWalkSize_fibBody]

theorem recordTreeSize_pushed_axis7 (rest : Noun) :
    recordTreeSize (fibPushed (.cell (.atom 0) rest)) rest 7 =
      44 + nounWalkSize rest := by
  simp [fibPushed, recordTreeSize_axis7, nounWalkSize_fibBody,
    descentForestSize_cell0_axis3]
  omega

theorem atom_ne_pushed (ax : ℕ) (n : Noun) :
    Noun.atom ax ≠ fibPushed n := by
  simp [fibPushed]

theorem mem_fib_halt (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} (s : Noun) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 1) s fibHalt = .ok (t, fibF1)) :
    (genMemForestFromTree E z α lmb t).length = 1 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 5 :=
  gen_op1_mem E z α n s 1 (by simpa [fibHalt] using h)

theorem mem_fib_body_n1 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN1) fibBody =
      .ok (t, fibF1)) :
    (genMemForestFromTree E z α lmb t).length = 6 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 136 := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot3 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN1)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInner) h3 h1
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  have hm := gen_op6_one_mem (lmb := lmb) E z α (n + 2) h3 h1 h
  have h0m := gen_op0_mem (lmb := lmb) E z α n (fib_slot3 fibN1) h0 (atom_ne_pushed 3 fibN1)
  have h3m := gen_op3_mem (lmb := lmb) E z α (n + 1) h0 (by simpa [op3] using h3)
  have h1m := mem_fib_halt (lmb := lmb) E z α (fibPushed fibN1) h1
  rcases h0m with ⟨h0l, h0s⟩
  rcases h3m with ⟨h3l, h3s⟩
  rcases h1m with ⟨h1l, h1s⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_cond3, nounWalkSize_fibInner, nounWalkSize_fibHalt,
      h3s, h0s, recordTreeSize_pushed_axis3, nounWalkSize_fibN1, h1s] at hs
    exact hs

theorem mem_fib_inner_n2 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN2) fibInner =
      .ok (t, fibF1)) :
    (genMemForestFromTree E z α lmb t).length = 6 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 114 := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot7 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN2)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInc) h3 h1
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN2 = .cell (.atom 0) fibN1 from rfl, hf] at h
  have hm := gen_op6_one_mem (lmb := lmb) E z α (n + 2) h3 h1 h
  have h0m := gen_op0_mem (lmb := lmb) E z α n (fib_slot7 fibN1) h0 (atom_ne_pushed 7 fibN2)
  have h3m := gen_op3_mem (lmb := lmb) E z α (n + 1) h0 (by simpa [op3] using h3)
  have h1m := mem_fib_halt (lmb := lmb) E z α (fibPushed fibN2) h1
  rcases h0m with ⟨h0l, h0s⟩
  rcases h3m with ⟨h3l, h3s⟩
  rcases h1m with ⟨h1l, h1s⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_cond7, nounWalkSize_fibInc, nounWalkSize_fibHalt,
      h3s, h0s, recordTreeSize_pushed_axis7, nounWalkSize_fibN1, h1s] at hs
    exact hs

theorem mem_fib_body_n2 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 4) (fibPushed fibN2) fibBody =
      .ok (t, fibF1)) :
    (genMemForestFromTree E z α lmb t).length = 11 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 247 := by
  have h0 := fib_gen_op0 (K := K) (n + 1) (fib_slot3 fibN2)
  have h3 := gen_op3 (K := K) (n + 2) h0
  have hI := fib_gen_inner_n2 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 3) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  have hm := gen_op6_zero_mem (lmb := lmb) E z α (n + 3) h3 hI h
  have h0m := gen_op0_mem (lmb := lmb) E z α (n + 1) (fib_slot3 fibN2) h0 (atom_ne_pushed 3 fibN2)
  have h3m := gen_op3_mem (lmb := lmb) E z α (n + 2) h0 (by simpa [op3] using h3)
  have hIm := mem_fib_inner_n2 (lmb := lmb) E z α hI
  rcases h0m with ⟨h0l, h0s⟩
  rcases h3m with ⟨h3l, h3s⟩
  rcases hIm with ⟨hIl, hIs⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_cond3, nounWalkSize_fibInner, nounWalkSize_fibHalt,
      h3s, h0s, recordTreeSize_pushed_axis3, nounWalkSize_fibN2, hIs] at hs
    exact hs

theorem mem_fib_recSample (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} (rest : Noun) {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 2)
      (fibPushed (.cell (.atom 0) rest)) fibRecSample = .ok (t, res)) :
    (genMemForestFromTree E z α lmb t).length = 5 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        107 + 2 * nounWalkSize rest := by
  have h2 := fib_gen_op0 (K := K) n (fib_slot2 (.cell (.atom 0) rest))
  have h7 := fib_gen_op0 (K := K) n (fib_slot7 rest)
  have hc := gen_cons (K := K) (n + 1) h2 h7
  have hf : fibRecSample = .cell (.cell (.atom 0) (.atom 2)) (op0 7) := by
    simp [fibRecSample, op0]
  rw [hf] at h
  have hm := gen_cons_mem (lmb := lmb) E z α (n + 1) h2 h7 h
  have h2m := gen_op0_mem (lmb := lmb) E z α n (fib_slot2 (.cell (.atom 0) rest)) h2
    (atom_ne_pushed 2 (.cell (.atom 0) rest))
  have h7m := gen_op0_mem (lmb := lmb) E z α n (fib_slot7 rest) h7
    (atom_ne_pushed 7 (.cell (.atom 0) rest))
  rcases h2m with ⟨h2l, h2s⟩
  rcases h7m with ⟨h7l, h7s⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · have hnwsL : nounWalkSize ((Noun.atom 0).cell (Noun.atom 2)) = 3 := by
      simp [nounWalkSize]
    rw [hnwsL, nounWalkSize_op0, h2s, h7s, recordTreeSize_pushed_axis2,
      recordTreeSize_pushed_axis7] at hs
    simp [nounWalkSize] at hs
    omega

theorem mem_fib_rec_n3 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 5) (fibPushed fibN3) fibRec =
      .ok (t, fibF1)) :
    (genMemForestFromTree E z α lmb t).length = 19 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 429 := by
  have hsamp := fib_gen_recSample (K := K) (n + 2) fibN2
  have hc := fib_gen_op0 (K := K) (n + 3) (fib_slot2 fibN3)
  have hm := fib_gen_body_n2 (K := K) n
  have h2g := gen_op2 (K := K) (n + 4) hsamp hc hm
  have h' :
      genComputeSkeleton (K := K) (n + 5) (fibPushed (.cell (.atom 0) fibN2))
        fibRec = .ok (t, fibF1) := by
    simpa [fibN3] using h
  have hf : fibRec = op2 fibRecSample (op0 2) := rfl
  rw [hf] at h'
  have h2m := gen_op2_mem (lmb := lmb) E z α (n + 4) hsamp hc hm (by simpa [op2] using h')
  have hsm := mem_fib_recSample (lmb := lmb) E z α (n := n + 2) fibN2 hsamp
  have hcm := gen_op0_mem (lmb := lmb) E z α (n + 3) (fib_slot2 fibN3) hc (atom_ne_pushed 2 fibN3)
  have hmm := mem_fib_body_n2 (lmb := lmb) E z α hm
  rcases hsm with ⟨hsl, hss⟩
  rcases hcm with ⟨hcl, hcs⟩
  rcases hmm with ⟨hml, hms⟩
  rcases h2m with ⟨hl, hs⟩
  constructor
  · omega
  · rw [hss, hcs, hms, nounWalkSize_fibRecSample, nounWalkSize_op0,
      recordTreeSize_pushed_axis2, nounWalkSize_fibN3, nounWalkSize_fibN2] at hs
    exact hs

theorem mem_fib_inc_n3 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (fibPushed fibN3) fibInc =
      .ok (t, fibF2)) :
    (genMemForestFromTree E z α lmb t).length = 20 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 446 := by
  have hr := fib_gen_rec_n3 (K := K) n
  have h4 := gen_op4 (K := K) (n + 5) hr fib_lus_1
  have hf : fibInc = op4 fibRec := rfl
  rw [hf] at h
  have hm := gen_op4_mem (lmb := lmb) E z α (n + 5) hr fib_lus_1 h
  have hrm := mem_fib_rec_n3 (lmb := lmb) E z α hr
  rcases hrm with ⟨hrl, hrs⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_fibRec, hrs] at hs
    exact hs

theorem mem_fib_inner_n3 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 7) (fibPushed fibN3) fibInner =
      .ok (t, fibF2)) :
    (genMemForestFromTree E z α lmb t).length = 25 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 557 := by
  have h0 := fib_gen_op0 (K := K) (n + 4) (fib_slot7 fibN2)
  have h3 := gen_op3 (K := K) (n + 5) h0
  have hi := fib_gen_inc_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 6) (d := fibHalt) h3 hi
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN3 = .cell (.atom 0) fibN2 from rfl, hf] at h
  have hm := gen_op6_zero_mem (lmb := lmb) E z α (n + 6) h3 hi h
  have h0m := gen_op0_mem (lmb := lmb) E z α (n + 4) (fib_slot7 fibN2) h0 (atom_ne_pushed 7 fibN3)
  have h3m := gen_op3_mem (lmb := lmb) E z α (n + 5) h0 (by simpa [op3] using h3)
  have him := mem_fib_inc_n3 (lmb := lmb) E z α hi
  rcases h0m with ⟨h0l, h0s⟩
  rcases h3m with ⟨h3l, h3s⟩
  rcases him with ⟨hil, his⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_cond7, nounWalkSize_fibInc, nounWalkSize_fibHalt,
      h3s, h0s, recordTreeSize_pushed_axis7, nounWalkSize_fibN2, his] at hs
    exact hs

theorem mem_fib_body_n3 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 8) (fibPushed fibN3) fibBody =
      .ok (t, fibF2)) :
    (genMemForestFromTree E z α lmb t).length = 30 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 692 := by
  have h0 := fib_gen_op0 (K := K) (n + 5) (fib_slot3 fibN3)
  have h3 := gen_op3 (K := K) (n + 6) h0
  have hI := fib_gen_inner_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 7) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  have hm := gen_op6_zero_mem (lmb := lmb) E z α (n + 7) h3 hI h
  have h0m := gen_op0_mem (lmb := lmb) E z α (n + 5) (fib_slot3 fibN3) h0 (atom_ne_pushed 3 fibN3)
  have h3m := gen_op3_mem (lmb := lmb) E z α (n + 6) h0 (by simpa [op3] using h3)
  have hIm := mem_fib_inner_n3 (lmb := lmb) E z α hI
  rcases h0m with ⟨h0l, h0s⟩
  rcases h3m with ⟨h3l, h3s⟩
  rcases hIm with ⟨hIl, hIs⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_cond3, nounWalkSize_fibInner, nounWalkSize_fibHalt,
      h3s, h0s, recordTreeSize_pushed_axis3, nounWalkSize_fibN3, hIs] at hs
    exact hs

theorem mem_fib_rec_n4 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 9) (fibPushed fibN4) fibRec =
      .ok (t, fibF2)) :
    (genMemForestFromTree E z α lmb t).length = 38 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 880 := by
  have hsamp := fib_gen_recSample (K := K) (n + 6) fibN3
  have hc := fib_gen_op0 (K := K) (n + 7) (fib_slot2 fibN4)
  have hm := fib_gen_body_n3 (K := K) n
  have h2g := gen_op2 (K := K) (n + 8) hsamp hc hm
  have h' :
      genComputeSkeleton (K := K) (n + 9) (fibPushed (.cell (.atom 0) fibN3))
        fibRec = .ok (t, fibF2) := by
    simpa [fibN4] using h
  have hf : fibRec = op2 fibRecSample (op0 2) := rfl
  rw [hf] at h'
  have h2m := gen_op2_mem (lmb := lmb) E z α (n + 8) hsamp hc hm (by simpa [op2] using h')
  have hsm := mem_fib_recSample (lmb := lmb) E z α (n := n + 6) fibN3 hsamp
  have hcm := gen_op0_mem (lmb := lmb) E z α (n + 7) (fib_slot2 fibN4) hc (atom_ne_pushed 2 fibN4)
  have hmm := mem_fib_body_n3 (lmb := lmb) E z α hm
  rcases hsm with ⟨hsl, hss⟩
  rcases hcm with ⟨hcl, hcs⟩
  rcases hmm with ⟨hml, hms⟩
  rcases h2m with ⟨hl, hs⟩
  constructor
  · omega
  · rw [hss, hcs, hms, nounWalkSize_fibRecSample, nounWalkSize_op0,
      recordTreeSize_pushed_axis2, nounWalkSize_fibN4, nounWalkSize_fibN3] at hs
    exact hs

theorem mem_fib_inc_n4 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 10) (fibPushed fibN4) fibInc =
      .ok (t, fibF3)) :
    (genMemForestFromTree E z α lmb t).length = 39 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 897 := by
  have hr := fib_gen_rec_n4 (K := K) n
  have h4 := gen_op4 (K := K) (n + 9) hr fib_lus_2
  have hf : fibInc = op4 fibRec := rfl
  rw [hf] at h
  have hm := gen_op4_mem (lmb := lmb) E z α (n + 9) hr fib_lus_2 h
  have hrm := mem_fib_rec_n4 (lmb := lmb) E z α hr
  rcases hrm with ⟨hrl, hrs⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_fibRec, hrs] at hs
    exact hs

theorem mem_fib_inner_n4 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 11) (fibPushed fibN4) fibInner =
      .ok (t, fibF3)) :
    (genMemForestFromTree E z α lmb t).length = 44 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 1010 := by
  have h0 := fib_gen_op0 (K := K) (n + 8) (fib_slot7 fibN3)
  have h3 := gen_op3 (K := K) (n + 9) h0
  have hi := fib_gen_inc_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 10) (d := fibHalt) h3 hi
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN4 = .cell (.atom 0) fibN3 from rfl, hf] at h
  have hm := gen_op6_zero_mem (lmb := lmb) E z α (n + 10) h3 hi h
  have h0m := gen_op0_mem (lmb := lmb) E z α (n + 8) (fib_slot7 fibN3) h0 (atom_ne_pushed 7 fibN4)
  have h3m := gen_op3_mem (lmb := lmb) E z α (n + 9) h0 (by simpa [op3] using h3)
  have him := mem_fib_inc_n4 (lmb := lmb) E z α hi
  rcases h0m with ⟨h0l, h0s⟩
  rcases h3m with ⟨h3l, h3s⟩
  rcases him with ⟨hil, his⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_cond7, nounWalkSize_fibInc, nounWalkSize_fibHalt,
      h3s, h0s, recordTreeSize_pushed_axis7, nounWalkSize_fibN3, his] at hs
    exact hs

theorem mem_fib_body_n4 (E : Noun → ComputeTable.FP K) (z α : K)
    {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 12) (fibPushed fibN4) fibBody =
      .ok (t, fibF3)) :
    (genMemForestFromTree E z α lmb t).length = 49 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 1147 := by
  have h0 := fib_gen_op0 (K := K) (n + 9) (fib_slot3 fibN4)
  have h3 := gen_op3 (K := K) (n + 10) h0
  have hI := fib_gen_inner_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 11) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  have hm := gen_op6_zero_mem (lmb := lmb) E z α (n + 11) h3 hI h
  have h0m := gen_op0_mem (lmb := lmb) E z α (n + 9) (fib_slot3 fibN4) h0 (atom_ne_pushed 3 fibN4)
  have h3m := gen_op3_mem (lmb := lmb) E z α (n + 10) h0 (by simpa [op3] using h3)
  have hIm := mem_fib_inner_n4 (lmb := lmb) E z α hI
  rcases h0m with ⟨h0l, h0s⟩
  rcases h3m with ⟨h3l, h3s⟩
  rcases hIm with ⟨hIl, hIs⟩
  rcases hm with ⟨hl, hs⟩
  constructor
  · omega
  · rw [nounWalkSize_cond3, nounWalkSize_fibInner, nounWalkSize_fibHalt,
      h3s, h0s, recordTreeSize_pushed_axis3, nounWalkSize_fibN4, hIs] at hs
    exact hs

/-- Unassigned memory forest of the compiled n = 4 tree. -/
theorem fibMemForest_unassigned (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (fibTree (K := K))).length = 51 ∧
      totalSize (genMemForestFromTree E z α lmb (fibTree (K := K))) = 1277 := by
  have hq := gen_quote (K := K) 30 fibSubject fibBody
  have hb := fib_gen_body_n4 (K := K) 19
  have h8 := gen_op8 (K := K) 31 hq hb
  have huniq := gen_ok_unique (fibTree_eq (K := K))
    (by simpa [fibFormula, op8] using h8)
  have hm := gen_op8_mem (lmb := lmb) E z α 31 hq hb (by simpa [op8] using h8)
  have hqm := gen_quote_mem (lmb := lmb) E z α 30 fibSubject fibBody hq
  have hbm := mem_fib_body_n4 (lmb := lmb) E z α hb
  rcases hqm with ⟨hql, hqs⟩
  rcases hbm with ⟨hbl, hbs⟩
  rcases hm with ⟨hl, hs⟩
  rw [huniq.1]
  constructor
  · omega
  · rw [hqs, hbs, nounWalkSize_quote, nounWalkSize_fibBody] at hs
    exact hs

theorem fibMemForest_assigned_length (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb
      (bfsAssign (airReorder (fibTree (K := K))))).length = 51 := by
  rw [genMemForestFromTree_eq_bfsLen, (bfsAssign_rowForest_sum E z α _).2,
    ← genMemForestFromTree_eq_bfsLen, ← treeMemLen_eq, airReorder_treeMemLen,
    treeMemLen_eq]
  exact (fibMemForest_unassigned E z α).1

theorem fibMemForest_assigned_totalSize (E : Noun → ComputeTable.FP K) (z α : K) :
    totalSize (genMemForestFromTree E z α lmb
      (bfsAssign (airReorder (fibTree (K := K))))) = 1277 := by
  rw [genMemForestFromTree_eq_bfsSum, (bfsAssign_rowForest_sum E z α _).1,
    ← genMemForestFromTree_eq_bfsSum, ← treeMemSize_eq, airReorder_treeMemSize,
    treeMemSize_eq]
  exact (fibMemForest_unassigned E z α).2

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.fibMemForest_unassigned
#print axioms Nock.NockVMROM.Thm54.TraceGen.fibMemForest_assigned_totalSize
