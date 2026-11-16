/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibGoldilocksHbad.lean

  `TraceSep` / `hbad` at `seedZ` for the Peano-fib tree.
  No OP5.  OP6 branches differ by leaf count (inner 14 vs halt 2;
  inc 8 vs halt 2).  Completeness, not a new bound summand.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenFibGoldilocksSeed
import Nock.NockVMROM.Thm54.TraceGen.GenGenericOffdiag
import Nock.NockVMROM.Thm54.GoldilocksParameters

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

theorem sep_inner_halt :
    GlobalCarryRecognizer.SepSeed seedZ fibInner fibHalt := by
  refine sepSeed_of_leaves_ne seedZ seedZ_ne_zero ?_ ?_
  · rw [fibInner_leaves, fibHalt_leaves]; decide
  · simp [leafGap, fibInner_leaves, fibHalt_leaves]
    rw [seedZ_order]
    exact not_dvd_pow32 12 (by decide) (by decide)

theorem sep_inc_halt :
    GlobalCarryRecognizer.SepSeed seedZ fibInc fibHalt := by
  refine sepSeed_of_leaves_ne seedZ seedZ_ne_zero ?_ ?_
  · rw [fibInc_leaves, fibHalt_leaves]; decide
  · simp [leafGap, fibInc_leaves, fibHalt_leaves]
    rw [seedZ_order]
    exact not_dvd_pow32 6 (by decide) (by decide)

theorem sep_fib_halt {n : ℕ} (s : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 1) s fibHalt = .ok (t, fibF1)) :
    TraceSep seedZ t :=
  traceSep_gen_op1 (by simpa [fibHalt] using h)

theorem sep_fib_body_n1 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN1) fibBody =
      .ok (t, fibF1)) :
    TraceSep seedZ t := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot3 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN1)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInner) h3 h1
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  exact traceSep_gen_op6_one h3 h1 h
    (traceSep_gen_op3 h0 (by simpa [op3] using h3)
      (traceSep_gen_op0 (fib_slot3 fibN1) h0))
    (sep_fib_halt (fibPushed fibN1) h1) sep_inner_halt

theorem sep_fib_inner_n2 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN2) fibInner =
      .ok (t, fibF1)) :
    TraceSep seedZ t := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot7 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN2)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInc) h3 h1
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN2 = .cell (.atom 0) fibN1 from rfl, hf] at h
  exact traceSep_gen_op6_one h3 h1 h
    (traceSep_gen_op3 h0 (by simpa [op3] using h3)
      (traceSep_gen_op0 (fib_slot7 fibN1) h0))
    (sep_fib_halt (fibPushed fibN2) h1) sep_inc_halt

theorem sep_fib_body_n2 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 4) (fibPushed fibN2) fibBody =
      .ok (t, fibF1)) :
    TraceSep seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 1) (fib_slot3 fibN2)
  have h3 := gen_op3 (K := K) (n + 2) h0
  have hI := fib_gen_inner_n2 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 3) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  exact traceSep_gen_op6_zero h3 hI h
    (traceSep_gen_op3 h0 (by simpa [op3] using h3)
      (traceSep_gen_op0 (fib_slot3 fibN2) h0))
    (sep_fib_inner_n2 hI) sep_inner_halt

theorem sep_fib_recSample {n : ℕ} (rest : Noun)
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 2)
      (fibPushed (.cell (.atom 0) rest)) fibRecSample = .ok (t, res)) :
    TraceSep seedZ t := by
  have h2 := fib_gen_op0 (K := K) n (fib_slot2 (.cell (.atom 0) rest))
  have h7 := fib_gen_op0 (K := K) n (fib_slot7 rest)
  have hc := gen_cons (K := K) (n + 1) h2 h7
  have hf : fibRecSample = .cell (.cell (.atom 0) (.atom 2)) (op0 7) := by
    simp [fibRecSample, op0]
  rw [hf] at h
  exact traceSep_gen_cons h2 h7 h
    (traceSep_gen_op0 (fib_slot2 (.cell (.atom 0) rest)) h2)
    (traceSep_gen_op0 (fib_slot7 rest) h7)

theorem sep_fib_rec_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 5) (fibPushed fibN3) fibRec =
      .ok (t, fibF1)) :
    TraceSep seedZ t := by
  have hsamp := fib_gen_recSample (K := K) (n + 2) fibN2
  have hc := fib_gen_op0 (K := K) (n + 3) (fib_slot2 fibN3)
  have hm := fib_gen_body_n2 (K := K) n
  have h' :
      genComputeSkeleton (K := K) (n + 5) (fibPushed (.cell (.atom 0) fibN2)) fibRec =
        .ok (t, fibF1) := by
    simpa [fibN3] using h
  have hf : fibRec = op2 fibRecSample (op0 2) := rfl
  rw [hf] at h'
  exact traceSep_gen_op2 hsamp hc (fib_gen_body_n2 (K := K) n)
    (by simpa [op2] using h')
    (sep_fib_recSample (n := n + 2) fibN2
      (by simpa [fibN3, fibN2] using hsamp))
    (traceSep_gen_op0 (fib_slot2 fibN3) hc) (sep_fib_body_n2 hm)

theorem sep_fib_inc_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (fibPushed fibN3) fibInc =
      .ok (t, fibF2)) :
    TraceSep seedZ t := by
  have hr := fib_gen_rec_n3 (K := K) n
  have hf : fibInc = op4 fibRec := rfl
  rw [hf] at h
  exact traceSep_gen_op4 hr fib_lus_1 h (sep_fib_rec_n3 hr)

theorem sep_fib_inner_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 7) (fibPushed fibN3) fibInner =
      .ok (t, fibF2)) :
    TraceSep seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 4) (fib_slot7 fibN2)
  have h3 := gen_op3 (K := K) (n + 5) h0
  have hi := fib_gen_inc_n3 (K := K) n
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN3 = .cell (.atom 0) fibN2 from rfl, hf] at h
  exact traceSep_gen_op6_zero h3 hi h
    (traceSep_gen_op3 h0 (by simpa [op3] using h3)
      (traceSep_gen_op0 (fib_slot7 fibN2) h0))
    (sep_fib_inc_n3 hi) sep_inc_halt

theorem sep_fib_body_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 8) (fibPushed fibN3) fibBody =
      .ok (t, fibF2)) :
    TraceSep seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 5) (fib_slot3 fibN3)
  have h3 := gen_op3 (K := K) (n + 6) h0
  have hI := fib_gen_inner_n3 (K := K) n
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  exact traceSep_gen_op6_zero h3 hI h
    (traceSep_gen_op3 h0 (by simpa [op3] using h3)
      (traceSep_gen_op0 (fib_slot3 fibN3) h0))
    (sep_fib_inner_n3 hI) sep_inner_halt

theorem sep_fib_rec_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 9) (fibPushed fibN4) fibRec =
      .ok (t, fibF2)) :
    TraceSep seedZ t := by
  have hsamp := fib_gen_recSample (K := K) (n + 6) fibN3
  have hc := fib_gen_op0 (K := K) (n + 7) (fib_slot2 fibN4)
  have hm := fib_gen_body_n3 (K := K) n
  have h' :
      genComputeSkeleton (K := K) (n + 9) (fibPushed (.cell (.atom 0) fibN3)) fibRec =
        .ok (t, fibF2) := by
    simpa [fibN4] using h
  have hf : fibRec = op2 fibRecSample (op0 2) := rfl
  rw [hf] at h'
  exact traceSep_gen_op2 hsamp hc hm (by simpa [op2] using h')
    (sep_fib_recSample (n := n + 6) fibN3
      (by simpa [fibN4, fibN3] using hsamp))
    (traceSep_gen_op0 (fib_slot2 fibN4) hc) (sep_fib_body_n3 hm)

theorem sep_fib_inc_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 10) (fibPushed fibN4) fibInc =
      .ok (t, fibF3)) :
    TraceSep seedZ t := by
  have hr := fib_gen_rec_n4 (K := K) n
  have hf : fibInc = op4 fibRec := rfl
  rw [hf] at h
  exact traceSep_gen_op4 hr fib_lus_2 h (sep_fib_rec_n4 hr)

theorem sep_fib_inner_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 11) (fibPushed fibN4) fibInner =
      .ok (t, fibF3)) :
    TraceSep seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 8) (fib_slot7 fibN3)
  have h3 := gen_op3 (K := K) (n + 9) h0
  have hi := fib_gen_inc_n4 (K := K) n
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN4 = .cell (.atom 0) fibN3 from rfl, hf] at h
  exact traceSep_gen_op6_zero h3 hi h
    (traceSep_gen_op3 h0 (by simpa [op3] using h3)
      (traceSep_gen_op0 (fib_slot7 fibN3) h0))
    (sep_fib_inc_n4 hi) sep_inc_halt

theorem sep_fib_body_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 12) (fibPushed fibN4) fibBody =
      .ok (t, fibF3)) :
    TraceSep seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 9) (fib_slot3 fibN4)
  have h3 := gen_op3 (K := K) (n + 10) h0
  have hI := fib_gen_inner_n4 (K := K) n
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  exact traceSep_gen_op6_zero h3 hI h
    (traceSep_gen_op3 h0 (by simpa [op3] using h3)
      (traceSep_gen_op0 (fib_slot3 fibN4) h0))
    (sep_fib_inner_n4 hI) sep_inner_halt

theorem fibTree_traceSep : TraceSep seedZ (fibTree (K := K)) := by
  have hq := gen_quote (K := K) 30 fibSubject fibBody
  have hb := fib_gen_body_n4 (K := K) 19
  have h := fibTree_eq (K := K)
  have hf : fibFormula = op8 (quote fibBody) fibBody := rfl
  rw [hf] at h
  exact traceSep_gen_op8 hq hb (by simpa [op8] using h)
    (traceSep_gen_quote hq) (sep_fib_body_n4 hb)

theorem fib_hoff5 :
    ∀ g ∈ bfsRows (airReorder (fibTree (K := K))),
      g.skel.state = .s5 →
        GlobalCarryRecognizer.SepSeed seedZ
          (skeletonSubformula g.skel 0 TripleSlot.result)
          (skeletonSubformula g.skel 1 TripleSlot.result) := by
  refine (forall_bfsRows_iff (airReorder (fibTree (K := K)))).mpr ?_
  intro u hu hs5
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (fibTree (K := K)) u hu
  have hrow := fibTree_traceSep.1 u0 hu0
  simpa [hl] using hrow.1 (by simpa [hl] using hs5)

theorem fib_hoff6 :
    ∀ g ∈ bfsRows (airReorder (fibTree (K := K))),
      g.skel.state = .s6 →
        GlobalCarryRecognizer.SepSeed seedZ
          (skeletonDec g.skel .f_tth) (skeletonDec g.skel .f_ttt) := by
  refine (forall_bfsRows_iff (airReorder (fibTree (K := K)))).mpr ?_
  intro u hu hs6
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (fibTree (K := K)) u hu
  have hrow := fibTree_traceSep.1 u0 hu0
  simpa [hl] using hrow.2 (by simpa [hl] using hs6)

end Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks

#print axioms Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks.fibTree_traceSep
