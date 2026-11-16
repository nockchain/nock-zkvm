/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibGoldilocksSeed.lean

  `SeedGood` / `hout` at `φ(7^(2^32−1))` for the Peano-fib
  tree.  Dyck of the one cons is `encC_cell_atom_atom_dyck_ne` on `op0 2`.
  OP3 cell seeds use `¬(2^32 ∣ leaves−1)`.  `hout` is the order argument
  (`sizeWindowFailureSeeds_subset_lowOrderRootSeeds`): `orderOf seedZ = 2^32 > 42`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenFibConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenFibTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksSeed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

theorem op3_skel_result (s tail callResult : Noun) :
    skeletonSubformula
      (genSkelOp3 s (.cell (.atom 3) tail) (.atom 3) tail s tail
        callResult (Noun.wut callResult))
      0 TripleSlot.result = callResult := by
  simp [skeletonSubformula, genSkelOp3, ComputeTable.fanoutComp]

theorem op3_ok_atom (z : K) (s tail : Noun) (k : ℕ) :
    op3CallSizeOk z
      (genSkelOp3 s (.cell (.atom 3) tail) (.atom 3) tail s tail
        (.atom k) (Noun.wut (.atom k))) :=
  op3CallSizeOk_of_atom (op3_skel_result s tail (.atom k))

theorem op3_ok_cell (z : K) (s tail x y : Noun)
    (hz : z ≠ 0)
    (hord : ¬ orderOf z ∣ ((Noun.cell x y).leaves - 1)) :
    op3CallSizeOk z
      (genSkelOp3 s (.cell (.atom 3) tail) (.atom 3) tail s tail
        (.cell x y) (Noun.wut (.cell x y))) :=
  op3CallSizeOk_of_cell_order (op3_skel_result s tail (.cell x y)) hz hord

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.SizeWindowCounting
open ComputeTable

theorem cons_sample_dyck : (encC seedZ (.cell (.atom 0) (.atom 2))).dyck ≠ 0 :=
  encC_cell_atom_atom_dyck_ne seedZ seedZ_ne_zero 0 2

theorem not_dvd_pow32 (k : ℕ) (hk : 0 < k) (hle : k < 2 ^ 32) :
    ¬ (2 ^ 32 : ℕ) ∣ k :=
  Nat.not_dvd_of_pos_of_lt hk hle

theorem op3_ok_n1 (s tail : Noun) :
    op3CallSizeOk seedZ
      (genSkelOp3 s (.cell (.atom 3) tail) (.atom 3) tail s tail
        fibN1 (Noun.wut fibN1)) := by
  simpa [fibN1] using op3_ok_atom seedZ s tail 0

theorem op3_ok_n2 (s tail : Noun) :
    op3CallSizeOk seedZ
      (genSkelOp3 s (.cell (.atom 3) tail) (.atom 3) tail s tail
        fibN2 (Noun.wut fibN2)) := by
  refine op3_ok_cell seedZ s tail (.atom 0) (.atom 0) seedZ_ne_zero ?_
  rw [show (Noun.cell (.atom 0) (.atom 0)).leaves = 2 from by
    simp [cell_leaves, atom_leaves], seedZ_order]
  exact not_dvd_pow32 1 (by decide) (by decide)

theorem op3_ok_n3 (s tail : Noun) :
    op3CallSizeOk seedZ
      (genSkelOp3 s (.cell (.atom 3) tail) (.atom 3) tail s tail
        fibN3 (Noun.wut fibN3)) := by
  refine op3_ok_cell seedZ s tail (.atom 0) fibN2 seedZ_ne_zero ?_
  rw [show (Noun.cell (.atom 0) fibN2).leaves = 3 from by
    simp [cell_leaves, atom_leaves, fibN2_leaves], seedZ_order]
  exact not_dvd_pow32 2 (by decide) (by decide)

theorem op3_ok_n4 (s tail : Noun) :
    op3CallSizeOk seedZ
      (genSkelOp3 s (.cell (.atom 3) tail) (.atom 3) tail s tail
        fibN4 (Noun.wut fibN4)) := by
  refine op3_ok_cell seedZ s tail (.atom 0) fibN3 seedZ_ne_zero ?_
  rw [show (Noun.cell (.atom 0) fibN3).leaves = 4 from by
    simp [cell_leaves, atom_leaves, fibN3_leaves], seedZ_order]
  exact not_dvd_pow32 3 (by decide) (by decide)

theorem seed_fib_halt {n : ℕ} (s : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 1) s fibHalt = .ok (t, fibF1)) :
    SeedGood seedZ t :=
  seedGood_gen_op1 (by simpa [fibHalt] using h)

theorem seed_fib_body_n1 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN1) fibBody =
      .ok (t, fibF1)) :
    SeedGood seedZ t := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot3 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN1)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInner) h3 h1
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  exact seedGood_gen_op6_one h3 h1 h
    (seedGood_gen_op3 h0 (by simpa [op3] using h3)
      (seedGood_gen_op0 (fib_slot3 fibN1) h0) (op3_ok_n1 _ _))
    (seed_fib_halt (fibPushed fibN1) h1)

theorem seed_fib_inner_n2 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 3) (fibPushed fibN2) fibInner =
      .ok (t, fibF1)) :
    SeedGood seedZ t := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot7 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN2)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInc) h3 h1
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN2 = .cell (.atom 0) fibN1 from rfl, hf] at h
  exact seedGood_gen_op6_one h3 h1 h
    (seedGood_gen_op3 h0 (by simpa [op3] using h3)
      (seedGood_gen_op0 (fib_slot7 fibN1) h0) (op3_ok_n1 _ _))
    (seed_fib_halt (fibPushed fibN2) h1)

theorem seed_fib_body_n2 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 4) (fibPushed fibN2) fibBody =
      .ok (t, fibF1)) :
    SeedGood seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 1) (fib_slot3 fibN2)
  have h3 := gen_op3 (K := K) (n + 2) h0
  have hI := fib_gen_inner_n2 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 3) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  exact seedGood_gen_op6_zero h3 hI h
    (seedGood_gen_op3 h0 (by simpa [op3] using h3)
      (seedGood_gen_op0 (fib_slot3 fibN2) h0) (op3_ok_n2 _ _))
    (seed_fib_inner_n2 hI)

theorem seed_fib_recSample {n : ℕ} (rest : Noun)
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 2)
      (fibPushed (.cell (.atom 0) rest)) fibRecSample = .ok (t, res)) :
    SeedGood seedZ t := by
  have h2 := fib_gen_op0 (K := K) n (fib_slot2 (.cell (.atom 0) rest))
  have h7 := fib_gen_op0 (K := K) n (fib_slot7 rest)
  have hc := gen_cons (K := K) (n + 1) h2 h7
  have hf : fibRecSample = .cell (.cell (.atom 0) (.atom 2)) (op0 7) := by
    simp [fibRecSample, op0]
  rw [hf] at h
  exact seedGood_gen_cons h2 h7 h
    (seedGood_gen_op0 (fib_slot2 (.cell (.atom 0) rest)) h2)
    (seedGood_gen_op0 (fib_slot7 rest) h7) cons_sample_dyck

theorem seed_fib_rec_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 5) (fibPushed fibN3) fibRec =
      .ok (t, fibF1)) :
    SeedGood seedZ t := by
  have hsamp := fib_gen_recSample (K := K) (n + 2) fibN2
  have hc := fib_gen_op0 (K := K) (n + 3) (fib_slot2 fibN3)
  have hm := fib_gen_body_n2 (K := K) n
  have h2g := gen_op2 (K := K) (n + 4) hsamp hc hm
  have h' :
      genComputeSkeleton (K := K) (n + 5) (fibPushed (.cell (.atom 0) fibN2)) fibRec =
        .ok (t, fibF1) := by
    simpa [fibN3] using h
  have hf : fibRec = op2 fibRecSample (op0 2) := rfl
  rw [hf] at h'
  exact seedGood_gen_op2 hsamp hc hm (by simpa [op2] using h')
    (seed_fib_recSample (n := n + 2) fibN2
      (by simpa [fibN3, fibN2] using hsamp))
    (seedGood_gen_op0 (fib_slot2 fibN3) hc) (seed_fib_body_n2 hm)

theorem seed_fib_inc_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (fibPushed fibN3) fibInc =
      .ok (t, fibF2)) :
    SeedGood seedZ t := by
  have hr := fib_gen_rec_n3 (K := K) n
  have h4 := gen_op4 (K := K) (n + 5) hr fib_lus_1
  have hf : fibInc = op4 fibRec := rfl
  rw [hf] at h
  exact seedGood_gen_op4 hr fib_lus_1 h (seed_fib_rec_n3 hr)

theorem seed_fib_inner_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 7) (fibPushed fibN3) fibInner =
      .ok (t, fibF2)) :
    SeedGood seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 4) (fib_slot7 fibN2)
  have h3 := gen_op3 (K := K) (n + 5) h0
  have hi := fib_gen_inc_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 6) (d := fibHalt) h3 hi
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN3 = .cell (.atom 0) fibN2 from rfl, hf] at h
  exact seedGood_gen_op6_zero h3 hi h
    (seedGood_gen_op3 h0 (by simpa [op3] using h3)
      (seedGood_gen_op0 (fib_slot7 fibN2) h0) (op3_ok_n2 _ _))
    (seed_fib_inc_n3 hi)

theorem seed_fib_body_n3 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 8) (fibPushed fibN3) fibBody =
      .ok (t, fibF2)) :
    SeedGood seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 5) (fib_slot3 fibN3)
  have h3 := gen_op3 (K := K) (n + 6) h0
  have hI := fib_gen_inner_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 7) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  exact seedGood_gen_op6_zero h3 hI h
    (seedGood_gen_op3 h0 (by simpa [op3] using h3)
      (seedGood_gen_op0 (fib_slot3 fibN3) h0) (op3_ok_n3 _ _))
    (seed_fib_inner_n3 hI)

theorem seed_fib_rec_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 9) (fibPushed fibN4) fibRec =
      .ok (t, fibF2)) :
    SeedGood seedZ t := by
  have hsamp := fib_gen_recSample (K := K) (n + 6) fibN3
  have hc := fib_gen_op0 (K := K) (n + 7) (fib_slot2 fibN4)
  have hm := fib_gen_body_n3 (K := K) n
  have h2g := gen_op2 (K := K) (n + 8) hsamp hc hm
  have h' :
      genComputeSkeleton (K := K) (n + 9) (fibPushed (.cell (.atom 0) fibN3)) fibRec =
        .ok (t, fibF2) := by
    simpa [fibN4] using h
  have hf : fibRec = op2 fibRecSample (op0 2) := rfl
  rw [hf] at h'
  exact seedGood_gen_op2 hsamp hc hm (by simpa [op2] using h')
    (seed_fib_recSample (n := n + 6) fibN3
      (by simpa [fibN4, fibN3] using hsamp))
    (seedGood_gen_op0 (fib_slot2 fibN4) hc) (seed_fib_body_n3 hm)

theorem seed_fib_inc_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 10) (fibPushed fibN4) fibInc =
      .ok (t, fibF3)) :
    SeedGood seedZ t := by
  have hr := fib_gen_rec_n4 (K := K) n
  have h4 := gen_op4 (K := K) (n + 9) hr fib_lus_2
  have hf : fibInc = op4 fibRec := rfl
  rw [hf] at h
  exact seedGood_gen_op4 hr fib_lus_2 h (seed_fib_rec_n4 hr)

theorem seed_fib_inner_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 11) (fibPushed fibN4) fibInner =
      .ok (t, fibF3)) :
    SeedGood seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 8) (fib_slot7 fibN3)
  have h3 := gen_op3 (K := K) (n + 9) h0
  have hi := fib_gen_inc_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 10) (d := fibHalt) h3 hi
  have hf : fibInner = op6 (.cell (.atom 3) (op0 7)) fibInc fibHalt := by
    simp [fibInner, op3]
  rw [show fibN4 = .cell (.atom 0) fibN3 from rfl, hf] at h
  exact seedGood_gen_op6_zero h3 hi h
    (seedGood_gen_op3 h0 (by simpa [op3] using h3)
      (seedGood_gen_op0 (fib_slot7 fibN3) h0) (op3_ok_n3 _ _))
    (seed_fib_inc_n4 hi)

theorem seed_fib_body_n4 {n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 12) (fibPushed fibN4) fibBody =
      .ok (t, fibF3)) :
    SeedGood seedZ t := by
  have h0 := fib_gen_op0 (K := K) (n + 9) (fib_slot3 fibN4)
  have h3 := gen_op3 (K := K) (n + 10) h0
  have hI := fib_gen_inner_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 11) (d := fibHalt) h3 hI
  have hf : fibBody = op6 (.cell (.atom 3) (op0 3)) fibInner fibHalt := by
    simp [fibBody, op3]
  rw [hf] at h
  exact seedGood_gen_op6_zero h3 hI h
    (seedGood_gen_op3 h0 (by simpa [op3] using h3)
      (seedGood_gen_op0 (fib_slot3 fibN4) h0) (op3_ok_n4 _ _))
    (seed_fib_inner_n4 hI)

/-- `SeedGood` at the compiled n = 4 tree. -/
theorem fibTree_seedGood : SeedGood seedZ (fibTree (K := K)) := by
  have hq := gen_quote (K := K) 30 fibSubject fibBody
  have hb := fib_gen_body_n4 (K := K) 19
  have h8 := gen_op8 (K := K) 31 hq hb
  have hf : fibFormula = op8 (quote fibBody) fibBody := rfl
  have h := fibTree_eq (K := K)
  rw [hf] at h
  exact seedGood_gen_op8 hq hb (by simpa [op8] using h)
    (seedGood_gen_quote hq) (seed_fib_body_n4 hb)

variable [Fintype K] [DecidableEq K]

set_option linter.unusedSectionVars false

theorem fib_sizeWindowBound :
    SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (fibTree (K := K))))
        (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (fibTree (K := K))))
      42 :=
  genComputeSkeleton_sizeWindowBound_gen (by decide : 1 ≤ 42)
    (fibTree_eq (K := K)) (fib_traceConfined (K := K)) _

/-- `hout` — seed order above `Λ = 42`. -/
theorem fib_hout :
    seedZ ∉ sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder (fibTree (K := K))))
        (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (fibTree (K := K)))) := by
  intro h
  have hlo : seedZ ∉ lowOrderRootSeeds (K := K) 42 :=
    MatmulConfigGoldilocks.not_mem_lowOrderRootSeeds_of_order (seedZ_order_gt 42 (by decide))
  exact hlo (sizeWindowFailureSeeds_subset_lowOrderRootSeeds _ 42 fib_sizeWindowBound h)

end Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks

#print axioms Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks.fibTree_seedGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks.fib_hout
