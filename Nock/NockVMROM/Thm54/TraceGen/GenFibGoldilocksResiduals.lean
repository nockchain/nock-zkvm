/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibGoldilocksResiduals.lean

  Residual suppliers for `nockCompiles_p67` and
  `nockCompiles_of_grom_atTree_p62` at the Peano-fib program over
  Goldilocks.
-/
import Nock.Field
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.NockVMROM.Thm54.TraceGen.GenFibConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenFibGoldilocksHbad
import Nock.NockVMROM.Thm54.TraceGen.GenFibMemSize
import Nock.NockVMROM.Thm54.TraceGen.GenFibTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenGenericBounded
import Nock.NockVMROM.Thm54.TraceGen.GenGenericOffdiag
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenServedRoots
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemWeb

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen.FibConfigGoldilocks
open ComputeTable

/-! ## `evalGRom` along the generated spine. -/

theorem evalGRom_fib_halt (q n : ℕ) (s : Noun) :
    evalGRom q (n + 1) s fibHalt = some fibF1 :=
  evalGRom_op1 q n s 1

theorem evalGRom_fib_body_n1 (q n : ℕ) :
    evalGRom q (n + 3) (fibPushed fibN1) fibBody = some fibF1 := by
  have h0 := evalGRom_op0 q n 3 (fib_slot3 fibN1)
  have h3 := evalGRom_op3 (q := q) (n := n + 1) h0
  have h1 := evalGRom_fib_halt q (n + 1) (fibPushed fibN1)
  have h6 := evalGRom_op6_one q (n + 2) (c := fibInner) h3 h1
  simpa [fibBody, op3, op6, fib_wut_n1] using h6

theorem evalGRom_fib_inner_n2 (q n : ℕ) :
    evalGRom q (n + 3) (fibPushed fibN2) fibInner = some fibF1 := by
  have h0 := evalGRom_op0 q n 7 (fib_slot7 fibN1)
  have h3 := evalGRom_op3 (q := q) (n := n + 1) h0
  have h1 := evalGRom_fib_halt q (n + 1) (fibPushed fibN2)
  have h6 := evalGRom_op6_one q (n + 2) (c := fibInc) h3 h1
  simpa [fibInner, op3, op6, fib_wut_n1, fibN2, fibN1] using h6

theorem evalGRom_fib_body_n2 (q n : ℕ) :
    evalGRom q (n + 4) (fibPushed fibN2) fibBody = some fibF1 := by
  have h0 := evalGRom_op0 q (n + 1) 3 (fib_slot3 fibN2)
  have h3 := evalGRom_op3 (q := q) (n := n + 2) h0
  have hI := evalGRom_fib_inner_n2 q n
  have h6 := evalGRom_op6_zero q (n + 3) (d := fibHalt) h3 hI
  simpa [fibBody, op3, op6, fib_wut_n2] using h6

theorem evalGRom_fib_recSample (q n : ℕ) (rest : Noun) :
    evalGRom q (n + 2) (fibPushed (.cell (.atom 0) rest)) fibRecSample =
      some (fibPushed rest) := by
  have h2 := evalGRom_op0 q n 2 (fib_slot2 (.cell (.atom 0) rest))
  have h7 := evalGRom_op0 q n 7 (fib_slot7 rest)
  have hc := evalGRom_cons q (n + 1) h2 h7
  simpa [fibRecSample, op0, fibPushed] using hc

theorem evalGRom_fib_rec_n3 (q n : ℕ) :
    evalGRom q (n + 5) (fibPushed fibN3) fibRec = some fibF1 := by
  have hs := evalGRom_fib_recSample q (n + 2) fibN2
  have hc := evalGRom_op0 q (n + 3) 2 (fib_slot2 fibN3)
  have hm := evalGRom_fib_body_n2 q n
  have h2 := evalGRom_op2 (q := q) (n := n + 4) hs hc hm
  simpa [fibRec, op2, op0, fibN3, fibN2, fibPushed] using h2

theorem evalGRom_fib_inc_n3 (q n : ℕ)
    (hinc : FieldEmbedding.lusGBy q fibF1 = some fibF2) :
    evalGRom q (n + 6) (fibPushed fibN3) fibInc = some fibF2 := by
  have hr := evalGRom_fib_rec_n3 q n
  have h4 := evalGRom_op4 q (n + 5) hr hinc
  simpa [fibInc, op4] using h4

theorem evalGRom_fib_inner_n3 (q n : ℕ)
    (hinc : FieldEmbedding.lusGBy q fibF1 = some fibF2) :
    evalGRom q (n + 7) (fibPushed fibN3) fibInner = some fibF2 := by
  have h0 := evalGRom_op0 q (n + 4) 7 (fib_slot7 fibN2)
  have h3 := evalGRom_op3 (q := q) (n := n + 5) h0
  have hi := evalGRom_fib_inc_n3 q n hinc
  have h6 := evalGRom_op6_zero q (n + 6) (d := fibHalt) h3 hi
  simpa [fibInner, op3, op6, fib_wut_n2, fibN3, fibN2] using h6

theorem evalGRom_fib_body_n3 (q n : ℕ)
    (hinc : FieldEmbedding.lusGBy q fibF1 = some fibF2) :
    evalGRom q (n + 8) (fibPushed fibN3) fibBody = some fibF2 := by
  have h0 := evalGRom_op0 q (n + 5) 3 (fib_slot3 fibN3)
  have h3 := evalGRom_op3 (q := q) (n := n + 6) h0
  have hI := evalGRom_fib_inner_n3 q n hinc
  have h6 := evalGRom_op6_zero q (n + 7) (d := fibHalt) h3 hI
  simpa [fibBody, op3, op6, fib_wut_n3] using h6

theorem evalGRom_fib_rec_n4 (q n : ℕ)
    (hinc : FieldEmbedding.lusGBy q fibF1 = some fibF2) :
    evalGRom q (n + 9) (fibPushed fibN4) fibRec = some fibF2 := by
  have hs := evalGRom_fib_recSample q (n + 6) fibN3
  have hc := evalGRom_op0 q (n + 7) 2 (fib_slot2 fibN4)
  have hm := evalGRom_fib_body_n3 q n hinc
  have h2 := evalGRom_op2 (q := q) (n := n + 8) hs hc hm
  simpa [fibRec, op2, op0, fibN4, fibN3, fibPushed] using h2

theorem evalGRom_fib_inc_n4 (q n : ℕ)
    (hinc1 : FieldEmbedding.lusGBy q fibF1 = some fibF2)
    (hinc2 : FieldEmbedding.lusGBy q fibF2 = some fibF3) :
    evalGRom q (n + 10) (fibPushed fibN4) fibInc = some fibF3 := by
  have hr := evalGRom_fib_rec_n4 q n hinc1
  have h4 := evalGRom_op4 q (n + 9) hr hinc2
  simpa [fibInc, op4] using h4

theorem evalGRom_fib_inner_n4 (q n : ℕ)
    (hinc1 : FieldEmbedding.lusGBy q fibF1 = some fibF2)
    (hinc2 : FieldEmbedding.lusGBy q fibF2 = some fibF3) :
    evalGRom q (n + 11) (fibPushed fibN4) fibInner = some fibF3 := by
  have h0 := evalGRom_op0 q (n + 8) 7 (fib_slot7 fibN3)
  have h3 := evalGRom_op3 (q := q) (n := n + 9) h0
  have hi := evalGRom_fib_inc_n4 q n hinc1 hinc2
  have h6 := evalGRom_op6_zero q (n + 10) (d := fibHalt) h3 hi
  simpa [fibInner, op3, op6, fib_wut_n3, fibN4, fibN3] using h6

theorem evalGRom_fib_body_n4 (q n : ℕ)
    (hinc1 : FieldEmbedding.lusGBy q fibF1 = some fibF2)
    (hinc2 : FieldEmbedding.lusGBy q fibF2 = some fibF3) :
    evalGRom q (n + 12) (fibPushed fibN4) fibBody = some fibF3 := by
  have h0 := evalGRom_op0 q (n + 9) 3 (fib_slot3 fibN4)
  have h3 := evalGRom_op3 (q := q) (n := n + 10) h0
  have hI := evalGRom_fib_inner_n4 q n hinc1 hinc2
  have h6 := evalGRom_op6_zero q (n + 11) (d := fibHalt) h3 hI
  simpa [fibBody, op3, op6, fib_wut_n4] using h6

theorem lusGBy_fibF1 {q : ℕ} (hq : 2 < q) :
    FieldEmbedding.lusGBy q fibF1 = some fibF2 := by
  simpa [FieldEmbedding.lusGBy, fibF1, fibF2] using hq

theorem lusGBy_fibF2 {q : ℕ} (hq : 3 < q) :
    FieldEmbedding.lusGBy q fibF2 = some fibF3 := by
  simpa [FieldEmbedding.lusGBy, fibF2, fibF3] using hq

theorem fib_evalGRom32 :
    evalGRom 32 32 fibSubject fibFormula = some fibResult := by
  have hq := evalGRom_quote 32 30 fibSubject fibBody
  have hb := evalGRom_fib_body_n4 32 19 (lusGBy_fibF1 (by decide)) (lusGBy_fibF2 (by decide))
  have h8 := evalGRom_op8 (q := 32) (n := 31) hq hb
  simpa [fibFormula, op8, quote, fibSubject, fibResult] using h8

theorem fib_grom :
    evalGRom Field.p 32 fibSubject fibFormula = some fibResult :=
  evalGRom_mod_le (q := 32) (q' := Field.p)
    (by simp only [Field.p]; norm_num) 32 fibSubject fibFormula fibResult fib_evalGRom32

/-! ## `BoundedBy` — program-text atoms are `{0,1,2,3,4,6,7,8}`. -/

theorem fibSubject_bounded32 : FieldEmbedding.BoundedBy 32 fibSubject := by
  simp [fibSubject, fibN4, fibN3, fibN2, fibN1, FieldEmbedding.BoundedBy]

theorem fibFormula_bounded32 : FieldEmbedding.BoundedBy 32 fibFormula := by
  simp [fibFormula, op8, quote, fibBody, op6, op3, op0, fibInner, op4, fibInc,
    fibRec, op2, fibRecSample, fibHalt, op1, FieldEmbedding.BoundedBy]

theorem fibSubject_bounded_p : FieldEmbedding.BoundedBy Field.p fibSubject :=
  BoundedBy_mono (by simp only [Field.p]; norm_num) fibSubject_bounded32

theorem fibFormula_bounded_p : FieldEmbedding.BoundedBy Field.p fibFormula :=
  BoundedBy_mono (by simp only [Field.p]; norm_num) fibFormula_bounded32

/-! ## Compute-row facts. -/

theorem fib_comp_rows (z α : K) :
    (bfsForest [genComputeRows z α (fibTree (K := K))]).length = 33 := by
  rw [genComputeRows_bfsForest_length]
  have hsz : (airReorder (fibTree (K := K))).size = 33 := by
    rw [airReorder_size, fibTree_size]
  simp [bfsRows, bfsForest_length, totalSize] at hsz ⊢
  exact hsz

theorem fib_acc_le : programAcc (fibTree (K := K)) ≤ 99 := by
  unfold programAcc
  have hlen : (bfsRows (airReorder (fibTree (K := K)))).length = 33 := by
    have hsz : (airReorder (fibTree (K := K))).size = 33 := by
      rw [airReorder_size, fibTree_size]
    simp [bfsRows, bfsForest_length, totalSize] at hsz ⊢
    exact hsz
  have h := accAt_le_three_mul (airReorder (fibTree (K := K)))
    (bfsRows (airReorder (fibTree (K := K)))).length
  simpa [hlen] using h

theorem fib_hwin :
    programAcc (fibTree (K := K)) + 3 < orderOf FibConfigGoldilocks.alphaA := by
  have hacc := fib_acc_le
  have hord : orderOf FibConfigGoldilocks.alphaA = 2 ^ 16 :=
    FibConfigGoldilocks.alphaA_order
  omega

theorem fib_hcomp (z α : K) :
    (bfsForest [genComputeRows z α (fibTree (K := K))]).length
      ≤ 2 ^ executionOrbit.h := by
  rw [fib_comp_rows, executionOrbit_h]
  norm_num

theorem fib_mem_rows (z α : K) :
    programMemRows z α (fibTree (K := K)) = 1277 := by
  unfold programMemRows programMemRowsL
  rw [bfsForest_length, genMemoryForest_eq_thread, threadGenForest_totalSize]
  exact fibMemForest_assigned_totalSize (encC z) z α

/-- The memory half of §1's `hwin` (weakest form) at the
Peano-fib program: `1277` memory rows, `orderOf α = 2^16`. -/
theorem fib_hmemOrd :
    programMemShape FibConfigGoldilocks.alphaA (fibTree (K := K))
      ≤ orderOf FibConfigGoldilocks.alphaA := by
  have hm : programMemShape FibConfigGoldilocks.alphaA (fibTree (K := K)) = 1277 :=
    fib_mem_rows 0 _
  rw [hm, FibConfigGoldilocks.alphaA_order]
  norm_num

theorem fib_mem_roots (z α : K) :
    programMemRoots z α (fibTree (K := K)) = 51 := by
  unfold programMemRoots programMemRootsL
  rw [genMemoryForest_eq_thread, threadGenForest_length]
  exact fibMemForest_assigned_length (encC z) z α

theorem fib_hmem (z α : K) :
    (bfsForest (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (fibTree (K := K)))).length
      ≤ 2 ^ executionOrbit.h := by
  rw [show (bfsForest (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (fibTree (K := K)))).length =
      programMemRows z α (fibTree (K := K)) from (programMemRows_eq_L _ z α _).symm, fib_mem_rows, executionOrbit_h]
  norm_num

theorem fib_hprogCap :
    programAcc (fibTree (K := K)) + 1 ≤ 2 ^ executionOrbit.h := by
  have hacc := fib_acc_le
  rw [executionOrbit_h]
  omega

theorem fib_hmemCap (z α : K) :
    programMemRows z α (fibTree (K := K)) + 1 ≤ 2 ^ executionOrbit.h := by
  rw [fib_mem_rows, executionOrbit_h]
  norm_num

theorem fib_compilerKsz (z α : K) :
    compilerKszOf z α (fibTree (K := K)) = 102 := by
  have hacc : programAcc (fibTree (K := K)) ≤ 99 := fib_acc_le
  have hmf : programMemRoots z α (fibTree (K := K)) = 51 := fib_mem_roots z α
  unfold compilerKszOf compilerKsz
  rw [hmf]
  have : 2 * 51 = 102 := by norm_num
  rw [this]
  exact Nat.max_eq_right (le_trans hacc (by norm_num))

theorem fib_hKszChar (z α : K) :
    compilerKszOf z α (fibTree (K := K)) < ringChar K := by
  rw [fib_compilerKsz, ringChar_K]
  simp only [Field.p]
  norm_num

theorem fib_compilerN (z α : K) :
    compilerNOf z α (fibTree (K := K)) = 1277 := by
  have hacc : programAcc (fibTree (K := K)) ≤ 99 := fib_acc_le
  have hmem : programMemRows z α (fibTree (K := K)) = 1277 := fib_mem_rows z α
  unfold compilerNOf compilerN
  rw [hmem]
  exact Nat.max_eq_right (le_trans hacc (by norm_num))

theorem fib_hcard (z α : K) :
    RecordCarrier.honestIOBound
      (compilerNOf z α (fibTree (K := K)))
      (compilerNOf z α (fibTree (K := K)))
      (Fintype.card K) < Fintype.card (K × K) := by
  rw [fib_compilerN]
  exact hcard_of_le_two_pow_92_honest 1277 (by norm_num)

theorem fib_rows_lt_card :
    (bfsForest [airReorder (fibTree (K := K))]).length < Fintype.card K := by
  have hlen : (bfsForest [airReorder (fibTree (K := K))]).length = 33 := by
    have hsz : (airReorder (fibTree (K := K))).size = 33 := by
      rw [airReorder_size, fibTree_size]
    simp [bfsForest_length, totalSize] at hsz ⊢
    exact hsz
  rw [hlen, Field.card_K]
  simp only [Field.p]
  norm_num

theorem fib_exists_computeCoins :
    ∃ a b c : FibConfigGoldilocks.K,
      ComputeCoinsGeneric (K := FibConfigGoldilocks.K)
        FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA a b c
        (airReorder (fibTree (K := FibConfigGoldilocks.K))) :=
  exists_computeCoinsGeneric_airReorder (K := FibConfigGoldilocks.K)
    FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA
    (fibTree (K := FibConfigGoldilocks.K)) fib_rows_lt_card

theorem fibTree_eq_of_gen {t : NTree (GenComputeRow K)}
    (ht : genComputeSkeleton (K := K) 32 fibSubject fibFormula = .ok (t, fibResult)) :
    fibTree (K := K) = t := by
  have h := fibTree_eq (K := K)
  rw [ht] at h
  injection h with h'
  exact (Prod.mk.inj h').1.symm

theorem fib_hG :
    FieldEmbedding.evalGBy Field.p 32 fibSubject fibFormula = some fibResult :=
  evalGRom_le_evalGBy fib_grom

theorem fibTree_inTree_bounded (u : NTree (GenComputeRow K))
    (hu : InTree (fibTree (K := K)) u) :
    computeNodeBounded Field.p u :=
  genComputeSkeleton_inTree_bounded (q := Field.p) (by
      simp only [Field.p]; norm_num)
    fibSubject_bounded_p fibFormula_bounded_p fib_hG
    (fibTree_eq (K := K)) u hu

theorem fib_hwrap :
    ∀ g ∈ bfsRows (airReorder (fibTree (K := K))),
      g.skel.state = .s4 →
        OpcodeSemantics.incMod (ringChar K)
          (skeletonSubformula g.skel 0 TripleSlot.result)
          = g.skel.evaluation := by
  refine (forall_bfsRows_iff (airReorder (fibTree (K := K)))).mpr ?_
  intro u hu hs4
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (fibTree (K := K)) u hu
  have hlus : Noun.lus (skeletonSubformula u.label.skel 0 TripleSlot.result)
      = some u.label.skel.evaluation := by
    have h := fibTree_traceSep.2 u0 hu0 (by simpa [hl] using hs4)
    simpa [hl] using h
  have hbnd : u.label.skel.BoundedBy Field.p := by
    have h := fibTree_inTree_bounded u0 hu0
    simpa [hl] using h.1
  have hr : FieldEmbedding.BoundedBy Field.p u.label.skel.evaluation := hbnd.2.2.1
  have hle : (Field.p : ℕ) ≤ ringChar K := by
    rw [ringChar_K]
  exact incMod_eq_of_lus hlus hr hle

variable [Fintype K] [DecidableEq K]

/-- `hbad` at `seedZ`. -/
theorem fib_hbad (hΛ : 1 ≤ (42 : ℕ)) :
    FibConfigGoldilocks.seedZ ∉ (genSkeletonP8Census (K := K) hΛ
      (fibTree_eq (K := K)) (fib_traceConfined (K := K))
      (genMemoryForest FibConfigGoldilocks.seedZ FibConfigGoldilocks.alphaA MemoryTable.formRDefault
        (memInputs FibConfigGoldilocks.seedZ)
        (fibTree (K := K)))).census.badSeeds :=
  notMem_badSeeds_of_offdiag_sep (fibTree_eq (K := K)) hΛ
    (fib_traceConfined (K := K)) _
    fib_hwrap FibConfigGoldilocks.seedZ fib_hoff5 fib_hoff6

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.fib_grom
#print axioms Nock.NockVMROM.Thm54.TraceGen.fib_comp_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.fib_mem_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.fib_hbad
