/-
  Nock/RedTeam/Batch885Thm54Part2aLiftReceipts.lean

  For a theorem the receipt is the `rfl` between the two proofs, i.e. the
  two statements are definitionally the same proposition.
-/
import Nock.NockVMROM.Thm54.FamilyEnvCore
import Nock.NockVMROM.Thm54.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.WalkQueueDeployed
import Nock.RedTeam.Batch786Thm54FamilyIOChain
import Nock.RedTeam.Batch824Thm54R4Bridge
import Nock.RedTeam.Batch883Thm54Part2aFamilyTarget
import Nock.RedTeam.Batch884Thm54Part2aFamIOInstance
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch885

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-! ## Definitions -/

theorem familyQc_eq (Qc : Fin P.computeChip.rap.w → F[X]) :
    FamilyEnvCore.familyQc P.optimized c Qc = FamilyComputeRows.familyQc P c Qc := rfl

theorem honestQc_eq (Qc : Fin (P.computeChipAt c).rap.w → F[X]) :
    FamilyEnvCore.honestQc P.optimized c Qc = FamilyComputeRows.honestQc P c Qc := rfl

theorem familyQm_eq (Qm : Fin P.memoryChip.rap.w → F[X]) :
    FamilyEnvCore.familyQm P.optimized c Qm = WrapMemoryConjuncts.familyQm P c Qm := rfl

theorem honestQm_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) :
    FamilyEnvCore.honestQm P.optimized c Qm = FamilyMemoryRows.honestQm P c Qm := rfl

theorem rowEnvAt_eq (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    FamilyEnvCore.rowEnvAt P.optimized c Qc i = FamilyComputeRows.rowEnvAt P c Qc i := rfl

theorem memoryBaseEnvAt_eq (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    FamilyEnvCore.memoryBaseEnvAt P.optimized c Qm i =
      FamilyComputeRows.memoryBaseEnvAt P c Qm i := rfl

theorem memorySourceEnvAt_eq (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    FamilyEnvCore.memorySourceEnvAt P.optimized c Qm i =
      FamilyComputeRows.memorySourceEnvAt P c Qm i := rfl

theorem memEnvF_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    FamilyEnvCore.memEnvF P.optimized c Qm i = FamilyIOChain.memEnvF P c Qm i := rfl

theorem memEnvK_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    FamilyEnvCore.memEnvK P.optimized c Qm i = FamilyIOChain.memEnvK P c Qm i := rfl

theorem hostileRequestsAt_eq (Qc : Fin (P.computeChipAt c).rap.w → F[X]) :
    FamilyEnvCore.hostileRequestsAt P.optimized c Qc = FamilyIOChain.hostileRequestsAt P c Qc :=
  rfl

theorem hostileResponsesAt_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) :
    FamilyEnvCore.hostileResponsesAt P.optimized c Qm =
      FamilyIOChain.hostileResponsesAt P c Qm := rfl

theorem hostileRecordsAt_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) :
    FamilyEnvCore.hostileRecordsAt P.optimized c Qm Qc =
      FamilyIOChain.hostileRecordsAt P c Qm Qc := rfl

theorem famIOEventOf_eq (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    FamilyEnvCore.famIOEventOf P.optimized Qc Qm = Batch884.famIOEventOf P Qc Qm := rfl

theorem famR_eq (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (r : FamilyEnvCore.Rest K) :
    FamilyEnvCore.famR P.optimized Qc Qm r = Batch884.famR P Qc Qm r := rfl

/-- `chalIdx` is structurally recursive, so its compiled recursor differs from `Batch881.chalIdx`;
the receipt is `rfl` constructor by constructor (the defining equations coincide). -/
theorem chalIdx_eq : ∀ e, FamilyEnvCore.chalIdx e = Batch881.chalIdx e
  | .Var .challenge _ => rfl
  | .Var .traceCur _ => rfl
  | .Var .traceNext _ => rfl
  | .Var .publicVal _ => rfl
  | .Const _ => rfl
  | .Add a b => by simp only [FamilyEnvCore.chalIdx, Batch881.chalIdx, chalIdx_eq a, chalIdx_eq b]
  | .Sub a b => by simp only [FamilyEnvCore.chalIdx, Batch881.chalIdx, chalIdx_eq a, chalIdx_eq b]
  | .Mul a b => by simp only [FamilyEnvCore.chalIdx, Batch881.chalIdx, chalIdx_eq a, chalIdx_eq b]
  | .Neg a => by simp only [FamilyEnvCore.chalIdx, Batch881.chalIdx, chalIdx_eq a]
  | .Pow a _ => by simp only [FamilyEnvCore.chalIdx, Batch881.chalIdx, chalIdx_eq a]
theorem slotExpr_eq : FamilyEnvCore.slotExpr = Batch881.slotExpr := rfl

theorem reIO_eq (q : K × K) : FamilyEnvCore.reIO c q = Batch884.reIO c q := rfl

theorem restOf_eq : FamilyEnvCore.restOf (F := F) c = Batch881.restOf c := rfl

/-! ## Theorems (the two statements are definitionally the same proposition) -/

theorem computeChipAt_width_eq :
    FamilyEnvCore.computeChipAt_width P.optimized c = FamilyComputeRows.computeChipAt_width P c :=
  rfl

theorem memoryChipAt_width_eq :
    FamilyEnvCore.memoryChipAt_width P.optimized c = FamilyComputeRows.memoryChipAt_width P c :=
  rfl

theorem honestQc_familyQc_eq (Qc : Fin P.computeChip.rap.w → F[X]) :
    FamilyEnvCore.honestQc_familyQc P.optimized c Qc = Batch786.honestQc_familyQc P c Qc := rfl

theorem familyQc_honestQc_eq (Qc : Fin (P.computeChipAt c).rap.w → F[X]) :
    FamilyEnvCore.familyQc_honestQc P.optimized c Qc = Batch824.familyQc_honestQc P c Qc :=
  rfl

theorem honestQm_familyQm_eq (Qm : Fin P.memoryChip.rap.w → F[X]) :
    FamilyEnvCore.honestQm_familyQm P.optimized c Qm = Batch786.honestQm_familyQm P c Qm := rfl

theorem familyQm_honestQm_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) :
    FamilyEnvCore.familyQm_honestQm P.optimized c Qm = Batch824.familyQm_honestQm P c Qm :=
  rfl

theorem hostileRequestsAt_length_eq_eq (Qc : Fin P.computeChip.rap.w → F[X]) :
    FamilyEnvCore.hostileRequestsAt_length_eq P.optimized c Qc =
      FamilyIOChain.hostileRequestsAt_length_eq P c (FamilyComputeRows.familyQc P c Qc) := rfl

theorem hostileRequestsAt_reIO_eq (q : K × K) (Qc : Fin P.computeChip.rap.w → F[X]) :
    FamilyEnvCore.hostileRequestsAt_reIO P.optimized c q Qc = Batch884.hostileRequestsAt_reIO P c q Qc :=
  rfl

/-- The two read-set statements are the same proposition up to `chalIdx_eq` (`slotExpr` is `rfl`). -/
theorem no_slot_reads_io_eq :
    (∀ j : Fin 3, ∀ c : Fin 10, ∀ i ∈ FamilyEnvCore.chalIdx (FamilyEnvCore.slotExpr j c),
        i ≠ 7 ∧ i ≠ 8) ↔
      (∀ j : Fin 3, ∀ c : Fin 10, ∀ i ∈ Batch881.chalIdx (Batch881.slotExpr j c),
        i ≠ 7 ∧ i ≠ 8) := by
  simp only [chalIdx_eq, slotExpr_eq]

theorem famIOEventOf_card_le_eq (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    FamilyEnvCore.famIOEventOf_card_le P.optimized Qc Qm = Batch884.famIOEventOf_card_le P Qc Qm :=
  rfl

theorem familyIOGood_of_not_mem_eq (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) (h : c ∉ FamilyEnvCore.famIOEventOf P.optimized Qc Qm) :
    FamilyEnvCore.familyIOGood_of_not_mem P.optimized Qc Qm c h =
      Batch884.familyIOGood_of_not_mem P Qc Qm c h := rfl

/-- This is the
propositional bridge between the two statements. -/
theorem mem_famIOEventOf_iff_bridge (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (c ∈ FamilyEnvCore.famIOEventOf P.optimized Qc Qm ↔
        c.2.1 ∈ FiniteIO.IOFailureEvent (FamilyEnvCore.hostileRecordsAt P.optimized c
          (FamilyEnvCore.familyQm P.optimized c Qm) (FamilyEnvCore.familyQc P.optimized c Qc))) ↔
      (c ∈ Batch884.famIOEventOf P Qc Qm ↔
        ¬ FamilyIOChain.FamilyIOGood P c (FamilyComputeRows.familyQc P c Qc) (Batch884.famQm P c Qm)) :=
  iff_of_true (FamilyEnvCore.mem_famIOEventOf_iff P.optimized Qc Qm c)
    (Batch884.mem_famIOEventOf_iff P Qc Qm c)

theorem row_obligations_at_eq (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (hsat : Nock.Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    FamilyEnvCore.row_obligations_at P.optimized c Qc hsat i =
      FamilyComputeRows.row_obligations_at P c Qc hsat i := rfl

theorem notLast_at_eq (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) (hacc : DeployedAcceptanceAt P c Qc Qm)
    (i : Fin P.optimized.family.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows) :
    FamilyEnvCore.notLast_at P.optimized c P.optimized.exact_chip_resources.1 Qc
        hacc.compute_satisfies i hi =
      Batch883.notLast_at P c Qc Qm hacc i hi := rfl

theorem memory_row_parts_at_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : Nock.Framework.RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (FamilyEnvCore.memory_row_parts_at P.optimized c Qm hsat i).1 =
        FamilyMemoryRows.base_at_family P c Qm hsat i ∧
      (FamilyEnvCore.memory_row_parts_at P.optimized c Qm hsat i).2 =
        FamilyMemoryRows.mixed_at_family P c Qm hsat i := ⟨rfl, rfl⟩

/-! ## Lifted helper lemmas -/

theorem activeMask_congr_eq {env env' : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K}
    (h : env.baseTrace = env'.baseTrace) (j : Fin 3) :
    FamilyEnvCore.activeMask_congr h j = FamilyIOChain.activeMask_congr h j := rfl

theorem rowRequests_length_congr_eq
    {env env' : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K}
    (h : ∀ j, OptimizedComputeHostileAccumulator.activeMask env j =
      OptimizedComputeHostileAccumulator.activeMask env' j) :
    FamilyEnvCore.rowRequests_length_congr h = FamilyIOChain.rowRequests_length_congr h := rfl

theorem eval_congr_of_chalIdx_eq (e : Nock.Reified.Expr) {E E' : Nock.Reified.Env K}
    (ht : E.trace = E'.trace) (htn : E.traceNext = E'.traceNext) (hp : E.pub = E'.pub)
    (hc : ∀ i ∈ Batch881.chalIdx e, E.chal i = E'.chal i) :
    FamilyEnvCore.eval_congr_of_chalIdx e ht htn hp (by rwa [chalIdx_eq]) =
      Batch884.eval_congr_of_chalIdx e ht htn hp hc := rfl

theorem computeKOfTuple_reIO_eq (q : K × K) (n : ℕ) (h7 : n ≠ 7) (h8 : n ≠ 8) :
    FamilyEnvCore.computeKOfTuple_reIO c q n h7 h8 = Batch884.computeKOfTuple_reIO c q n h7 h8 :=
  rfl

theorem computeChalValOfTuple_reIO_eq (b : Module.Basis (Fin 3) F K) (q : K × K) (j : ℕ)
    (hj : ¬ (21 ≤ j ∧ j < 27)) :
    FamilyEnvCore.computeChalValOfTuple_reIO b c q j hj =
      Batch884.computeChalValOfTuple_reIO b c q j hj := rfl

theorem baseTrace_reIO_eq (q : K × K) (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    FamilyEnvCore.baseTrace_reIO P.optimized c q Qc i = Batch884.baseTrace_reIO P c q Qc i := rfl

theorem chal_reIO_eq (q : K × K) (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (k : Fin 12) (h7 : (k : ℕ) ≠ 7)
    (h8 : (k : ℕ) ≠ 8) :
    FamilyEnvCore.chal_reIO P.optimized c q Qc i k h7 h8 = Batch884.chal_reIO P c q Qc i k h7 h8 :=
  rfl

theorem toSourceEnv_chal_reIO_eq (q : K × K) (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (j : ℕ) (h7 : j ≠ 7) (h8 : j ≠ 8) :
    FamilyEnvCore.toSourceEnv_chal_reIO P.optimized c q Qc i j h7 h8 =
      Batch884.toSourceEnv_chal_reIO P c q Qc i j h7 h8 := rfl

theorem rowRecord_reIO_eq (q : K × K) (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3) :
    FamilyEnvCore.rowRecord_reIO P.optimized c q Qc i j = Batch884.rowRecord_reIO P c q Qc i j :=
  rfl

theorem rowRequests_reIO_eq (q : K × K) (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    FamilyEnvCore.rowRequests_reIO P.optimized c q Qc i = Batch884.rowRequests_reIO P c q Qc i :=
  rfl

theorem card_Rest_eq : FamilyEnvCore.card_Rest (K := K) = Batch881.card_Rest := rfl

theorem records_eq_famR_eq (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    FamilyEnvCore.records_eq_famR P.optimized Qc Qm c = Batch884.records_eq_famR P Qc Qm c := rfl

theorem hostileRecordsAt_requests_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) :
    FamilyEnvCore.hostileRecordsAt_requests P.optimized c Qm Qc =
      FamilyIOChain.hostileRecordsAt_requests P c Qm Qc := rfl

theorem hostileRecordsAt_responses_eq (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) :
    FamilyEnvCore.hostileRecordsAt_responses P.optimized c Qm Qc =
      FamilyIOChain.hostileRecordsAt_responses P c Qm Qc := rfl

end

end Nock.RedTeam.Batch885
