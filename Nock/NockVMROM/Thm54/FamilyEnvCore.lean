/-
  Nock/NockVMROM/Thm54/FamilyEnvCore.lean

  Nothing here mentions
  `OptimizedFullStrictNockVMROMPackage`.  `FamilyIOGood` is NOT lifted: the target states it unfolded.

  Paper: the paper (IO), `:1450` (Thm 5.4 acceptance), `:1726-1742` (`V_comp`),
  `:2049-2088` (`V_mem`).
-/
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.OptimizedStrictPackage

namespace Nock.NockVMROM.Thm54.FamilyEnvCore

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open OptimizedStrictPackage
open OptimizedComputeHostileAccumulator
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open DeployedChipFamily
open CoordinateBasis
open CoordinateCompiler
open Module
open MonolithicRAP
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryCanonicalSatisfaction
open OptimizedComputeCollisionBound
open OptimizedMemoryCollisionAccounting

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false


set_option quotPrecheck false

/-- `P.computeChip` at `O := P.optimized`. -/
local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

/-- `P.memoryChip` at `O := P.optimized`. -/
local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

/-- `P.familyComputePublic c` at `O := P.optimized`. -/
local notation "FCP[" O ", " c "]" =>
  computePublicOfTuple (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.verifier O).raw.claim
    (OptimizedStrictNockVMROMPackage.computePublic O) c

/-- `P.familyMemoryPublic c` at `O := P.optimized`. -/
local notation "FMP[" O ", " c "]" =>
  memoryPublicOfTuple (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.verifier O).raw.claim
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem
    (OptimizedStrictNockVMROMPackage.memoryPublic O) c

/-- `P.computeChipAt c` at `O := P.optimized`. -/
local notation "CCA[" O ", " c "]" =>
  DeployedChipFamily.computeChipAt
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (FCP[O, c]) (OptimizedStrictNockVMROMPackage.orbit O) c

/-- `P.memoryChipAt c` at `O := P.optimized`. -/
local notation "MCA[" O ", " c "]" =>
  DeployedChipFamily.memoryChipAt
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (FMP[O, c]) (OptimizedStrictNockVMROMPackage.orbit O) c
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

local notation "NSM[" O "]" =>
  (namedSourceMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-! ## A. Widths, casts and round trips -/

/-- Family and honest compute chips have the same width (`w = 303`). -/
theorem computeChipAt_width
    (c : OptimizedProductionChallengeTuple K F) :
    (CCA[O, c]).rap.w = (CC[O]).rap.w := by
  have hc : (CCA[O, c]).rap.w = 303 := by
    simp only [DeployedChipFamily.computeChipAt, ProductionNamedComputeRAP]
    exact (corrected_rap_fingerprint O.basis
      (computeChalValOfTuple O.basis c) (FCP[O, c])
      O.orbit (rowNodeSet O.computeNodes)).1
  have h0 : (CC[O]).rap.w = 303 := by
    simp only [ProductionNamedComputeRAP]
    exact (corrected_rap_fingerprint O.basis
      O.computeChallenge O.computePublic
      O.orbit (rowNodeSet O.computeNodes)).1
  exact hc.trans h0.symm

/-- Family and honest memory chips have the same width (`w = 205`). -/
theorem memoryChipAt_width
    (c : OptimizedProductionChallengeTuple K F) :
    (MCA[O, c]).rap.w = (MC[O]).rap.w := by
  have hc : (MCA[O, c]).rap.w = 205 := by
    simp only [DeployedChipFamily.memoryChipAt]
    exact (finalMemoryRAP_fingerprint
      O.family.problem.cfg.memRows_pos O.memoryNodes
      O.basis (memoryChalValOfTuple O.basis c)
      (FMP[O, c]) O.orbit
      O.family.problem.cfg.kMem).1
  have h0 : (MC[O]).rap.w = 205 := by
    exact (finalMemoryRAP_fingerprint
      O.family.problem.cfg.memRows_pos O.memoryNodes
      O.basis O.memoryChallenge
      O.memoryPublic O.orbit
      O.family.problem.cfg.kMem).1
  exact hc.trans h0.symm

/-- Reindex a constant-chip compute trace at the family width. -/
def familyQc
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (CC[O]).rap.w → F[X]) :
    Fin (CCA[O, c]).rap.w → F[X] :=
  fun j => Qc (Fin.cast (computeChipAt_width O c) j)

/-- Reindex a family compute trace at the honest-chip width. -/
def honestQc
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (CCA[O, c]).rap.w → F[X]) :
    Fin (CC[O]).rap.w → F[X] :=
  fun j => Qc (Fin.cast (computeChipAt_width O c).symm j)

/-- Reindex a constant-chip memory trace at the family width. -/
def familyQm
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MC[O]).rap.w → F[X]) :
    Fin (MCA[O, c]).rap.w → F[X] :=
  fun j => Qm (Fin.cast (memoryChipAt_width O c) j)

/-- Reindex a family memory trace at the honest-chip width. -/
def honestQm
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X]) :
    Fin (MC[O]).rap.w → F[X] :=
  fun j => Qm (Fin.cast (memoryChipAt_width O c).symm j)

theorem honestQc_familyQc (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (CC[O]).rap.w → F[X]) : honestQc O c (familyQc O c Qc) = Qc := by
  funext j
  unfold honestQc familyQc
  apply congrArg Qc
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

theorem familyQc_honestQc (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (CCA[O, c]).rap.w → F[X]) : familyQc O c (honestQc O c Qc) = Qc := by
  funext j
  unfold honestQc familyQc
  apply congrArg Qc
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

theorem honestQm_familyQm (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MC[O]).rap.w → F[X]) : honestQm O c (familyQm O c Qm) = Qm := by
  funext j
  unfold honestQm familyQm
  apply congrArg Qm
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

theorem familyQm_honestQm (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X]) : familyQm O c (honestQm O c Qm) = Qm := by
  funext j
  unfold honestQm familyQm
  apply congrArg Qm
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

/-! ## B. The family row environments -/

/-- Family-chip gather of `Qc` at tuple `c`. -/
def rowEnvAt
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (CCA[O, c]).rap.w → F[X])
    (i : Fin O.family.problem.cfg.compRows) :
    CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv O.basis
    (envOfTrace Qc O.orbit.ω (O.computeNodes i)
      (computeChalValOfTuple O.basis c) (FCP[O, c]))

def memoryBaseEnvAt
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MC[O]).rap.w → F[X])
    (i : Fin O.family.problem.cfg.memRows) : Env F :=
  envOfTrace
    (RAPPadding.projectTrace (NSM[O]).rap
      (RAPPadding.firstRoundExtra (NSM[O]).rap (NSM[O]).rounds_pos
        (RAPPadding.memoryResidualColumns 3)) Qm)
    O.orbit.ω (O.memoryNodes i)
    (memoryChalValOfTuple O.basis c) (FMP[O, c])

/-- Family `𝕂` memory environment of a package-width `Qm`. -/
def memorySourceEnvAt
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MC[O]).rap.w → F[X])
    (i : Fin O.family.problem.cfg.memRows) : Env K :=
  gatherEnv O.basis ((memorySourceTemplate O.basis).col0 3)
    (memoryBaseEnvAt O c Qm i)

/-- Base-field family memory row environment of a family trace. -/
abbrev memEnvF (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X]) (i : Fin O.family.problem.cfg.memRows) : Env F :=
  memoryBaseEnvAt O c (honestQm O c Qm) i

/-- Gathered `𝕂` family memory row environment of a family trace. -/
abbrev memEnvK (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X]) (i : Fin O.family.problem.cfg.memRows) : Env K :=
  memorySourceEnvAt O c (honestQm O c Qm) i

/-! ## C. The family records -/

/-- The request list a family compute trace commits to. -/
def hostileRequestsAt (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (CCA[O, c]).rap.w → F[X]) : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin O.family.problem.cfg.compRows => rowRequests (rowEnvAt O c Qc i)).flatten

/-- The response list a family memory trace commits to. -/
def hostileResponsesAt (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X]) : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin O.family.problem.cfg.memRows =>
    OptimizedMemoryHostileAccumulator.rowResponses (memEnvK O c Qm i) (memEnvF O c Qm i)).flatten

/-- The records both family chips commit to. -/
def hostileRecordsAt (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X])
    (Qc : Fin (CCA[O, c]).rap.w → F[X]) : FiniteIO.PreChallengeRecords K 10 :=
  ⟨hostileRequestsAt O c Qc, hostileResponsesAt O c Qm⟩

@[simp] theorem hostileRecordsAt_requests (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X]) (Qc : Fin (CCA[O, c]).rap.w → F[X]) :
    (hostileRecordsAt O c Qm Qc).requests = hostileRequestsAt O c Qc := rfl

@[simp] theorem hostileRecordsAt_responses (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X]) (Qc : Fin (CCA[O, c]).rap.w → F[X]) :
    (hostileRecordsAt O c Qm Qc).responses = hostileResponsesAt O c Qm := rfl

theorem hostileRequestsAt_length_le (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (CCA[O, c]).rap.w → F[X]) :
    (hostileRequestsAt O c Qc).length ≤ 3 * O.family.problem.cfg.compRows := by
  unfold hostileRequestsAt
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc (∑ i : Fin O.family.problem.cfg.compRows, (rowRequests (rowEnvAt O c Qc i)).length)
        ≤ ∑ _i : Fin O.family.problem.cfg.compRows, 3 :=
          Finset.sum_le_sum fun i _ => rowRequests_length_le _
      _ = 3 * O.family.problem.cfg.compRows := by simp [mul_comm]

theorem hostileResponsesAt_length_le (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MCA[O, c]).rap.w → F[X]) :
    (hostileResponsesAt O c Qm).length ≤ O.family.problem.cfg.memRows := by
  unfold hostileResponsesAt
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc (∑ i : Fin O.family.problem.cfg.memRows,
          (OptimizedMemoryHostileAccumulator.rowResponses (memEnvK O c Qm i)
            (memEnvF O c Qm i)).length)
        ≤ ∑ _i : Fin O.family.problem.cfg.memRows, 1 :=
          Finset.sum_le_sum fun i _ =>
            OptimizedMemoryHostileAccumulator.rowResponses_length_le _ _
      _ = O.family.problem.cfg.memRows := by simp

/-- `activeMask` reads the base selectors only. -/
theorem activeMask_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.baseTrace = env'.baseTrace) (j : Fin 3) : activeMask env j = activeMask env' j := by
  fin_cases j <;> simp [activeMask, sampledActive, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, h]

theorem rowRequests_length_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : ∀ j, activeMask env j = activeMask env' j) :
    (rowRequests env).length = (rowRequests env').length := by
  simp only [rowRequests, List.finRange, List.ofFn_succ, List.ofFn_zero, List.filterMap_cons,
    List.filterMap_nil, h]
  split_ifs <;> simp

/-- **The family request count is the package request count at the reindexed trace** (the
activity masks read base selector columns only). -/
theorem hostileRequestsAt_length_eq (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (CC[O]).rap.w → F[X]) :
    (hostileRequestsAt O c (familyQc O c Qc)).length =
      ((List.ofFn fun i : Fin O.family.problem.cfg.compRows =>
        rowRequests (gatherCorrectedFinalTypedEnv O.basis
          (envOfTrace Qc O.orbit.ω (O.computeNodes i) O.computeChallenge
            O.computePublic))).flatten).length := by
  unfold hostileRequestsAt
  rw [List.length_flatten, List.length_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn,
    List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine rowRequests_length_congr fun j => activeMask_congr ?_ j
  funext k
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, envOfTrace, familyQc]
  have hw := computeChipAt_width O c
  by_cases h : (k : ℕ) < (CC[O]).rap.w
  · have h' : (k : ℕ) < (CCA[O, c]).rap.w := by rw [hw]; exact h
    rw [dif_pos h, dif_pos h']
    rfl
  · have h' : ¬ (k : ℕ) < (CCA[O, c]).rap.w := by rw [hw]; exact h
    rw [dif_neg h, dif_neg h']

/-! ## D. -/

/-- Challenge indices read by an `Expr`. -/
def chalIdx : Expr → List ℕ
  | .Var .challenge i => [i]
  | .Var _ _ => []
  | .Const _ => []
  | .Add a b => chalIdx a ++ chalIdx b
  | .Sub a b => chalIdx a ++ chalIdx b
  | .Mul a b => chalIdx a ++ chalIdx b
  | .Neg a => chalIdx a
  | .Pow a _ => chalIdx a

/-- The slot expression `HostileRecordLists.rowRecord` evaluates (its case split, verbatim). -/
def slotExpr (j : Fin 3) (c : Fin 10) : Expr :=
  if (c : ℕ) = 9 then (sampledSlotE .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else if (c : ℕ) = 6 then (sampledSlotT .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else if (c : ℕ) = 8 then (sampledSlotC .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).subst finalSampledNamespace

/-- **No request-record slot reads the IO pair** (slots `7`/`8` = `c.2.1`). -/
theorem no_slot_reads_io :
    ∀ j : Fin 3, ∀ c : Fin 10, ∀ i ∈ chalIdx (slotExpr j c), i ≠ 7 ∧ i ≠ 8 := by
  decide +kernel

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] [Algebra F K] [Field F] in
theorem eval_congr_of_chalIdx (e : Expr) {E E' : Env K}
    (ht : E.trace = E'.trace) (htn : E.traceNext = E'.traceNext) (hp : E.pub = E'.pub)
    (hc : ∀ i ∈ chalIdx e, E.chal i = E'.chal i) :
    e.eval E = e.eval E' := by
  induction e with
  | Var kind i =>
      cases kind
      · simp only [Expr.eval, ht]
      · simp only [Expr.eval, htn]
      · exact hc i (by simp [chalIdx])
      · simp only [Expr.eval, hp]
  | Const c => rfl
  | Add a b iha ihb =>
      simp only [chalIdx, List.mem_append] at hc
      simp only [Expr.eval, iha (fun j hj => hc j (Or.inl hj)), ihb (fun j hj => hc j (Or.inr hj))]
  | Sub a b iha ihb =>
      simp only [chalIdx, List.mem_append] at hc
      simp only [Expr.eval, iha (fun j hj => hc j (Or.inl hj)), ihb (fun j hj => hc j (Or.inr hj))]
  | Mul a b iha ihb =>
      simp only [chalIdx, List.mem_append] at hc
      simp only [Expr.eval, iha (fun j hj => hc j (Or.inl hj)), ihb (fun j hj => hc j (Or.inr hj))]
  | Neg a ih =>
      simp only [chalIdx] at hc
      simp only [Expr.eval, ih hc]
  | Pow a n ih =>
      simp only [chalIdx] at hc
      simp only [Expr.eval, ih hc]

/-- `c` with its IO pair replaced by `q`. -/
def reIO (c : OptimizedProductionChallengeTuple K F) (q : K × K) :
    OptimizedProductionChallengeTuple K F := (c.1, (q, c.2.2))

theorem computeKOfTuple_reIO (c : OptimizedProductionChallengeTuple K F) (q : K × K) :
    ∀ n : ℕ, n ≠ 7 → n ≠ 8 → computeKOfTuple (reIO c q) n = computeKOfTuple c n
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, h, _ => absurd rfl h
  | 8, _, h => absurd rfl h
  | 9, _, _ => rfl
  | 10, _, _ => rfl
  | _ + 11, _, _ => rfl

theorem computeChalValOfTuple_reIO (b : Module.Basis (Fin 3) F K)
    (c : OptimizedProductionChallengeTuple K F) (q : K × K) (j : ℕ)
    (hj : ¬ (21 ≤ j ∧ j < 27)) :
    computeChalValOfTuple b (reIO c q) j = computeChalValOfTuple b c j := by
  unfold computeChalValOfTuple
  split_ifs with h
  · rw [computeKOfTuple_reIO c q (j / 3) (by omega) (by omega)]
  · rfl

section Gather
variable {e e' : Env F}

theorem gather_toSourceEnv_trace_congr (ht : e.trace = e'.trace) :
    (gatherCorrectedFinalTypedEnv O.basis e).toSourceEnv.trace =
      (gatherCorrectedFinalTypedEnv O.basis e').toSourceEnv.trace := by
  funext k
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv, ht]

theorem gather_toSourceEnv_traceNext_congr (ht : e.traceNext = e'.traceNext) :
    (gatherCorrectedFinalTypedEnv O.basis e).toSourceEnv.traceNext =
      (gatherCorrectedFinalTypedEnv O.basis e').toSourceEnv.traceNext := by
  funext k
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv, ht]

theorem gather_toSourceEnv_pub_congr (hp : e.pub = e'.pub) :
    (gatherCorrectedFinalTypedEnv O.basis e).toSourceEnv.pub =
      (gatherCorrectedFinalTypedEnv O.basis e').toSourceEnv.pub := by
  funext k
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv, hp]

end Gather

section Rows
variable (c : OptimizedProductionChallengeTuple K F) (q : K × K)
  (Qc : Fin (CC[O]).rap.w → F[X]) (i : Fin O.family.problem.cfg.compRows)

theorem familyQc_envTrace (c' : OptimizedProductionChallengeTuple K F) (ω x : F)
    (ch pb : ℕ → F) :
    (envOfTrace (familyQc O c' Qc) ω x ch pb).trace = (envOfTrace Qc ω x ch pb).trace := by
  funext k
  have hw := computeChipAt_width O c'
  simp only [envOfTrace]
  by_cases h : k < (CC[O]).rap.w
  · have h' : k < (CCA[O, c']).rap.w := by rw [hw]; exact h
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ k < (CCA[O, c']).rap.w := by rw [hw]; exact h
    rw [dif_neg h', dif_neg h]

theorem familyQc_envTraceNext (c' : OptimizedProductionChallengeTuple K F) (ω x : F)
    (ch pb : ℕ → F) :
    (envOfTrace (familyQc O c' Qc) ω x ch pb).traceNext =
      (envOfTrace Qc ω x ch pb).traceNext := by
  funext k
  have hw := computeChipAt_width O c'
  simp only [envOfTrace]
  by_cases h : k < (CC[O]).rap.w
  · have h' : k < (CCA[O, c']).rap.w := by rw [hw]; exact h
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ k < (CCA[O, c']).rap.w := by rw [hw]; exact h
    rw [dif_neg h', dif_neg h]

theorem baseEnv_trace_reIO :
    (envOfTrace (familyQc O (reIO c q) Qc) O.orbit.ω (O.computeNodes i)
      (computeChalValOfTuple O.basis (reIO c q)) (FCP[O, reIO c q])).trace =
    (envOfTrace (familyQc O c Qc) O.orbit.ω (O.computeNodes i)
      (computeChalValOfTuple O.basis c) (FCP[O, c])).trace := by
  rw [familyQc_envTrace, familyQc_envTrace]
  rfl

theorem baseEnv_traceNext_reIO :
    (envOfTrace (familyQc O (reIO c q) Qc) O.orbit.ω (O.computeNodes i)
      (computeChalValOfTuple O.basis (reIO c q)) (FCP[O, reIO c q])).traceNext =
    (envOfTrace (familyQc O c Qc) O.orbit.ω (O.computeNodes i)
      (computeChalValOfTuple O.basis c) (FCP[O, c])).traceNext := by
  rw [familyQc_envTraceNext, familyQc_envTraceNext]
  rfl

theorem baseTrace_reIO :
    (rowEnvAt O (reIO c q) (familyQc O (reIO c q) Qc) i).baseTrace =
      (rowEnvAt O c (familyQc O c Qc) i).baseTrace := by
  funext j
  exact congrFun (baseEnv_trace_reIO O c q Qc i) (j : ℕ)

theorem chal_reIO (k : Fin 12) (h7 : (k : ℕ) ≠ 7) (h8 : (k : ℕ) ≠ 8) :
    (rowEnvAt O (reIO c q) (familyQc O (reIO c q) Qc) i).chal k =
      (rowEnvAt O c (familyQc O c Qc) i).chal k := by
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, envOfTrace]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hk := k.isLt
  have hm := m.isLt
  rw [computeChalValOfTuple_reIO _ _ _ _ (by omega)]

theorem toSourceEnv_chal_reIO (j : ℕ) (h7 : j ≠ 7) (h8 : j ≠ 8) :
    (rowEnvAt O (reIO c q) (familyQc O (reIO c q) Qc) i).toSourceEnv.chal j =
      (rowEnvAt O c (familyQc O c Qc) i).toSourceEnv.chal j := by
  have h9 := chal_reIO O c q Qc i (9 : Fin 12) (by decide) (by decide)
  simp only [CorrectedFinalTypedEnv.toSourceEnv]
  split_ifs with h1 h2
  · exact chal_reIO O c q Qc i ⟨j, h1⟩ h7 h8
  · rw [h9]
  · rfl

/-- The record of every request slot is unchanged when the IO coordinate moves. -/
theorem rowRecord_reIO (j : Fin 3) :
    rowRecord (rowEnvAt O (reIO c q) (familyQc O (reIO c q) Qc) i) j =
      rowRecord (rowEnvAt O c (familyQc O c Qc) i) j := by
  funext k
  have hc : ∀ e : Expr, (∀ n ∈ chalIdx e, n ≠ 7 ∧ n ≠ 8) →
      e.eval (rowEnvAt O (reIO c q) (familyQc O (reIO c q) Qc) i).toSourceEnv =
        e.eval (rowEnvAt O c (familyQc O c Qc) i).toSourceEnv :=
    fun e he => eval_congr_of_chalIdx e
      (gather_toSourceEnv_trace_congr O (baseEnv_trace_reIO O c q Qc i))
      (gather_toSourceEnv_traceNext_congr O (baseEnv_traceNext_reIO O c q Qc i))
      (gather_toSourceEnv_pub_congr O rfl)
      (fun n hn => toSourceEnv_chal_reIO O c q Qc i n (he n hn).1 (he n hn).2)
  have hslot := no_slot_reads_io j k
  unfold rowRecord
  simp only [slotExpr] at hslot
  split_ifs at hslot ⊢ <;> exact hc _ hslot

theorem rowRequests_reIO :
    rowRequests (rowEnvAt O (reIO c q) (familyQc O (reIO c q) Qc) i) =
      rowRequests (rowEnvAt O c (familyQc O c Qc) i) := by
  simp only [rowRequests]
  congr 1
  funext j
  rw [activeMask_congr (baseTrace_reIO O c q Qc i) j, rowRecord_reIO O c q Qc i j]

end Rows

/-- **The family request list does not read the IO pair.** -/
theorem hostileRequestsAt_reIO (c : OptimizedProductionChallengeTuple K F) (q : K × K)
    (Qc : Fin (CC[O]).rap.w → F[X]) :
    hostileRequestsAt O (reIO c q) (familyQc O (reIO c q) Qc) =
      hostileRequestsAt O c (familyQc O c Qc) := by
  unfold hostileRequestsAt
  exact congrArg List.flatten (congrArg List.ofFn (funext fun i => rowRequests_reIO O c q Qc i))

theorem rowResponses_congr {envK envK' : Env K} {envF envF' : Env F}
    (hK : envK.trace = envK'.trace) (hF : envF.trace = envF'.trace) :
    OptimizedMemoryHostileAccumulator.rowResponses envK envF =
      OptimizedMemoryHostileAccumulator.rowResponses envK' envF' := by
  have hrec : OptimizedMemoryHostileAccumulator.rowRecord envK envF =
      OptimizedMemoryHostileAccumulator.rowRecord envK' envF' := by
    funext j
    simp only [OptimizedMemoryHostileAccumulator.rowRecord, hK, hF]
  simp only [OptimizedMemoryHostileAccumulator.rowResponses,
    OptimizedMemoryHostileAccumulator.rowResponseTerms,
    OptimizedMemoryHostileAccumulator.rowDenominator, hK, hrec]

/-- **The family response list at a reindexed package trace is coin-free.** -/
theorem hostileResponsesAt_familyQm (c c' : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (MC[O]).rap.w → F[X]) :
    hostileResponsesAt O c (familyQm O c Qm) = hostileResponsesAt O c' (familyQm O c' Qm) := by
  unfold hostileResponsesAt
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
  apply rowResponses_congr
  · simp only [memEnvK, memorySourceEnvAt, gatherEnv, memoryBaseEnvAt, envOfTrace,
      honestQm_familyQm]
  · simp only [memEnvF, memoryBaseEnvAt, envOfTrace, honestQm_familyQm]

/-! ## E. -/

/-- The nine non-IO coordinates. -/
abbrev Rest (K : Type) := JointCoins K × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)

def restOf (c : OptimizedProductionChallengeTuple K F) : Rest K := (c.1, c.2.2)

omit [Field K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] [Algebra F K] in
theorem card_Rest : Fintype.card (Rest K) = Fintype.card K ^ 9 := by
  simp only [Rest, JointCoins, Fintype.card_prod, card_finalComputeChallengeTuple,
    card_memoryChallengeTuple]
  ring

def famIOEventOf (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    c.2.1 ∈ FiniteIO.IOFailureEvent (hostileRecordsAt O c (familyQm O c Qm) (familyQc O c Qc))

/-- The record function of the nine non-IO coordinates `famIOEventOf` is fibred over. -/
def famR (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) (r : Rest K) :
    FiniteIO.PreChallengeRecords K 10 :=
  hostileRecordsAt O (r.1, ((0, 0), r.2)) (familyQm O (r.1, ((0, 0), r.2)) Qm)
    (familyQc O (r.1, ((0, 0), r.2)) Qc)

theorem records_eq_famR (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    hostileRecordsAt O c (familyQm O c Qm) (familyQc O c Qc) = famR O Qc Qm (restOf c) := by
  obtain ⟨c1, q, c22⟩ := c
  show hostileRecordsAt O (c1, (q, c22)) (familyQm O (c1, (q, c22)) Qm)
      (familyQc O (c1, (q, c22)) Qc) =
    hostileRecordsAt O (c1, ((0, 0), c22)) (familyQm O (c1, ((0, 0), c22)) Qm)
      (familyQc O (c1, ((0, 0), c22)) Qc)
  unfold hostileRecordsAt
  have hreq := hostileRequestsAt_reIO O (c1, ((0, 0), c22)) q Qc
  simp only [reIO] at hreq
  rw [hostileResponsesAt_familyQm O (c1, (q, c22)) (c1, ((0, 0), c22)) Qm, hreq]

theorem mem_famIOEventOf_iff (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    c ∈ famIOEventOf O Qc Qm ↔
      c.2.1 ∈ FiniteIO.IOFailureEvent (hostileRecordsAt O c (familyQm O c Qm) (familyQc O c Qc)) := by
  simp [famIOEventOf]

/-- What the twins consume (`FamilyIOGood`, unfolded): outside the event, the IO coins avoid the
IO failure event at the family records. -/
theorem familyIOGood_of_not_mem (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) (h : c ∉ famIOEventOf O Qc Qm) :
    c.2.1 ∉ FiniteIO.IOFailureEvent (hostileRecordsAt O c (familyQm O c Qm) (familyQc O c Qc)) :=
  fun hm => h ((mem_famIOEventOf_iff O Qc Qm c).2 hm)

theorem fibre_card_le (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])
    (r : Rest K) :
    ((famIOEventOf O Qc Qm).filter (fun c => restOf c = r)).card ≤
      (FiniteIO.IOFailureEvent (famR O Qc Qm r)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun c : OptimizedProductionChallengeTuple K F => c.2.1) ?_ ?_
  · intro c hc
    simp only [Finset.coe_filter, famIOEventOf, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hc
    obtain ⟨hmem, hr⟩ := hc
    rw [records_eq_famR, hr] at hmem
    exact hmem
  · intro c hc c' hc' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc hc'
    have hr : restOf c = restOf c' := hc.2.trans hc'.2.symm
    have h1 : c.1 = c'.1 := congrArg (fun r : Rest K => r.1) hr
    have h2 : c.2.2 = c'.2.2 := congrArg (fun r : Rest K => r.2) hr
    have h3 : c.2.1 = c'.2.1 := h
    exact Prod.ext h1 (Prod.ext h3 h2)

theorem famIOEventOf_card_le (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) :
    (famIOEventOf O Qc Qm).card ≤
      Fintype.card K ^ 9 *
        FiniteIO.ioFailureUnionBound 10 (3 * O.family.problem.cfg.compRows)
          O.family.problem.cfg.memRows (Fintype.card K) := by
  classical
  calc (famIOEventOf O Qc Qm).card
      = ∑ r ∈ (Finset.univ : Finset (Rest K)),
          ((famIOEventOf O Qc Qm).filter (fun c => restOf c = r)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _r ∈ (Finset.univ : Finset (Rest K)),
          FiniteIO.ioFailureUnionBound 10 (3 * O.family.problem.cfg.compRows)
            O.family.problem.cfg.memRows (Fintype.card K) := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact (fibre_card_le O Qc Qm r).trans
          ((FiniteIO.IOFailureEvent_card_le (famR O Qc Qm r)).trans
            (ioFailureUnionBound_mono₂ 10 _ _ _ _ (Fintype.card K)
              (hostileRequestsAt_length_le O _ _) (hostileResponsesAt_length_le O _ _)))
    _ = Fintype.card K ^ 9 *
          FiniteIO.ioFailureUnionBound 10 (3 * O.family.problem.cfg.compRows)
            O.family.problem.cfg.memRows (Fintype.card K) := by
        rw [Finset.sum_const, Finset.card_univ, card_Rest, smul_eq_mul]

/-! ## F. -/

section Gates
variable (c : OptimizedProductionChallengeTuple K F)

/-- `FamilyComputeRows.row_obligations_at`, lifted. -/
theorem row_obligations_at (Qc : Fin (CCA[O, c]).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (CCA[O, c]) Qc)
    (i : Fin O.family.problem.cfg.compRows) :
    CorrectedComputeSourceObligations O.family.problem.cfg.compRows (rowEnvAt O c Qc i)
      (envOfTrace Qc O.orbit.ω (O.computeNodes i)
        (computeChalValOfTuple O.basis c) (FCP[O, c])) := by
  have h :=
    (productionNamedComputeRAP_satisfies_iff_sourceLanguage
      O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computeChalValOfTuple O.basis c)
      (FCP[O, c]) O.orbit Qc).1 hsat
  exact h.2 _ (by simp [rowNodeSet])

theorem notLast_at (hw0 : (CC[O]).rap.w = 303) (Qc : Fin (CCA[O, c]).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (CCA[O, c]) Qc)
    (i : Fin O.family.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < O.family.problem.cfg.compRows) :
    (rowEnvAt O c Qc i).baseTrace 12 = 0 := by
  have hbind := hsat.2 (1 : Fin 2)
  have hw : (CCA[O, c]).rap.w = 303 := (computeChipAt_width O c).trans hw0
  have hj12 : 12 < (CCA[O, c]).rap.w := by omega
  change Qc ⟨12, hj12⟩ =
    Nock.Framework.lastRowMask O.family.problem.cfg.compRows_pos O.computeNodes at hbind
  have heval := congrArg (fun f : F[X] => f.eval (O.computeNodes i)) hbind
  rw [Nock.Framework.lastRowMask_eval O.family.problem.cfg.compRows_pos
    O.computeNodes O.computeNodes_injective] at heval
  have hne : i ≠
      ⟨O.family.problem.cfg.compRows - 1,
        Nat.sub_lt O.family.problem.cfg.compRows_pos (by omega)⟩ := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only at hv
    omega
  simp only [hne, if_false] at heval
  show (envOfTrace Qc O.orbit.ω (O.computeNodes i)
    (computeChalValOfTuple O.basis c) (FCP[O, c])).trace 12 = 0
  simp only [envOfTrace, hj12, dite_true]
  exact heval

/-- `FamilyMemoryRows.source_sat_at`, lifted (with `projAt` inlined as the family trace's
first `182` columns). -/
theorem memory_row_parts_at (Qm : Fin (MCA[O, c]).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (MCA[O, c]) Qm)
    (i : Fin O.family.problem.cfg.memRows) :
    (∀ g ∈ baseTransitionGates O.basis, g.eval (memEnvF O c Qm i) = 0) ∧
    (∀ g ∈ mixedTransitionGates (F := F) (K := K) O.basis,
      g.eval (memEnvK O c Qm i) (memEnvF O c Qm i) = 0) := by
  have hw : (MCA[O, c]).rap.w = 205 :=
    (finalMemoryRAP_fingerprint O.family.problem.cfg.memRows_pos O.memoryNodes O.basis
      (memoryChalValOfTuple O.basis c) (FMP[O, c]) O.orbit O.family.problem.cfg.kMem).1
  let proj : Fin 182 → F[X] := fun j => Qm ⟨j.val, by omega⟩
  have hsrc :
      RAP.SatisfiesWithPreprocessing
        (namedSourceMemoryRAP O.family.problem.cfg.memRows_pos O.memoryNodes O.basis
          (memoryChalValOfTuple O.basis c) (FMP[O, c]) O.orbit O.family.problem.cfg.kMem)
        proj :=
    (final_satisfies_iff_source O.family.problem.cfg.memRows_pos O.memoryNodes O.basis
      (memoryChalValOfTuple O.basis c) (FMP[O, c]) O.orbit O.family.problem.cfg.kMem Qm).mp hsat
  have hraw :
      (sourceMemoryRAP O.basis (memoryChalValOfTuple O.basis c) (FMP[O, c]) O.orbit
        (rowNodeSet O.memoryNodes)).Satisfies proj := hsrc.1
  rw [sourceMemoryRAP_satisfies_iff_language O.sampled] at hraw
  have hx : O.memoryNodes i ∈ rowNodeSet O.memoryNodes := by simp [rowNodeSet]
  have hparts := hraw _ hx
  have hF : envOfTrace proj O.orbit.ω (O.memoryNodes i) (memoryChalValOfTuple O.basis c)
      (FMP[O, c]) = memEnvF O c Qm i := by
    simp only [memEnvF, memoryBaseEnvAt]
    congr 1
  rw [hF] at hparts
  refine ⟨hparts.1, ?_⟩
  have h4 := hparts.2.2.2
  dsimp only [memEnvK, memorySourceEnvAt]
  rw [memorySourceTemplate_col0]
  exact h4

end Gates

end

end Nock.NockVMROM.Thm54.FamilyEnvCore
