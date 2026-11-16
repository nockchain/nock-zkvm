import Nock.RedTeam.Batch881Thm54Part2aFamIOAtQD
import Nock.NockVMROM.Thm54.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.P8Core.Batch884Thm54Part2aFamIOInstance
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
This file supplies it:

* `eval_congr_of_chalIdx` — `Expr.eval` depends on the challenge map only through `chalIdx`;
* `hostileRequestsAt_reIO` — replacing `c`'s IO coordinate leaves the family REQUEST list
  unchanged (trace columns agree through `familyQc`, publics are coin-free off the walk block and
  depend on `c.1` only on it, challenge slots `≠ 7, 8` agree; the record slot expressions read
  none of `7`, `8` by `Batch881.no_slot_reads_io`);
* `hostileResponsesAt_famQm` — the family RESPONSE list is the package's at `Qm`
  (`hostileResponsesAt_eq_package`), hence coin-free;

`famQm` is `WrapMemoryConjuncts.familyQm`
restated locally so this file does not import above `FamilyIOChainRouteB`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2000

namespace Nock.RedTeam.Batch884

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.RedTeam.Batch881 (chalIdx slotExpr no_slot_reads_io Rest restOf famIOEvent famIOEvent_card_le)

/-! ## A. Evaluation reads the challenge map only through `chalIdx` -/

section Eval
variable {K : Type} [Field K]

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

end Eval

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## A′. The gathered typed env's source view reads each `Env F` field separately -/

section Gather
variable {F K : Type} [Field F] [Field K] [Algebra F K] (b : Module.Basis (Fin 3) F K)
  {e e' : Env F}

theorem gather_baseTrace_congr (ht : e.trace = e'.trace) :
    (gatherCorrectedFinalTypedEnv b e).baseTrace = (gatherCorrectedFinalTypedEnv b e').baseTrace := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_baseTraceNext_congr (ht : e.traceNext = e'.traceNext) :
    (gatherCorrectedFinalTypedEnv b e).baseTraceNext =
      (gatherCorrectedFinalTypedEnv b e').baseTraceNext := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_extTrace_congr (ht : e.trace = e'.trace) :
    (gatherCorrectedFinalTypedEnv b e).extTrace = (gatherCorrectedFinalTypedEnv b e').extTrace := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_extTraceNext_congr (ht : e.traceNext = e'.traceNext) :
    (gatherCorrectedFinalTypedEnv b e).extTraceNext =
      (gatherCorrectedFinalTypedEnv b e').extTraceNext := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_certBase_congr (ht : e.trace = e'.trace) :
    (gatherCorrectedFinalTypedEnv b e).certBase = (gatherCorrectedFinalTypedEnv b e').certBase := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_certBaseNext_congr (ht : e.traceNext = e'.traceNext) :
    (gatherCorrectedFinalTypedEnv b e).certBaseNext =
      (gatherCorrectedFinalTypedEnv b e').certBaseNext := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_certExt_congr (ht : e.trace = e'.trace) :
    (gatherCorrectedFinalTypedEnv b e).certExt = (gatherCorrectedFinalTypedEnv b e').certExt := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_certExtNext_congr (ht : e.traceNext = e'.traceNext) :
    (gatherCorrectedFinalTypedEnv b e).certExtNext =
      (gatherCorrectedFinalTypedEnv b e').certExtNext := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_expCol_congr (ht : e.trace = e'.trace) :
    (gatherCorrectedFinalTypedEnv b e).expCol = (gatherCorrectedFinalTypedEnv b e').expCol := by
  simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_expColNext_congr (ht : e.traceNext = e'.traceNext) :
    (gatherCorrectedFinalTypedEnv b e).expColNext = (gatherCorrectedFinalTypedEnv b e').expColNext := by
  simp only [gatherCorrectedFinalTypedEnv, ht]
theorem gather_extensionPublic_congr (hp : e.pub = e'.pub) :
    (gatherCorrectedFinalTypedEnv b e).extensionPublic =
      (gatherCorrectedFinalTypedEnv b e').extensionPublic := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, hp]
theorem gather_scalarPublic_congr (hp : e.pub = e'.pub) :
    (gatherCorrectedFinalTypedEnv b e).scalarPublic =
      (gatherCorrectedFinalTypedEnv b e').scalarPublic := by
  funext j; simp only [gatherCorrectedFinalTypedEnv, hp]

theorem gather_toSourceEnv_trace_congr (ht : e.trace = e'.trace) :
    (gatherCorrectedFinalTypedEnv b e).toSourceEnv.trace =
      (gatherCorrectedFinalTypedEnv b e').toSourceEnv.trace := by
  funext k
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gather_baseTrace_congr b ht,
    gather_extTrace_congr b ht, gather_certBase_congr b ht, gather_certExt_congr b ht,
    gather_expCol_congr b ht]

theorem gather_toSourceEnv_traceNext_congr (ht : e.traceNext = e'.traceNext) :
    (gatherCorrectedFinalTypedEnv b e).toSourceEnv.traceNext =
      (gatherCorrectedFinalTypedEnv b e').toSourceEnv.traceNext := by
  funext k
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gather_baseTraceNext_congr b ht,
    gather_extTraceNext_congr b ht, gather_certBaseNext_congr b ht, gather_certExtNext_congr b ht,
    gather_expColNext_congr b ht]

theorem gather_toSourceEnv_pub_congr (hp : e.pub = e'.pub) :
    (gatherCorrectedFinalTypedEnv b e).toSourceEnv.pub =
      (gatherCorrectedFinalTypedEnv b e').toSourceEnv.pub := by
  funext k
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gather_extensionPublic_congr b hp,
    gather_scalarPublic_congr b hp]

end Gather

/-! ## B. Replacing the IO coordinate -/

/-- `c` with its IO pair replaced by `q`; `(reIO c q).1 ≡ c.1`, `(reIO c q).2.2 ≡ c.2.2`. -/
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

/-- The family public map depends on `c` through `c.1` only (walk block) — so it is unchanged. -/
theorem familyComputePublic_reIO (c : OptimizedProductionChallengeTuple K F) (q : K × K) :
    P.familyComputePublic (reIO c q) = P.familyComputePublic c := by
  funext j
  rfl

/-- Reindexed package traces have the same trace columns at every family width. -/
theorem familyQc_trace (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin P.computeChip.rap.w → F[X]) (ω x : F) (ch pb : ℕ → F) :
    (envOfTrace (familyQc P c Qc) ω x ch pb).trace = (envOfTrace Qc ω x ch pb).trace := by
  funext k
  have hw := computeChipAt_width P c
  simp only [envOfTrace]
  by_cases h : k < P.computeChip.rap.w
  · have h' : k < (P.computeChipAt c).rap.w := by rw [hw]; exact h
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ k < (P.computeChipAt c).rap.w := by rw [hw]; exact h
    rw [dif_neg h', dif_neg h]

theorem familyQc_traceNext (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin P.computeChip.rap.w → F[X]) (ω x : F) (ch pb : ℕ → F) :
    (envOfTrace (familyQc P c Qc) ω x ch pb).traceNext = (envOfTrace Qc ω x ch pb).traceNext := by
  funext k
  have hw := computeChipAt_width P c
  simp only [envOfTrace]
  by_cases h : k < P.computeChip.rap.w
  · have h' : k < (P.computeChipAt c).rap.w := by rw [hw]; exact h
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ k < (P.computeChipAt c).rap.w := by rw [hw]; exact h
    rw [dif_neg h', dif_neg h]

section Rows
variable (c : OptimizedProductionChallengeTuple K F) (q : K × K)
  (Qc : Fin P.computeChip.rap.w → F[X]) (i : Fin (rows P))

/-- The two family envs under comparison: at `c` and at `reIO c q`, both of the package trace `Qc`. -/
abbrev envAt : CorrectedFinalTypedEnv F K := rowEnvAt P c (familyQc P c Qc) i
abbrev envAt' : CorrectedFinalTypedEnv F K := rowEnvAt P (reIO c q) (familyQc P (reIO c q) Qc) i

theorem baseEnv_trace_reIO :
    (envOfTrace (familyQc P (reIO c q) Qc) P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis (reIO c q)) (P.familyComputePublic (reIO c q))).trace =
    (envOfTrace (familyQc P c Qc) P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace := by
  rw [familyQc_trace, familyQc_trace]
  rfl

theorem baseEnv_traceNext_reIO :
    (envOfTrace (familyQc P (reIO c q) Qc) P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis (reIO c q)) (P.familyComputePublic (reIO c q))).traceNext =
    (envOfTrace (familyQc P c Qc) P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).traceNext := by
  rw [familyQc_traceNext, familyQc_traceNext]
  rfl

theorem baseEnv_pub_reIO :
    (envOfTrace (familyQc P (reIO c q) Qc) P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis (reIO c q)) (P.familyComputePublic (reIO c q))).pub =
    (envOfTrace (familyQc P c Qc) P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).pub := by
  show P.familyComputePublic (reIO c q) = P.familyComputePublic c
  exact familyComputePublic_reIO P c q

theorem baseTrace_reIO : (envAt' P c q Qc i).baseTrace = (envAt P c Qc i).baseTrace := by
  funext j
  exact congrFun (baseEnv_trace_reIO P c q Qc i) (j : ℕ)

theorem toSourceEnv_trace_reIO :
    (envAt' P c q Qc i).toSourceEnv.trace = (envAt P c Qc i).toSourceEnv.trace :=
  gather_toSourceEnv_trace_congr P.optimized.basis (baseEnv_trace_reIO P c q Qc i)

theorem toSourceEnv_traceNext_reIO :
    (envAt' P c q Qc i).toSourceEnv.traceNext = (envAt P c Qc i).toSourceEnv.traceNext :=
  gather_toSourceEnv_traceNext_congr P.optimized.basis (baseEnv_traceNext_reIO P c q Qc i)

theorem toSourceEnv_pub_reIO :
    (envAt' P c q Qc i).toSourceEnv.pub = (envAt P c Qc i).toSourceEnv.pub :=
  gather_toSourceEnv_pub_congr P.optimized.basis (baseEnv_pub_reIO P c q Qc i)

/-- The gathered `𝕂` challenge slots `≠ 7, 8` agree. -/
theorem chal_reIO (k : Fin 12) (h7 : (k : ℕ) ≠ 7) (h8 : (k : ℕ) ≠ 8) :
    (envAt' P c q Qc i).chal k = (envAt P c Qc i).chal k := by
  simp only [envAt', envAt, rowEnvAt, gatherCorrectedFinalTypedEnv, envOfTrace]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hk := k.isLt
  have hm := m.isLt
  rw [computeChalValOfTuple_reIO _ _ _ _ (by omega)]

theorem toSourceEnv_chal_reIO (j : ℕ) (h7 : j ≠ 7) (h8 : j ≠ 8) :
    (envAt' P c q Qc i).toSourceEnv.chal j = (envAt P c Qc i).toSourceEnv.chal j := by
  have h9 := chal_reIO P c q Qc i (9 : Fin 12) (by decide) (by decide)
  simp only [CorrectedFinalTypedEnv.toSourceEnv]
  split_ifs with h1 h2
  · exact chal_reIO P c q Qc i ⟨j, h1⟩ h7 h8
  · rw [h9]
  · rfl

/-- **The record of every request slot is unchanged** when the IO coordinate moves. -/
theorem rowRecord_reIO (j : Fin 3) :
    rowRecord (envAt' P c q Qc i) j = rowRecord (envAt P c Qc i) j := by
  funext k
  have hc : ∀ e : Expr, (∀ n ∈ chalIdx e, n ≠ 7 ∧ n ≠ 8) →
      e.eval (envAt' P c q Qc i).toSourceEnv = e.eval (envAt P c Qc i).toSourceEnv :=
    fun e he => eval_congr_of_chalIdx e (toSourceEnv_trace_reIO P c q Qc i)
      (toSourceEnv_traceNext_reIO P c q Qc i) (toSourceEnv_pub_reIO P c q Qc i)
      (fun n hn => toSourceEnv_chal_reIO P c q Qc i n (he n hn).1 (he n hn).2)
  have hslot := no_slot_reads_io j k
  unfold rowRecord
  simp only [slotExpr] at hslot
  split_ifs at hslot ⊢ <;> exact hc _ hslot

theorem rowRequests_reIO :
    rowRequests (envAt' P c q Qc i) = rowRequests (envAt P c Qc i) := by
  simp only [rowRequests]
  congr 1
  funext j
  rw [activeMask_congr (baseTrace_reIO P c q Qc i) j, rowRecord_reIO P c q Qc i j]

end Rows

/-- **The family request list does not read the IO pair.** -/
theorem hostileRequestsAt_reIO (c : OptimizedProductionChallengeTuple K F) (q : K × K)
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    hostileRequestsAt P (reIO c q) (familyQc P (reIO c q) Qc) =
      hostileRequestsAt P c (familyQc P c Qc) := by
  unfold hostileRequestsAt
  exact congrArg List.flatten (congrArg List.ofFn (funext fun i => rowRequests_reIO P c q Qc i))

/-! ## C. The memory side: reindexing and the package response list -/

theorem honestQm_famQm (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X]) : honestQm P c (famQm P c Qm) = Qm := by
  funext j
  unfold honestQm famQm
  apply congrArg Qm
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

theorem honestQc_familyQc (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin P.computeChip.rap.w → F[X]) : honestQc P c (familyQc P c Qc) = Qc := by
  funext j
  unfold honestQc familyQc
  apply congrArg Qc
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

/-- The family response list at a reindexed package trace is the package's: coin-free. -/
theorem hostileResponsesAt_famQm (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    hostileResponsesAt P c (famQm P c Qm) = P.hostileResponses Qm := by
  rw [hostileResponsesAt_eq_package, honestQm_famQm]

/-! ## D. -/

variable (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])

/-- The record function of the nine non-IO coordinates that `famIOEventOf` is fibred over. -/
def famR (r : Rest K) : FiniteIO.PreChallengeRecords K 10 :=
  hostileRecordsAt P (r.1, ((0, 0), r.2)) (famQm P (r.1, ((0, 0), r.2)) Qm)
    (familyQc P (r.1, ((0, 0), r.2)) Qc)

/-- `hostileRequestsAt_reIO` in destructured form. -/
theorem hostileRequestsAt_io_free (c1 : JointCoins K) (q q' : K × K)
    (c22 : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K ×
      OptimizedMemoryCollisionAccounting.MemoryChallengeTuple K)
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    hostileRequestsAt P (c1, (q, c22)) (familyQc P (c1, (q, c22)) Qc) =
      hostileRequestsAt P (c1, (q', c22)) (familyQc P (c1, (q', c22)) Qc) :=
  hostileRequestsAt_reIO P (c1, (q', c22)) q Qc

theorem records_eq_famR (c : OptimizedProductionChallengeTuple K F) :
    hostileRecordsAt P c (famQm P c Qm) (familyQc P c Qc) = famR P Qc Qm (restOf c) := by
  obtain ⟨c1, q, c22⟩ := c
  show hostileRecordsAt P (c1, (q, c22)) (famQm P (c1, (q, c22)) Qm) (familyQc P (c1, (q, c22)) Qc) =
    hostileRecordsAt P (c1, ((0, 0), c22)) (famQm P (c1, ((0, 0), c22)) Qm)
      (familyQc P (c1, ((0, 0), c22)) Qc)
  unfold hostileRecordsAt
  rw [hostileResponsesAt_famQm, hostileResponsesAt_famQm,
    hostileRequestsAt_io_free P c1 q (0, 0) c22 Qc]

theorem famIOEventOf_eq_fibred :
    famIOEventOf P Qc Qm = famIOEvent (F := F) (famR P Qc Qm) := by
  ext c
  simp only [famIOEventOf, famIOEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    records_eq_famR]

theorem famR_requests_le (r : Rest K) :
    (famR P Qc Qm r).requests.length ≤ 3 * P.optimized.family.problem.cfg.compRows := by
  simp only [famR, hostileRecordsAt_requests]
  rw [hostileRequestsAt_length_eq, honestQc_familyQc]
  exact P.hostileRequests_length_le Qc

theorem famR_responses_le (r : Rest K) :
    (famR P Qc Qm r).responses.length ≤ P.optimized.family.problem.cfg.memRows := by
  simp only [famR, hostileRecordsAt_responses]
  rw [hostileResponsesAt_famQm]
  exact P.hostileResponses_length_le Qm

theorem famIOEventOf_card_le :
    (famIOEventOf P Qc Qm).card ≤
      Fintype.card K ^ 9 *
        FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
          P.optimized.family.problem.cfg.memRows (Fintype.card K) := by
  rw [famIOEventOf_eq_fibred]
  exact famIOEvent_card_le _ _ _ (famR_requests_le P Qc Qm) (famR_responses_le P Qc Qm)

theorem famIOEventOf_card_le_hostileIOWork :
    (famIOEventOf P Qc Qm).card ≤ Fintype.card K ^ 9 * P.hostileIOWork :=
  famIOEventOf_card_le P Qc Qm

/-- And conversely: the event is exactly the complement of `FamilyIOGood`. -/
theorem mem_famIOEventOf_iff (c : OptimizedProductionChallengeTuple K F) :
    c ∈ famIOEventOf P Qc Qm ↔ ¬ FamilyIOGood P c (familyQc P c Qc) (famQm P c Qm) := by
  simp [famIOEventOf, FamilyIOGood]

end

end Nock.RedTeam.Batch884

#print axioms Nock.RedTeam.Batch884.hostileRequestsAt_reIO
#print axioms Nock.RedTeam.Batch884.famIOEventOf_card_le
#print axioms Nock.RedTeam.Batch884.familyIOGood_of_not_mem
