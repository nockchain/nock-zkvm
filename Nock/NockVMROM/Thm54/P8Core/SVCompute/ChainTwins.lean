/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/ChainTwins.lean

  **The `FamilyIOChainCompute` / `FamilyIOChainRouteB` chain skeletons
  at a datum and a layout.**  The accumulator chain (`acc_first`, `step_at`, `chain_at`,
  `next_acc`, `acc_eq_prefixSum`), the `ln` chain (`ln_chain_at`, `ln_recurrence`, `lnPrev_at`),
  the serial carrier (`expCol_first`, `expCol_step`, `expCol_eq_prefixExp`) and the bound
  `totalRequests ≤ 3·rows` — every statement over `(D : ChipData) (L : ChipLayout)` and the row
  facts `RF : RowFacts D L c Q` of an accepted family trace `Q : Fin (chipOf D L c).rap.w → F[X]`.
  The gate-reading twins (`expCol_*`) take the layout's gate membership (`hL`) and read the serial
  column at `L.serial`.  Each twin is the live proof with `rowEnvAt P c Qc` replaced by
  `rowEnvAtD D c Q`, `rows P` by `D.N`, `row_obligations_at` / `masks_at_row_at` by `RF`.
-/
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.FamilyIOChainCompute
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.P8Core.SVCompute.EnvTwins

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyIOChain

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] {h : ℕ}
  (D : ChipData F K h) (L : ChipLayout F K h)
  (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOf D L c).rap.w → F[X])

/-! ## 0. Width and challenge facts -/

/-- Every `𝕂`-role coordinate (roles `< 63`) is a column of the chip. -/
theorem ext_idx_lt (hR : 63 ≤ L.nRoles) (r : Fin 63) (k : Fin 3) :
    correctedFinalExtCoordIndex (e := 3) r k < (chipOf D L c).rap.w := by
  rw [chipOf_w]
  have h1 := L.roles_fit
  have h2 := r.isLt
  have h3 := k.isLt
  unfold correctedFinalExtCoordIndex
  omega

/-- Slot `q` of the family environment is `computeKOfTuple c q`. -/
theorem rowEnvAtD_chal (i : Fin D.N) (q : Fin 12) :
    (rowEnvAtD D c Q i).toSourceEnv.chal q.val = computeKOfTuple c q.val := by
  have hq : (q : ℕ) < 12 := q.isLt
  simp only [CorrectedFinalTypedEnv.toSourceEnv, rowEnvAtD, gatherCorrectedFinalTypedEnv,
    envOfTrace, hq, ↓reduceDIte]
  change (∑ k : Fin 3,
      computeChalValOfTuple D.basis c (3 * (q : ℕ) + (k : ℕ)) • D.basis k) =
    computeKOfTuple c q.val
  have hslot : ∀ k : Fin 3, 3 * (q : ℕ) + (k : ℕ) < 36 := by
    intro k; omega
  have hcoord : ∀ k : Fin 3,
      computeChalValOfTuple D.basis c (3 * (q : ℕ) + (k : ℕ)) =
        coord D.basis (computeKOfTuple c q.val) k := by
    intro k
    simp only [computeChalValOfTuple, hslot k, ↓reduceIte]
    have hdiv : (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by omega
    have hmod : (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by omega
    rw [hdiv]
    apply congrArg
    exact Fin.ext hmod
  simp_rw [hcoord]
  exact reconstruct_coord D.basis (computeKOfTuple c q.val)

theorem zZinv_at_rowEnvAtD (i : Fin D.N) (hz : nprSeed c.1 ≠ 0) :
    (zZinvExpr.subst computeSubst).eval (rowEnvAtD D c Q i).toSourceEnv = 0 := by
  have h1 := rowEnvAtD_chal D L c Q i ⟨1, by decide⟩
  have h5 := rowEnvAtD_chal D L c Q i ⟨5, by decide⟩
  simp [zZinvExpr, Expr.subst, computeSubst, computeTraceSubst, chl, tc, Expr.eval, h1, h5]
  show nprSeed c.1 * (nprSeed c.1)⁻¹ - 1 = 0
  rw [mul_inv_cancel₀ hz, sub_self]

theorem alphaAt_rowEnvAtD (i : Fin D.N) : alphaAt (rowEnvAtD D c Q i) = chipAlphaAt c := by
  unfold alphaAt
  exact rowEnvAtD_chal D L c Q i ⟨0, by decide⟩

variable {D L c Q}

/-! ## 1. The accumulator chain -/

section Acc

variable (RF : RowFacts D L c Q)
include RF

/-- Twin of `acc_first`. -/
theorem acc_first_atD : (rowEnvAtD D c Q (firstRowD D)).extTrace 32 = 0 := by
  have hgate := (RF.obl (firstRowD D)).endpointDegreeTwo2 _ anchors_mem_endpoint2.1
  rw [accInit_eval, (RF.masks (firstRowD D)).1] at hgate
  simpa using hgate

/-- Twin of `step_at`. -/
theorem step_at_atD (i : Fin D.N) : correctedAccAfterStep.eval (rowEnvAtD D c Q i) = 0 := by
  have h := (RF.obl i).residualAux3 2
  simpa [correctedAuxSemanticValue] using h

/-- Off the last row the base mask `12` is `0`. -/
theorem notLast_atD (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (rowEnvAtD D c Q i).baseTrace 12 = 0 := by
  rw [(RF.masks i).2, if_neg]
  omega

/-- Twin of `chain_at`. -/
theorem chain_at_atD (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (rowEnvAtD D c Q i).extTrace 60 = (rowEnvAtD D c Q i).extTraceNext 32 := by
  have h := (RF.obl i).extensionCore21 packedChainId
  have hnl := notLast_atD RF i hi
  simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
    ↓reduceIte] at h
  simpa [accAfterChain, CorrectedFinalTypedExpr.eval, hnl, sub_eq_zero] using h

end Acc

/-- Twin of `next_acc` (orbit alignment of role `32`). -/
theorem next_acc_atD (hadj : D.Adjacent) (hR : 63 ≤ L.nRoles) (i : Fin D.N)
    (hi : (i : ℕ) + 1 < D.N) :
    (rowEnvAtD D c Q i).extTraceNext 32 = (rowEnvAtD D c Q ⟨(i : ℕ) + 1, hi⟩).extTrace 32 := by
  have hadj := hadj i hi
  simp only [rowEnvAtD, gatherCorrectedFinalTypedEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt := ext_idx_lt D L c hR (32 : Fin 63) k
  simp only [envOfTrace, dif_pos hlt]
  rw [hadj]

/-- Twin of `prefixSum`. -/
def prefixSumAtD (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F) {w : ℕ}
    (Q : Fin w → F[X]) (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if hk : k < D.N then rowTerm (rowEnvAtD D c Q ⟨k, hk⟩) else 0

theorem prefixSumAtD_succ (m : ℕ) (hm : m < D.N) :
    prefixSumAtD D c Q (m + 1) = prefixSumAtD D c Q m + rowTerm (rowEnvAtD D c Q ⟨m, hm⟩) := by
  simp [prefixSumAtD, Finset.sum_range_succ, hm]

/-- Twin of `acc_eq_prefixSum`. -/
theorem acc_eq_prefixSum_atD (RF : RowFacts D L c Q) (hadj : D.Adjacent) (hR : 63 ≤ L.nRoles)
    (hden : ∀ (i : Fin D.N) (j : Fin 3), safeDenomWitness (rowEnvAtD D c Q i) j ≠ 0) :
    ∀ (m : ℕ) (hm : m < D.N), (rowEnvAtD D c Q ⟨m, hm⟩).extTrace 32 = prefixSumAtD D c Q m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixSumAtD, Finset.range_zero, Finset.sum_empty]
      exact acc_first_atD RF
  | succ m ih =>
      intro hm
      have hm' : m < D.N := by omega
      rw [← next_acc_atD hadj hR ⟨m, hm'⟩ hm, ← chain_at_atD RF ⟨m, hm'⟩ hm,
        accAfter_eq_of_step _ (step_at_atD RF ⟨m, hm'⟩) (hden _), ih hm',
        prefixSumAtD_succ m hm']

/-! ## 2. The `ln` chain -/

/-- Twin of `ln_chain_at`. -/
theorem ln_chain_at_atD (RF : RowFacts D L c Q) (hadj : D.Adjacent) (hR : 63 ≤ L.nRoles)
    (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    lnCurAt (rowEnvAtD D c Q i) = lnPrevAt (rowEnvAtD D c Q ⟨(i : ℕ) + 1, hi⟩) := by
  have hnl := notLast_atD RF i hi
  rw [ln_chain (RF.obl i) hnl]
  have hadj := hadj i hi
  unfold lnPrevAt
  simp only [rowEnvAtD, gatherCorrectedFinalTypedEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt := ext_idx_lt D L c hR (54 : Fin 63) k
  simp only [envOfTrace, dif_pos hlt]
  rw [hadj]

/-- The selector gates at a row (twin of `selector_gates_at_family`). -/
theorem selector_gates_atD (RF : RowFacts D L c Q) (i : Fin D.N) :
    (∀ (k : ℕ) (hk : k < 11),
      (rowEnvAtD D c Q i).baseTrace ⟨k, by omega⟩ = 0 ∨
        (rowEnvAtD D c Q i).baseTrace ⟨k, by omega⟩ = 1) ∧
    ((rowEnvAtD D c Q i).baseTrace ⟨0, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨1, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨2, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨3, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨4, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨5, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨6, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨7, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨8, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨9, by norm_num⟩ +
      (rowEnvAtD D c Q i).baseTrace ⟨10, by norm_num⟩) = 1 := by
  have hb := (RF.obl i).base15
  set envF := envFAtD D c Q i with hE
  have hbase : ∀ k : ℕ, (hk : k < 13) →
      (rowEnvAtD D c Q i).baseTrace ⟨k, hk⟩ = envF.trace k :=
    fun _ _ => rfl
  constructor
  · intro k hk
    have hg := hb (selectorBool k) (by
      simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨k, hk, rfl⟩)
    rw [hbase k (by omega)]
    simp only [selectorBool, bv, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at hg
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · have hg := hb selectorOneHot (by simp [finalBaseTransitionGates])
    simp [selectorOneHot, selectorSum, CoeffExpr.sumList, List.range_succ, bv, CoeffExpr.eval,
      sub_eq_zero] at hg
    change envF.trace 0 + envF.trace 1 + envF.trace 2 + envF.trace 3 + envF.trace 4 +
      envF.trace 5 + envF.trace 6 + envF.trace 7 + envF.trace 8 + envF.trace 9 +
      envF.trace 10 = 1
    linear_combination hg

/-- Twin of `rowSelector_oneHot_at`. -/
theorem rowSelector_oneHot_atD (RF : RowFacts D L c Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin D.N) :
    ∃ s, rowSelector (rowEnvAtD D c Q i) = Nock.ComputeTable.opSel s := by
  obtain ⟨hbool, hsum⟩ := selector_gates_atD RF i
  apply Nock.ComputeTable.oneHot_of_bool_sum _ hchar
  · intro st
    rcases hbool (Nock.Reified.opCol st) (by cases st <;> decide) with h | h
    · left; simp [rowSelector, h]
    · right; simp [rowSelector, h]
  · have hK := congrArg (algebraMap F K) hsum
    simp only [map_add, map_one] at hK
    simp only [rowSelector, Nock.ComputeTable.sum09, Nock.Reified.opCol]
    linear_combination hK

/-- Twin of `source_selector_at`. -/
theorem source_selector_atD (RF : RowFacts D L c Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin D.N) :
    ∃ s, ∀ st, (rowEnvAtD D c Q i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot_atD RF hchar i
  refine ⟨s, fun st => ?_⟩
  rw [source_trace_base _ (opCol st) (by cases st <;> decide)]
  exact congrFun hs st

/-- Twin of `rowArity_eq_arity_at`. -/
theorem rowArity_eq_arity_atD (i : Fin D.N) (s : ComputeTable.State)
    (hsel : ∀ st, (rowEnvAtD D c Q i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) :
    rowArity (rowEnvAtD D c Q i) = arity s := by
  have h0 := hsel .s0; have h2 := hsel .s2; have h5 := hsel .s5; have h6 := hsel .s6
  have h7 := hsel .s7; have h8 := hsel .s8; have h9 := hsel .s9
  simp only [opCol] at h0 h2 h5 h6 h7 h8 h9
  unfold rowArity
  simp only [activeMask, sampledActive, Expr.eval, Fin.isValue, Fin.val_one, Fin.val_two, h0, h2,
    h5, h6, h7, h8, h9]
  cases s <;> simp [ComputeTable.opSel, arity]

/-- Twin of `ln_recurrence_at`. -/
theorem ln_recurrence_at_atD (RF : RowFacts D L c Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (hz0 : nprSeed c.1 ≠ 0) (i : Fin D.N) :
    lnCurAt (rowEnvAtD D c Q i) =
      lnPrevAt (rowEnvAtD D c Q i) * chipAlphaAt c ^ rowArity (rowEnvAtD D c Q i) := by
  obtain ⟨s, hsel⟩ := source_selector_atD RF hchar i
  have h := ln_recurrence (RF.obl i) s hsel (zZinv_at_rowEnvAtD D L c Q i hz0)
  rw [alphaAt_rowEnvAtD] at h
  rw [rowArity_eq_arity_atD i s hsel]
  exact h

/-- Twin of `prefixExp`. -/
def prefixExpAtD (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F) {w : ℕ}
    (Q : Fin w → F[X]) (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, if hk : k < D.N then rowArity (rowEnvAtD D c Q ⟨k, hk⟩) else 0

theorem prefixExpAtD_succ (m : ℕ) (hm : m < D.N) :
    prefixExpAtD D c Q (m + 1) = prefixExpAtD D c Q m + rowArity (rowEnvAtD D c Q ⟨m, hm⟩) := by
  simp [prefixExpAtD, Finset.sum_range_succ, hm]

theorem prefixExpAtD_mono {a b : ℕ} (hab : a ≤ b) :
    prefixExpAtD D c Q a ≤ prefixExpAtD D c Q b := by
  unfold prefixExpAtD
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun _ _ _ => Nat.zero_le _)

/-- Twin of `ln0`. -/
def ln0AtD (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F) {w : ℕ}
    (Q : Fin w → F[X]) : K :=
  lnPrevAt (rowEnvAtD D c Q (firstRowD D))

/-- Twin of `hostile_ln0_eq_one`. -/
theorem hostile_ln0_eq_one_atD (RF : RowFacts D L c Q) : ln0AtD D c Q = 1 := by
  have hgate := (RF.obl (firstRowD D)).endpointDegreeTwo2 _ lnInit_mem_endpoint2
  rw [lnInit_eval, (RF.masks (firstRowD D)).1] at hgate
  simp only [firstRowD, if_true, map_one, one_mul, sub_eq_zero] at hgate
  exact hgate

/-- Twin of `lnPrev_at`: `ln_prev(m) = ln₀ · (alphaM c.1)^{S(m)}`. -/
theorem lnPrev_at_atD (RF : RowFacts D L c Q) (hadj : D.Adjacent) (hR : 63 ≤ L.nRoles)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (hz0 : nprSeed c.1 ≠ 0) :
    ∀ (m : ℕ) (hm : m < D.N),
      lnPrevAt (rowEnvAtD D c Q ⟨m, hm⟩) = ln0AtD D c Q * chipAlphaAt c ^ prefixExpAtD D c Q m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixExpAtD, Finset.range_zero, Finset.sum_empty, pow_zero, mul_one]
      rfl
  | succ m ih =>
      intro hm
      have hm' : m < D.N := by omega
      rw [← ln_chain_at_atD RF hadj hR ⟨m, hm'⟩ hm,
        ln_recurrence_at_atD RF hchar hz0 ⟨m, hm'⟩, ih hm', prefixExpAtD_succ m hm',
        pow_add, mul_assoc]

/-! ## 3. The request count -/

/-- Twin of `totalRequests`. -/
def totalRequestsAtD (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F) {w : ℕ}
    (Q : Fin w → F[X]) : ℕ := prefixExpAtD D c Q D.N

/-- Twin of `totalRequestsAt_le`. -/
theorem totalRequestsAt_leD : totalRequestsAtD D c Q ≤ 3 * D.N := by
  unfold totalRequestsAtD prefixExpAtD
  calc (∑ k ∈ Finset.range D.N,
        if hk : k < D.N then rowArity (rowEnvAtD D c Q ⟨k, hk⟩) else 0)
      ≤ ∑ _k ∈ Finset.range D.N, 3 := by
        refine Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact rowArity_le _
        · omega
    _ = 3 * D.N := by simp [mul_comm]

/-! ## 4. The serial carrier (gates read at `L.serial`) -/

section Serial

/-- The typed environment's carrier column is base column `computeExpCol` (`302`), which the layout
names as its serial (`hs : L.serial = computeExpCol`, `rfl` at `layout309`). -/
theorem expCol_eq_trace_atD (i : Fin D.N) :
    (rowEnvAtD D c Q i).expCol = (envFAtD D c Q i).trace computeExpCol := rfl

theorem baseTrace_eq_atD (i : Fin D.N) (k : Fin 13) :
    (rowEnvAtD D c Q i).baseTrace k = (envFAtD D c Q i).trace k := rfl

theorem next_expCol_atD (hadj : D.Adjacent) (hs : (L.serial : ℕ) = computeExpCol) (i : Fin D.N)
    (hi : (i : ℕ) + 1 < D.N) :
    (envFAtD D c Q i).traceNext computeExpCol = (rowEnvAtD D c Q ⟨(i : ℕ) + 1, hi⟩).expCol := by
  have hadj := hadj i hi
  have hlt : computeExpCol < (chipOf D L c).rap.w := by
    rw [chipOf_w, ← hs]; exact L.serial.isLt
  simp only [envFAtD, envOfTrace, dif_pos hlt]
  show _ = (envFAtD D c Q ⟨(i : ℕ) + 1, hi⟩).trace computeExpCol
  simp only [envFAtD, envOfTrace, dif_pos hlt]
  rw [hadj]

/-- The serial gates of the layout are the carrier gates (`computeExpGates`) — the premise a layout
instance discharges (`gates309`'s `serial` is `computeExpGates`). -/
def SerialIsExp (D : ChipData F K h) (L : ChipLayout F K h) : Prop :=
  ∀ g ∈ computeExpGates (F := F), g ∈ (L.gates D).serial

/-- Twin of `Batch672.expCol_first`: `S(0) = 0`. -/
theorem expCol_first_atD (RF : RowFacts D L c Q) (hL : L.GatesOK D) (hse : SerialIsExp D L) :
    (rowEnvAtD D c Q (firstRowD D)).expCol = 0 := by
  have h := RF.gates (firstRowD D) expInitGate (hL _ (by
    simp only [SharedGateSet.toList, List.mem_append]
    exact Or.inr (hse expInitGate (by simp [computeExpGates]))))
  have hm := (RF.masks (firstRowD D)).1
  rw [baseTrace_eq_atD] at hm
  simp only [expInitGate, CoeffExpr.eval] at h
  have h11 : (envFAtD D c Q (firstRowD D)).trace 11 = 1 := by simpa using hm
  rw [expCol_eq_trace_atD]
  simpa [h11] using h

/-- Twin of `Batch672.base_selector`. -/
theorem base_selector_atD (RF : RowFacts D L c Q) (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin D.N) :
    ∃ s, (∀ st, (rowEnvAtD D c Q i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) ∧
      ∀ k : ℕ, k < 11 →
        (envFAtD D c Q i).trace k =
          if k = (OptimizedComputeCodec.stateIndex s : ℕ) then 1 else 0 := by
  obtain ⟨s, hsel⟩ := source_selector_atD RF hchar i
  refine ⟨s, hsel, fun k hk => ?_⟩
  have hF : ∀ st, (envFAtD D c Q i).trace (opCol st) = ComputeTable.opSel s st := by
    intro st
    have h := hsel st
    rw [source_trace_base _ (opCol st) (by cases st <;> decide)] at h
    have hinj := (algebraMap F K).injective
    apply hinj
    rw [show (rowEnvAtD D c Q i).baseTrace ⟨opCol st, by cases st <;> decide⟩ =
      (envFAtD D c Q i).trace (opCol st) from rfl] at h
    rw [h]
    simp only [ComputeTable.opSel]
    split_ifs <;> simp
  obtain ⟨st, rfl⟩ : ∃ st : ComputeTable.State, opCol st = k := by
    interval_cases k
    exacts [⟨.s0, rfl⟩, ⟨.s1, rfl⟩, ⟨.s2, rfl⟩, ⟨.s3, rfl⟩, ⟨.s4, rfl⟩, ⟨.s5, rfl⟩,
      ⟨.s6, rfl⟩, ⟨.s7, rfl⟩, ⟨.s8, rfl⟩, ⟨.s9, rfl⟩, ⟨.cons, rfl⟩]
  rw [hF st]
  by_cases h : st = s
  · subst h; simp [ComputeTable.opSel, (opCol_eq_stateIndex_iff' st st).2 rfl]
  · have h' : opCol st ≠ (OptimizedComputeCodec.stateIndex s : ℕ) :=
      fun he => h ((opCol_eq_stateIndex_iff' st s).1 he)
    simp [ComputeTable.opSel, h, h']

/-- Twin of `Batch672.expCol_step`: `S(i + 1) = S(i) + arity(i)` off the last row. -/
theorem expCol_step_atD (RF : RowFacts D L c Q) (hL : L.GatesOK D)
    (hadj : D.Adjacent) (hs : (L.serial : ℕ) = computeExpCol)
    (hse : SerialIsExp D L)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (rowEnvAtD D c Q ⟨(i : ℕ) + 1, hi⟩).expCol =
      (rowEnvAtD D c Q i).expCol + ((rowArity (rowEnvAtD D c Q i) : ℕ) : F) := by
  have h := RF.gates i expStepGate (hL _ (by
    simp only [SharedGateSet.toList, List.mem_append]
    exact Or.inr (hse expStepGate (by simp [computeExpGates]))))
  have hm := (RF.masks i).2
  rw [baseTrace_eq_atD] at hm
  have h12 : (envFAtD D c Q i).trace 12 = 0 := by
    have hne : (i : ℕ) ≠ D.N - 1 := by omega
    simpa [hne] using hm
  obtain ⟨s, hsel, hselF⟩ := base_selector_atD RF hchar i
  have harity : (arityForm (F := F)).eval (envFAtD D c Q i) = ((arity s : ℕ) : F) := by
    simp only [arityForm, List.range, List.range.loop, List.foldr, CoeffExpr.eval]
    rw [hselF 0 (by omega), hselF 1 (by omega), hselF 2 (by omega), hselF 3 (by omega),
      hselF 4 (by omega), hselF 5 (by omega), hselF 6 (by omega), hselF 7 (by omega),
      hselF 8 (by omega), hselF 9 (by omega), hselF 10 (by omega)]
    cases s <;> simp [OptimizedComputeCodec.stateIndex, arityCoeff, arity]
  have hra := rowArity_eq_arity_atD i s hsel
  simp only [expStepGate, CoeffExpr.eval] at h
  rw [h12, sub_zero, one_mul, harity, next_expCol_atD hadj hs i hi] at h
  rw [hra, ← expCol_eq_trace_atD] at *
  linear_combination h

/-- Twin of `Batch672.expCol_eq_prefixExp`: `S(m) = (prefixExpAtD m : 𝔽)`. -/
theorem expCol_eq_prefixExp_atD (RF : RowFacts D L c Q) (hL : L.GatesOK D)
    (hadj : D.Adjacent) (hs : (L.serial : ℕ) = computeExpCol)
    (hse : SerialIsExp D L)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    ∀ (m : ℕ) (hm : m < D.N),
      (rowEnvAtD D c Q ⟨m, hm⟩).expCol = ((prefixExpAtD D c Q m : ℕ) : F) := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixExpAtD, Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
      exact expCol_first_atD RF hL hse
  | succ m ih =>
      intro hm
      have hm' : m < D.N := by omega
      rw [expCol_step_atD RF hL hadj hs hse hchar ⟨m, hm'⟩ hm, ih hm', prefixExpAtD_succ m hm']
      push_cast
      ring

end Serial

end

end Nock.NockVMROM.Thm54.SVCompute
