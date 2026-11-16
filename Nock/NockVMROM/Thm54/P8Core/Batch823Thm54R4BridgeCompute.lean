/-
  Nock/NockVMROM/Thm54/P8Core/Batch823Thm54R4BridgeCompute.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch823Thm54R4BridgeCompute`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch823Thm54R4BridgeCompute.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.FormRBridgeTelescope
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainRouteB
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch823

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.OptimizedComputeFormRSlots
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent

noncomputable section

section Generic

variable {K : Type} [Field K]

/-- Truncate a range sum at a vanishing tail. -/
theorem sum_range_trunc (f : ℕ → K) (n m : ℕ) (h : ∀ j, m ≤ j → j < n → f j = 0) :
    ∑ j ∈ Finset.range n, f j = ∑ j ∈ Finset.range (min n m), f j := by
  symm
  refine Finset.sum_subset (Finset.range_mono (min_le_left n m)) fun j hj hj' => ?_
  have h1 := Finset.mem_range.mp hj
  have h2 : ¬ j < min n m := fun h => hj' (Finset.mem_range.mpr h)
  exact h j (by omega) h1

/-- `Cpoly` evaluated at `λ`. -/
theorem Cpoly_eval (N : ℕ) (cb : ℕ → Bool) (l : K) :
    (Batch554.Cpoly (K := K) N cb).eval l =
      l ^ N + ∑ j ∈ Finset.range N, Batch554.bit (K := K) (cb (j + 1)) * l ^ (N - (j + 1)) := by
  simp [Batch554.Cpoly, eval_finsetSum]

/-- The in-gate `C'` sum of a source environment with boolean certificate bits is
`(C'poly n (rowBits E)).eval λ`. -/
theorem cprime_eval (E : Env K) (l : K) (n : ℕ) (hn : MemoryTable.pwScaleExp K = n - 1)
    (h100 : ∀ d, d < 64 → E.chal (100 + d) = lamPowVal l d)
    (hbits : ∀ j, j < 63 → j + 1 ≤ n - 1 → E.trace (202 + j) = 0 ∨ E.trace (202 + j) = 1) :
    (sampledCprime .traceCur).eval E = (Batch575.C'poly (K := K) n (rowBits E)).eval l := by
  rw [sampledCprime_eval, h100 0 (by decide), lamPowVal_zero]
  unfold Batch575.C'poly
  rw [Cpoly_eval, hn]
  congr 1
  set N := n - 1
  have hL : ∑ j ∈ Finset.range 63, E.trace (202 + j) * E.chal (100 + (j + 1)) =
      ∑ j ∈ Finset.range (min 63 N), E.trace (202 + j) * E.chal (100 + (j + 1)) := by
    refine sum_range_trunc _ 63 N fun j hj hj63 => ?_
    rw [h100 (j + 1) (by omega)]
    simp [lamPowVal, hn, show ¬ j + 1 ≤ N by omega]
  have hR : ∑ j ∈ Finset.range N, Batch554.bit (K := K) (rowBits E (j + 1)) * l ^ (N - (j + 1)) =
      ∑ j ∈ Finset.range (min N 63),
        Batch554.bit (K := K) (rowBits E (j + 1)) * l ^ (N - (j + 1)) := by
    refine sum_range_trunc _ N 63 fun j hj hjN => ?_
    simp [rowBits, show ¬ j + 1 ≤ 63 by omega, Batch554.bit]
  rw [hL, hR, min_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [h100 (j + 1) (by omega)]
  simp only [lamPowVal, hn, if_pos (show j + 1 ≤ N by omega)]
  congr 1
  rcases hbits j (by omega) (by omega) with h0 | h1
  · rw [h0]; simp [rowBits, h0, Batch554.bit]
  · rw [h1]; simp [rowBits, h1, Batch554.bit, show 1 ≤ j + 1 by omega, show j + 1 ≤ 63 by omega]

/-- `finalSampledNamespace` leaves every trace variable and every challenge other than `6, 7`. -/
theorem ofSubst_trace (E : Env K) : (Env.ofSubst finalSampledNamespace E).trace = E.trace := by
  funext i; rfl

theorem ofSubst_chal (E : Env K) (i : ℕ) (h6 : i ≠ 6) (h7 : i ≠ 7) :
    (Env.ofSubst finalSampledNamespace E).chal i = E.chal i := by
  change (finalSampledNamespace .challenge i).eval E = E.chal i
  unfold finalSampledNamespace
  split
  · exact absurd rfl h6
  · exact absurd rfl h7
  · rfl

/-- **The slot map on one environment.**  One-hot selectors `s`, `λ` at challenge `9`, the
`λ`-power leaves at `100 + d`, `T = λ^{rowShift}` at trace `299`, boolean certificate bits: an
active slot `j`'s Form R record slots are `λ ^ shift` and `C'poly n bits` at `λ` of the C-a
certificate `slotCert`. -/
theorem slots_of_env {N : ℕ} (envsC : Fin N → Env K) (a : Fin N) (E : Env K)
    (hE : (envsC a).trace = E.trace) (l : K) (n : ℕ) (hn : MemoryTable.pwScaleExp K = n - 1)
    (s : ComputeTable.State)
    (hsel : ∀ st, E.trace (Nock.Reified.opCol st) = ComputeTable.opSel s st)
    (h9 : E.chal 9 = l)
    (h100 : ∀ d, d < 64 → E.chal (100 + d) = lamPowVal l d)
    (hbits : ∀ j, j < 63 → j + 1 ≤ n - 1 → E.trace (202 + j) = 0 ∨ E.trace (202 + j) = 1)
    (hT : E.trace 299 = l ^ rowShift E)
    (j : Fin 3) (hact : (sampledActive .traceCur (j : ℕ)).eval E = 1) :
    (sampledSlotT .traceCur (67 + 8 * (j : ℕ))).eval E = l ^ (slotCert envsC a j).1 ∧
      (sampledSlotC .traceCur (67 + 8 * (j : ℕ))).eval E =
        (Batch575.C'poly (K := K) n (slotCert envsC a j).2).eval l := by
  have hC := cprime_eval E l n hn h100 hbits
  have hl0 : E.chal 100 = l ^ (n - 1) := by
    rw [h100 0 (by decide), lamPowVal_zero, hn]
  have hl1 : E.chal 101 = if 1 ≤ n - 1 then l ^ (n - 1 - 1) else 0 := by
    rw [h100 1 (by decide)]; simp [lamPowVal, hn]
  have hrow : rowShift (envsC a) = rowShift E := by unfold rowShift; rw [hE]
  have hbitsEq : rowBits (envsC a) = rowBits E := by funext k; unfold rowBits; rw [hE]
  have s0 := hsel .s0; have s2 := hsel .s2; have s5 := hsel .s5; have s6 := hsel .s6
  have s7 := hsel .s7; have s8 := hsel .s8; have s9 := hsel .s9; have s1 := hsel .s1
  have s3 := hsel .s3; have s4 := hsel .s4
  simp only [Nock.Reified.opCol, ComputeTable.opSel] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  have t0 : (envsC a).trace 0 = E.trace 0 := by rw [hE]
  have t9 : (envsC a).trace 9 = E.trace 9 := by rw [hE]
  -- `C'poly n (k = 1)` and `C'poly n ∅` at `λ`
  have hCone : (Batch575.C'poly (K := K) n (fun k => decide (k = 1))).eval l =
      l ^ (n - 1) + (if 1 ≤ n - 1 then l ^ (n - 1 - 1) else 0) := by
    unfold Batch575.C'poly
    rw [Cpoly_eval]
    congr 1
    rcases Nat.eq_zero_or_pos (n - 1) with h0 | hpos
    · rw [h0]; simp
    · rw [if_pos (by omega)]
      obtain ⟨M, hM⟩ : ∃ M, n - 1 = M + 1 := ⟨n - 1 - 1, by omega⟩
      rw [hM, Finset.sum_range_succ']
      simp [Batch554.bit]
  have hCnone : (Batch575.C'poly (K := K) n (fun _ => false)).eval l = l ^ (n - 1) := by
    unfold Batch575.C'poly
    rw [Cpoly_eval]
    simp [Batch554.bit]
  fin_cases j
  · -- slot 0 (base 67): the constant `(λ, λ^{n−1} + λ^{n−2})` = certificate `(1, {1})`
    simp only [slotCert]
    refine ⟨?_, ?_⟩
    · simp [sampledSlotT, sampledLam, Expr.eval, h9]
    · simp only [mul_zero, add_zero, sampledSlotC, lamPowVar,
        Expr.eval]
      rw [hCone, hl0, hl1]
  · -- slot 1 (base 75): `op₀·T + G·λ`, `op₀·C' + G·λ^{n−1}`
    simp only [slotCert]
    rw [t0]
    have hact' := hact
    simp only [sampledActive, Expr.eval] at hact'
    cases s <;> simp at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 <;>
      simp [s0, s2, s5, s6, s7, s8, s9] at hact' ⊢ <;>
      refine ⟨?_, ?_⟩ <;>
      simp [sampledSlotT, sampledSlotC, sampledGSel, certTVar, sampledLam, lamPowVar, Expr.eval,
        s0, s2, s5, s6, s7, s8, s9, h9, hl0, hT, hrow, hbitsEq, hC, hCnone]
  · -- slot 2 (base 83): `op₆·λ + op₉·T`, `op₆·λ^{n−1} + op₉·C'`
    simp only [slotCert]
    rw [t9]
    have hact' := hact
    simp only [sampledActive, Expr.eval] at hact'
    cases s <;> simp at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 <;>
      simp [s6, s9] at hact' ⊢ <;>
      refine ⟨?_, ?_⟩ <;>
      simp [sampledSlotT, sampledSlotC, certTVar, sampledLam, lamPowVar, Expr.eval,
        s6, s9, h9, hl0, hT, hrow, hbitsEq, hC, hCnone]

end Generic

section Deployed

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

/-- The package compute env the decoded event reads, at the reindexed family trace. -/
abbrev envsC : Fin P.optimized.family.problem.cfg.compRows → Env K :=
  P.computeSourceEnv (honestQc P c Qc)

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
theorem gather_toSource_trace_congr (b : Module.Basis (Fin 3) F K) (E E' : Env F)
    (h : E.trace = E'.trace) :
    (gatherCorrectedFinalTypedEnv b E).toSourceEnv.trace =
      (gatherCorrectedFinalTypedEnv b E').toSourceEnv.trace := by
  funext k
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv, h]

theorem envsC_trace (a : Fin P.optimized.family.problem.cfg.compRows) :
    (envsC P c Qc a).trace = (rowEnvAt P c Qc a).toSourceEnv.trace :=
  gather_toSource_trace_congr P.optimized.basis _ _ (computeBaseEnv_honestQc_trace P c Qc a)

/-- **The named premise `CertBitsBoolean`**: shift bits and the record-visible certificate bits
are `0`/`1` on every family compute row. -/
structure CertBitsBoolean : Prop where
  shift : ∀ (a : Fin P.optimized.family.problem.cfg.compRows) (k : ℕ) (hk : k < 6),
    (rowEnvAt P c Qc a).certBase ⟨63 + k, by omega⟩ = 0 ∨
      (rowEnvAt P c Qc a).certBase ⟨63 + k, by omega⟩ = 1
  bits : ∀ (a : Fin P.optimized.family.problem.cfg.compRows) (j : ℕ) (hj : j < 63),
    j + 1 ≤ FormRAxisEvent.formRN K - 1 →
    (rowEnvAt P c Qc a).certBase ⟨j, by omega⟩ = 0 ∨ (rowEnvAt P c Qc a).certBase ⟨j, by omega⟩ = 1

theorem bool_of_bbool {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

/-- **`CertBitsBoolean` at the CURRENT gates** (reads `booleanGates`' current body). -/
theorem certBitsBoolean_of_sat : CertBitsBoolean P c Qc := by
  have hform := fun a => (row_obligations_at P c Qc hsat a).formR99
  refine ⟨fun a k hk => ?_, fun a j hj _ => ?_⟩
  · have hg := hform a (bbool (colM k)) (by
      simp only [formRCertificateGates, booleanGates, List.mem_append, List.mem_map,
        List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩)))))
    apply bool_of_bbool
    have hx : (rowEnvAt P c Qc a).certBase ⟨63 + k, by omega⟩ =
        (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes a)
          (DeployedChipFamily.computeChalValOfTuple P.optimized.basis c)
          (P.familyComputePublic c)).trace (col0 + 63 + k) := by
      simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, col0, Nat.add_assoc]
    rw [hx]
    simpa [bbool, colM, bcur, CoeffExpr.eval] using hg
  ·
    -- `if formRN F − 1 < j + 1 then colC j else bbool (colC j)`; both branches give `0 ∨ 1`.
    have hg := hform a
      (if OptimizedComputeRangeCertificate.formRN F - 1 < j + 1 then colC j else bbool (colC j)) (by
      simp only [formRCertificateGates, booleanGates, List.mem_append, List.mem_map,
        List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩)))))
    have hx : (rowEnvAt P c Qc a).certBase ⟨j, by omega⟩ =
        (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes a)
          (DeployedChipFamily.computeChalValOfTuple P.optimized.basis c)
          (P.familyComputePublic c)).trace (col0 + j) := by
      simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, col0]
    rw [hx]
    split_ifs at hg
    · left; simpa [colC, bcur, CoeffExpr.eval] using hg
    · apply bool_of_bbool
      simpa [bbool, colC, bcur, CoeffExpr.eval] using hg

omit hsat in
theorem lamFactor_eval (b : F) (hb : b = 0 ∨ b = 1) (l : K) (k : ℕ) :
    1 + algebraMap F K b * (l ^ 2 ^ k - 1) = l ^ (if algebraMap F K b = 1 then 2 ^ k else 0) := by
  rcases hb with rfl | rfl <;> simp

/-- **`T = λ^{rowShift}`** from the `𝕂` power pins `formRLamPins` and shift booleanity. -/
theorem certT_eq (hb : CertBitsBoolean P c Qc) (a : Fin P.optimized.family.problem.cfg.compRows) :
    (rowEnvAt P c Qc a).toSourceEnv.trace 299 =
      c.2.2.2.lambda ^ rowShift (rowEnvAt P c Qc a).toSourceEnv := by
  have hob := row_obligations_at P c Qc hsat a
  have hT := hob.formRLam formRLamTPin (by simp [formRLamPins])
  have hH := hob.formRLam formRLamHPin (by simp [formRLamPins])
  have h9 : (rowEnvAt P c Qc a).chal 9 = c.2.2.2.lambda := by
    rw [← toSource_chal9]; exact rowEnvAt_chal9_lambda P c Qc a
  simp only [formRLamTPin, formRLamHPin, formRLamFactor, CorrectedFinalTypedExpr.eval,
    Int.cast_one, sub_eq_zero, h9] at hT hH
  simp only [show ((0 : Fin 6) : ℕ) = 0 from rfl, show ((1 : Fin 6) : ℕ) = 1 from rfl,
    show ((2 : Fin 6) : ℕ) = 2 from rfl, show ((3 : Fin 6) : ℕ) = 3 from rfl,
    show ((4 : Fin 6) : ℕ) = 4 from rfl, show ((5 : Fin 6) : ℕ) = 5 from rfl] at hT hH
  rw [toSource_certT, hT, hH]
  have hf : ∀ k (hk : k < 6),
      1 + algebraMap F K ((rowEnvAt P c Qc a).certBase ⟨63 + k, by omega⟩) *
          (c.2.2.2.lambda ^ 2 ^ k - 1) =
        c.2.2.2.lambda ^ (if (rowEnvAt P c Qc a).toSourceEnv.trace (265 + k) = 1 then 2 ^ k
          else 0) := by
    intro k hk
    rw [lamFactor_eval _ (hb.shift a k hk)]
    congr 2
    rw [show 265 + k = 202 + (63 + k) by omega, toSource_certBase _ _ (by omega)]
  have e0 := hf 0 (by decide); have e1 := hf 1 (by decide); have e2 := hf 2 (by decide)
  have e3 := hf 3 (by decide); have e4 := hf 4 (by decide); have e5 := hf 5 (by decide)
  rw [e0, e1, e2, e3, e4, e5]
  unfold rowShift
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_add]
  ring_nf

omit hsat in
theorem activeMask_eval_congr {E E' : Env K} (h : E.trace = E'.trace) (j : Fin 3) :
    (sampledActive .traceCur (j : ℕ)).eval E = (sampledActive .traceCur (j : ℕ)).eval E' := by
  fin_cases j <;> simp [sampledActive, Expr.eval, h]

/-- **The request record's Form R slots are the located certificate's `(T, C')`.** -/
theorem slot_values (hb : CertBitsBoolean P c Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    rowRecord (rowEnvAt P c Qc a) j 6 = c.2.2.2.lambda ^ (slotCert (envsC P c Qc) a j).1 ∧
      rowRecord (rowEnvAt P c Qc a) j 8 =
        (Batch575.C'poly (K := K) (FormRAxisEvent.formRN K)
          (slotCert (envsC P c Qc) a j).2).eval c.2.2.2.lambda := by
  set env := rowEnvAt P c Qc a
  set E := Env.ofSubst finalSampledNamespace env.toSourceEnv
  have hEtr : E.trace = env.toSourceEnv.trace := ofSubst_trace _
  obtain ⟨s, hsel⟩ := source_selector_at P c Qc hsat hchar a
  have h9env : env.chal 9 = c.2.2.2.lambda := by
    rw [← toSource_chal9]; exact rowEnvAt_chal9_lambda P c Qc a
  have hE9 : E.chal 9 = c.2.2.2.lambda := by
    rw [ofSubst_chal _ 9 (by decide) (by decide), toSource_chal9]; exact h9env
  have hE100 : ∀ d, d < 64 → E.chal (100 + d) = lamPowVal c.2.2.2.lambda d := by
    intro d hd
    rw [ofSubst_chal _ _ (by omega) (by omega), toSource_lamPow _ d hd, h9env]
  have hEbits : ∀ j, j < 63 → j + 1 ≤ FormRAxisEvent.formRN K - 1 →
      E.trace (202 + j) = 0 ∨ E.trace (202 + j) = 1 := by
    intro j hj hjn
    rw [hEtr, toSource_certBase _ _ (by omega)]
    rcases hb.bits a j hj hjn with h | h
    · left; rw [h, map_zero]
    · right; rw [h, map_one]
  have hET : E.trace 299 = c.2.2.2.lambda ^ rowShift E := by
    have : rowShift E = rowShift env.toSourceEnv := by unfold rowShift; rw [hEtr]
    rw [this, hEtr]; exact certT_eq P c Qc hsat hb a
  have hEsel : ∀ st, E.trace (Nock.Reified.opCol st) = ComputeTable.opSel s st := by
    intro st; rw [hEtr]; exact hsel st
  have hEact : (sampledActive .traceCur (j : ℕ)).eval E = 1 := by
    rw [activeMask_eval_congr hEtr]; exact hact
  have hE : (envsC P c Qc a).trace = E.trace := by rw [envsC_trace, hEtr]
  obtain ⟨h6, h8⟩ := slots_of_env (envsC P c Qc) a E hE c.2.2.2.lambda (FormRAxisEvent.formRN K)
    FormRAxisEvent.formRN_sub_one.symm s hEsel hE9 hE100 hEbits hET j hEact
  refine ⟨?_, ?_⟩
  · simp only [rowRecord, show ((6 : Fin 10) : ℕ) = 6 from rfl, if_neg (show (6 : ℕ) ≠ 9 by decide),
      ]
    rw [Expr.eval_subst]; exact h6
  · simp only [rowRecord, show ((8 : Fin 10) : ℕ) = 8 from rfl, if_neg (show (8 : ℕ) ≠ 9 by decide),
      if_neg (show (8 : ℕ) ≠ 6 by decide)]
    rw [Expr.eval_subst]; exact h8

theorem computeArity_eq (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (a : Fin P.optimized.family.problem.cfg.compRows) :
    computeArity (envsC P c Qc a) = rowArity (rowEnvAt P c Qc a) := by
  obtain ⟨s, hsel⟩ := source_selector_at P c Qc hsat hchar a
  rw [rowArity_eq_arity_at P c Qc a s hsel]
  have ht := envsC_trace P c Qc a
  have s0 := hsel .s0; have s2 := hsel .s2; have s5 := hsel .s5; have s6 := hsel .s6
  have s7 := hsel .s7; have s8 := hsel .s8; have s9 := hsel .s9
  simp only [Nock.Reified.opCol, ComputeTable.opSel] at s0 s2 s5 s6 s7 s8 s9
  unfold computeArity
  rw [ht]
  cases s <;> simp [s0, s2, s5, s6, s7, s8, s9, OptimizedHostileTimestamps.arity]

theorem computePrefix_eq (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (a : Fin P.optimized.family.problem.cfg.compRows) :
    computePrefix (envsC P c Qc) a = prefixExpAt P c Qc a := by
  unfold computePrefix prefixExpAt
  have hg : ∀ i : Fin P.optimized.family.problem.cfg.compRows,
      computeArity (envsC P c Qc i) =
        (fun k => if h : k < P.optimized.family.problem.cfg.compRows then
          rowArity (rowEnvAt P c Qc ⟨k, h⟩) else 0) (i : ℕ) := by
    intro i
    rw [computeArity_eq P c Qc hsat hchar i]
    simp [i.isLt]
  rw [Finset.sum_filter]
  simp_rw [hg]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < (a : ℕ) then
    (if h : k < P.optimized.family.problem.cfg.compRows then
      rowArity (rowEnvAt P c Qc ⟨k, h⟩) else 0) else 0) P.optimized.family.problem.cfg.compRows]
  rw [← Finset.sum_filter]
  have hfil : (Finset.range P.optimized.family.problem.cfg.compRows).filter
      (fun k => k < (a : ℕ)) = Finset.range a := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; have := a.isLt; omega
  rw [hfil]

/-- **The exponent locator finds `(a, j)` at `e = S(a) + j + 1`.** -/
theorem locateExp_expOfAt (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    locateExp (envsC P c Qc) (expOfAt P c Qc a j) = some (a, (j : ℕ)) := by
  have hpre : ∀ i, computePrefix (envsC P c Qc) i = prefixExpAt P c Qc i :=
    computePrefix_eq P c Qc hsat hchar
  have har : ∀ i, computeArity (envsC P c Qc i) = rowArity (rowEnvAt P c Qc i) :=
    computeArity_eq P c Qc hsat hchar
  have hj := active_lt_rowArity (rowEnvAt P c Qc a) j hact
  unfold locateExp
  have hfind : (List.finRange P.optimized.family.problem.cfg.compRows).find?
      (fun i => decide (computePrefix (envsC P c Qc) i < expOfAt P c Qc a j ∧
        expOfAt P c Qc a j ≤ computePrefix (envsC P c Qc) i + computeArity (envsC P c Qc i))) =
      some a := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, (a : ℕ), by simp, by rw [List.getElem_finRange]; exact Fin.ext rfl, ?_⟩
    · simp only [decide_eq_true_eq, hpre, har, expOfAt]
      omega
    · intro k hk
      simp only [List.getElem_finRange, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
        not_le, hpre, har]
      intro _
      have hk' : k < P.optimized.family.problem.cfg.compRows := by
        have := a.isLt; omega
      have hsucc := prefixExpAt_succ P c Qc k hk'
      have hmono := prefixExpAt_mono P c Qc (show k + 1 ≤ (a : ℕ) by omega)
      simp only [expOfAt]
      change prefixExpAt P c Qc k + rowArity (rowEnvAt P c Qc ⟨k, hk'⟩) <
        prefixExpAt P c Qc a + (j : ℕ) + 1
      omega
  rw [hfind]
  simp only [Option.map_some, hpre, expOfAt]
  congr 2
  omega

/-- **Decoded `(shift, bits)` of an active request's exponent are its C-a certificate.** -/
theorem decoded_eq_slotCert (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    decodedShift (envsC P c Qc) (expOfAt P c Qc a j) = (slotCert (envsC P c Qc) a j).1 ∧
      decodedBits (envsC P c Qc) (expOfAt P c Qc a j) = (slotCert (envsC P c Qc) a j).2 := by
  have h := locateExp_expOfAt P c Qc hsat hchar a j hact
  refine ⟨?_, ?_⟩
  · unfold decodedShift; rw [h]
  · funext k; unfold decodedBits; rw [h]

end Deployed

end

end Nock.RedTeam.Batch823
