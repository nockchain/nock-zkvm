/-
  Nock/RedTeam/Batch997Thm54HonestComputeCertDecode.lean

  No acceptance, no
  event: every statement is about the package's own canonical trace.

  The decoded λ-event reads the certificate of exponent `e` off round-0 compute columns through the
  exponent locator `locateExp` and the C-a slot map `slotCert` (`DecodedLambdaEvent`).  At the
  canonical compute trace of ANY package:

  * the arity read off the selectors is the opcode's request arity (`computeArity_canon`), so the
    locator's prefix sums are the honest carrier `honestS` (`computePrefix_canon`) and the exponent
    `honestS i + j + 1` of row `i`'s `j`-th active request is located at `(i, j)`
    (`locateExp_canon`);
  * under `FormRAxisBound` (the compiler's `genComputeRows_rowsFormRAxisBound`) and `FormRWidth`,
    the located certificate is the certificate of the request record's natural axis
    `nockAxisOf mr.axis` (`slotCert_canon`): slot `0` is `mr₁` at axis `3`, slot `1` is `mr₂` (the
    `s0` lookup, else axis `2`), slot `2` is `mr₃` (the `s9` lookup, else axis `2`).

  So `decodedShift` / `decodedBits` at the honest exponent of an active request are that request's
  axis certificate (`decoded_canon`).
-/
import Nock.RedTeam.Batch996Thm54HonestDecodedTreeBFS
import Nock.RedTeam.Batch963Thm54HonestEventAssembly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch997

open scoped Classical Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.OptimizedComputeFormRSlots
open Nock.NockVMROM.Thm54.OptimizedComputeFormRDenoms
open Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)] [FiniteDimensional F K]
variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The canonical compute source environments (what the decoded λ-event reads). -/
abbrev envsC : Fin P.optimized.family.problem.cfg.compRows → Env K :=
  P.computeSourceEnv (MultiRootOptimizedAcceptance.canonicalComputeTrace P)

theorem envsC_eq (i : Fin P.optimized.family.problem.cfg.compRows) :
    envsC P i = (honestRow P i).toSourceEnv := rfl

/-! ## A. Selectors, arity, prefix, locator -/

theorem envsC_trace_lt (i : Fin P.optimized.family.problem.cfg.compRows) (n : ℕ) (hn : n < 71) :
    (envsC P i).trace n = (exactRow P i).toSourceEnv.trace n := by
  have h := honestRow_eval_eq P i (.Var .traceCur n) (by simp [Expr.rowScoped, hn])
  rw [envsC_eq]
  simpa [Expr.eval] using h

/-- The canonical selectors are the row's one-hot state. -/
theorem envsC_sel (i : Fin P.optimized.family.problem.cfg.compRows) (s : State) :
    (envsC P i).trace (Nock.Reified.opCol s) =
      if s = (P.optimized.family.problem.exec.computePubAt i).state then 1 else 0 := by
  rw [envsC_trace_lt P i _ (by cases s <;> decide)]
  exact exactFinalCurrentEnv_selectors P.optimized.sampled i s

/-- The decoded arity is the opcode's request arity. -/
theorem computeArity_canon (i : Fin P.optimized.family.problem.cfg.compRows) :
    computeArity (envsC P i) =
      (NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i)).length := by
  have h := fun s => envsC_sel P i s
  have h0 := h .s0; have h2 := h .s2; have h5 := h .s5; have h6 := h .s6
  have h7 := h .s7; have h8 := h .s8; have h9 := h .s9
  simp only [Nock.Reified.opCol] at h0 h2 h5 h6 h7 h8 h9
  unfold computeArity
  rw [h0, h2, h5, h6, h7, h8, h9]
  cases hs : (P.optimized.family.problem.exec.computePubAt i).state <;>
    simp [NockVM.activeRequestRecords, hs]

theorem honestS_succ' (n : ℕ) (hn : n < P.optimized.family.problem.cfg.compRows) :
    honestS P.optimized.family (n + 1) = honestS P.optimized.family n +
      (NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt ⟨n, hn⟩)).length :=
  honestS_succ (R := P.optimized.family) (i := ⟨n, hn⟩)

/-- The decoded prefix sum is the honest carrier `S(i)`. -/
theorem computePrefix_canon (i : Fin P.optimized.family.problem.cfg.compRows) :
    computePrefix (envsC P) i = honestS P.optimized.family i := by
  unfold computePrefix
  simp_rw [computeArity_canon P]
  suffices key : ∀ n, n ≤ P.optimized.family.problem.cfg.compRows →
      (∑ i' ∈ Finset.univ.filter (fun i' : Fin P.optimized.family.problem.cfg.compRows =>
        (i' : ℕ) < n),
        (NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i')).length) =
        honestS P.optimized.family n from key _ i.isLt.le
  intro n
  induction n with
  | zero => intro _; simp [honestS]
  | succ n ih =>
      intro hle
      have hlt : n < P.optimized.family.problem.cfg.compRows := by omega
      rw [honestS_succ' P n hlt, ← ih hlt.le]
      have hsplit : (Finset.univ.filter fun i' : Fin P.optimized.family.problem.cfg.compRows =>
          (i' : ℕ) < n + 1) =
          insert ⟨n, hlt⟩ (Finset.univ.filter
            fun i' : Fin P.optimized.family.problem.cfg.compRows => (i' : ℕ) < n) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]; omega
      rw [hsplit, Finset.sum_insert (by simp), add_comm]

/-- `S(i + 1) = S(i) + arity(i)` and monotonicity of `honestS`. -/
theorem honestS_mono {a b : ℕ} (h : a ≤ b) :
    honestS P.optimized.family a ≤ honestS P.optimized.family b := by
  unfold honestS
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  omega

/-- **The locator finds `(i, j)` at the honest exponent `S(i) + j + 1`.** -/
theorem locateExp_canon (i : Fin P.optimized.family.problem.cfg.compRows) (j : ℕ)
    (hj : j < (NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i)).length) :
    locateExp (envsC P) (honestS P.optimized.family i + j + 1) = some (i, j) := by
  unfold locateExp
  have hfind : (List.finRange P.optimized.family.problem.cfg.compRows).find?
      (fun i' => decide (computePrefix (envsC P) i' < honestS P.optimized.family i + j + 1 ∧
        honestS P.optimized.family i + j + 1 ≤
          computePrefix (envsC P) i' + computeArity (envsC P i'))) = some i := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, (i : ℕ), by simp, by rw [List.getElem_finRange]; exact Fin.ext rfl, ?_⟩
    · simp only [decide_eq_true_eq, computePrefix_canon, computeArity_canon]; omega
    · intro k hk
      have hk' : k < P.optimized.family.problem.cfg.compRows := by have := i.isLt; omega
      have hx : (List.finRange P.optimized.family.problem.cfg.compRows)[k]'(by simp; omega) =
          ⟨k, hk'⟩ := Fin.ext (by simp)
      simp only [hx, Bool.not_eq_true', decide_eq_false_iff_not, not_and, not_le,
        computePrefix_canon, computeArity_canon]
      intro _
      have hsucc := honestS_succ' P k hk'
      have hmono := honestS_mono P (show k + 1 ≤ (i : ℕ) by omega)
      try simp only at hsucc hmono ⊢
      omega
  rw [hfind]
  simp only [Option.map_some, computePrefix_canon]
  congr 2
  omega

/-! ## B. The certificate columns -/

theorem sum_testBit_six : ∀ m : ℕ, m < 64 →
    (∑ k ∈ Finset.range 6, if m.testBit k then 2 ^ k else 0) = m := by
  decide

theorem algebraMap_bit01_eq_one (b : Bool) :
    (algebraMap F K (bit01 (F := F) b) = 1) ↔ b = true := by
  cases b <;> simp [bit01]

/-- The canonical certificate columns of row `i` are the exact certificate of `axisNatK`. -/
theorem envsC_cert (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (i : Fin P.optimized.family.problem.cfg.compRows) (j : ℕ) (hj : j < 94) :
    (envsC P i).trace (202 + j) =
      algebraMap F K (formROffNat (F := F) (axisNatK P.optimized.sampled i) j) := by
  rw [envsC_eq, toSource_certBase _ j hj, honestRow_certBase P hax i]
  rfl

theorem certShift_lt_64 {a : ℕ} (ha : a < 2 ^ 64) : certShift a < 64 := by
  unfold certShift
  have := (Nat.size_le).mpr ha
  omega

/-- The canonical row shift is the certificate shift of `axisNatK`. -/
theorem rowShift_canon (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    rowShift (envsC P i) = MemoryTable.formRCertShift (axisNatK P.optimized.sampled i) := by
  have hsmall := formRAxisSmall_of_bound _ _ hax i
  have hm := certShift_lt_64 hsmall
  unfold rowShift
  calc _ = ∑ k ∈ Finset.range 6,
        (if (certShift (axisNatK P.optimized.sampled i)).testBit k then 2 ^ k else 0) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk6 : k < 6 := Finset.mem_range.mp hk
        rw [show 265 + k = 202 + (63 + k) by omega, envsC_cert P hax i _ (by omega)]
        simp only [formROffNat, axisCertM, show ¬ (63 + k < 63) by omega, if_false,
          show 63 + k < 69 by omega, if_true, Nat.add_sub_cancel_left, rangeShiftExp_of_lt64 hm,
          leftoverHornerExp_of_lt hm]
        by_cases hb : (certShift (axisNatK P.optimized.sampled i)).testBit k
        · simp [hb, bit01]
        · simp [hb, bit01]
    _ = _ := sum_testBit_six _ hm

/-- The canonical row bits are the certificate bits of `axisNatK`. -/
theorem rowBits_canon (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (i : Fin P.optimized.family.problem.cfg.compRows) (k : ℕ) (hk : 1 ≤ k) :
    rowBits (envsC P i) k = MemoryTable.formRCertBit (axisNatK P.optimized.sampled i) (k - 1) := by
  have hsmall := formRAxisSmall_of_bound _ _ hax i
  have hm := certShift_lt_64 hsmall
  unfold rowBits
  by_cases hk63 : k ≤ 63
  · rw [envsC_cert P hax i _ (by omega)]
    simp only [formROffNat, show k - 1 < 63 by omega, if_true]
    rw [show MemoryTable.formRCertBit (axisNatK P.optimized.sampled i) (k - 1) =
      certCBit (axisNatK P.optimized.sampled i) (k - 1) from rfl]
    cases hb : certCBit (axisNatK P.optimized.sampled i) (k - 1) <;> simp [bit01, hk, hk63]
  · have hfalse : MemoryTable.formRCertBit (axisNatK P.optimized.sampled i) (k - 1) = false := by
      unfold MemoryTable.formRCertBit
      rw [if_neg]
      unfold MemoryTable.formRCertShift
      have := certShift_lt_64 hsmall
      unfold certShift at this
      omega
    rw [hfalse]
    simp [hk63]


/-! ## C. The slot records' axes and the located certificate -/

/-- The canonical record columns of slot `j` are the encoded slot record. -/
theorem canon_hcol (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3) (c8 : Fin 8) :
    (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c8 : ℕ))).eval
        (Env.ofSubst finalSampledNamespace (envsC P i)) =
      NockVM.encRecC (slotRecord P.optimized.family i j) 1 c8.castSucc := by
  rw [envsC_eq, ← Expr.eval_subst, honestRow_eval_eq P i _ (rowRecord_rowScoped j c8),
    Expr.eval_subst]
  have ht := exactFinalCurrentEnv_table_current P.optimized.sampled
    P.optimized.computeObligations i (67 + 8 * (j : ℕ) + (c8 : ℕ)) (by omega)
  fin_cases j <;> fin_cases c8 <;> exact ht

theorem canon_trace_ofSubst (i : Fin P.optimized.family.problem.cfg.compRows) (k : ℕ) :
    (Env.ofSubst finalSampledNamespace (envsC P i)).trace k = (envsC P i).trace k := by
  simp only [Env.ofSubst, finalSampledNamespace_traceCur, Expr.eval]

/-- **The natural axis of an active request slot**, read off the canonical row:
slot `0` is axis `3`; slot `1` the `s0` lookup `axisNatK` (else axis `2`); slot `2` the `s9`
lookup `axisNatK` (else axis `2`). -/
theorem slotAxis_canon (hwidth : FormRWidth F) (i : Fin P.optimized.family.problem.cfg.compRows)
    (j : Fin 3) (hact : slotActive P.optimized.family i j = 1) :
    MemoryTable.nockAxisOf (slotRecord P.optimized.family i j).axis =
      match j with
      | 0 => 3
      | 1 => if (P.optimized.family.problem.exec.computePubAt i).state = .s0 then
          axisNatK P.optimized.sampled i else 2
      | 2 => if (P.optimized.family.problem.exec.computePubAt i).state = .s9 then
          axisNatK P.optimized.sampled i else 2 := by
  set st := (P.optimized.family.problem.exec.computePubAt i).state with hst
  have htr := canon_trace_ofSubst P i
  have hsel' : ∀ s : State, (Env.ofSubst finalSampledNamespace (envsC P i)).trace
      (Nock.Reified.opCol s) = if s = st then 1 else 0 := fun s => by
    rw [htr]; exact envsC_sel P i s
  have hdec : decodeState (encodedRowAt P.optimized.sampled i).base = st :=
    decodeState_encodedRowAt P.optimized.sampled i
  have h41 : (envsC P i).trace 54 =
      coreExtensionValue (encodedRowAt P.optimized.sampled i) ⟨41, by decide⟩ := by
    rw [envsC_trace_lt P i 54 (by decide)]
    simpa using exactFinalCurrentEnv_extension_current P.optimized.sampled i ⟨41, by decide⟩
  have h44 : (envsC P i).trace 57 =
      coreExtensionValue (encodedRowAt P.optimized.sampled i) ⟨44, by decide⟩ := by
    rw [envsC_trace_lt P i 57 (by decide)]
    simpa using exactFinalCurrentEnv_extension_current P.optimized.sampled i ⟨44, by decide⟩
  have hsel0 := hsel' .s0
  have hsel2 := hsel' .s2
  have hsel5 := hsel' .s5
  have hsel6 := hsel' .s6
  have hsel7 := hsel' .s7
  have hsel8 := hsel' .s8
  have hsel9 := hsel' .s9
  simp only [Nock.Reified.opCol] at hsel0 hsel2 hsel5 hsel6 hsel7 hsel8 hsel9
  have hc6 := canon_hcol P i j 6
  fin_cases j
  · have hax : (P.optimized.family.problem.exec.computePubAt i).mr1.axis = 3 := by
      simp [computeTraceSubst, Expr.eval, NockVM.encRecC, slotRecord] at hc6
      exact hc6.symm
    simp only [Fin.zero_eta, Fin.isValue, slotRecord]
    rw [hax, nockAxisOf_three hwidth]
  · simp only [Fin.mk_one, Fin.isValue, slotRecord, slotActive] at hact hc6 ⊢
    cases hs : st with
    | s0 =>
        have hax : (P.optimized.family.problem.exec.computePubAt i).mr2.axis =
            coreExtensionValue (encodedRowAt P.optimized.sampled i) ⟨41, by decide⟩ := by
          simp [computeTraceSubst, mr2Field, mr2Group, decFP, ext0, Expr.eval,
            NockVM.encRecC, hsel0, hsel2, hsel5, hsel6, hsel7, hsel8, hsel9, hs,
            htr, h41] at hc6
          exact hc6.symm
        rw [hax]
        simp [axisNatK, axisLeafK, hdec, hs]
    | s2 | s5 | s6 | s7 | s8 | s9 =>
        have hax : (P.optimized.family.problem.exec.computePubAt i).mr2.axis = 2 := by
          simp [computeTraceSubst, mr2Field, mr2Group, decFP, ext0, Expr.eval,
            NockVM.encRecC, hsel0, hsel2, hsel5, hsel6, hsel7, hsel8, hsel9, hs] at hc6
          exact hc6.symm
        rw [hax, nockAxisOf_two hwidth]
        simp
    | s1 | s3 | s4 | cons =>
        rw [← hst, hs] at hact
        simp [secondRequestMask] at hact
  · simp only [Fin.reduceFinMk, Fin.isValue, slotRecord, slotActive] at hact hc6 ⊢
    cases hs : st with
    | s6 =>
        have hax : (P.optimized.family.problem.exec.computePubAt i).mr3.axis = 2 := by
          simp [computeTraceSubst, mr3Field, mr3Group, decFP, ext0, Expr.eval,
            NockVM.encRecC, hsel6, hsel9, hs] at hc6
          exact hc6.symm
        rw [hax, nockAxisOf_two hwidth]
        simp
    | s9 =>
        have hax : (P.optimized.family.problem.exec.computePubAt i).mr3.axis =
            coreExtensionValue (encodedRowAt P.optimized.sampled i) ⟨44, by decide⟩ := by
          simp [computeTraceSubst, mr3Field, mr3Group, decFP, ext0, Expr.eval,
            NockVM.encRecC, hsel6, hsel9, hs, htr, h44] at hc6
          exact hc6.symm
        rw [hax]
        simp [axisNatK, axisLeafK, hdec, hs]
    | s0 | s1 | s2 | s3 | s4 | s5 | s7 | s8 | cons =>
        rw [← hst, hs] at hact
        simp [thirdRequestMask] at hact

/-- The certificate of axis `3` is the constant slot-`0` certificate. -/
theorem cert_three (k : ℕ) (hk : 1 ≤ k) :
    MemoryTable.formRCertShift 3 = 1 ∧ MemoryTable.formRCertBit 3 (k - 1) = decide (k = 1) := by
  refine ⟨by decide, ?_⟩
  unfold MemoryTable.formRCertBit
  rw [show MemoryTable.formRCertShift 3 = 1 by decide]
  by_cases h1 : k = 1
  · subst h1; decide
  · rw [if_neg (by omega)]; simp [h1]

/-- The certificate of axis `2` is the constant `(1, ∅)`. -/
theorem cert_two (k : ℕ) (hk : 1 ≤ k) :
    MemoryTable.formRCertShift 2 = 1 ∧ MemoryTable.formRCertBit 2 (k - 1) = false := by
  refine ⟨by decide, ?_⟩
  unfold MemoryTable.formRCertBit
  rw [show MemoryTable.formRCertShift 2 = 1 by decide]
  by_cases h1 : k = 1
  · subst h1; decide
  · rw [if_neg (by omega)]

/-- **The located certificate is the request axis's certificate.** -/
theorem slotCert_canon (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hwidth : FormRWidth F) (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : slotActive P.optimized.family i j = 1) :
    (slotCert (envsC P) i j).1 =
        MemoryTable.formRCertShift
          (MemoryTable.nockAxisOf (slotRecord P.optimized.family i j).axis) ∧
      ∀ k, 1 ≤ k → (slotCert (envsC P) i j).2 k =
        MemoryTable.formRCertBit
          (MemoryTable.nockAxisOf (slotRecord P.optimized.family i j).axis) (k - 1) := by
  have hA := slotAxis_canon P hwidth i j hact
  have h0 := envsC_sel P i .s0
  have h9 := envsC_sel P i .s9
  simp only [Nock.Reified.opCol] at h0 h9
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue] at hA ⊢
    rw [hA]
    refine ⟨(cert_three 1 le_rfl).1.symm, fun k hk => ?_⟩
    rw [(cert_three k hk).2]
    rfl
  · simp only [Fin.mk_one, Fin.isValue] at hA ⊢
    rw [hA]
    by_cases hs : (P.optimized.family.problem.exec.computePubAt i).state = .s0
    · have ht0 : (envsC P i).trace 0 = 1 := by rw [h0, if_pos hs.symm]
      simp only [if_pos hs, slotCert, if_pos ht0]
      exact ⟨rowShift_canon P hax i, fun k hk => rowBits_canon P hax i k hk⟩
    · have ht0 : ¬ (envsC P i).trace 0 = 1 := by
        rw [h0, if_neg (Ne.symm hs)]; exact zero_ne_one
      simp only [if_neg hs, slotCert, if_neg ht0]
      exact ⟨(cert_two 1 le_rfl).1.symm, fun k hk => (cert_two k hk).2.symm⟩
  · simp only [Fin.reduceFinMk, Fin.isValue] at hA ⊢
    rw [hA]
    by_cases hs : (P.optimized.family.problem.exec.computePubAt i).state = .s9
    · have ht9 : (envsC P i).trace 9 = 1 := by rw [h9, if_pos hs.symm]
      simp only [if_pos hs, slotCert, if_pos ht9]
      exact ⟨rowShift_canon P hax i, fun k hk => rowBits_canon P hax i k hk⟩
    · have ht9 : ¬ (envsC P i).trace 9 = 1 := by
        rw [h9, if_neg (Ne.symm hs)]; exact zero_ne_one
      simp only [if_neg hs, slotCert, if_neg ht9]
      exact ⟨(cert_two 1 le_rfl).1.symm, fun k hk => (cert_two k hk).2.symm⟩

/-- **The decoded certificate at an active request's honest exponent is that request's axis
certificate.** -/
theorem decoded_canon (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hwidth : FormRWidth F) (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : slotActive P.optimized.family i j = 1) :
    decodedShift (envsC P) (honestS P.optimized.family i + (j : ℕ) + 1) =
        MemoryTable.formRCertShift
          (MemoryTable.nockAxisOf (slotRecord P.optimized.family i j).axis) ∧
      ∀ k, 1 ≤ k → decodedBits (envsC P) (honestS P.optimized.family i + (j : ℕ) + 1) k =
        MemoryTable.formRCertBit
          (MemoryTable.nockAxisOf (slotRecord P.optimized.family i j).axis) (k - 1) := by
  obtain ⟨hj, -⟩ := slotRecord_active P.optimized.family i j hact
  have hloc := locateExp_canon P i j hj
  have hc := slotCert_canon P hax hwidth i j hact
  refine ⟨?_, fun k hk => ?_⟩
  · unfold decodedShift; rw [hloc]; exact hc.1
  · unfold decodedBits; rw [hloc]; exact hc.2 k hk

end

end Nock.RedTeam.Batch997

#print axioms Nock.RedTeam.Batch997.locateExp_canon
#print axioms Nock.RedTeam.Batch997.slotCert_canon
#print axioms Nock.RedTeam.Batch997.decoded_canon
