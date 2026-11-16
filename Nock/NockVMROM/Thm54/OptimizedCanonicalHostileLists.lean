import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.ComputeEnvAgreement

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The hostile record lists at the honest traces ARE the package's records (W6.1 stage 2B)

`OptimizedFullStrictNockVMROMPackage.hostileRecords P Qc Qm` is what the consumed failure event
prices since W6.1 stage 2B.

-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedCanonicalHostileLists

open scoped Classical Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryCodec
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
open OptimizedComputeHostileAccumulator OptimizedMemoryHostileAccumulator
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)] [FiniteDimensional F K]
variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The canonical `199`-column compute trace of the package's own chip
(`MultiRootOptimizedAcceptance.canonicalComputeTrace`, spelled out). -/
abbrev honestComputeTrace : Fin P.computeChip.rap.w → F[X] :=
  correctedCanonicalFinalTrace P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic
    P.optimized.orbit

/-- The canonical `196`-column memory trace of the package's own chip
(`MultiRootOptimizedAcceptance.canonicalMemoryTrace`, spelled out). -/
abbrev honestMemoryTrace : Fin P.memoryChip.rap.w → F[X] :=
  canonicalFinalMemoryTrace P.optimized.sampled P.optimized.memoryNodes
    P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic
    P.optimized.orbit

omit [Fintype F] [DecidableEq F] in
theorem canonical_memoryBaseEnv (i : Fin P.optimized.family.problem.cfg.memRows) :
    P.memoryBaseEnv (honestMemoryTrace P) i =
      canonicalPhysicalEnv P.optimized.sampled
        P.optimized.memoryNodes P.optimized.basis
        P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit i := by
  unfold OptimizedFullStrictNockVMROMPackage.memoryBaseEnv
  unfold OptimizedFullStrictNockVMROMPackage.memorySourceTrace
  unfold honestMemoryTrace
  unfold canonicalPhysicalEnv
  unfold canonicalFinalMemoryTrace
  dsimp only
  erw [project_rightPadTrace]

omit [Fintype F] [DecidableEq F] in
theorem canonical_memorySourceEnv (i : Fin P.optimized.family.problem.cfg.memRows) :
    P.memorySourceEnv (honestMemoryTrace P) i =
      canonicalGatheredEnv P.optimized.sampled
        P.optimized.memoryNodes P.optimized.basis
        P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit i := by
  unfold OptimizedFullStrictNockVMROMPackage.memorySourceEnv
  unfold canonicalGatheredEnv
  rw [canonical_memoryBaseEnv]

/-! ### The hostile record lists at the canonical traces ARE the package's records (W6.1 stage 2B)

`OptimizedFullStrictNockVMROMPackage.hostileRecords P Qc Qm` is what the consumed failure event
prices since W6.1 stage 2B. These are the
`OptimizedComputeCanonicalDenominator` §B–§C / `OptimizedHostileIOAssembly` §G facts, hoisted to the first module where the canonical traces exist, in a sub-namespace so
the downstream copies keep their names. -/


/-- Slot `j`'s record column `c` reads only current-row trace columns `< 71` and challenges
`< 12`. -/
theorem rowRecord_rowScoped (j : Fin 3) (c : Fin 8) :
    ((computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).subst
      finalSampledNamespace).rowScoped 71 12 = true := by
  fin_cases j <;> fin_cases c <;> decide

/-- The activity masks read only the current-row selector columns. -/
theorem sampledActive_rowScoped (j : Fin 3) :
    (sampledActive .traceCur j).rowScoped 71 12 = true := by
  fin_cases j <;> decide

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
/-- Two typed environments agreeing on the current-row base columns, the extension core roles
`< 58` and the twelve challenges give the same value to every `rowScoped 71 12` source
expression. -/
theorem eval_eq_of_rowScoped_typed {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ q, a.baseTrace q = b.baseTrace q)
    (hext : ∀ r : Fin 63, (r : ℕ) < 58 → a.extTrace r = b.extTrace r)
    (hchal : ∀ q : Fin 12, a.chal q = b.chal q)
    (e : Expr) (he : e.rowScoped 71 12 = true) :
    e.eval a.toSourceEnv = e.eval b.toSourceEnv := by
  apply Expr.eval_eq_of_rowScoped he
  · intro n hn
    simp only [CorrectedFinalTypedEnv.toSourceEnv]
    by_cases h13 : n < 13
    · rw [dif_pos h13, dif_pos h13, hbase]
    · rw [dif_neg h13, dif_neg h13, dif_pos (by omega), dif_pos (by omega)]
      exact hext ⟨n - 13, by omega⟩ (by simp; omega)
  · intro n hn
    simp only [CorrectedFinalTypedEnv.toSourceEnv]
    rw [dif_pos hn, dif_pos hn, hchal]

/-- The honest gathered compute row. -/
abbrev honestRow (i : Fin P.optimized.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv (honestComputeTrace P) i)

/-- The successor-free exact row of the package's own sampled assignment. -/
abbrev exactRow (i : Fin P.optimized.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  exactFinalCurrentEnv P.optimized.sampled i

omit [Fintype F] [DecidableEq F] in
theorem honestRow_base (i : Fin P.optimized.family.problem.cfg.compRows) (q : Fin 13) :
    (honestRow P i).baseTrace q = (exactRow P i).baseTrace q := by
  show (gatherCorrectedFinalTypedEnv P.optimized.basis
      (P.computeBaseEnv (honestComputeTrace P) i)).baseTrace q =
    OptimizedComputeFinalTrace.finalBaseCell P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos i q
  unfold honestComputeTrace OptimizedFullStrictNockVMROMPackage.computeBaseEnv
  exact canonical_gather_base_current P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
      P.optimized.computePublic P.optimized.orbit i q

omit [Fintype F] [DecidableEq F] in
theorem honestRow_ext_core (i : Fin P.optimized.family.problem.cfg.compRows) (r : Fin 63)
    (hr : (r : ℕ) < 58) :
    (honestRow P i).extTrace r = (exactRow P i).extTrace r := by
  have hc := canonical_gather_ext_core P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit i ⟨r, hr⟩
  have he : (exactRow P i).extTrace r =
      OptimizedComputeFinalTrace.coreExtensionValue (encodedRowAt P.optimized.sampled i)
        ⟨r, hr⟩ := by
    simp [exactRow, exactFinalCurrentEnv, exactFinalExtensionRow, hr]
  rw [he]
  show (gatherCorrectedFinalTypedEnv P.optimized.basis
    (P.computeBaseEnv (honestComputeTrace P) i)).extTrace r = _
  unfold honestComputeTrace OptimizedFullStrictNockVMROMPackage.computeBaseEnv
  exact hc

omit [Fintype F] [DecidableEq F] in
theorem honestRow_chal (i : Fin P.optimized.family.problem.cfg.compRows) (q : Fin 12) :
    (honestRow P i).chal q = (exactRow P i).chal q := by
  have hc := canonical_gather_challenge P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit
    P.optimized.computeChallengePins i q
  show (gatherCorrectedFinalTypedEnv P.optimized.basis
    (P.computeBaseEnv (honestComputeTrace P) i)).chal q =
    exactFinalChallenge P.optimized.sampled q
  unfold honestComputeTrace OptimizedFullStrictNockVMROMPackage.computeBaseEnv
  exact hc

omit [Fintype F] [DecidableEq F] in
/-- Any `rowScoped 71 12` source expression evaluates the same on the gathered honest row and on
the exact row. -/
theorem honestRow_eval_eq (i : Fin P.optimized.family.problem.cfg.compRows) (e : Expr)
    (he : e.rowScoped 71 12 = true) :
    e.eval (honestRow P i).toSourceEnv = e.eval (exactRow P i).toSourceEnv :=
  eval_eq_of_rowScoped_typed (honestRow_base P i) (honestRow_ext_core P i) (honestRow_chal P i)
    e he

/-- The `j`-th request register of compute row `i` of the package's execution. -/
abbrev requestRegister (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3) :
    ComputeTable.MemRec K :=
  match j with
  | 0 => (P.optimized.family.problem.exec.computePubAt i).mr1
  | 1 => (P.optimized.family.problem.exec.computePubAt i).mr2
  | 2 => (P.optimized.family.problem.exec.computePubAt i).mr3

omit [Fintype F] [DecidableEq F] in
/-- At the honest gathered compute row the activity masks are the opcode's request-arity masks. -/
theorem canonical_activeMask (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3) :
    activeMask (honestRow P i) j =
      match j with
      | 0 => 1
      | 1 => secondRequestMask (P.optimized.family.problem.exec.computePubAt i).state
      | 2 => thirdRequestMask (P.optimized.family.problem.exec.computePubAt i).state := by
  unfold activeMask
  rw [honestRow_eval_eq P i _ (sampledActive_rowScoped j)]
  exact exactFinalCurrentEnv_sampledActive P.optimized.sampled i j

omit [Fintype F] [DecidableEq F] in
/-- The honest gathered certificate base columns are the exact row's. -/
theorem honestRow_certBase (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (honestRow P i).certBase =
      OptimizedComputeFormRDenoms.exactFinalCertBase P.optimized.sampled i := by
  funext q
  show (gatherCorrectedFinalTypedEnv P.optimized.basis
      (P.computeBaseEnv (honestComputeTrace P) i)).certBase q = _
  unfold honestComputeTrace OptimizedFullStrictNockVMROMPackage.computeBaseEnv
  exact canonical_gather_certBase P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit hax i q

omit [Fintype F] [DecidableEq F] in
/-- The honest gathered `𝕂` certificate helpers are the exact row's at the package `λ`
(`cfg.challenges.lam`, compute challenge slot `9`). -/
theorem honestRow_certExt (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (honestRow P i).certExt =
      OptimizedComputeFormRDenoms.exactFinalCertExt P.optimized.sampled i
        P.optimized.family.problem.cfg.challenges.lam := by
  funext q
  show (gatherCorrectedFinalTypedEnv P.optimized.basis
      (P.computeBaseEnv (honestComputeTrace P) i)).certExt q = _
  unfold honestComputeTrace OptimizedFullStrictNockVMROMPackage.computeBaseEnv
  exact canonical_gather_certExt P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit hax
    (fun k => P.optimized.computeChallengePins 9 k) i q

omit [Fintype F] [DecidableEq F] in
/-- At the honest gathered compute row, an **active** slot `j`'s decoded Form R record **is** the
Form R encode of the `j`-th request register. -/
theorem canonical_rowRecord (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hwidth : FormRWidth F)
    (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : OptimizedComputeFormRDenoms.slotActive P.optimized.family i j = 1) :
    OptimizedComputeHostileAccumulator.rowRecord (honestRow P i) j =
      RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
        (NockVM.encRecFormR (requestRegister P i j)
          P.optimized.family.problem.cfg.challenges.lam) := by
  have hcol : ∀ c8 : Fin 8,
      (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c8 : ℕ))).eval
          (Env.ofSubst finalSampledNamespace (honestRow P i).toSourceEnv) =
        NockVM.encRecC (OptimizedComputeFormRDenoms.slotRecord P.optimized.family i j) 1
          c8.castSucc := by
    intro c8
    rw [← Expr.eval_subst, honestRow_eval_eq P i _ (rowRecord_rowScoped j c8), Expr.eval_subst]
    have ht := exactFinalCurrentEnv_table_current P.optimized.sampled
      P.optimized.computeObligations i (67 + 8 * (j : ℕ) + (c8 : ℕ)) (by omega)
    fin_cases j <;> fin_cases c8 <;> exact ht
  have hvar : ∀ n, n < 71 →
      (honestRow P i).toSourceEnv.trace n = (exactRow P i).toSourceEnv.trace n := by
    intro n hn
    have h := honestRow_eval_eq P i (.Var .traceCur n)
      (by simp [Expr.rowScoped, hn])
    simpa [Expr.eval] using h
  have hsel : ∀ s : State, (honestRow P i).toSourceEnv.trace (Nock.Reified.opCol s) =
      if s = (P.optimized.family.problem.exec.computePubAt i).state then 1 else 0 := by
    intro s
    rw [hvar _ (by cases s <;> decide)]
    exact exactFinalCurrentEnv_selectors P.optimized.sampled i s
  have h9 : (honestRow P i).chal 9 = P.optimized.family.problem.cfg.challenges.lam :=
    (honestRow_chal P i 9).trans rfl
  have h41 : (honestRow P i).toSourceEnv.trace 54 =
      coreExtensionValue (encodedRowAt P.optimized.sampled i) ⟨41, by decide⟩ := by
    rw [hvar 54 (by decide)]
    simpa using exactFinalCurrentEnv_extension_current P.optimized.sampled i ⟨41, by decide⟩
  have h44 : (honestRow P i).toSourceEnv.trace 57 =
      coreExtensionValue (encodedRowAt P.optimized.sampled i) ⟨44, by decide⟩ := by
    rw [hvar 57 (by decide)]
    simpa using exactFinalCurrentEnv_extension_current P.optimized.sampled i ⟨44, by decide⟩
  have hrec := OptimizedComputeFormRDenoms.sampledSlotRecord_eq_formR P.optimized.sampled i
    (OptimizedComputeFormRDenoms.formRAxisSmall_of_bound _ _ hax) hwidth (honestRow P i) j _
    hsel hcol h9 (honestRow_certBase P hax i) (honestRow_certExt P hax i) h41 h44 hact
  have hreg : OptimizedComputeFormRDenoms.slotRecord P.optimized.family i j =
      requestRegister P i j := by
    fin_cases j <;> rfl
  have h9 : (fun c : Fin 9 => OptimizedComputeHostileAccumulator.rowRecord (honestRow P i) j
      c.castSucc) = NockVM.encRecFormR (requestRegister P i j)
        P.optimized.family.problem.cfg.challenges.lam := by
    rw [← hreg, ← hrec]
    funext c
    have hc9 : ((c.castSucc : Fin 10) : ℕ) ≠ 9 := by simp; omega
    unfold OptimizedComputeHostileAccumulator.rowRecord
      OptimizedComputeFormRDenoms.sampledSlotRecord
    rw [if_neg hc9]
    simp only [Expr.eval_subst, Fin.val_castSucc]
  have hexp : (honestRow P i).expCol =
      ((OptimizedComputeFinalTrace.honestS P.optimized.family i : ℕ) : F) := by
    show (gatherCorrectedFinalTypedEnv P.optimized.basis
      (P.computeBaseEnv (honestComputeTrace P) i)).expCol = _
    unfold honestComputeTrace OptimizedFullStrictNockVMROMPackage.computeBaseEnv
    exact canonical_gather_expCol P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
      P.optimized.computePublic P.optimized.orbit i
  have hlast : OptimizedComputeHostileAccumulator.rowRecord (honestRow P i) j 9 =
      (((OptimizedComputeFinalTrace.honestS P.optimized.family i + (j : ℕ) + 1 : ℕ)) : K) := by
    unfold OptimizedComputeHostileAccumulator.rowRecord
    rw [if_pos (by rfl)]
    fin_cases j <;>
      simp [sampledSlotE, Expr.subst, finalSampledNamespace, Expr.eval,
        CorrectedFinalTypedEnv.toSourceEnv, hexp] <;> ring
  rw [RecordCarrier.eq_withExp (OptimizedComputeHostileAccumulator.rowRecord (honestRow P i) j),
    h9, show (Fin.last 9 : Fin 10) = 9 from rfl, hlast, ← hreg]
  exact OptimizedComputeFormRDenoms.withExp_honestS_eq_extRec P.optimized.sampled i j hact

omit [Fintype F] [DecidableEq F] in
/-- At the honest row the emitted request list is the opcode's active request prefix, Form R
encoded (`NockVM.activeRequestRecords`). -/
theorem canonical_rowRequests (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hwidth : FormRWidth F) (i : Fin P.optimized.family.problem.cfg.compRows) :
    rowRequests (honestRow P i) =
      (NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i)).map
        (fun r => RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
          (NockVM.encRecFormR r P.optimized.family.problem.cfg.challenges.lam)) := by
  have h0 := canonical_activeMask P i 0
  have h1 := canonical_activeMask P i 1
  have h2 := canonical_activeMask P i 2
  simp only at h0 h1 h2
  have r0 := canonical_rowRecord P hax hwidth i 0 rfl
  have r1 := canonical_rowRecord P hax hwidth i 1
  have r2 := canonical_rowRecord P hax hwidth i 2
  simp only [rowRequests, List.finRange, List.ofFn_succ, List.ofFn_zero, List.filterMap_cons,
    List.filterMap_nil, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h0, h1, h2]
  simp only [OptimizedComputeFormRDenoms.slotActive] at r1 r2
  cases hs : (P.optimized.family.problem.exec.computePubAt i).state <;>
    simp [NockVM.activeRequestRecords, hs, secondRequestMask, thirdRequestMask, r0, r1, r2,
      requestRegister] at r1 r2 ⊢ <;>
    simp_all

omit [Fintype F] [DecidableEq F] in
/-- **The hostile request list at the honest compute trace is the package's sampled request
list.** -/
theorem canonical_hostileRequests (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hwidth : FormRWidth F) :
    P.hostileRequests (honestComputeTrace P) = (honestRecords10 P.optimized.family).requests := by
  rw [honestRecords10, RecordCarrier.extRecords_requests]
  set L := P.optimized.family.problem.exec.derivedRequestIO with hLdef
  have hL2 : L = (List.ofFn fun i : Fin P.optimized.family.problem.cfg.compRows =>
      (NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i)).map
        (fun r => NockVM.encRecFormR r P.optimized.family.problem.cfg.challenges.lam)).flatten := by
    rw [hLdef, ExactExecution.derivedRequestIO,
      ExactExecution.rawRequests_eq_computeRows, List.map_flatMap, List.flatMap_def,
      ExactExecution.computeRows_eq_ofFn_computeRowAt, List.map_ofFn]
    rfl
  have hstep : P.hostileRequests (honestComputeTrace P) =
      (List.ofFn fun i : Fin P.optimized.family.problem.cfg.compRows =>
        ((NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i)).map
          (fun r => NockVM.encRecFormR r P.optimized.family.problem.cfg.challenges.lam)).map
          (RecordCarrier.extRec L)).flatten := by
    unfold OptimizedFullStrictNockVMROMPackage.hostileRequests
    congr 1
    exact congrArg List.ofFn (funext fun i => by
      have h := canonical_rowRequests P hax hwidth i
      simp only [honestRow] at h
      rw [h, List.map_map]
      rfl)
  rw [hstep]
  have key : ∀ M : List (Fin 9 → K), M = (List.ofFn fun i : Fin P.optimized.family.problem.cfg.compRows =>
      (NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i)).map
        (fun r => NockVM.encRecFormR r P.optimized.family.problem.cfg.challenges.lam)).flatten →
      (List.ofFn fun i : Fin P.optimized.family.problem.cfg.compRows =>
        ((NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i)).map
          (fun r => NockVM.encRecFormR r P.optimized.family.problem.cfg.challenges.lam)).map
          (RecordCarrier.extRec L)).flatten = M.map (RecordCarrier.extRec L) := by
    intro M hM
    rw [hM, List.map_flatten, List.map_ofFn]
    rfl
  exact key L hL2

/-- The honest gathered memory row. -/
abbrev honestMemRow (i : Fin P.optimized.family.problem.cfg.memRows) : Env K :=
  P.memorySourceEnv (honestMemoryTrace P) i

/-- The honest base memory row. -/
abbrev honestMemBase (i : Fin P.optimized.family.problem.cfg.memRows) : Env F :=
  P.memoryBaseEnv (honestMemoryTrace P) i

omit [Fintype F] [DecidableEq F] in
/-- Honest `ver` (role `39`) is the `read_root` indicator (`responseActive`). -/
theorem canonical_ver (i : Fin P.optimized.family.problem.cfg.memRows) :
    (honestMemRow P i).trace 39 =
      OptimizedMemorySemanticRealization.responseActive (K := K)
        (P.optimized.family.problem.exec.memoryPubAt i).ver := by
  show (P.memorySourceEnv (honestMemoryTrace P) i).trace 39 = _
  rw [canonical_memorySourceEnv]
  have h := canonical_gather_sampled_index P.optimized.sampled P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit i (2 : Fin 14) (by decide)
  simpa [OptimizedMemorySemanticRealization.sampledMemoryRoleValue] using h

omit [Fintype F] [DecidableEq F] in
/-- Honest roles `19..26` are the encoded memory record of the row (nine-slot prefix). -/
theorem canonical_memRowRecord9 (i : Fin P.optimized.family.problem.cfg.memRows) :
    (fun c : Fin 9 => OptimizedMemoryHostileAccumulator.rowRecord (honestMemRow P i)
      (honestMemBase P i) c.castSucc) =
      NockVM.encRecC (P.optimized.family.problem.exec.memoryPubAt i).mem
        (P.optimized.family.problem.exec.memoryPubAt i).cprime := by
  funext c
  unfold OptimizedMemoryHostileAccumulator.rowRecord
  refine Fin.lastCases ?last (fun c8 => ?init) c
  case last =>
    have r57 : (honestMemRow P i).trace 57 =
        (P.optimized.family.problem.exec.memoryPubAt i).cprime := by
      show (P.memorySourceEnv (honestMemoryTrace P) i).trace 57 =
        (P.optimized.family.problem.exec.memoryPubAt i).cprime
      rw [canonical_memorySourceEnv]
      exact canonical_gather_cprime P.optimized.sampled P.optimized.memoryNodes
        P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
        P.optimized.memoryPublic P.optimized.orbit i
    simp [NockVM.encRecC, MemoryTable.Pub.cprime, r57]
  case init =>
    simp only [Fin.val_castSucc]
    rw [dif_pos c8.isLt]
    show (P.memorySourceEnv (honestMemoryTrace P) i).trace (19 + (c8 : ℕ)) = _
    rw [canonical_memorySourceEnv]
    have hrole := canonical_table_role P.optimized.sampled P.optimized.memoryNodes
      P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit P.optimized.memoryCoordinatePins i
      (23 + (c8 : ℕ)) (by omega) (by omega) (by omega)
    rw [show 23 + (c8 : ℕ) - 4 = 19 + (c8 : ℕ) by omega] at hrole
    rw [hrole]
    fin_cases c8 <;>
      simp [OptimizedMemorySemanticRealization.exactMemoryRowEnv,
        memoryEnvFull, NockVM.encRecC, MemoryTable.Pub.cprime]

omit [Fintype F] [DecidableEq F] in
/-- **The 31st:** the honest row's ten-slot record is `rowRecord10` (roles `19..26`, `C'` and the
base column `reqIdx`). -/
theorem canonical_memRowRecord (i : Fin P.optimized.family.problem.cfg.memRows) :
    OptimizedMemoryHostileAccumulator.rowRecord (honestMemRow P i) (honestMemBase P i) =
      OptimizedMemorySemanticRealization.rowRecord10 P.optimized.family i := by
  rw [RecordCarrier.eq_withExp (OptimizedMemoryHostileAccumulator.rowRecord _ _),
    canonical_memRowRecord9]
  unfold OptimizedMemorySemanticRealization.rowRecord10
  congr 1
  show OptimizedMemoryHostileAccumulator.rowRecord (honestMemRow P i) (honestMemBase P i) 9 = _
  unfold OptimizedMemoryHostileAccumulator.rowRecord
  simp only [show ¬ ((9 : Fin 10) : ℕ) < 8 by decide, dif_neg, not_false_eq_true,
    show ((9 : Fin 10) : ℕ) ≠ 8 by decide, if_false]
  rw [show honestMemBase P i = P.memoryBaseEnv (honestMemoryTrace P) i from rfl,
    canonical_memoryBaseEnv]
  rw [canonical_physical_reqIdx P.optimized.sampled P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit i]
  simp [OptimizedMemorySemanticRealization.honestReqIdx]

omit [Fintype F] [DecidableEq F] in
/-- At the honest row the served response list is `MemoryTable.responseRecords`, encoded with its
honest exponent. -/
theorem canonical_rowResponses (i : Fin P.optimized.family.problem.cfg.memRows) :
    rowResponses (honestMemRow P i) (honestMemBase P i) =
      (MemoryTable.responseRecords (P.optimized.family.problem.exec.memoryPubAt i)).map
        (fun r => RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
          (NockVM.encRecC r (P.optimized.family.problem.exec.memoryPubAt i).cprime)) := by
  simp only [rowResponses, rowResponseTerms, canonical_ver, canonical_memRowRecord,
    OptimizedMemorySemanticRealization.responseActive]
  cases hv : (P.optimized.family.problem.exec.memoryPubAt i).ver
  · simp [MemoryTable.responseRecords, hv]
  · have hst : (P.optimized.family.problem.exec.memoryPubAt i).st = .read_root := by
      have h := P.optimized.sampled.honestVer _
        (ExactExecution.memoryRowAt_mem P.optimized.family.problem.exec i)
      have h' : (P.optimized.family.problem.exec.memoryPubAt i).ver =
          decide ((P.optimized.family.problem.exec.memoryPubAt i).st =
            MemoryTable.MState.read_root) := h
      rw [hv] at h'
      simpa using h'.symm
    simp [MemoryTable.responseRecords, hv,
      OptimizedMemorySemanticRealization.rowRecord10_of_active _ i (Or.inl hst),
      MemoryTable.Pub.cprime]

omit [Fintype F] [DecidableEq F] in
/-- **The hostile response list at the honest memory trace is the package's sampled response
list.** -/
theorem canonical_hostileResponses :
    P.hostileResponses (honestMemoryTrace P) =
      (honestRecords10 P.optimized.family).responses := by
  rw [honestRecords10, RecordCarrier.extRecords_responses]
  conv_rhs => rw [ExactExecution.derivedResponseIO_eq_memoryRows,
    ExactExecution.memoryRows_eq_ofFn_memoryRowAt, List.flatMap_def, List.map_ofFn,
    List.map_flatten, List.map_ofFn]
  unfold OptimizedFullStrictNockVMROMPackage.hostileResponses
  congr 1
  exact congrArg List.ofFn (funext fun i => by
    have h := canonical_rowResponses P i
    simp only [honestMemRow, honestMemBase] at h
    rw [h]
    simp [MemoryTable.responseRecords, ExactExecution.memoryPubAt]
    split_ifs with hv <;> simp [hv])

omit [Fintype F] [DecidableEq F] in
/-- **The hostile records at the honest traces are the package's sampled records.** -/
theorem canonical_hostileRecords (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hwidth : FormRWidth F) :
    P.hostileRecords (honestComputeTrace P) (honestMemoryTrace P) =
      honestRecords10 P.optimized.family := by
  unfold OptimizedFullStrictNockVMROMPackage.hostileRecords
  rw [canonical_hostileRequests P hax hwidth, canonical_hostileResponses]

omit [Fintype F] [DecidableEq F] in
/-- **The sampled coins are outside the IO events at the honest traces' records** — the package's
`coins_not_failure`, read at `hostileRecords`. -/
theorem canonical_coins_not_hostile_failure
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F) :
    (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole) ∉
      FiniteIO.IOFailureEvent
        (P.hostileRecords (honestComputeTrace P) (honestMemoryTrace P)) := by
  rw [canonical_hostileRecords P hax hwidth]
  exact P.optimized.sampled.ioGood10

omit [Fintype F] [DecidableEq F] in
/-- **A base of order at least `3·compRows` is outside the α-collision event at any trace's
request count** (`hostileRequests_length_le`; the `horb` shape of `nockCompiles`). -/
theorem alpha_not_collision_of_orderOf
    (Qc : Fin P.computeChip.rap.w → F[X]) {α : K}
    (hα0 : α ≠ 0) (hord : 3 * P.optimized.family.problem.cfg.compRows ≤ orderOf α) :
    α ∉ OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length :=
  OptimizedHostileTimestamps.not_mem_event_of_le_orderOf hα0
    ((P.hostileRequests_length_le Qc).trans hord)

/-! ### Intermediate pole at the honest traces (W4 stage 2) -/

omit [Fintype F] [DecidableEq F] in
theorem canonical_base_sel (i : Fin P.optimized.family.problem.cfg.memRows)
    (j : Fin 6) :
    (P.memoryBaseEnv (honestMemoryTrace P) i).trace j =
      (encodedRowAt P.optimized.sampled i).base j := by
  rw [canonical_memoryBaseEnv]
  exact canonical_base_current P.optimized.sampled P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis
    P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit i j

theorem encodedRowAt_base_state
    (i : Fin P.optimized.family.problem.cfg.memRows) (j : Fin 4) :
    (OptimizedMemorySemanticRealization.encodedRowAt P.optimized.sampled i).base
      ⟨j.val, by omega⟩ =
      stateSelector (F := F)
        (P.optimized.family.problem.exec.memoryPubAt i).st j := by
  unfold OptimizedMemorySemanticRealization.encodedRowAt OptimizedMemoryCodec.encode
  change encodeBase (OptimizedMemorySemanticRealization.semanticRowAt
      P.optimized.sampled i) ⟨j.val, by omega⟩ = _
  unfold encodeBase
  simp [dif_pos (show j.val < 4 from j.isLt),
    OptimizedMemorySemanticRealization.semanticRowAt]

theorem canonical_sel2 (i : Fin P.optimized.family.problem.cfg.memRows) :
    (P.memoryBaseEnv (honestMemoryTrace P) i).trace 2 =
      stateSelector (F := F)
        (P.optimized.family.problem.exec.memoryPubAt i).st 2 := by
  refine (canonical_base_sel P i (⟨2, by omega⟩ : Fin 6)).trans ?_
  exact encodedRowAt_base_state P i (2 : Fin 4)

theorem canonical_sel3 (i : Fin P.optimized.family.problem.cfg.memRows) :
    (P.memoryBaseEnv (honestMemoryTrace P) i).trace 3 =
      stateSelector (F := F)
        (P.optimized.family.problem.exec.memoryPubAt i).st 3 := by
  refine (canonical_base_sel P i (⟨3, by omega⟩ : Fin 6)).trans ?_
  exact encodedRowAt_base_state P i (3 : Fin 4)

theorem canonical_rowInterReads
    (hC : P.optimized.family.problem.exec.CprimeCoherent)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (if (P.memoryBaseEnv (honestMemoryTrace P) i).trace 2 = 1 then
      [OptimizedMemoryHostileAccumulator.rowRecord
        (P.memorySourceEnv (honestMemoryTrace P) i) (P.memoryBaseEnv (honestMemoryTrace P) i)]
      else []) =
    (match (P.optimized.family.problem.exec.memoryPubAt i).st with
      | .read_root => [(P.optimized.family.problem.exec.memoryPubAt i).mem]
      | .decompose | .halt | .verify_child => []).map
        (fun r => RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
          (NockVM.encRecC r (P.optimized.family.problem.exec.cprimeOf r))) := by
  have hc : (P.optimized.family.problem.exec.memoryPubAt i).cprime =
      P.optimized.family.problem.exec.cprimeOf (P.optimized.family.problem.exec.memoryPubAt i).mem
          :=
    ExactExecution.cprime_eq_cprimeOf hC _ (ExactExecution.memoryRowAt_mem _ i)
  have hrec := canonical_memRowRecord P i
  simp only [honestMemRow, honestMemBase] at hrec
  rw [canonical_sel2, hrec]
  cases hst : (P.optimized.family.problem.exec.memoryPubAt i).st with
  | read_root =>
    rw [OptimizedMemorySemanticRealization.rowRecord10_of_active _ i (Or.inl hst), hc]
    simp [stateSelector, stateIndex, hst]
  | _ => simp [stateSelector, stateIndex, hst]

theorem canonical_rowInterVerifies
    (hC : P.optimized.family.problem.exec.CprimeCoherent)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (if (P.memoryBaseEnv (honestMemoryTrace P) i).trace 3 = 1 then
      [OptimizedMemoryHostileAccumulator.rowRecord
        (P.memorySourceEnv (honestMemoryTrace P) i) (P.memoryBaseEnv (honestMemoryTrace P) i)]
      else []) =
    (RowLayout.consumedRecords
      (P.optimized.family.problem.exec.memoryPubAt i)).map
        (fun r => RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
          (NockVM.encRecC r (P.optimized.family.problem.exec.cprimeOf r))) := by
  have hc : (P.optimized.family.problem.exec.memoryPubAt i).cprime =
      P.optimized.family.problem.exec.cprimeOf (P.optimized.family.problem.exec.memoryPubAt i).mem
          :=
    ExactExecution.cprime_eq_cprimeOf hC _ (ExactExecution.memoryRowAt_mem _ i)
  have hrec := canonical_memRowRecord P i
  simp only [honestMemRow, honestMemBase] at hrec
  rw [canonical_sel3, hrec]
  cases hst : (P.optimized.family.problem.exec.memoryPubAt i).st with
  | verify_child =>
    rw [OptimizedMemorySemanticRealization.rowRecord10_of_active _ i (Or.inr hst), hc]
    simp [stateSelector, stateIndex, RowLayout.consumedRecords, hst]
  | _ => simp [stateSelector, stateIndex, RowLayout.consumedRecords, hst]

theorem canonical_hostileInterReads
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    P.hostileInterReads (honestMemoryTrace P) =
      (RowLayout.addedRecordList P.optimized.family.problem.exec).map
        (fun r => RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
          (NockVM.encRecC r (P.optimized.family.problem.exec.cprimeOf r))) := by
  rw [RowLayout.addedRecordList, ExactExecution.memoryRows_eq_ofFn_memoryRowAt,
    List.map_flatMap, List.flatMap_def, List.map_ofFn]
  unfold OptimizedFullStrictNockVMROMPackage.hostileInterReads
  congr 1
  exact congrArg List.ofFn (funext fun i => canonical_rowInterReads P hC i)

theorem canonical_hostileInterVerifies
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    P.hostileInterVerifies (honestMemoryTrace P) =
      (RowLayout.consumedRecordList P.optimized.family.problem.exec).map
        (fun r => RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
          (NockVM.encRecC r (P.optimized.family.problem.exec.cprimeOf r))) := by
  rw [RowLayout.consumedRecordList, ExactExecution.memoryRows_eq_ofFn_memoryRowAt,
    List.map_flatMap, List.flatMap_def, List.map_ofFn]
  unfold OptimizedFullStrictNockVMROMPackage.hostileInterVerifies
  congr 1
  exact congrArg List.ofFn (funext fun i => canonical_rowInterVerifies P hC i)

/-- Hostile intermediate lists at the honest memory trace are the package's honest ten-slot
in-table lists, swapped (reads = added, verifies = consumed). -/
theorem canonical_hostileInterRecords
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    P.hostileInterRecords (honestMemoryTrace P) =
      ⟨(honestInterRecords10 P.optimized.family).responses,
        (honestInterRecords10 P.optimized.family).requests⟩ := by
  unfold OptimizedFullStrictNockVMROMPackage.hostileInterRecords
  rw [canonical_hostileInterReads P hC, canonical_hostileInterVerifies P hC]
  have henc : P.optimized.family.problem.exec.derivedResponseIO =
      (RowLayout.addedRecordList P.optimized.family.problem.exec).map
        (fun r => NockVM.encRecC r (P.optimized.family.problem.exec.cprimeOf r)) := by
    rw [← RowLayout.rawResponses_eq_addedRecordList _
      P.optimized.sampled.honestVer]
    exact ExactExecution.derivedResponseIO_eq_map_encRecC _ hC
  simp only [honestInterRecords10, RecordCarrier.extRecords_requests,
    RecordCarrier.extRecords_responses, henc, List.map_map]
  rfl

theorem encRec_zero :
    NockVM.encRec (ComputeTable.MemRec.zero : ComputeTable.MemRec K) = 0 := by
  ext c
  fin_cases c <;> simp [NockVM.encRec, ComputeTable.MemRec.zero]

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K] in
theorem rlc_encRecC_memRec_zero (γ c : K) :
    Walk.rlc (node_size := 9) γ
      (NockVM.encRecC (ComputeTable.MemRec.zero : ComputeTable.MemRec K) c) =
      γ ^ 8 * c := by
  have hv : ∀ i : Fin 9, i.val ≠ 8 →
      NockVM.encRecC (ComputeTable.MemRec.zero : ComputeTable.MemRec K) c i = 0 := by
    intro i hi
    fin_cases i <;> simp [NockVM.encRecC, ComputeTable.MemRec.zero] at hi ⊢
  have h8 :
      NockVM.encRecC (ComputeTable.MemRec.zero : ComputeTable.MemRec K) c
        (8 : Fin 9) = c := by
    simp [NockVM.encRecC, ComputeTable.MemRec.zero]
  unfold Walk.rlc
  rw [Finset.sum_eq_single (8 : Fin 9)]
  · rw [h8]; simp
  · intro i _ hne
    have : i.val ≠ 8 := fun h => hne (Fin.ext h)
    simp [hv i this]
  · simp

/-- All-row pole-hit at the honest encodings: active rows by `interPoleHitGood10`,
inactive (`halt`/`decompose`) rows by `mem = 0`, `reqIdx = 0` and `interPole ≠ 0`. -/
theorem canonical_allRow_not_hit
    (h0 : P.optimized.sampled.interPole ≠ 0)
    (hγ8 : P.optimized.sampled.interPole +
      P.optimized.sampled.sampled.coins.gamma ^ 8 ≠ 0)
    (hz : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      (P.optimized.family.problem.exec.memoryPubAt i).mem = ComputeTable.MemRec.zero)
    (hzc : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      (P.optimized.family.problem.exec.memoryPubAt i).cprime = 1)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.interPole) ∉
      allRowPoleHitEvent (P.memorySourceEnv (honestMemoryTrace P))
        (P.memoryBaseEnv (honestMemoryTrace P)) := by
  intro h
  simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨v, hv, hcomp⟩ := h
  have hv' : v ∈ List.ofFn (fun i : Fin P.optimized.family.problem.cfg.memRows =>
      OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv (honestMemoryTrace P) i)
        (P.memoryBaseEnv (honestMemoryTrace P) i)) := by
    simpa [List.mem_append] using hv
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hv'
  have hvrec : v = OptimizedMemorySemanticRealization.rowRecord10 P.optimized.family i := by
    rw [← hi]; exact canonical_memRowRecord P i
  cases hst : (P.optimized.family.problem.exec.memoryPubAt i).st with
  | read_root =>
    apply P.optimized.sampled.interPoleHitGood10
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨v, ?_, hcomp⟩
    rw [hvrec, OptimizedMemorySemanticRealization.rowRecord10_of_active _ i (Or.inl hst)]
    apply List.mem_append_right
    refine List.mem_map.mpr ⟨_, ?_, rfl⟩
    rw [ExactExecution.derivedResponseIO]
    refine List.mem_flatMap.mpr
      ⟨P.optimized.family.problem.exec.memoryRowAt i,
        ExactExecution.memoryRowAt_mem _ i, ?_⟩
    have hv := P.optimized.sampled.honestVer _
      (ExactExecution.memoryRowAt_mem _ i)
    have hpub : (P.optimized.family.problem.exec.memoryRowAt i).2.2 =
        P.optimized.family.problem.exec.memoryPubAt i := rfl
    rw [hpub, hst] at hv
    rw [decide_eq_true rfl] at hv
    have hver : (P.optimized.family.problem.exec.memoryRowAt i).2.2.ver = true := by
      rw [hpub]; exact hv
    rw [if_pos hver]
    exact List.mem_singleton.mpr (by simp [hpub])
  | verify_child =>
    apply P.optimized.sampled.interPoleHitGood10
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc : (P.optimized.family.problem.exec.memoryPubAt i).cprime =
        P.optimized.family.problem.exec.cprimeOf
          (P.optimized.family.problem.exec.memoryPubAt i).mem :=
      ExactExecution.cprime_eq_cprimeOf hC _ (ExactExecution.memoryRowAt_mem _ i)
    refine ⟨v, ?_, hcomp⟩
    rw [hvrec, OptimizedMemorySemanticRealization.rowRecord10_of_active _ i (Or.inr hst), hc]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_, List.mem_map.mpr
      ⟨_, RowLayout.mem_consumedRecordList_of_verify_child _ i hst, rfl⟩, rfl⟩)
  | halt =>
    have hmem := hz i (by simp [hst]) (by simp [hst])
    have hc := hzc i (by simp [hst]) (by simp [hst])
    have hrlc : Walk.rlc P.optimized.sampled.sampled.coins.gamma v =
        P.optimized.sampled.sampled.coins.gamma ^ 8 := by
      rw [hvrec, OptimizedMemorySemanticRealization.rowRecord10, RecordCarrier.rlc_withExp]
      simp only [OptimizedMemorySemanticRealization.reqIdxNat, hst]
      rw [hmem, hc, rlc_encRecC_memRec_zero]
      simp
    exact hγ8 (by simpa [hrlc] using hcomp)
  | decompose =>
    have hmem := hz i (by simp [hst]) (by simp [hst])
    have hc := hzc i (by simp [hst]) (by simp [hst])
    have hrlc : Walk.rlc P.optimized.sampled.sampled.coins.gamma v =
        P.optimized.sampled.sampled.coins.gamma ^ 8 := by
      rw [hvrec, OptimizedMemorySemanticRealization.rowRecord10, RecordCarrier.rlc_withExp]
      simp only [OptimizedMemorySemanticRealization.reqIdxNat, hst]
      rw [hmem, hc, rlc_encRecC_memRec_zero]
      simp
    exact hγ8 (by simpa [hrlc] using hcomp)

/-- Twin of `canonical_coins_not_hostile_failure` on the priced internal-pole pairs. -/
theorem canonical_inter_not_hostile_failure
    (h0 : P.optimized.sampled.interPole ≠ 0)
    (hγ8 : P.optimized.sampled.interPole +
      P.optimized.sampled.sampled.coins.gamma ^ 8 ≠ 0)
    (hz : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      (P.optimized.family.problem.exec.memoryPubAt i).mem = ComputeTable.MemRec.zero)
    (hzc : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      (P.optimized.family.problem.exec.memoryPubAt i).cprime = 1)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.interPole) ∉
      interFailurePairs
        (P.hostileInterRecords (honestMemoryTrace P))
        (P.memorySourceEnv (honestMemoryTrace P))
        (P.memoryBaseEnv (honestMemoryTrace P)) := by
  intro h
  simp only [interFailurePairs, Finset.mem_union] at h
  rcases h with hio | hrow
  · rw [canonical_hostileInterRecords P hC] at hio
    have hswap := FiniteIO.IOFailureEvent_swap
      (honestInterRecords10 P.optimized.family).responses
      (honestInterRecords10 P.optimized.family).requests
    rw [hswap] at hio
    exact P.optimized.sampled.inter_coins_not_failure10
      P.optimized.pairedRecordLayout hC hio
  · exact canonical_allRow_not_hit P h0 hγ8 hz hzc hC hrow

end
end OptimizedCanonicalHostileLists
end Nock.NockVMROM.Thm54
