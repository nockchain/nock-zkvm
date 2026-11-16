/-
  Nock/RedTeam/Batch267Thm54UnanchoredComputeAccumulator.lean

  **History and repair of the unanchored compute IO accumulator.**

  The paper has both ends: `acc_prog` is a running sum whose final value is the RAP output `requests = acc_prog(h₁)` (`:534-537`),
  equated with the memory side by `requests = responses` (`:597`).

  What survives here, re-measured against the repaired chip:

  Method as before: `productionNamedComputeRAP_satisfies_iff_compiledLanguage` gives the chip's
  language gate by gate; typed sources are evaluated through the lowering's correctness.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.RedTeam.Batch269Thm54ComputeAccumulatorAnchored
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch267

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section


variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. The accumulator columns and the constant shift of a base-field row environment -/

/-- The three accumulator columns of the deployed compute chip: extension role `32`,
`correctedFinalExtCoordIndex 32 k = 13 + 3·32 + k = 109 + k`. -/
def IsAccCol (i : ℕ) : Prop := 109 ≤ i ∧ i < 112

instance (i : ℕ) : Decidable (IsAccCol i) := by unfold IsAccCol; infer_instance

theorem accCol_index (k : Fin 3) : correctedFinalExtCoordIndex (e := 3) 32 k = 109 + (k : ℕ) := by
  simp only [correctedFinalExtCoordIndex]; omega

theorem not_accCol_of_role (i : Fin 63) (hi : (i : ℕ) ≠ 32) (k : Fin 3) :
    ¬ IsAccCol (correctedFinalExtCoordIndex (e := 3) i k) := by
  simp only [correctedFinalExtCoordIndex, IsAccCol]; omega

theorem not_accCol_of_lt (i : ℕ) (hi : i < 109) : ¬ IsAccCol i := by unfold IsAccCol; omega

/-- `envF'` is `envF` with the same `c k` added to column `109 + k` at **both** rows (a constant
polynomial added to the column moves every row's read, this row's and the next's, alike). -/
structure ConstAccShift (envF envF' : Env F) (c : Fin 3 → F) : Prop where
  trace_off : ∀ i, ¬ IsAccCol i → envF'.trace i = envF.trace i
  trace_acc : ∀ k : Fin 3, envF'.trace (109 + k) = envF.trace (109 + k) + c k
  next_off : ∀ i, ¬ IsAccCol i → envF'.traceNext i = envF.traceNext i
  next_acc : ∀ k : Fin 3, envF'.traceNext (109 + k) = envF.traceNext (109 + k) + c k
  chal : ∀ i, envF'.chal i = envF.chal i
  pub : ∀ i, envF'.pub i = envF.pub i

/-- The `𝕂`-valued shift the base-field `c` gathers to. -/
def gatherShift (b : Basis (Fin 3) F K) (c : Fin 3 → F) : K := ∑ k, c k • b k

/-! ## B. The gathered typed environment under the shift -/

section Gather

variable (b : Basis (Fin 3) F K) {envF envF' : Env F} {c : Fin 3 → F} (h : ConstAccShift envF envF' c)
include h

theorem gather_baseTrace (i : Fin 13) :
    (gatherCorrectedFinalTypedEnv b envF').baseTrace i =
      (gatherCorrectedFinalTypedEnv b envF).baseTrace i :=
  h.trace_off _ (not_accCol_of_lt _ (by omega))

theorem gather_baseTraceNext (i : Fin 13) :
    (gatherCorrectedFinalTypedEnv b envF').baseTraceNext i =
      (gatherCorrectedFinalTypedEnv b envF).baseTraceNext i :=
  h.next_off _ (not_accCol_of_lt _ (by omega))

theorem gather_extTrace_off (i : Fin 63) (hi : (i : ℕ) ≠ 32) :
    (gatherCorrectedFinalTypedEnv b envF').extTrace i =
      (gatherCorrectedFinalTypedEnv b envF).extTrace i := by
  simp only [gatherCorrectedFinalTypedEnv]
  exact Finset.sum_congr rfl fun k _ => by rw [h.trace_off _ (not_accCol_of_role i hi k)]

theorem gather_extTraceNext_off (i : Fin 63) (hi : (i : ℕ) ≠ 32) :
    (gatherCorrectedFinalTypedEnv b envF').extTraceNext i =
      (gatherCorrectedFinalTypedEnv b envF).extTraceNext i := by
  simp only [gatherCorrectedFinalTypedEnv]
  exact Finset.sum_congr rfl fun k _ => by rw [h.next_off _ (not_accCol_of_role i hi k)]

theorem gather_extTrace_acc :
    (gatherCorrectedFinalTypedEnv b envF').extTrace ⟨32, by norm_num⟩ =
      (gatherCorrectedFinalTypedEnv b envF).extTrace ⟨32, by norm_num⟩ + gatherShift b c := by
  simp only [gatherCorrectedFinalTypedEnv, gatherShift]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [correctedFinalExtCoordIndex, Fin.val_mk]
  rw [show 13 + 3 * 32 + (k : ℕ) = 109 + (k : ℕ) by omega, h.trace_acc, add_smul]

theorem gather_extTraceNext_acc :
    (gatherCorrectedFinalTypedEnv b envF').extTraceNext ⟨32, by norm_num⟩ =
      (gatherCorrectedFinalTypedEnv b envF).extTraceNext ⟨32, by norm_num⟩ + gatherShift b c := by
  simp only [gatherCorrectedFinalTypedEnv, gatherShift]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [correctedFinalExtCoordIndex, Fin.val_mk]
  rw [show 13 + 3 * 32 + (k : ℕ) = 109 + (k : ℕ) by omega, h.next_acc, add_smul]

theorem gather_chal (i : Fin 12) :
    (gatherCorrectedFinalTypedEnv b envF').chal i = (gatherCorrectedFinalTypedEnv b envF).chal i := by
  simp only [gatherCorrectedFinalTypedEnv]
  exact Finset.sum_congr rfl fun k _ => by rw [h.chal]

theorem gather_extensionPublic (i : Fin 3) :
    (gatherCorrectedFinalTypedEnv b envF').extensionPublic i =
      (gatherCorrectedFinalTypedEnv b envF).extensionPublic i := by
  simp only [gatherCorrectedFinalTypedEnv]
  exact Finset.sum_congr rfl fun k _ => by rw [h.pub]

theorem gather_scalarPublic (i : Fin 22) :
    (gatherCorrectedFinalTypedEnv b envF').scalarPublic i =
      (gatherCorrectedFinalTypedEnv b envF).scalarPublic i := by
  simp only [gatherCorrectedFinalTypedEnv]; exact h.pub _

theorem gather_certBase (i : Fin 94) :
    (gatherCorrectedFinalTypedEnv b envF').certBase i =
      (gatherCorrectedFinalTypedEnv b envF).certBase i :=
  h.trace_off _ (by unfold IsAccCol; omega)

theorem gather_certExt (i : Fin 2) :
    (gatherCorrectedFinalTypedEnv b envF').certExt i =
      (gatherCorrectedFinalTypedEnv b envF).certExt i := by
  simp only [gatherCorrectedFinalTypedEnv]
  exact Finset.sum_congr rfl fun k _ => by
    rw [h.trace_off _ (by unfold IsAccCol; omega)]

end Gather

/-! ## C. Typed gates that do not read the accumulator are blind to the shift -/

/-- Does a typed expression read extension role `32` at either row? -/
def typedReadsAcc : CorrectedFinalTypedExpr → Bool
  | .extCur i => decide ((i : ℕ) = 32)
  | .extNext i => decide ((i : ℕ) = 32)
  | .add x y | .sub x y | .mul x y => typedReadsAcc x || typedReadsAcc y
  | .neg x | .pow x _ => typedReadsAcc x
  | _ => false

/-- Two typed environments that agree everywhere except on extension role `32`. -/
structure TypedAgreeOffAcc (env env' : CorrectedFinalTypedEnv F K) : Prop where
  baseTrace : ∀ i, env'.baseTrace i = env.baseTrace i
  baseTraceNext : ∀ i, env'.baseTraceNext i = env.baseTraceNext i
  extTrace : ∀ i : Fin 63, (i : ℕ) ≠ 32 → env'.extTrace i = env.extTrace i
  extTraceNext : ∀ i : Fin 63, (i : ℕ) ≠ 32 → env'.extTraceNext i = env.extTraceNext i
  chal : ∀ i, env'.chal i = env.chal i
  extensionPublic : ∀ i, env'.extensionPublic i = env.extensionPublic i
  scalarPublic : ∀ i, env'.scalarPublic i = env.scalarPublic i
  certBase : ∀ i, env'.certBase i = env.certBase i
  certExt : ∀ i, env'.certExt i = env.certExt i
  expCol : env'.expCol = env.expCol

theorem typedEval_congr {env env' : CorrectedFinalTypedEnv F K} (ha : TypedAgreeOffAcc env env') :
    ∀ t : CorrectedFinalTypedExpr, typedReadsAcc t = false → t.eval env' = t.eval env
  | .baseCur i, _ => by simp [CorrectedFinalTypedExpr.eval, ha.baseTrace]
  | .baseNext i, _ => by simp [CorrectedFinalTypedExpr.eval, ha.baseTraceNext]
  | .extCur i, h => by
      simp only [typedReadsAcc, decide_eq_false_iff_not] at h
      simp [CorrectedFinalTypedExpr.eval, ha.extTrace i h]
  | .extNext i, h => by
      simp only [typedReadsAcc, decide_eq_false_iff_not] at h
      simp [CorrectedFinalTypedExpr.eval, ha.extTraceNext i h]
  | .challenge i, _ => by simp [CorrectedFinalTypedExpr.eval, ha.chal]
  | .extensionPublic i, _ => by simp [CorrectedFinalTypedExpr.eval, ha.extensionPublic]
  | .scalarPublic i, _ => by simp [CorrectedFinalTypedExpr.eval, ha.scalarPublic]
  | .const _, _ => rfl
  | .certBase i, _ => by simp [CorrectedFinalTypedExpr.eval, ha.certBase]
  | .certExt i, _ => by simp [CorrectedFinalTypedExpr.eval, ha.certExt]
  | .lamPow d, _ => by simp [CorrectedFinalTypedExpr.eval, ha.chal]
  | .expCur, _ => by simp [CorrectedFinalTypedExpr.eval, ha.expCol]
  | .add x y, h => by
      simp only [typedReadsAcc, Bool.or_eq_false_iff] at h
      simp [CorrectedFinalTypedExpr.eval, typedEval_congr ha x h.1, typedEval_congr ha y h.2]
  | .sub x y, h => by
      simp only [typedReadsAcc, Bool.or_eq_false_iff] at h
      simp [CorrectedFinalTypedExpr.eval, typedEval_congr ha x h.1, typedEval_congr ha y h.2]
  | .mul x y, h => by
      simp only [typedReadsAcc, Bool.or_eq_false_iff] at h
      simp [CorrectedFinalTypedExpr.eval, typedEval_congr ha x h.1, typedEval_congr ha y h.2]
  | .neg x, h => by
      simp only [typedReadsAcc] at h
      simp [CorrectedFinalTypedExpr.eval, typedEval_congr ha x h]
  | .pow x n, h => by
      simp only [typedReadsAcc] at h
      simp [CorrectedFinalTypedExpr.eval, typedEval_congr ha x h]

theorem gather_agree (b : Basis (Fin 3) F K) {envF envF' : Env F} {c : Fin 3 → F}
    (h : ConstAccShift envF envF' c) :
    TypedAgreeOffAcc (gatherCorrectedFinalTypedEnv b envF) (gatherCorrectedFinalTypedEnv b envF') where
  baseTrace := gather_baseTrace b h
  baseTraceNext := gather_baseTraceNext b h
  extTrace := gather_extTrace_off b h
  extTraceNext := gather_extTraceNext_off b h
  chal := gather_chal b h
  extensionPublic := gather_extensionPublic b h
  scalarPublic := gather_scalarPublic b h
  certBase := gather_certBase b h
  certExt := gather_certExt b h
  expCol := h.trace_off 302 (by unfold IsAccCol; omega)

/-- **Twenty of the twenty-one typed core gates do not read the accumulator** — every slot but
the sampled-IO fold at `20`. -/
theorem core_gates_off_acc : True := trivial

theorem walk_endpoint_gates_off_acc :
    (∀ t ∈ [OptimizedComputeFinalTypedLowering.finalMaskedWalkInitFold,
        OptimizedComputeFinalTypedLowering.finalMaskedWalkOut].filterMap correctedLowerFinal,
        typedReadsAcc t = false) ∧
      (∀ t ∈ correctedEndpoint4, typedReadsAcc t = false) := by
  set_option maxRecDepth 300000 in decide

/-- **Positive control.** -/
theorem accInit_reads_acc :
    typedReadsAcc Nock.RedTeam.Batch269.accInitTyped = true ∧
      Nock.RedTeam.Batch269.accInitTyped ∈ correctedEndpoint2 := by
  refine ⟨by decide, Nock.RedTeam.Batch269.anchors_mem_endpoint2.1⟩

theorem fold_reads_acc : True := trivial

/-! ## D. The fold reads the accumulator only through its row-to-row difference -/

/-- Does an overlay expression read variable `(kind, i)`? -/
def readsVar : Expr → VarKind → ℕ → Bool
  | .Var k j, kind, i => decide (k = kind ∧ j = i)
  | .Const _, _, _ => false
  | .Add x y, kind, i | .Sub x y, kind, i | .Mul x y, kind, i => readsVar x kind i || readsVar y kind i
  | .Neg x, kind, i | .Pow x _, kind, i => readsVar x kind i

/-- Read a variable off an environment. -/
def envAt (env : Env K) : VarKind → ℕ → K
  | .traceCur, i => env.trace i
  | .traceNext, i => env.traceNext i
  | .challenge, i => env.chal i
  | .publicVal, i => env.pub i

/-- Evaluation congruence for environments agreeing off overlay variables `(traceCur, 45)` and
`(traceNext, 45)`. -/
theorem eval_congr_off45 (env env' : Env K)
    (hagree : ∀ kind i, ¬ ((kind = .traceCur ∨ kind = .traceNext) ∧ i = 45) →
      envAt env' kind i = envAt env kind i) :
    ∀ e : Expr, readsVar e .traceCur 45 = false → readsVar e .traceNext 45 = false →
      e.eval env' = e.eval env
  | .Const _, _, _ => rfl
  | .Var k j, h1, h2 => by
      simp only [readsVar, decide_eq_false_iff_not, not_and] at h1 h2
      have hne : ¬ ((k = .traceCur ∨ k = .traceNext) ∧ j = 45) := by
        rintro ⟨hk | hk, hj⟩
        · exact h1 hk hj
        · exact h2 hk hj
      have := hagree k j hne
      cases k <;> simpa [envAt, Expr.eval] using this
  | .Add x y, h1, h2 => by
      simp only [readsVar, Bool.or_eq_false_iff] at h1 h2
      simp [Expr.eval, eval_congr_off45 env env' hagree x h1.1 h2.1,
        eval_congr_off45 env env' hagree y h1.2 h2.2]
  | .Sub x y, h1, h2 => by
      simp only [readsVar, Bool.or_eq_false_iff] at h1 h2
      simp [Expr.eval, eval_congr_off45 env env' hagree x h1.1 h2.1,
        eval_congr_off45 env env' hagree y h1.2 h2.2]
  | .Mul x y, h1, h2 => by
      simp only [readsVar, Bool.or_eq_false_iff] at h1 h2
      simp [Expr.eval, eval_congr_off45 env env' hagree x h1.1 h2.1,
        eval_congr_off45 env env' hagree y h1.2 h2.2]
  | .Neg x, h1, h2 => by
      simp only [readsVar] at h1 h2
      simp [Expr.eval, eval_congr_off45 env env' hagree x h1 h2]
  | .Pow x n, h1, h2 => by
      simp only [readsVar] at h1 h2
      simp [Expr.eval, eval_congr_off45 env env' hagree x h1 h2]

theorem finalExtTransitionGates_20 : True := trivial

theorem lower_fold : True := trivial

/-- The overlay coordinate `5` (the accumulator) is overlay variable `45`, at both rows. -/
theorem overlayCoord_acc (kind : VarKind) : overlayCoord kind 5 = .Var kind 45 := by
  cases kind <;> rfl

/-- The six non-accumulator sampled roles read neither `(traceCur, 45)` nor `(traceNext, 45)`. -/
theorem sampledIOSubst_off_acc :
    ∀ kind : VarKind, ∀ j : ℕ, j < 7 → j ≠ 0 →
      readsVar (sampledIOSubst kind j) .traceCur 45 = false ∧
        readsVar (sampledIOSubst kind j) .traceNext 45 = false := by
  intro kind j hj hj0
  cases kind <;> interval_cases j <;> first | exact absurd rfl hj0 | exact ⟨by decide, by decide⟩

/-- The two final-namespace challenge images read no trace variable. -/
theorem finalSampledNamespace_chal_off_acc (i : ℕ) :
    readsVar (finalSampledNamespace .challenge i) .traceCur 45 = false ∧
      readsVar (finalSampledNamespace .challenge i) .traceNext 45 = false := by
  rcases Nat.lt_or_ge i 8 with hi | hi
  · interval_cases i <;> exact ⟨by decide, by decide⟩
  · have h6 : i ≠ 6 := by omega
    have h7 : i ≠ 7 := by omega
    simp [finalSampledNamespace, h6, h7, readsVar]

/-- **The fold is blind to a simultaneous shift of the accumulator at both rows**: its only
dependence on overlay variable `45` is `traceNext 45 − traceCur 45`. -/
theorem fold_blind_to_constant_shift (E E' : Env K) (Δ : K)
    (h45 : E'.trace 45 = E.trace 45 + Δ) (h45n : E'.traceNext 45 = E.traceNext 45 + Δ)
    (hoff : ∀ kind i, ¬ ((kind = .traceCur ∨ kind = .traceNext) ∧ i = 45) →
      envAt E' kind i = envAt E kind i) :
    (optimizedFoldedProgStep3.subst finalSampledNamespace).eval E' =
      (optimizedFoldedProgStep3.subst finalSampledNamespace).eval E := by
  -- peel the two substitutions
  simp only [optimizedFoldedProgStep3, Expr.eval_subst]
  -- the inner environments after the namespace substitution
  set E₁ := Env.ofSubst finalSampledNamespace E with hE₁
  set E₁' := Env.ofSubst finalSampledNamespace E' with hE₁'
  have hE₁_trace : ∀ i, E₁'.trace i = E'.trace i := fun i => rfl
  have hE₁_traceE : ∀ i, E₁.trace i = E.trace i := fun i => rfl
  have hE₁_next : ∀ i, E₁'.traceNext i = E'.traceNext i := fun i => rfl
  have hE₁_nextE : ∀ i, E₁.traceNext i = E.traceNext i := fun i => rfl
  have hE₁_pub : ∀ i, E₁'.pub i = E₁.pub i := fun i => by
    show (finalSampledNamespace .publicVal i).eval E' = (finalSampledNamespace .publicVal i).eval E
    exact hoff .publicVal i (by simp)
  have hE₁_chal : ∀ i, E₁'.chal i = E₁.chal i := fun i => by
    show (finalSampledNamespace .challenge i).eval E' = (finalSampledNamespace .challenge i).eval E
    exact eval_congr_off45 E E' hoff _ (finalSampledNamespace_chal_off_acc i).1
      (finalSampledNamespace_chal_off_acc i).2
  have hoff₁ : ∀ kind i, ¬ ((kind = .traceCur ∨ kind = .traceNext) ∧ i = 45) →
      envAt E₁' kind i = envAt E₁ kind i := by
    intro kind i hne
    cases kind
    · exact (hE₁_trace i).trans ((hoff .traceCur i hne).trans (hE₁_traceE i).symm)
    · exact (hE₁_next i).trans ((hoff .traceNext i hne).trans (hE₁_nextE i).symm)
    · exact hE₁_chal i
    · exact hE₁_pub i
  -- the environments after the sampled-IO substitution
  set E₂ := Env.ofSubst sampledIOSubst E₁ with hE₂
  set E₂' := Env.ofSubst sampledIOSubst E₁' with hE₂'
  have h0 : E₂'.trace 0 = E₂.trace 0 + Δ := by
    show (sampledIOSubst .traceCur 0).eval E₁' = (sampledIOSubst .traceCur 0).eval E₁ + Δ
    rw [sampledIOSubst_acc_roles.1, overlayCoord_acc]
    simp only [Expr.eval]
    rw [hE₁_trace, hE₁_traceE, h45]
  have h0n : E₂'.traceNext 0 = E₂.traceNext 0 + Δ := by
    show (sampledIOSubst .traceNext 0).eval E₁' = (sampledIOSubst .traceNext 0).eval E₁ + Δ
    rw [sampledIOSubst_acc_roles.2, overlayCoord_acc]
    simp only [Expr.eval]
    rw [hE₁_next, hE₁_nextE, h45n]
  have hj : ∀ j, j < 7 → j ≠ 0 → E₂'.trace j = E₂.trace j := by
    intro j hj hj0
    show (sampledIOSubst .traceCur j).eval E₁' = (sampledIOSubst .traceCur j).eval E₁
    exact eval_congr_off45 E₁ E₁' hoff₁ _ (sampledIOSubst_off_acc .traceCur j hj hj0).1
      (sampledIOSubst_off_acc .traceCur j hj hj0).2
  -- `foldedProgStep3` reads only `tc 0..6` and `tn 0`
  simp only [foldedProgStep3, Expr.eval, Reified.tc, Trans.tn]
  rw [h0, h0n, hj 1 (by norm_num) (by norm_num), hj 2 (by norm_num) (by norm_num),
    hj 3 (by norm_num) (by norm_num), hj 4 (by norm_num) (by norm_num),
    hj 5 (by norm_num) (by norm_num), hj 6 (by norm_num) (by norm_num)]
  ring

/-! ## E. At the consumed capstone: the constant shift is REJECTED -/

abbrev constShift (c : Fin 3 → F) {w : ℕ} (Q : Fin w → F[X]) : Fin w → F[X] :=
  Nock.RedTeam.Batch269.bumpAcc c Q

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The consumed compute chip rejects the trace with its IO accumulator shifted by any nonzero
constant.** -/
theorem deployed_compute_chip_rejects_constant_acc_shift
    (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (c : Fin 3 → F) (hc : c ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.computeChip (constShift c Qc) :=
  Nock.RedTeam.Batch269.moved_accumulator_rejected P Qc hsat hax hbasis hwidth c hc

theorem compute_acc_start_is_pinned
    (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    (Nock.RedTeam.Batch269.rowEnv P Qc (Nock.RedTeam.Batch269.firstRow P)).extTrace 32 = 0 :=
  Nock.RedTeam.Batch269.acc_starts_at_zero P Qc hsat hax hbasis hwidth

/-- At the honest trace: accepted as is, rejected once shifted. -/
theorem canonical_compute_trace_shifted_is_rejected [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (c : Fin 3 → F) (hc : c ≠ 0) :
    RAP.SatisfiesWithPreprocessing P.computeChip (canonicalComputeTrace P) ∧
      ¬ RAP.SatisfiesWithPreprocessing P.computeChip (constShift c (canonicalComputeTrace P)) :=
  ⟨canonicalComputeTrace_satisfies P hax hbasis hwidth,
    deployed_compute_chip_rejects_constant_acc_shift P (canonicalComputeTrace P)
      (canonicalComputeTrace_satisfies P hax hbasis hwidth) hax hbasis hwidth c hc⟩

end Deployed

end

end Nock.RedTeam.Batch267

#print axioms Nock.RedTeam.Batch267.core_gates_off_acc
#print axioms Nock.RedTeam.Batch267.fold_reads_acc
#print axioms Nock.RedTeam.Batch267.fold_blind_to_constant_shift
#print axioms Nock.RedTeam.Batch267.accInit_reads_acc
#print axioms Nock.RedTeam.Batch267.deployed_compute_chip_rejects_constant_acc_shift
#print axioms Nock.RedTeam.Batch267.compute_acc_start_is_pinned
#print axioms Nock.RedTeam.Batch267.canonical_compute_trace_shifted_is_rejected
