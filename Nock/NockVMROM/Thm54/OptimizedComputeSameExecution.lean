import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.NockVMROM.Thm54.SampledIOSameExecution
import Nock.NockVMROM.Thm54.ComputePaperPacking
import Nock.NockVMROM.Thm54.OptimizedComputeFormRDenoms

/-!
# Exact same-execution source realization for optimized compute

This module connects one sampled same-execution assignment to the non-IO source side of the
corrected `13/62` optimized compute compiler.  It is an implementation connective: the table
row, table auxiliary, walk row, next row, and challenges are all projections of the same
`SampledIOSameExecutionAssignment`.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeSameExecution

open Nock
open Nock.ComputeTable
open Nock.Reified
open Nock.Framework Reify
open OptimizedComputeCodec
open OptimizedComputeOverlay
open OptimizedComputeSampledTrace
open OptimizedComputeSubstitution
open OptimizedComputeGateBasis
open OptimizedComputeFinalTrace
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open OptimizedComputeFormRDenoms
open ComputePaperPacking (OneHotSelector paperPacking_iff_atomic paperPacking_iff_sources
  paperPackingCoreGates mem_nonIO_of_mem_core zZinv_mem_finalNonIO)

set_option maxRecDepth 20000

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- The exact table/walk/sampled-IO challenge namespace used by the corrected compute source
families.  In particular roles `7/8` are the sampled strategy's own `gamma/pole`, not independent
compiler witnesses. -/
def exactFinalChallenge (A : SampledIOSameExecutionAssignment R p) : ℕ → K
  | 0 => R.problem.cfg.challenges.computeInputs.α
  | 1 => R.problem.cfg.challenges.computeInputs.z
  | 2 => R.problem.cfg.challenges.computeInputs.a
  | 3 => R.problem.cfg.challenges.computeInputs.b
  | 4 => R.problem.cfg.challenges.computeInputs.c
  | 5 => R.problem.cfg.challenges.computeInputs.z⁻¹
  | 6 => R.computeWalkAlpha
  | 7 => A.sampled.coins.gamma
  | 8 => A.sampled.coins.pole
  -- 28th: the `𝕂` λ coin of the Form R certificate and record slots; the honest
  -- compiler draws the configuration's own `λ` (`cfg.challenges.lam`, `honestProductionTuple`).
  | 9 => R.problem.cfg.challenges.lam
  | 10 => R.walkGamma
  | _ => 0

/-- Verifier-parameterized production compute namespace.  Slots `0..8` retain the exact
table/walk/sampled-IO values.  Until W3 stage 2 slots `9` and `11` carried the fold coins;
those coordinates are deleted, so this is `exactFinalChallenge`. -/
def exactFinalChallengeWith
    (A : SampledIOSameExecutionAssignment R p)
    (_c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K) : ℕ → K :=
  exactFinalChallenge A


def withFinalComputeChallenges
    (_A : SampledIOSameExecutionAssignment R p)
    (env : CorrectedFinalTypedEnv F K)
    (_c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K) :
    CorrectedFinalTypedEnv F K :=
  env

/-- One exact corrected final extension row.  Roles `0..57` are the co-resident encoded row,
role `60` is `acc_after(i)` — the co-resident request accumulator after row `i` — role `61` is the
independently namespaced walk line, and role `62` is the walk-queue inverse
`(count − ln)⁻¹`.  The residual roles `58, 59`
are computed later by `correctedCanonicalFinalTrace`; they are not source inputs. -/
def exactFinalExtensionRow
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) : Fin 63 → K :=
  fun role =>
    if h58 : role.val < 58 then
      coreExtensionValue (encodedRowAt A i) ⟨role.val, h58⟩
    else if role.val = 61 then
      A.exact.computeWalk.ln ((i : ℕ) + 1)
    else if role.val = 60 then
      ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1)
    else if role.val = 62 then
      let c := A.exact.computeWalk.count ((i : ℕ) + 1)
      let l := A.exact.computeWalk.ln ((i : ℕ) + 1)
      if c = l then 0 else (c - l)⁻¹
    else
      0

/-- Successor-free view of one exact corrected final row.  This is the terminal decoder
environment: every current coordinate comes from row `i`, while the unused next-row fields are
fixed to zero.  Row-local source expressions cannot observe that choice. -/
def exactFinalCurrentEnv
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    CorrectedFinalTypedEnv F K where
  baseTrace := finalBaseCell A R.problem.cfg.compRows_pos i
  baseTraceNext := fun _ => 0
  extTrace := exactFinalExtensionRow A i
  extTraceNext := fun _ => 0
  chal := fun q => exactFinalChallenge A q
  extensionPublic := fun _ => 0
  scalarPublic := fun _ => 0
  certBase := exactFinalCertBase A i
  certExt := exactFinalCertExt A i (exactFinalChallenge A 9)
  expCol := ((OptimizedComputeFinalTrace.honestS R i : ℕ) : F)

/-- The canonical corrected mixed environment on one active nonterminal compute row and its exact
successor.  Base slots `11/12` are the fixed first/last masks; all other values come from the same
assignment `A`. -/
def exactFinalTransitionEnv
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    CorrectedFinalTypedEnv F K where
  baseTrace :=
    finalBaseCell A R.problem.cfg.compRows_pos i
  baseTraceNext :=
    finalBaseCell A R.problem.cfg.compRows_pos ⟨(i : ℕ) + 1, hi⟩
  extTrace := exactFinalExtensionRow A i
  extTraceNext := exactFinalExtensionRow A ⟨(i : ℕ) + 1, hi⟩
  chal := fun q => exactFinalChallenge A q
  extensionPublic := fun _ => 0
  scalarPublic := fun _ => 0
  certBase := exactFinalCertBase A i
  certExt := exactFinalCertExt A i (exactFinalChallenge A 9)
  certBaseNext := exactFinalCertBase A ⟨(i : ℕ) + 1, hi⟩
  certExtNext := exactFinalCertExt A ⟨(i : ℕ) + 1, hi⟩ (exactFinalChallenge A 9)
  expCol := ((OptimizedComputeFinalTrace.honestS R i : ℕ) : F)
  expColNext := ((OptimizedComputeFinalTrace.honestS R ((i : ℕ) + 1) : ℕ) : F)

/-- Parameterized successor-free exact environment for arbitrary verifier compiler challenges. -/
def exactFinalCurrentEnvWith
    (A : SampledIOSameExecutionAssignment R p)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (i : Fin R.problem.cfg.compRows) :
    CorrectedFinalTypedEnv F K :=
  withFinalComputeChallenges A (exactFinalCurrentEnv A i) c

/-- Parameterized adjacent-row exact environment for arbitrary verifier compiler challenges. -/
def exactFinalTransitionEnvWith
    (A : SampledIOSameExecutionAssignment R p)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    CorrectedFinalTypedEnv F K :=
  withFinalComputeChallenges A (exactFinalTransitionEnv A i hi) c

/-- Source expressions preceding the production compiler consume only semantic challenges
`0..8` and — since H1.W — the walk-node RLC coin at slot `10`; compiler slots `9`
and `11` are introduced by the enclosing folded gates. -/
def CompilerInputFree : Expr → Prop
  | .Var .challenge q => q ≠ 11
  | .Var _ _ | .Const _ => True
  | .Add x y | .Sub x y | .Mul x y => CompilerInputFree x ∧ CompilerInputFree y
  | .Neg x | .Pow x _ => CompilerInputFree x

def compilerInputFreeB : Expr → Bool
  | .Var .challenge q => decide (q ≠ 11)
  | .Var _ _ | .Const _ => true
  | .Add x y | .Sub x y | .Mul x y => compilerInputFreeB x && compilerInputFreeB y
  | .Neg x | .Pow x _ => compilerInputFreeB x

theorem compilerInputFreeB_iff (e : Expr) :
    compilerInputFreeB e ↔ CompilerInputFree e := by
  induction e with
  | Var kind q => cases kind <;> simp [compilerInputFreeB, CompilerInputFree]
  | Const c => simp [compilerInputFreeB, CompilerInputFree]
  | Add x y ihx ihy | Sub x y ihx ihy | Mul x y ihx ihy =>
      simp [compilerInputFreeB, CompilerInputFree, ihx, ihy]
  | Neg x ih | Pow x n ih => simpa [compilerInputFreeB, CompilerInputFree] using ih

theorem eval_withFinalComputeChallenges_of_free
    (A : SampledIOSameExecutionAssignment R p)
    (env : CorrectedFinalTypedEnv F K)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (e : Expr) (_hfree : CompilerInputFree e) :
    e.eval (withFinalComputeChallenges A env c).toSourceEnv =
      e.eval env.toSourceEnv :=
  rfl

theorem exactFinalTransitionEnv_base_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (j : Fin 11) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.trace j =
      algebraMap F K ((encodedRowAt A i).base (.inl j)) := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalTransitionEnv, finalBaseCell] <;> omega

theorem exactFinalTransitionEnv_extension_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (j : Fin 58) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.trace (13 + j) =
      coreExtensionValue (encodedRowAt A i) j := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalTransitionEnv,
    exactFinalExtensionRow] <;> omega

theorem exactFinalTransitionEnv_extension_next
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (j : Fin 58) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.traceNext (13 + j) =
      coreExtensionValue
        (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) j := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalTransitionEnv,
    exactFinalExtensionRow] <;> omega

@[simp] theorem exactFinalTransitionEnv_sampled_gamma
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.chal 7 =
      A.sampled.coins.gamma := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalTransitionEnv, exactFinalChallenge]

@[simp] theorem exactFinalTransitionEnv_sampled_pole
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.chal 8 =
      A.sampled.coins.pole := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalTransitionEnv, exactFinalChallenge]

set_option maxHeartbeats 8000000 in
private theorem exactFinalTransitionEnv_selectors_sampled
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (st : State) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.trace (Nock.Reified.opCol st) =
      if st = (R.problem.exec.computePubAt i).state then 1 else 0 := by
  cases st <;> cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [exactFinalTransitionEnv, finalBaseCell, encodedRowAt, sampledEncode,
      OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex,
      CorrectedFinalTypedEnv.toSourceEnv, Nock.Reified.opCol, hs]

private theorem exactFinalTransitionEnv_pubFP_sampled_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 12) (c : Fin 3) :
    (pubFP .traceCur r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (encodedRowAt A i).extension (.inl (r, c)) := by
  let j : Fin 58 := ⟨3 * (r : ℕ) + c, by omega⟩
  simp only [pubFP, ext0, Expr.eval]
  have hj := exactFinalTransitionEnv_extension_current A i hi j
  rw [show 13 + 3 * (r : ℕ) + c = 13 + (j : ℕ) by simp [j]; omega, hj]
  fin_cases r <;> fin_cases c <;> simp [j, coreExtensionValue]

private theorem exactFinalTransitionEnv_pubFP_sampled_next
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 12) (c : Fin 3) :
    (pubFP .traceNext r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩).extension (.inl (r, c)) := by
  let j : Fin 58 := ⟨3 * (r : ℕ) + c, by omega⟩
  simp only [pubFP, ext0, Expr.eval]
  have hj := exactFinalTransitionEnv_extension_next A i hi j
  rw [show 13 + 3 * (r : ℕ) + c = 13 + (j : ℕ) by simp [j]; omega, hj]
  fin_cases r <;> fin_cases c <;> simp [j, coreExtensionValue]

theorem exactFinalTransitionEnv_sampledActive_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (j : Fin 3) :
    (sampledActive .traceCur j).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      match j with
      | 0 => 1
      | 1 => secondRequestMask (R.problem.exec.computePubAt i).state
      | 2 => thirdRequestMask (R.problem.exec.computePubAt i).state := by
  have h0 := exactFinalTransitionEnv_selectors_sampled A i hi .s0
  have h1 := exactFinalTransitionEnv_selectors_sampled A i hi .s1
  have h2 := exactFinalTransitionEnv_selectors_sampled A i hi .s2
  have h3 := exactFinalTransitionEnv_selectors_sampled A i hi .s3
  have h4 := exactFinalTransitionEnv_selectors_sampled A i hi .s4
  have h5 := exactFinalTransitionEnv_selectors_sampled A i hi .s5
  have h6 := exactFinalTransitionEnv_selectors_sampled A i hi .s6
  have h7 := exactFinalTransitionEnv_selectors_sampled A i hi .s7
  have h8 := exactFinalTransitionEnv_selectors_sampled A i hi .s8
  have h9 := exactFinalTransitionEnv_selectors_sampled A i hi .s9
  fin_cases j <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [Nock.Reified.opCol, hs] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 <;>
    simp [sampledActive, Expr.eval, secondRequestMask, thirdRequestMask, hs,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem exactFinalTransitionEnv_sampledDenomWitness_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (j : Fin 3) :
    (sampledDenomWitness .traceCur j).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      match j with
      | 0 => (overlayAt A i).denom0
      | 1 => (overlayAt A i).denom1
      | 2 => (overlayAt A i).denom2 := by
  have h3 : ¬ 6 + (j : ℕ) < 3 := by omega
  have h5 : ¬ 6 + (j : ℕ) < 5 := by omega
  have heq : 6 + (j : ℕ) ≠ 5 := by omega
  simp only [sampledDenomWitness, overlayCoord, h3, h5, heq,
    if_false, Nat.add_sub_cancel_left]
  change (pubFP .traceCur 11 j).eval
    (exactFinalTransitionEnv A i hi).toSourceEnv = _
  have hp :
      (pubFP .traceCur 11 j).eval
          (exactFinalTransitionEnv A i hi).toSourceEnv =
        (encodedRowAt A i).extension (.inl ((11 : Fin 12), j)) := by
    simpa using exactFinalTransitionEnv_pubFP_sampled_current
      A i hi (11 : Fin 12) j
  rw [hp]
  fin_cases j <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [overlayAt, encodedRowAt, sampledEncode, sampledEncodeExtension,
      OptimizedComputeCodec.encodeExtension, sampledOverlayA, overlayDenoms,
      OptimizedComputeCodec.fpCoordinate,
      overlayRoleA, overlayRoleB, overlayANat, overlayBNat, hs]

theorem exactFinalTransitionEnv_sampledAcc_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (sampledIOSubst .traceCur 0).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      ComputeSampledIO.coResidentAccC A.compress10
        R.problem.cfg.challenges.lam R.problem.exec.computeRows i := by
  change (pubFP .traceCur (10 : Fin 12) (2 : Fin 3)).eval
    (exactFinalTransitionEnv A i hi).toSourceEnv = _
  rw [exactFinalTransitionEnv_pubFP_sampled_current]
  cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [encodedRowAt, sampledEncode, sampledEncodeExtension,
      OptimizedComputeCodec.encodeExtension, sampledOverlayA, overlayRoleA,
      overlayRoleB, overlayANat, overlayBNat, overlayAt, hs]

theorem exactFinalTransitionEnv_sampledAcc_next
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (sampledIOSubst .traceNext 0).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      ComputeSampledIO.coResidentAccC A.compress10
        R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1) := by
  change (pubFP .traceNext (10 : Fin 12) (2 : Fin 3)).eval
    (exactFinalTransitionEnv A i hi).toSourceEnv = _
  rw [exactFinalTransitionEnv_pubFP_sampled_next]
  cases hs : (R.problem.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).state <;>
    simp [encodedRowAt, sampledEncode, sampledEncodeExtension,
      OptimizedComputeCodec.encodeExtension, sampledOverlayA, overlayRoleA,
      overlayRoleB, overlayANat, overlayBNat, overlayAt, hs]

set_option maxHeartbeats 8000000 in
theorem exactFinalTransitionEnv_selectors
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (st : State) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.trace (Nock.Reified.opCol st) =
      if st = (R.problem.exec.computePubAt i).state then 1 else 0 := by
  cases st <;> cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [exactFinalTransitionEnv, finalBaseCell, encodedRowAt, sampledEncode,
      OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex,
      CorrectedFinalTypedEnv.toSourceEnv, Nock.Reified.opCol, hs]

@[simp] theorem exactFinalTransitionEnv_pubFP
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 12) (c : Fin 3) :
    (pubFP .traceCur r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (encodedRowAt A i).extension (.inl (r, c)) := by
  let j : Fin 58 := ⟨3 * (r : ℕ) + c, by omega⟩
  simp only [pubFP, ext0, Expr.eval]
  have hj := exactFinalTransitionEnv_extension_current A i hi j
  rw [show 13 + 3 * (r : ℕ) + c = 13 + (j : ℕ) by simp [j]; omega, hj]
  fin_cases r <;> fin_cases c <;> simp [j, coreExtensionValue]

@[simp] theorem exactFinalTransitionEnv_decFP
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 6) (c : Fin 3) :
    (decFP .traceCur r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (encodedRowAt A i).extension (.inr (.inl (r, c))) := by
  let j : Fin 58 := ⟨36 + 3 * (r : ℕ) + c, by omega⟩
  simp only [decFP, ext0, Expr.eval]
  have hj := exactFinalTransitionEnv_extension_current A i hi j
  rw [show 13 + 36 + 3 * (r : ℕ) + c = 13 + (j : ℕ) by simp [j]; omega, hj]
  fin_cases r <;> fin_cases c <;> simp [j, coreExtensionValue]

theorem exactFinalTransitionEnv_pubFPNat
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r c : ℕ) (hr : r < 12) (hc : c < 3) :
    (pubFP .traceCur r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (encodedRowAt A i).extension (.inl (⟨r, hr⟩, ⟨c, hc⟩)) := by
  simpa using exactFinalTransitionEnv_pubFP A i hi ⟨r, hr⟩ ⟨c, hc⟩

theorem exactFinalTransitionEnv_decFPNat
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r c : ℕ) (hr : r < 6) (hc : c < 3) :
    (decFP .traceCur r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (encodedRowAt A i).extension (.inr (.inl (⟨r, hr⟩, ⟨c, hc⟩))) := by
  simpa using exactFinalTransitionEnv_decFP A i hi ⟨r, hr⟩ ⟨c, hc⟩

theorem restoredPub_eval_of_oneHot
    (env : Env K) (active : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = active then 1 else 0)
    (r c : ℕ) :
    (restoredPub .traceCur r c).eval env =
      (sourcePubAt .traceCur active r c).eval env := by
  have h0 := hsel .s0
  have h1 := hsel .s1
  have h2 := hsel .s2
  have h3 := hsel .s3
  have h4 := hsel .s4
  have h5 := hsel .s5
  have h6 := hsel .s6
  have h7 := hsel .s7
  have h8 := hsel .s8
  have h9 := hsel .s9
  have hc := hsel .cons
  cases active <;>
    simp [Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hc <;>
    simp [restoredPub, Nock.Reified.allStates, Nock.Reified.opCol, Expr.eval,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem exactFinalTransitionEnv_semanticPub
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 12) (c : Fin 3) :
    (semanticPub .traceCur r c).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      (sampledRestoreExtension
        (encodedRowAt A i).base (encodedRowAt A i).extension) (.inl (r, c)) := by
  have hv := vcompAt_of_compute_obligations A h i
  have hrestore := sampledRestore_encode_of_vcomp (F := F)
    (ex := A.exact.computeTableAux i) (v := overlayAt A i) hv
  have hrestoreAt := congrFun hrestore (.inl (r, c))
  change _ = sampledRestoreExtension
    (OptimizedComputeCodec.encodeBase (R.problem.exec.computePubAt i).state)
    (sampledEncodeExtension (R.problem.exec.computePubAt i)
      (R.problem.exec.computeDecAt i) (A.exact.computeTableAux i) (overlayAt A i)) (.inl (r, c))
  rw [hrestore]
  simp only [semanticPub]
  split
  · rw [restoredPub_eval_of_oneHot _ _ (exactFinalTransitionEnv_selectors A i hi) r c]
    fin_cases r <;> fin_cases c <;>
      cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [sourcePubAt, restoredAField, restoredBField, restoredIOHostField,
        restoredDenomHostField, OptimizedComputeCodec.encodeExtension,
        OptimizedComputeCodec.pubFingerprint, OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate, overlayANat, overlayBNat,
        overlayRoleA, overlayRoleB,
        encodedRowAt, sampledEncode, sampledEncodeExtension,
        exactFinalTransitionEnv_pubFPNat, exactFinalTransitionEnv_decFPNat,
        Expr.eval, Vcomp, evalV, sfz1, sfz2, sfz3, hs] at hv hrestoreAt ⊢ <;>
      aesop
  · fin_cases r <;> fin_cases c <;>
      cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [OptimizedComputeCodec.encodeExtension, OptimizedComputeCodec.pubFingerprint,
        OptimizedComputeCodec.fpCoordinate, encodedRowAt, sampledEncode,
        sampledEncodeExtension, overlayRoleA, overlayRoleB,
        exactFinalTransitionEnv_pubFPNat, hs] at *

theorem exactFinalTransitionEnv_semanticPub_value
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 12) (c : Fin 3) :
    (semanticPub .traceCur r c).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      fpCoordinate (pubFingerprint (R.problem.exec.computePubAt i) r) c := by
  rw [exactFinalTransitionEnv_semanticPub A h i hi]
  have hv := vcompAt_of_compute_obligations A h i
  change sampledRestoreExtension
    (OptimizedComputeCodec.encodeBase (R.problem.exec.computePubAt i).state)
    (sampledEncodeExtension (R.problem.exec.computePubAt i)
      (R.problem.exec.computeDecAt i) (A.exact.computeTableAux i) (overlayAt A i)) (.inl (r, c)) = _
  rw [sampledRestore_encode_of_vcomp (F := F)
    (ex := A.exact.computeTableAux i) (v := overlayAt A i) hv]
  rfl

theorem exactFinalTransitionEnv_decFP_value
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 6) (c : Fin 3) :
    (decFP .traceCur r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      fpCoordinate (decFingerprint (R.problem.exec.computeDecAt i) r) c := by
  rw [exactFinalTransitionEnv_decFP]
  rfl

theorem exactFinalTransitionEnv_semanticPubNat_value
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r c : ℕ) (hr : r < 12) (hc : c < 3) :
    (semanticPub .traceCur r c).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      fpCoordinate (pubFingerprint (R.problem.exec.computePubAt i) ⟨r, hr⟩) ⟨c, hc⟩ := by
  simpa using exactFinalTransitionEnv_semanticPub_value A h i hi ⟨r, hr⟩ ⟨c, hc⟩

theorem exactFinalTransitionEnv_decFPNat_value
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r c : ℕ) (hr : r < 6) (hc : c < 3) :
    (decFP .traceCur r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      fpCoordinate (decFingerprint (R.problem.exec.computeDecAt i) ⟨r, hr⟩) ⟨c, hc⟩ := by
  simpa using exactFinalTransitionEnv_decFP_value A i hi ⟨r, hr⟩ ⟨c, hc⟩

/-
set_option maxHeartbeats 8000000 in
set_option maxHeartbeats 8000000 in
theorem exactFinalTransitionEnv_sampledDenom_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (j : Fin 3) :
    ((sampledDenom .traceCur j).subst finalSampledNamespace).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      A.compress10
        (NockVM.encRec
          (match j with
          | 0 => (R.problem.exec.computePubAt i).mr1
          | 1 => (R.problem.exec.computePubAt i).mr2
          | 2 => (R.problem.exec.computePubAt i).mr3)) := by
  fin_cases j <;>
    simp [sampledDenom, sampledRecordRLC, FiniteIO.compress, Walk.rlc,
      sampledPole, sampledGamma, finalSampledNamespace, finalSampledPole,
      finalSampledGamma, sampledChallenge, sampledChallengeBase,
      Expr.eval, Expr.eval_subst, Env.ofSubst,
      exactFinalTransitionEnv_sampled_gamma,
      exactFinalTransitionEnv_sampled_pole,
      computeTraceSubst,
      exactFinalTransitionEnv_semanticPubNat_value A h,
      NockVM.encRec, Fin.sum_univ_succ, List.range, List.range.loop]

theorem exact_finalSampled_denom_pins
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ j : Fin 3,
      ((sampledDenomPin .traceCur j).subst finalSampledNamespace).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  intro j
  rw [Expr.eval_subst]
  simp only [sampledDenomPin, Expr.eval]
  have hw :
      (sampledDenomWitness .traceCur j).eval
          (Env.ofSubst finalSampledNamespace
            (exactFinalTransitionEnv A i hi).toSourceEnv) =
        (sampledDenomWitness .traceCur j).eval
          (exactFinalTransitionEnv A i hi).toSourceEnv := by
    fin_cases j <;> rfl
  have hs :
      (sampledSafeDenom .traceCur j).eval
        (Env.ofSubst finalSampledNamespace
          (exactFinalTransitionEnv A i hi).toSourceEnv) =
      OptimizedComputeFiniteIOGates.SafeDenom
        ((sampledActive .traceCur j).eval
          (exactFinalTransitionEnv A i hi).toSourceEnv)
        (((sampledDenom .traceCur j).subst finalSampledNamespace).eval
          (exactFinalTransitionEnv A i hi).toSourceEnv) := by
    fin_cases j <;>
      simp [sampledSafeDenom, sampledActive,
        OptimizedComputeFiniteIOGates.SafeDenom,
        Expr.eval, Expr.eval_subst, Env.ofSubst, finalSampledNamespace]
  rw [sub_eq_zero, hw, exactFinalTransitionEnv_sampledDenomWitness_current, hs,
    exactFinalTransitionEnv_sampledActive_current,
    exactFinalTransitionEnv_sampledDenom_current A h]
  fin_cases j <;>
    simp [overlayAt, inactiveSafe, OptimizedComputeFiniteIOGates.SafeDenom,
      secondRequestMask, thirdRequestMask]

private theorem exact_active_request_nonzero
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    {v : Fin 9 → K}
    (hv : v ∈ ComputeSampledIO.rowRequests R.problem.cfg.challenges.lam
      (R.problem.exec.computeRowAt i)) :
    A.compress10 v ≠ 0 := by
  intro hzero
  have hrow :
      R.problem.exec.computeRowAt i ∈ R.problem.exec.computeRows := by
    rw [ExactExecution.computeRows_eq_ofFn_computeRowAt]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hmem := ComputeSampledIO.rowRequest_mem_sampled A hrow hv
  rw [A.requests_eq] at hmem
  exact A.compress10_ne_zero hmem hzero

theorem exact_finalSampled_folded_step
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3.subst
      finalSampledNamespace).eval
      (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  let env := (exactFinalTransitionEnv A i hi).toSourceEnv
  let row := R.problem.exec.computeRowAt i
  let a1 : K := secondRequestMask (R.problem.exec.computePubAt i).state
  let a2 : K := thirdRequestMask (R.problem.exec.computePubAt i).state
  let d0 := A.compress10
    (NockVM.encRec (R.problem.exec.computePubAt i).mr1)
  let d1 := A.compress10
    (NockVM.encRec (R.problem.exec.computePubAt i).mr2)
  let d2 := A.compress10
    (NockVM.encRec (R.problem.exec.computePubAt i).mr3)
  have ha1 : a1 = 0 ∨ a1 = 1 := by
    cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [a1, secondRequestMask, hs]
  have ha2 : a2 = 0 ∨ a2 = 1 := by
    cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [a2, thirdRequestMask, hs]
  have hd0 : d0 ≠ 0 :=
    exact_active_request_nonzero A i (by
      apply List.mem_map_of_mem
      simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt]
      cases (R.problem.exec.computeRowAt i).2.2.1.state <;> simp)
  have hd1 : a1 = 1 → d1 ≠ 0 := by
    intro ha
    apply exact_active_request_nonzero A i
    apply List.mem_map_of_mem
    simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt,
      secondRequestMask, a1] at ha ⊢
    cases hst : (R.problem.exec.computeRowAt i).2.2.1.state <;> simp [hst] at ha ⊢
  have hd2 : a2 = 1 → d2 ≠ 0 := by
    intro ha
    apply exact_active_request_nonzero A i
    apply List.mem_map_of_mem
    simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt,
      thirdRequestMask, a2] at ha ⊢
    cases hst : (R.problem.exec.computeRowAt i).2.2.1.state <;> simp [hst] at ha ⊢
  have hacc := ComputeSampledIO.coResidentAccC_succ A.compress10
    R.problem.cfg.challenges.lam R.problem.exec.computeRows hi
  rw [rowTermC_eq_fixed_slots] at hacc
  have hfold :
      OptimizedComputeFiniteIOGates.FoldedProgStep3
        (ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows i)
        (ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1))
        (overlayAt A i).denom0 (overlayAt A i).denom1 (overlayAt A i).denom2
        1 a1 a2 := by
    apply (OptimizedComputeFiniteIOGates.foldedProgStep3_safe_iff
      _ _ d0 d1 d2 1 a1 a2 (by simp) ha1 ha2
      (fun _ => hd0) hd1 hd2).2
    simpa [row, a1, a2, d0, d1, d2, overlayAt, inactiveSafe,
      ComputeSampledIO.requestInv, ExactExecution.computePubAt] using hacc
  have hpins := exact_finalSampled_denom_pins A h i hi
  have hden (j : Fin 3) :
      (sampledSafeDenom .traceCur j).eval
          (Env.ofSubst finalSampledNamespace env) =
        (sampledDenomWitness .traceCur j).eval env := by
    have hp := hpins j
    rw [Expr.eval_subst] at hp
    simp only [sampledDenomPin, Expr.eval, sub_eq_zero] at hp
    have hw :
        (sampledDenomWitness .traceCur j).eval
            (Env.ofSubst finalSampledNamespace env) =
          (sampledDenomWitness .traceCur j).eval env := by
      fin_cases j <;> rfl
    exact hp.symm.trans hw
  rw [Expr.eval_subst,
    OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3_eval]
  have hc := exactFinalTransitionEnv_sampledAcc_current A i hi
  have hn := exactFinalTransitionEnv_sampledAcc_next A i hi
  have ha0 := exactFinalTransitionEnv_sampledActive_current A i hi 0
  have ha1' := exactFinalTransitionEnv_sampledActive_current A i hi 1
  have ha2' := exactFinalTransitionEnv_sampledActive_current A i hi 2
  have hw0 := exactFinalTransitionEnv_sampledDenomWitness_current A i hi 0
  have hw1 := exactFinalTransitionEnv_sampledDenomWitness_current A i hi 1
  have hw2 := exactFinalTransitionEnv_sampledDenomWitness_current A i hi 2
  change OptimizedComputeFiniteIOGates.FoldedProgStep3
    ((sampledIOSubst .traceCur 0).eval (Env.ofSubst finalSampledNamespace env))
    ((sampledIOSubst .traceNext 0).eval (Env.ofSubst finalSampledNamespace env))
    _ _ _ _ _ _
  simp only [sampledIOSubst]
  rw [hden 0, hden 1, hden 2]
  change OptimizedComputeFiniteIOGates.FoldedProgStep3
    ((sampledIOSubst .traceCur 0).eval env)
    ((sampledIOSubst .traceNext 0).eval env)
    ((sampledDenomWitness .traceCur 0).eval env)
    ((sampledDenomWitness .traceCur 1).eval env)
    ((sampledDenomWitness .traceCur 2).eval env)
    ((sampledActive .traceCur 0).eval env)
    ((sampledActive .traceCur 1).eval env)
    ((sampledActive .traceCur 2).eval env)
  rw [hc, hn, hw0, hw1, hw2, ha0, ha1', ha2']
  exact hfold

theorem exact_finalSampledIOTransitionGates
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ g ∈ finalSampledIOTransitionGates,
      g.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  intro g hg
  simp only [finalSampledIOTransitionGates, List.mem_map] at hg
  obtain ⟨e, he, rfl⟩ := hg
  change e ∈ [sampledDenomPin .traceCur 0, sampledDenomPin .traceCur 1,
    sampledDenomPin .traceCur 2,
    OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact exact_finalSampled_denom_pins A h i hi 0
  · exact exact_finalSampled_denom_pins A h i hi 1
  · exact exact_finalSampled_denom_pins A h i hi 2
  · exact exact_finalSampled_folded_step A h i hi

-/
theorem exactFinalTransitionEnv_lnPrev
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (lnPrev .traceCur).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (R.problem.exec.computePubAt i).ln_prev := by
  change (exactFinalTransitionEnv A i hi).toSourceEnv.trace (13 + (54 : Fin 58)) = _
  rw [exactFinalTransitionEnv_extension_current A i hi]
  rfl

theorem exactFinalTransitionEnv_lnCur
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (lnCur .traceCur).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (R.problem.exec.computePubAt i).ln := by
  change (exactFinalTransitionEnv A i hi).toSourceEnv.trace (13 + (55 : Fin 58)) = _
  rw [exactFinalTransitionEnv_extension_current A i hi]
  rfl

theorem exactFinalTransitionEnv_consInv
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (consInv .traceCur).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (A.exact.computeTableAux i).consInv := by
  change (exactFinalTransitionEnv A i hi).toSourceEnv.trace (13 + (56 : Fin 58)) = _
  rw [exactFinalTransitionEnv_extension_current A i hi]
  rfl

theorem exactFinalTransitionEnv_invGen
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (invGen .traceCur).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (A.exact.computeTableAux i).invGen := by
  change (exactFinalTransitionEnv A i hi).toSourceEnv.trace (13 + (57 : Fin 58)) = _
  rw [exactFinalTransitionEnv_extension_current A i hi]
  rfl

theorem exactFinalTransitionEnv_chalAlpha
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.chal 0 =
      R.problem.cfg.challenges.computeInputs.α := by
  simp [exactFinalTransitionEnv, CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge]

theorem exactFinalTransitionEnv_chalZInv
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (exactFinalTransitionEnv A i hi).toSourceEnv.chal 5 =
      R.problem.cfg.challenges.computeInputs.z⁻¹ := by
  simp [exactFinalTransitionEnv, CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge]

set_option maxHeartbeats 8000000 in
theorem exactFinalTransitionEnv_table_selector
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (q : Fin 11) :
    (Env.ofSubst computeSubst (exactFinalTransitionEnv A i hi).toSourceEnv).trace q =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace q := by
  fin_cases q
  all_goals norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull]
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s0
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s1
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s2
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s3
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s4
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s5
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s6
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s7
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s8
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .s9
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalTransitionEnv_selectors A i hi .cons

theorem exactFinalTransitionEnv_table_pub
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 12) (c : Fin 3) :
    (Env.ofSubst computeSubst (exactFinalTransitionEnv A i hi).toSourceEnv).trace
        (11 + 3 * (r : ℕ) + c) =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace (11 + 3 * (r : ℕ) + c) := by
  rw [show (Env.ofSubst computeSubst
      (exactFinalTransitionEnv A i hi).toSourceEnv).trace (11 + 3 * (r : ℕ) + c) =
      (semanticPub .traceCur r c).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv by
    fin_cases r <;> fin_cases c <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst]]
  rw [exactFinalTransitionEnv_semanticPub_value A h i hi]
  fin_cases r <;> fin_cases c <;> rfl

theorem exactFinalTransitionEnv_table_dec
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (r : Fin 6) (c : Fin 3) :
    (Env.ofSubst computeSubst (exactFinalTransitionEnv A i hi).toSourceEnv).trace
        (47 + 3 * (r : ℕ) + c) =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace (47 + 3 * (r : ℕ) + c) := by
  rw [show (Env.ofSubst computeSubst
      (exactFinalTransitionEnv A i hi).toSourceEnv).trace (47 + 3 * (r : ℕ) + c) =
      (decFP .traceCur r c).eval (exactFinalTransitionEnv A i hi).toSourceEnv by
    fin_cases r <;> fin_cases c <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst]]
  rw [exactFinalTransitionEnv_decFP_value]
  fin_cases r <;> fin_cases c <;> rfl

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- All 94 current table columns decoded from the canonical mixed row are exactly the existing
`computeEnvFull` row for the same execution index and the same auxiliary witness. -/
theorem exactFinalTransitionEnv_table_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (j : ℕ) (hj : j < 94) :
    (Env.ofSubst computeSubst (exactFinalTransitionEnv A i hi).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i)
        (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  have hv := vcompAt_of_compute_obligations A h i
  have hrecords := OptimizedComputeCodec.records_eq_expected_of_vcomp hv
  have h0 := exactFinalTransitionEnv_selectors A i hi .s0
  have h1 := exactFinalTransitionEnv_selectors A i hi .s1
  have h2 := exactFinalTransitionEnv_selectors A i hi .s2
  have h3 := exactFinalTransitionEnv_selectors A i hi .s3
  have h4 := exactFinalTransitionEnv_selectors A i hi .s4
  have h5 := exactFinalTransitionEnv_selectors A i hi .s5
  have h6 := exactFinalTransitionEnv_selectors A i hi .s6
  have h7 := exactFinalTransitionEnv_selectors A i hi .s7
  have h8 := exactFinalTransitionEnv_selectors A i hi .s8
  have h9 := exactFinalTransitionEnv_selectors A i hi .s9
  by_cases h11 : j < 11
  · simpa using exactFinalTransitionEnv_table_selector A i hi ⟨j, h11⟩
  by_cases h47 : j < 47
  · let r : Fin 12 := ⟨(j - 11) / 3, by omega⟩
    let c : Fin 3 := ⟨(j - 11) % 3, Nat.mod_lt _ (by omega)⟩
    have hidx : j = 11 + 3 * (r : ℕ) + c := by
      have hdiv := Nat.mod_add_div (j - 11) 3
      dsimp [r, c]
      omega
    rw [hidx]
    exact exactFinalTransitionEnv_table_pub A h i hi r c
  by_cases h65 : j < 65
  · let r : Fin 6 := ⟨(j - 47) / 3, by omega⟩
    let c : Fin 3 := ⟨(j - 47) % 3, Nat.mod_lt _ (by omega)⟩
    have hidx : j = 47 + 3 * (r : ℕ) + c := by
      have hdiv := Nat.mod_add_div (j - 47) 3
      dsimp [r, c]
      omega
    rw [hidx]
    exact exactFinalTransitionEnv_table_dec A i hi r c
  by_cases h67 : j < 67
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
      simpa [exactFinalTransitionEnv_lnPrev, exactFinalTransitionEnv_lnCur]
  by_cases h75 : j < 75
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
      simp [Expr.eval, exactFinalTransitionEnv_pubFPNat,
        exactFinalTransitionEnv_semanticPubNat_value A h i hi,
        exactFinalTransitionEnv_decFPNat_value, exactFinalTransitionEnv_lnPrev,
        exactFinalTransitionEnv_chalAlpha, encodedRowAt, sampledEncode,
        sampledEncodeExtension, OptimizedComputeCodec.encodeExtension,
        OptimizedComputeCodec.pubFingerprint, OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
      cases hs : (R.problem.exec.computePubAt i).state <;>
      (try simp [hs, overlayRoleA, overlayRoleB] at hrecords ⊢) <;>
      aesop
  by_cases h83 : j < 83
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull,
        mr2Field, mr2Group] <;>
      simp [Expr.eval, exactFinalTransitionEnv_selectors,
        exactFinalTransitionEnv_pubFPNat,
        exactFinalTransitionEnv_semanticPubNat_value A h i hi,
        exactFinalTransitionEnv_decFPNat_value,
        exactFinalTransitionEnv_lnPrev, exactFinalTransitionEnv_chalAlpha,
        encodedRowAt, sampledEncode, sampledEncodeExtension,
        OptimizedComputeCodec.encodeExtension, OptimizedComputeCodec.pubFingerprint,
        OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
      cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [hs, overlayRoleA, overlayRoleB,
        OptimizedComputeCodec.expectedMr2, opSel, Nock.Reified.opCol]
        at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hrecords ⊢ <;>
      aesop
  by_cases h91 : j < 91
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull,
        mr3Field, mr3Group] <;>
      simp [Expr.eval, exactFinalTransitionEnv_selectors,
        exactFinalTransitionEnv_pubFPNat,
        exactFinalTransitionEnv_semanticPubNat_value A h i hi,
        exactFinalTransitionEnv_decFPNat_value,
        exactFinalTransitionEnv_lnPrev, exactFinalTransitionEnv_chalAlpha,
        encodedRowAt, sampledEncode, sampledEncodeExtension,
        OptimizedComputeCodec.encodeExtension, OptimizedComputeCodec.pubFingerprint,
        OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
      cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [hs, overlayRoleA, overlayRoleB,
        OptimizedComputeCodec.expectedMr3, opSel, Nock.Reified.opCol]
        at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hrecords ⊢ <;>
      aesop
  interval_cases j <;>
    norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
    simpa [Expr.eval, exactFinalTransitionEnv_consInv,
      exactFinalTransitionEnv_invGen, exactFinalTransitionEnv_chalZInv]

set_option maxHeartbeats 8000000 in
/-- 28th (Form R record slots): an *active* request slot's deployed denominator is the
compressed Form R encode of the request record (`encRecFormR _ cfg.challenges.lam`, the derived compute
IO).  Inactive slots are normalized by the inactive-safe denominator and carry no claim. -/
theorem exactFinalTransitionEnv_sampledDenom_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F)
    (j : Fin 3)
    (hact : slotActive R i j = 1) :
    ((sampledDenom .traceCur j).subst finalSampledNamespace).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      A.compress10
        (NockVM.encRecFormR
          (slotRecord R i j) R.problem.cfg.challenges.lam) := by
  have hcol (c : Fin 8) :
      (computeTraceSubst .traceCur
        (67 + 8 * (j : ℕ) + (c : ℕ))).eval
          (Env.ofSubst finalSampledNamespace
            (exactFinalTransitionEnv A i hi).toSourceEnv) =
        NockVM.encRecC (slotRecord R i j) 1 c.castSucc := by
    have ht := exactFinalTransitionEnv_table_current A h i hi
      (67 + 8 * (j : ℕ) + (c : ℕ)) (by omega)
    fin_cases j <;> fin_cases c <;> exact ht
  have hx : (sampledSlotE .traceCur (67 + 8 * (j : ℕ))).eval
      (Env.ofSubst finalSampledNamespace (exactFinalTransitionEnv A i hi).toSourceEnv) =
        (((OptimizedComputeFinalTrace.honestS R i + (j : ℕ) + 1 : ℕ)) : K) := by
    fin_cases j <;>
      simp [sampledSlotE, Expr.eval, Env.ofSubst, finalSampledNamespace,
        CorrectedFinalTypedEnv.toSourceEnv, exactFinalTransitionEnv] <;> ring
  rw [SampledIOSameExecutionAssignment.compress10,
    ← withExp_honestS_eq_extRec A i j hact]
  refine sampledDenom_eq_formR A i hsmall hwidth (exactFinalTransitionEnv A i hi) j
    R.problem.cfg.challenges.lam
    (fun s => exactFinalTransitionEnv_selectors A i hi s) hcol
    (exactFinalTransitionEnv_sampled_gamma A i hi) (exactFinalTransitionEnv_sampled_pole A i hi)
    rfl rfl rfl
    (by simpa using exactFinalTransitionEnv_extension_current A i hi ⟨41, by decide⟩)
    (by simpa using exactFinalTransitionEnv_extension_current A i hi ⟨44, by decide⟩) hact _ hx

theorem exact_finalSampled_denom_pins
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F) :
    ∀ j : Fin 3,
      ((sampledDenomPin .traceCur j).subst finalSampledNamespace).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  intro j
  rw [Expr.eval_subst]
  simp only [sampledDenomPin, Expr.eval]
  have hw :
      (sampledDenomWitness .traceCur j).eval
          (Env.ofSubst finalSampledNamespace
            (exactFinalTransitionEnv A i hi).toSourceEnv) =
        (sampledDenomWitness .traceCur j).eval
          (exactFinalTransitionEnv A i hi).toSourceEnv := by
    fin_cases j <;> rfl
  have hs :
      (sampledSafeDenom .traceCur j).eval
        (Env.ofSubst finalSampledNamespace
          (exactFinalTransitionEnv A i hi).toSourceEnv) =
      OptimizedComputeFiniteIOGates.SafeDenom
        ((sampledActive .traceCur j).eval
          (exactFinalTransitionEnv A i hi).toSourceEnv)
        (((sampledDenom .traceCur j).subst finalSampledNamespace).eval
          (exactFinalTransitionEnv A i hi).toSourceEnv) := by
    fin_cases j <;>
      simp [sampledSafeDenom, sampledActive,
        OptimizedComputeFiniteIOGates.SafeDenom,
        Expr.eval, Expr.eval_subst, Env.ofSubst, finalSampledNamespace]
  rw [sub_eq_zero, hw, exactFinalTransitionEnv_sampledDenomWitness_current, hs,
    exactFinalTransitionEnv_sampledActive_current]
  fin_cases j
  · have hd := exactFinalTransitionEnv_sampledDenom_current A h i hi hsmall hwidth 0 rfl
    simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero] at hd ⊢
    rw [hd]
    simp [overlayAt, slotRecord, OptimizedComputeFiniteIOGates.SafeDenom]
  · by_cases hm : secondRequestMask (K := K) (R.problem.exec.computePubAt i).state = 1
    · have hd := exactFinalTransitionEnv_sampledDenom_current A h i hi hsmall hwidth 1 hm
      simp only [Fin.mk_one, Fin.isValue, Fin.val_one] at hd ⊢
      rw [hd]
      simp [overlayAt, inactiveSafe, slotRecord, OptimizedComputeFiniteIOGates.SafeDenom, hm]
    · have hm0 : secondRequestMask (K := K) (R.problem.exec.computePubAt i).state = 0 := by
        cases hs : (R.problem.exec.computePubAt i).state <;>
          simp_all [secondRequestMask]
      simp [overlayAt, inactiveSafe, OptimizedComputeFiniteIOGates.SafeDenom, hm0]
  · by_cases hm : thirdRequestMask (K := K) (R.problem.exec.computePubAt i).state = 1
    · have hd := exactFinalTransitionEnv_sampledDenom_current A h i hi hsmall hwidth 2 hm
      simp only [Fin.reduceFinMk, Fin.isValue, Fin.val_two] at hd ⊢
      rw [hd]
      simp [overlayAt, inactiveSafe, slotRecord, OptimizedComputeFiniteIOGates.SafeDenom, hm]
    · have hm0 : thirdRequestMask (K := K) (R.problem.exec.computePubAt i).state = 0 := by
        cases hs : (R.problem.exec.computePubAt i).state <;>
          simp_all [thirdRequestMask]
      simp [overlayAt, inactiveSafe, OptimizedComputeFiniteIOGates.SafeDenom, hm0]

private theorem exact_active_request_nonzero
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    {v : Fin 9 → K}
    (hv : v ∈ ComputeSampledIO.rowRequests R.problem.cfg.challenges.lam
      (R.problem.exec.computeRowAt i)) :
    A.compress10 v ≠ 0 := by
  intro hzero
  have hrow :
      R.problem.exec.computeRowAt i ∈ R.problem.exec.computeRows := by
    rw [ExactExecution.computeRows_eq_ofFn_computeRowAt]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hmem := ComputeSampledIO.rowRequest_mem_sampled A hrow hv
  rw [A.requests_eq] at hmem
  exact A.compress10_ne_zero hmem hzero

theorem exact_finalSampled_folded_step
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3.subst
      finalSampledNamespace).eval
      (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  let env := (exactFinalTransitionEnv A i hi).toSourceEnv
  let row := R.problem.exec.computeRowAt i
  let a1 : K := secondRequestMask (R.problem.exec.computePubAt i).state
  let a2 : K := thirdRequestMask (R.problem.exec.computePubAt i).state
  let d0 := A.compress10
    (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr1 R.problem.cfg.challenges.lam)
  let d1 := A.compress10
    (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr2 R.problem.cfg.challenges.lam)
  let d2 := A.compress10
    (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr3 R.problem.cfg.challenges.lam)
  have ha1 : a1 = 0 ∨ a1 = 1 := by
    cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [a1, secondRequestMask, hs]
  have ha2 : a2 = 0 ∨ a2 = 1 := by
    cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [a2, thirdRequestMask, hs]
  have hd0 : d0 ≠ 0 :=
    exact_active_request_nonzero A i (by
      apply List.mem_map_of_mem
      simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt]
      cases (R.problem.exec.computeRowAt i).2.2.1.state <;> simp)
  have hd1 : a1 = 1 → d1 ≠ 0 := by
    intro ha
    apply exact_active_request_nonzero A i
    apply List.mem_map_of_mem
    simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt,
      secondRequestMask, a1] at ha ⊢
    cases hst : (R.problem.exec.computeRowAt i).2.2.1.state <;> simp [hst] at ha ⊢
  have hd2 : a2 = 1 → d2 ≠ 0 := by
    intro ha
    apply exact_active_request_nonzero A i
    apply List.mem_map_of_mem
    simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt,
      thirdRequestMask, a2] at ha ⊢
    cases hst : (R.problem.exec.computeRowAt i).2.2.1.state <;> simp [hst] at ha ⊢
  have hiRows : (i : ℕ) < R.problem.exec.computeRows.length := by
    simpa using i.isLt
  have hacc := ComputeSampledIO.coResidentAccC_succ A.compress10
    R.problem.cfg.challenges.lam R.problem.exec.computeRows hiRows
  rw [rowTermC_eq_fixed_slots] at hacc
  have hfoldSafe :
      OptimizedComputeFiniteIOGates.FoldedProgStep3
        (ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows i)
        (ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1))
        (OptimizedComputeFiniteIOGates.SafeDenom 1 d0)
        (OptimizedComputeFiniteIOGates.SafeDenom a1 d1)
        (OptimizedComputeFiniteIOGates.SafeDenom a2 d2)
        1 a1 a2 :=
    (OptimizedComputeFiniteIOGates.foldedProgStep3_safe_iff
      _ _ d0 d1 d2 1 a1 a2 (by simp) ha1 ha2
      (fun _ => hd0) hd1 hd2).2 (by
        simpa [row, a1, a2, d0, d1, d2,
          ComputeSampledIO.requestInv, ExactExecution.computePubAt,
          ExactExecution.computeRowAt, add_assoc] using hacc)
  have hfold :
      OptimizedComputeFiniteIOGates.FoldedProgStep3
        (ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows i)
        (ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1))
        (overlayAt A i).denom0 (overlayAt A i).denom1 (overlayAt A i).denom2
        1 a1 a2 := by
    simpa [a1, a2, d0, d1, d2, overlayAt, inactiveSafe,
      OptimizedComputeFiniteIOGates.SafeDenom] using hfoldSafe
  rw [Expr.eval_subst,
    OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3_eval]
  have hc := exactFinalTransitionEnv_sampledAcc_current A i hi
  have hn := exactFinalTransitionEnv_sampledAcc_next A i hi
  have ha0 := exactFinalTransitionEnv_sampledActive_current A i hi 0
  have ha1' := exactFinalTransitionEnv_sampledActive_current A i hi 1
  have ha2' := exactFinalTransitionEnv_sampledActive_current A i hi 2
  have hw0 := exactFinalTransitionEnv_sampledDenomWitness_current A i hi 0
  have hw1 := exactFinalTransitionEnv_sampledDenomWitness_current A i hi 1
  have hw2 := exactFinalTransitionEnv_sampledDenomWitness_current A i hi 2
  have hc' :
      (sampledIOSubst .traceCur 0).eval
          (Env.ofSubst finalSampledNamespace env) =
        ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows i := by
    change (sampledIOSubst .traceCur 0).eval env = _
    exact hc
  have hn' :
      (sampledIOSubst .traceNext 0).eval
          (Env.ofSubst finalSampledNamespace env) =
        ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1) := by
    change (sampledIOSubst .traceNext 0).eval env = _
    exact hn
  have hw0' :
      (sampledDenomWitness .traceCur 0).eval
          (Env.ofSubst finalSampledNamespace env) = (overlayAt A i).denom0 := by
    change (sampledDenomWitness .traceCur 0).eval env = _
    exact hw0
  have hw1' :
      (sampledDenomWitness .traceCur 1).eval
          (Env.ofSubst finalSampledNamespace env) = (overlayAt A i).denom1 := by
    change (sampledDenomWitness .traceCur 1).eval env = _
    exact hw1
  have hw2' :
      (sampledDenomWitness .traceCur 2).eval
          (Env.ofSubst finalSampledNamespace env) = (overlayAt A i).denom2 := by
    change (sampledDenomWitness .traceCur 2).eval env = _
    exact hw2
  have ha0' :
      (sampledActive .traceCur 0).eval
          (Env.ofSubst finalSampledNamespace env) = 1 := by
    change (sampledActive .traceCur 0).eval env = 1
    exact ha0
  have ha1'' :
      (sampledActive .traceCur 1).eval
          (Env.ofSubst finalSampledNamespace env) = a1 := by
    change (sampledActive .traceCur 1).eval env = a1
    simpa [a1] using ha1'
  have ha2'' :
      (sampledActive .traceCur 2).eval
          (Env.ofSubst finalSampledNamespace env) = a2 := by
    change (sampledActive .traceCur 2).eval env = a2
    simpa [a2] using ha2'
  rw [hc', hn']
  simp only [sampledIOSubst]
  rw [hw0', hw1', hw2', ha0', ha1'', ha2'']
  exact hfold

theorem exact_finalSampledIOTransitionGates
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F) :
    ∀ g ∈ finalSampledIOTransitionGates,
      g.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  intro g hg
  simp only [finalSampledIOTransitionGates, List.mem_map] at hg
  obtain ⟨e, he, rfl⟩ := hg
  change e ∈ [sampledDenomPin .traceCur 0, sampledDenomPin .traceCur 1,
    sampledDenomPin .traceCur 2,
    OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact exact_finalSampled_denom_pins A h i hi hsmall hwidth 0
  · exact exact_finalSampled_denom_pins A h i hi hsmall hwidth 1
  · exact exact_finalSampled_denom_pins A h i hi hsmall hwidth 2
  · exact exact_finalSampled_folded_step A h i hi

/-- Syntactic footprint of an ordinary compute-row expression.  It may read the 94 current
table columns and the five table challenges, but no next-row column. -/
def CurrentComputeExpr : Expr → Bool
  | .Var .traceCur j => decide (j < 94)
  | .Var .traceNext _ => false
  | .Var .challenge j => decide (j < 5)
  | .Var .publicVal _ => true
  | .Const _ => true
  | .Add x y | .Sub x y | .Mul x y => CurrentComputeExpr x && CurrentComputeExpr y
  | .Neg x | .Pow x _ => CurrentComputeExpr x

theorem CurrentComputeExpr.eval_eq {L : Type*} [Field L]
    {e : Expr} (he : CurrentComputeExpr e = true) {env env' : Env L}
    (htrace : ∀ j, j < 94 → env.trace j = env'.trace j)
    (hchal : ∀ j, j < 5 → env.chal j = env'.chal j)
    (hpub : ∀ j, env.pub j = env'.pub j) :
    e.eval env = e.eval env' := by
  induction e with
  | Var kind j =>
      cases kind with
      | traceCur =>
          simp only [CurrentComputeExpr] at he
          exact htrace j (of_decide_eq_true he)
      | traceNext =>
          simp only [CurrentComputeExpr] at he
          contradiction
      | challenge =>
          simp only [CurrentComputeExpr] at he
          exact hchal j (of_decide_eq_true he)
      | publicVal =>
          exact hpub j
  | Const => rfl
  | Add x y ihx ihy =>
      simp only [CurrentComputeExpr] at he
      simp only [Bool.and_eq_true] at he
      simp [Expr.eval, ihx he.1, ihy he.2]
  | Sub x y ihx ihy =>
      simp only [CurrentComputeExpr] at he
      simp only [Bool.and_eq_true] at he
      simp [Expr.eval, ihx he.1, ihy he.2]
  | Mul x y ihx ihy =>
      simp only [CurrentComputeExpr] at he
      simp only [Bool.and_eq_true] at he
      simp [Expr.eval, ihx he.1, ihy he.2]
  | Neg x ih =>
      simp only [CurrentComputeExpr] at he
      simp [Expr.eval, ih he]
  | Pow x n ih =>
      simp only [CurrentComputeExpr] at he
      simp [Expr.eval, ih he]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem computeAIR_current_footprint :
    ∀ c ∈ Nock.Reified.computeAIR.constraints, CurrentComputeExpr c.expr = true := by
  decide

/-- The exact table segment supplies every ordinary row-local compute AIR equation for the
canonical auxiliary witness. -/
theorem exact_computeAIR_row
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) :
    ∀ c ∈ Nock.Reified.computeAIR.constraints,
      c.expr.eval
        (computeEnvFull R.problem.cfg.challenges.computeInputs
          (opSel (R.problem.exec.computePubAt i).state)
          (R.problem.exec.computePubAt i)
          (R.problem.exec.computeDecAt i)
          (A.exact.computeTableAux i)) = 0 := by
  let rows := fun q : Fin R.problem.cfg.compRows =>
    computeEnvFull R.problem.cfg.challenges.computeInputs
      (opSel (R.problem.exec.computePubAt q).state)
      (R.problem.exec.computePubAt q)
      (R.problem.exec.computeDecAt q)
      (A.exact.computeTableAux q)
  have hrowRAP :=
    (computeRowSegment_iff R.problem.cfg A.exact.computeTableTrace).1 (h.1 .row)
  have hrows :
      ∀ q, ∀ c ∈ Nock.Reified.computeAIR.constraints, c.expr.eval (rows q) = 0 := by
    apply (satisfies_iff_perRow_env rows R.problem.cfg.compNodes
      R.problem.cfg.compNodes_injective R.problem.cfg.challenges.computeValuation
      R.problem.cfg.eDeg R.problem.cfg.orbit.h R.problem.cfg.orbit.ω
      R.problem.cfg.orbit.βcoset R.problem.cfg.orbit.βcoset_ne_zero
      R.problem.cfg.orbit_h_pos (fun _ => rfl) (fun _ => rfl)).1
    simpa [rows, PlusIOSameExecutionAssignment.computeTableTrace,
      exactCanonicalEncodeProg] using hrowRAP
  exact hrows i

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000
/-- Every row-local source constraint commutes to the canonical physical row of the same exact
assignment. -/
theorem exact_computeAIR_row_substituted
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ c ∈ Nock.Reified.computeAIR.constraints,
      (c.expr.subst computeSubst).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  intro c hc
  rw [eval_computeSubst]
  rw [CurrentComputeExpr.eval_eq (computeAIR_current_footprint c hc)
    (fun j hj => exactFinalTransitionEnv_table_current A h i hi j hj)
    (fun j hj => by
      interval_cases j <;>
        simp [Expr.eval, Env.ofSubst, computeSubst, exactFinalTransitionEnv,
          CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge, computeEnvFull])
    (fun j => by
      simp [Expr.eval, Env.ofSubst, computeSubst, exactFinalTransitionEnv,
        CorrectedFinalTypedEnv.toSourceEnv, computeEnvFull])]
  exact exact_computeAIR_row A h i c hc

/-- Evaluation identity for the paper-displayed four-way nonlinear fold. -/
theorem combinedSourceExpr_eval_computeEnv
    (inp : Inputs K) (op : State → K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    combinedSourceExpr.eval (computeEnvFull inp op pub dec ex) =
      combinedGate inp pub op ex.invGen -
        (op .s3 + op .s5 + op .s8 + op .cons) := by
  simp only [combinedSourceExpr, Expr.eval, Nock.Reified.eval_op3,
    Nock.Reified.eval_op5, Nock.Reified.eval_op8, Nock.Reified.eval_op10,
    Nock.Reified.eval_invGen, Nock.Reified.eval_chZ, Nock.Reified.eval_chA,
    Nock.Reified.eval_chB, Nock.Reified.eval_chC, Nock.Reified.eval_cSf1e,
    Nock.Reified.eval_cSf2e, Nock.Reified.eval_cE, Nock.Reified.eval_cS,
    FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf,
    ComputeTable.combinedGate, combinedSelectorExpr]
  ring

/-- Under an honest one-hot selector, the combined source is exactly the active nonlinear
equation and tautologically zero on every opcode not participating in the fold. -/
theorem combinedSourceExpr_opSel_iff
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) (st : State) :
    combinedSourceExpr.eval (computeEnvFull inp (opSel st) pub dec ex) = 0 ↔
      match st with
      | .s3 => ex.invGen * (inp.z - pub.sf1_e.size) + pub.e.leaf = 1
      | .s5 => ex.invGen * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
          + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
          + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)) = 1
      | .s8 => pub.sf2_e.size * pub.s.size * ex.invGen = 1
      | .cons => pub.sf1_e.size * pub.sf2_e.size * ex.invGen = 1
      | _ => True := by
  rw [combinedSourceExpr_eval_computeEnv, combinedGate_opSel]
  cases st <;> simp [opSel, sub_eq_zero]

/-- Concrete inactive-state regression: S1 contributes no nonlinear obligation. -/
theorem combinedSourceExpr_s1_regression
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    combinedSourceExpr.eval (computeEnvFull inp (opSel .s1) pub dec ex) = 0 :=
  (combinedSourceExpr_opSel_iff inp pub dec ex .s1).2 trivial

/-- Concrete active-state regressions for all four selector-activated nonlinear branches. -/
theorem combinedSourceExpr_active_regressions
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    (combinedSourceExpr.eval (computeEnvFull inp (opSel .s3) pub dec ex) = 0 ↔
      ex.invGen * (inp.z - pub.sf1_e.size) + pub.e.leaf = 1) ∧
    (combinedSourceExpr.eval (computeEnvFull inp (opSel .s5) pub dec ex) = 0 ↔
      ex.invGen * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
        + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
        + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)) = 1) ∧
    (combinedSourceExpr.eval (computeEnvFull inp (opSel .s8) pub dec ex) = 0 ↔
      pub.sf2_e.size * pub.s.size * ex.invGen = 1) ∧
    (combinedSourceExpr.eval (computeEnvFull inp (opSel .cons) pub dec ex) = 0 ↔
      pub.sf1_e.size * pub.sf2_e.size * ex.invGen = 1) := by
  exact ⟨combinedSourceExpr_opSel_iff inp pub dec ex .s3,
    combinedSourceExpr_opSel_iff inp pub dec ex .s5,
    combinedSourceExpr_opSel_iff inp pub dec ex .s8,
    combinedSourceExpr_opSel_iff inp pub dec ex .cons⟩

theorem combinedSourceExpr_current_footprint :
    CurrentComputeExpr combinedSourceExpr = true := by
  decide

/-- The production family list contains the selector-activated combined source. -/
theorem optimizedCombinedGate_mem_final_nonIO :
    optimizedCombinedGate ∈ finalNonIOSourceFamilies17.flatten := by
  simp [finalNonIOSourceFamilies17, nonIOSourceFamilies17With, optimizedCombinedGate]

/-- Updating one list entry preserves a pointwise source equation. -/
theorem all_mem_set_zero (env : Env K) (xs : List Expr) (n : ℕ) (y : Expr)
    (hxs : ∀ x ∈ xs, x.eval env = 0) (hy : y.eval env = 0) :
    ∀ x ∈ xs.set n y, x.eval env = 0 := by
  induction xs generalizing n with
  | nil => simp
  | cons hd tl ih =>
      cases n with
      | zero =>
          intro z hz
          simp only [List.set, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hy
          · exact hxs z (by simp [hz])
      | succ n =>
          intro z hz
          simp only [List.set, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hxs _ (by simp)
          · exact ih n (fun w hw => hxs w (by simp [hw])) z hz

/-- Exact row AIR satisfaction also supplies the two refolded leaf-booleanity replacements. -/
theorem exact_refoldedPerStateGates
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ e ∈ refoldedPerStateGates,
      e.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  let env := (exactFinalTransitionEnv A i hi).toSourceEnv
  have hair := exact_computeAIR_row_substituted A h i hi
  have hmap :
      ∀ e ∈ Nock.Reified.perStateGated.map (fun e => e.subst computeSubst),
        e.eval env = 0 := by
    intro e he
    obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp he
    apply hair ⟨.row, src⟩
    simp [Nock.Reified.computeAIR, hsrc]
  have hfix := fixed_overlay_leaf_booleanity_degrees
  have hop3mem :
      op3ELeafBool.subst computeSubst ∈
        Nock.Reified.perStateGated.map (fun e => e.subst computeSubst) := by
    apply List.mem_map.mpr
    refine ⟨op3ELeafBool, ?_, rfl⟩
    rw [← hfix.1]
    exact List.get_mem _ _
  have hop5mem :
      op5ELeafBool.subst computeSubst ∈
        Nock.Reified.perStateGated.map (fun e => e.subst computeSubst) := by
    apply List.mem_map.mpr
    refine ⟨op5ELeafBool, ?_, rfl⟩
    rw [← hfix.2.1]
    exact List.get_mem _ _
  have hop3 : op3ELeafBoolRefold.eval env = 0 := by
    rw [← op3ELeafBool_refold_eval_oneHot env
      (R.problem.exec.computePubAt i).state (exactFinalTransitionEnv_selectors A i hi)]
    exact hmap _ hop3mem
  have hop5 : op5ELeafBoolRefold.eval env = 0 := by
    rw [← op5ELeafBool_refold_eval_oneHot env
      (R.problem.exec.computePubAt i).state (exactFinalTransitionEnv_selectors A i hi)]
    exact hmap _ hop5mem
  rw [refoldedPerStateGates]
  exact all_mem_set_zero env _ 270 op5ELeafBoolRefold
    (all_mem_set_zero env _ 177 op3ELeafBoolRefold hmap hop3) hop5

theorem stateBlock_mem_refolded (st : State) (e : Expr) (he : e ∈ stateBlock st) :
    e ∈ refoldedPerStateGates := by
  cases st <;> simp only [stateBlock] at he
  · exact List.mem_of_mem_take he
  all_goals
    apply List.mem_of_mem_drop
    exact List.mem_of_mem_take he

/-- The selector-activated combined source follows from the active `evalR` equation of the exact
row and is zero on every inactive opcode. -/
theorem exact_optimizedCombinedGate
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    optimizedCombinedGate.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  rw [optimizedCombinedGate, eval_computeSubst]
  rw [CurrentComputeExpr.eval_eq combinedSourceExpr_current_footprint
    (fun j hj => exactFinalTransitionEnv_table_current A h i hi j hj)
    (fun j hj => by
      interval_cases j <;>
        simp [Expr.eval, Env.ofSubst, computeSubst, exactFinalTransitionEnv,
          CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge, computeEnvFull])
    (fun j => by
      simp [Expr.eval, Env.ofSubst, computeSubst, exactFinalTransitionEnv,
        CorrectedFinalTypedEnv.toSourceEnv, computeEnvFull])]
  rw [combinedSourceExpr_opSel_iff]
  have hair := exact_computeAIR_row A h i
  have hrap := (Nock.Reified.computeAIR_sound
    R.problem.cfg.challenges.computeInputs
    (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
    (A.exact.computeTableAux i)).1 hair |>.1
  obtain ⟨_, _, _, _, heval⟩ := hrap
  cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [Nock.ComputeTable.evalR, hs] at heval ⊢ <;>
    aesop

/-- The five current-row walk overlay coordinates: `count`/`acc` and, in slots `2..4`, the three
declared child state tags (H1.W Option A). -/
theorem exactFinalTransitionEnv_walkOverlay_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (c : Fin 5) :
    (overlayCoord .traceCur c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      match c with
      | 0 => A.exact.computeWalk.count ((i : ℕ) + 1)
      | 1 => A.exact.computeWalk.acc ((i : ℕ) + 1)
      | 2 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) 0
      | 3 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) 1
      | 4 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) 2 := by
  fin_cases c <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    norm_num [overlayCoord, Nock.Reified.allStates, Nock.Reified.opCol, Expr.eval,
      Fin.ext_iff,
      pubFP, ext0, exactFinalTransitionEnv_selectors, exactFinalTransitionEnv_pubFP,
      exactFinalTransitionEnv, CorrectedFinalTypedEnv.toSourceEnv,
      exactFinalExtensionRow, coreExtensionValue, encodedRowAt, sampledEncode,
      sampledEncodeExtension, sampledOverlayA, OptimizedComputeCodec.fpCoordinate,
      OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex, finalBaseCell,
      overlayRoleA, overlayRoleB, overlayANat, overlayBNat, overlayAt, hs]

/-- Next-row counterpart of `exactFinalTransitionEnv_walkOverlay_current`. -/
theorem exactFinalTransitionEnv_walkOverlay_next
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (c : Fin 5) :
    (overlayCoord .traceNext c).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      match c with
      | 0 => A.exact.computeWalk.count ((i : ℕ) + 2)
      | 1 => A.exact.computeWalk.acc ((i : ℕ) + 2)
      | 2 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 2) 0
      | 3 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 2) 1
      | 4 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 2) 2 := by
  fin_cases c <;>
    cases hs : (R.problem.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).state <;>
    norm_num [overlayCoord, Nock.Reified.allStates, Nock.Reified.opCol, Expr.eval,
      Fin.ext_iff, pubFP, ext0, exactFinalTransitionEnv,
      CorrectedFinalTypedEnv.toSourceEnv, exactFinalExtensionRow, coreExtensionValue,
      encodedRowAt, sampledEncode, sampledEncodeExtension, sampledOverlayA,
      OptimizedComputeCodec.fpCoordinate, OptimizedComputeCodec.encodeBase,
      OptimizedComputeCodec.stateIndex, finalBaseCell, overlayRoleA, overlayRoleB,
      overlayANat, overlayBNat, overlayAt, hs]

theorem exactFinalTransitionEnv_walkLine_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (finalWalkLine .traceCur).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      A.exact.computeWalk.ln ((i : ℕ) + 1) := by
  simp [finalWalkLine, finalWalkLineIndex, exactFinalTransitionEnv,
    finalWalkLineRole, ext0, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalExtensionRow, Expr.eval]

theorem exactFinalTransitionEnv_walkLine_next
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (finalWalkLine .traceNext).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      A.exact.computeWalk.ln ((i : ℕ) + 2) := by
  simp [finalWalkLine, finalWalkLineIndex, exactFinalTransitionEnv,
    finalWalkLineRole, ext0, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalExtensionRow, Expr.eval]

theorem exactFinalTransitionEnv_walkChallenge
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (walkChallenge 0).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      R.computeWalkAlpha := by
  simp [walkChallenge, walkChallengeBase, Expr.eval, exactFinalTransitionEnv,
    CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge]

/-! ## Successor-free current-row decoder

The terminal row has no successor.  These block lemmas decode only the current row; the zeroed
next-row fields of `exactFinalCurrentEnv` are therefore semantically irrelevant. -/

set_option maxHeartbeats 8000000 in
theorem exactFinalCurrentEnv_selectors
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (st : State) :
    (exactFinalCurrentEnv A i).toSourceEnv.trace (Nock.Reified.opCol st) =
      if st = (R.problem.exec.computePubAt i).state then 1 else 0 := by
  cases st <;> cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [exactFinalCurrentEnv, finalBaseCell, encodedRowAt, sampledEncode,
      OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex,
      CorrectedFinalTypedEnv.toSourceEnv, Nock.Reified.opCol, hs]

/-- Current-row extension coordinates decode without any successor row. -/
theorem exactFinalCurrentEnv_extension_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (j : Fin 58) :
    (exactFinalCurrentEnv A i).toSourceEnv.trace (13 + j) =
      coreExtensionValue (encodedRowAt A i) j := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv,
    exactFinalExtensionRow] <;> omega

@[simp] theorem exactFinalCurrentEnv_pubFP
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (r : Fin 12) (c : Fin 3) :
    (pubFP .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (encodedRowAt A i).extension (.inl (r, c)) := by
  let j : Fin 58 := ⟨3 * (r : ℕ) + c, by omega⟩
  simp only [pubFP, ext0, Expr.eval]
  have hj := exactFinalCurrentEnv_extension_current A i j
  rw [show 13 + 3 * (r : ℕ) + c = 13 + (j : ℕ) by simp [j]; omega, hj]
  fin_cases r <;> fin_cases c <;> simp [j, coreExtensionValue]

@[simp] theorem exactFinalCurrentEnv_decFP
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (r : Fin 6) (c : Fin 3) :
    (decFP .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (encodedRowAt A i).extension (.inr (.inl (r, c))) := by
  let j : Fin 58 := ⟨36 + 3 * (r : ℕ) + c, by omega⟩
  simp only [decFP, ext0, Expr.eval]
  have hj := exactFinalCurrentEnv_extension_current A i j
  rw [show 13 + 36 + 3 * (r : ℕ) + c = 13 + (j : ℕ) by simp [j]; omega, hj]
  fin_cases r <;> fin_cases c <;> simp [j, coreExtensionValue]

theorem exactFinalCurrentEnv_pubFPNat
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (r c : ℕ) (hr : r < 12) (hc : c < 3) :
    (pubFP .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (encodedRowAt A i).extension (.inl (⟨r, hr⟩, ⟨c, hc⟩)) := by
  simpa using exactFinalCurrentEnv_pubFP A i ⟨r, hr⟩ ⟨c, hc⟩

theorem exactFinalCurrentEnv_decFPNat
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (r c : ℕ) (hr : r < 6) (hc : c < 3) :
    (decFP .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (encodedRowAt A i).extension (.inr (.inl (⟨r, hr⟩, ⟨c, hc⟩))) := by
  simpa using exactFinalCurrentEnv_decFP A i ⟨r, hr⟩ ⟨c, hc⟩

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem exactFinalCurrentEnv_semanticPub
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (r : Fin 12) (c : Fin 3) :
    (semanticPub .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (sampledRestoreExtension
        (encodedRowAt A i).base (encodedRowAt A i).extension) (.inl (r, c)) := by
  have hv := vcompAt_of_compute_obligations A h i
  have hrestore := sampledRestore_encode_of_vcomp (F := F)
    (ex := A.exact.computeTableAux i) (v := overlayAt A i) hv
  have hrestoreAt := congrFun hrestore (.inl (r, c))
  change _ = sampledRestoreExtension
    (OptimizedComputeCodec.encodeBase (R.problem.exec.computePubAt i).state)
    (sampledEncodeExtension (R.problem.exec.computePubAt i)
      (R.problem.exec.computeDecAt i) (A.exact.computeTableAux i) (overlayAt A i)) (.inl (r, c))
  rw [hrestore]
  simp only [semanticPub]
  split
  · rw [restoredPub_eval_of_oneHot _ _ (exactFinalCurrentEnv_selectors A i) r c]
    fin_cases r <;> fin_cases c <;>
      cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [sourcePubAt, restoredAField, restoredBField, restoredIOHostField,
        restoredDenomHostField, OptimizedComputeCodec.encodeExtension,
        OptimizedComputeCodec.pubFingerprint, OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate, overlayANat, overlayBNat,
        overlayRoleA, overlayRoleB, encodedRowAt, sampledEncode, sampledEncodeExtension,
        exactFinalCurrentEnv_pubFPNat, exactFinalCurrentEnv_decFPNat,
        Expr.eval, Vcomp, evalV, sfz1, sfz2, sfz3, hs] at hv hrestoreAt ⊢ <;>
      aesop
  · fin_cases r <;> fin_cases c <;>
      cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [OptimizedComputeCodec.encodeExtension, OptimizedComputeCodec.pubFingerprint,
        OptimizedComputeCodec.fpCoordinate, encodedRowAt, sampledEncode,
        sampledEncodeExtension, overlayRoleA, overlayRoleB,
        exactFinalCurrentEnv_pubFPNat, hs] at *

theorem exactFinalCurrentEnv_semanticPub_value
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (r : Fin 12) (c : Fin 3) :
    (semanticPub .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      fpCoordinate (pubFingerprint (R.problem.exec.computePubAt i) r) c := by
  rw [exactFinalCurrentEnv_semanticPub A h i]
  have hv := vcompAt_of_compute_obligations A h i
  change sampledRestoreExtension
    (OptimizedComputeCodec.encodeBase (R.problem.exec.computePubAt i).state)
    (sampledEncodeExtension (R.problem.exec.computePubAt i)
      (R.problem.exec.computeDecAt i) (A.exact.computeTableAux i) (overlayAt A i)) (.inl (r, c)) = _
  rw [sampledRestore_encode_of_vcomp (F := F)
    (ex := A.exact.computeTableAux i) (v := overlayAt A i) hv]
  rfl

theorem exactFinalCurrentEnv_semanticPubNat_value
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (r c : ℕ) (hr : r < 12) (hc : c < 3) :
    (semanticPub .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      fpCoordinate (pubFingerprint (R.problem.exec.computePubAt i) ⟨r, hr⟩) ⟨c, hc⟩ := by
  simpa using exactFinalCurrentEnv_semanticPub_value A h i ⟨r, hr⟩ ⟨c, hc⟩

theorem exactFinalCurrentEnv_decFP_value
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (r : Fin 6) (c : Fin 3) :
    (decFP .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      fpCoordinate (decFingerprint (R.problem.exec.computeDecAt i) r) c := by
  rw [exactFinalCurrentEnv_decFP A i r c]
  rfl

theorem exactFinalCurrentEnv_decFPNat_value
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (r c : ℕ) (hr : r < 6) (hc : c < 3) :
    (decFP .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv =
      fpCoordinate (decFingerprint (R.problem.exec.computeDecAt i) ⟨r, hr⟩) ⟨c, hc⟩ := by
  simpa using exactFinalCurrentEnv_decFP_value A i ⟨r, hr⟩ ⟨c, hc⟩

/-! ## H1.W: the in-gate walk label on the honest rows

`ComputeWalkLabel.labelRLC` / `childSumCC` / `selectorCM` on the successor row of the transition
environment evaluate to the paper's values: `RLC^γ` of the successor's `LT_comp` label vector,
the one-hot `Σ_k α^k · RLC^γ` of its declared child payloads (hosted tag + `sf_k`), and
`α^{fanout}`.  The `WalkLabelObligations` conjunct then identifies these with the walk
certificate's `curCol` / `walkCC` / `walkCM`. -/

/-- In a one-hot row, the restored source of every public coordinate is `semanticPub`. -/
theorem sourcePubAt_eval_eq_semanticPub (env : Env K) (active : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = active then 1 else 0)
    (r c : ℕ) (hr12 : r < 12) (hc3 : c < 3) :
    (sourcePubAt .traceCur active r c).eval env = (semanticPub .traceCur r c).eval env := by
  by_cases hr : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 6 ∨ r = 7 ∨ r = 9 ∨ r = 10 ∨ r = 11
  · rw [semanticPub, if_pos hr, restoredPub_eval_of_oneHot env active hsel]
  · rw [semanticPub, if_neg hr]
    have h1 : ¬ (r = 10 ∧ c = 2) := by omega
    have h2 : r ≠ 11 := by omega
    have h3 : r ≠ overlayANat active := by
      cases active <;> simp only [overlayANat] <;> omega
    have h4 : ¬ (r = overlayBNat active ∧ c < 2) := by
      cases active <;> simp only [overlayBNat] <;> omega
    rw [sourcePubAt, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

theorem exactFinalCurrentEnv_sourcePubAtR
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (r c : ℕ) (hr : r < 12) (hc : c < 3) :
    (ComputeWalkLabel.sourcePubAtR ComputeWalkLabel.curReader
        (R.problem.exec.computePubAt i).state r c).eval
        (exactFinalCurrentEnv A i).toSourceEnv =
      fpCoordinate (pubFingerprint (R.problem.exec.computePubAt i) ⟨r, hr⟩) ⟨c, hc⟩ := by
  rw [ComputeWalkLabel.sourcePubAtR_cur,
    sourcePubAt_eval_eq_semanticPub _ _ (exactFinalCurrentEnv_selectors A i) r c hr hc]
  exact exactFinalCurrentEnv_semanticPubNat_value A h i r c hr hc

set_option maxHeartbeats 4000000 in
/-- The hosted child state tags of the current row are the tree's (`overlayAt`). -/
theorem exactFinalCurrentEnv_childTagHost
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : Fin 3) :
    (ComputeWalkLabel.childTagHost ComputeWalkLabel.curReader
        (R.problem.exec.computePubAt i).state j).eval
        (exactFinalCurrentEnv A i).toSourceEnv =
      ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) j := by
  fin_cases j <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    norm_num [ComputeWalkLabel.childTagHost, ComputeWalkLabel.pubFPR,
      ComputeWalkLabel.curReader, Expr.eval, ext0, Fin.ext_iff, exactFinalCurrentEnv,
      CorrectedFinalTypedEnv.toSourceEnv, exactFinalExtensionRow, coreExtensionValue,
      encodedRowAt, sampledEncode, sampledEncodeExtension, sampledOverlayA,
      OptimizedComputeCodec.fpCoordinate, overlayRoleA, overlayRoleB, overlayANat,
      overlayBNat, overlayAt, hs]

/-- The successor row of the transition environment, read as a current row, is the successor's
current-row environment on every trace column. -/
theorem shiftNext_transitionEnv_trace
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (ComputeWalkLabel.shiftNext (exactFinalTransitionEnv A i hi).toSourceEnv).trace =
      (exactFinalCurrentEnv A ⟨(i : ℕ) + 1, hi⟩).toSourceEnv.trace := by
  funext j
  simp [ComputeWalkLabel.shiftNext, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalTransitionEnv, exactFinalCurrentEnv]

theorem shiftNext_transitionEnv_chal
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) (q : ℕ) :
    (ComputeWalkLabel.shiftNext (exactFinalTransitionEnv A i hi).toSourceEnv).chal q =
      (exactFinalTransitionEnv A i hi).toSourceEnv.chal q := rfl

theorem exactFinalTransitionEnv_walkGamma
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ComputeWalkLabel.walkGammaChallenge.eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      R.walkGamma := by
  simp [ComputeWalkLabel.walkGammaChallenge, ComputeWalkLabel.walkGammaChallengeIndex,
    Expr.eval, exactFinalTransitionEnv, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalChallenge]

theorem exactFinalTransitionEnv_labelRLC_next
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (ComputeWalkLabel.labelRLC ComputeWalkLabel.nextReader).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      Walk.rlc R.walkGamma
        (ComputeTable.labelVecOfPub (R.problem.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩)) := by
  rw [ComputeWalkLabel.labelRLC_next_eval]
  have htr := shiftNext_transitionEnv_trace A i hi
  apply ComputeWalkLabel.labelRLC_eval
  · intro st
    show (ComputeWalkLabel.shiftNext _).trace (Nock.Reified.opCol st) = _
    rw [htr]
    exact exactFinalCurrentEnv_selectors A _ st
  · intro r c hr hc
    rw [ComputeWalkLabel.sourcePubAtR_cur_eval_congr (fun j _ => congrFun htr j) _ r c hr hc]
    exact exactFinalCurrentEnv_sourcePubAtR A h _ r c hr hc
  · show (ComputeWalkLabel.shiftNext _).chal 10 = _
    rw [shiftNext_transitionEnv_chal]
    exact exactFinalTransitionEnv_walkGamma A i hi

theorem exactFinalTransitionEnv_childSumCC_next
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (ComputeWalkLabel.childSumCC ComputeWalkLabel.nextReader).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (R.problem.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).state),
        R.computeWalkAlpha ^ l *
          Walk.rlc R.walkGamma
            (ComputeWalkLabel.childVecN (R.problem.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩)
              (fun j => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1 + 1) j)
              (l - 1)) := by
  rw [ComputeWalkLabel.childSumCC_next_eval]
  have htr := shiftNext_transitionEnv_trace A i hi
  apply ComputeWalkLabel.childSumCC_eval
  · intro st
    show (ComputeWalkLabel.shiftNext _).trace (Nock.Reified.opCol st) = _
    rw [htr]
    exact exactFinalCurrentEnv_selectors A _ st
  · intro r c hr hc
    rw [ComputeWalkLabel.sourcePubAtR_cur_eval_congr (fun j _ => congrFun htr j) _ r c hr hc]
    exact exactFinalCurrentEnv_sourcePubAtR A h _ r c hr hc
  · show (ComputeWalkLabel.shiftNext _).chal (walkChallengeBase + 0) = _
    rw [shiftNext_transitionEnv_chal]
    simpa [walkChallenge, walkChallengeBase, Expr.eval] using
      exactFinalTransitionEnv_walkChallenge A i hi
  · show (ComputeWalkLabel.shiftNext _).chal 10 = _
    rw [shiftNext_transitionEnv_chal]
    exact exactFinalTransitionEnv_walkGamma A i hi
  · intro j
    rw [ComputeWalkLabel.childTagHost_cur_eval_congr (fun j _ => congrFun htr j)]
    exact exactFinalCurrentEnv_childTagHost A ⟨(i : ℕ) + 1, hi⟩ j

theorem exactFinalTransitionEnv_selectorCM_next
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (ComputeWalkLabel.selectorCM ComputeWalkLabel.nextReader).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv =
      R.computeWalkAlpha ^ fanoutComp (R.problem.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).state := by
  rw [ComputeWalkLabel.selectorCM_next_eval]
  have htr := shiftNext_transitionEnv_trace A i hi
  apply ComputeWalkLabel.selectorCM_eval
  · intro st
    show (ComputeWalkLabel.shiftNext _).trace (Nock.Reified.opCol st) = _
    rw [htr]
    exact exactFinalCurrentEnv_selectors A _ st
  · show (ComputeWalkLabel.shiftNext _).chal (walkChallengeBase + 0) = _
    rw [shiftNext_transitionEnv_chal]
    simpa [walkChallenge, walkChallengeBase, Expr.eval] using
      exactFinalTransitionEnv_walkChallenge A i hi

/-! ### The walk certificate's columns at the label (`WalkLabelObligations`) -/

/-- The `i`-th authoritative BFS node (0-indexed) carries the `i`-th canonical row. -/
theorem computeWalkRows_getElem?_row (i : Fin R.problem.cfg.compRows) :
    ∃ t, R.computeWalkRows[(i : ℕ)]? = some t ∧ t.label = R.problem.exec.computeRowAt i := by
  have hlen : R.computeWalkRows.length = R.problem.cfg.compRows := by
    have := R.problem.exec.computeRows_length
    simpa [ExactExecution.computeRows, PlusIOSegmentedFamily.computeWalkRows,
      List.length_map] using this
  have hi : (i : ℕ) < R.computeWalkRows.length := by rw [hlen]; exact i.isLt
  refine ⟨R.computeWalkRows[(i : ℕ)], List.getElem?_eq_getElem hi, ?_⟩
  show _ = R.problem.exec.computeRows.get (Fin.cast R.problem.exec.computeRows_length.symm i)
  simp [ExactExecution.computeRows, PlusIOSegmentedFamily.computeWalkRows, List.getElem_map]
  rfl

theorem curCol_eq_rlc_label
    (hEnc : ∀ t, R.computeNodeVal t =
      Walk.rlc R.walkGamma (ComputeTable.labelVecOfPub t.label.2.2.1))
    (i : Fin R.problem.cfg.compRows) :
    Walk.curCol R.computeNodeVal R.computeWalkRows ((i : ℕ) + 1) =
      Walk.rlc R.walkGamma (ComputeTable.labelVecOfPub (R.problem.exec.computePubAt i)) := by
  obtain ⟨t, ht, hl⟩ := computeWalkRows_getElem?_row (R := R) i
  simp only [Walk.curCol, Nat.add_sub_cancel, ht, Option.map_some, Option.getD_some, hEnc, hl]
  rfl

theorem foCol_eq_fanout
    (htopo : ∀ t ∈ R.computeWalkRows,
      t.label.1 = t.label.2.2.1.state ∧
        fanoutComp t.label.1 = t.children.length ∧
        childLinkComp t.label (fun j => t.childLabel j))
    (i : Fin R.problem.cfg.compRows) :
    Walk.foCol R.computeWalkRows ((i : ℕ) + 1) =
      fanoutComp (R.problem.exec.computePubAt i).state := by
  obtain ⟨t, ht, hl⟩ := computeWalkRows_getElem?_row (R := R) i
  obtain ⟨hst, hfan, -⟩ := htopo t (List.mem_of_getElem? ht)
  simp only [Walk.foCol, Nat.add_sub_cancel, ht, Option.map_some, Option.getD_some]
  rw [← hfan, hst, hl]
  rfl

theorem chldCol_eq_childVec
    (hEnc : ∀ t, R.computeNodeVal t =
      Walk.rlc R.walkGamma (ComputeTable.labelVecOfPub t.label.2.2.1))
    (htopo : ∀ t ∈ R.computeWalkRows,
      t.label.1 = t.label.2.2.1.state ∧
        fanoutComp t.label.1 = t.children.length ∧
        childLinkComp t.label (fun j => t.childLabel j))
    (i : Fin R.problem.cfg.compRows) (l : ℕ) (hl1 : 1 ≤ l)
    (hl : l ≤ fanoutComp (R.problem.exec.computePubAt i).state) :
    Walk.chldCol R.computeNodeVal R.computeWalkRows ((i : ℕ) + 1) l =
      Walk.rlc R.walkGamma
        (ComputeWalkLabel.childVecN (R.problem.exec.computePubAt i)
          (fun j => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) j) (l - 1)) := by
  obtain ⟨t, ht, hl⟩ := computeWalkRows_getElem?_row (R := R) i
  obtain ⟨hst, hfan, hlink⟩ := htopo t (List.mem_of_getElem? ht)
  have hpub : R.problem.exec.computePubAt i = t.label.2.2.1 := by
    show (R.problem.exec.computeRowAt i).2.2.1 = _
    rw [hl]
  have hfo : fanoutComp (R.problem.exec.computePubAt i).state = t.children.length := by
    rw [hpub, ← hst, hfan]
  have hlt : l - 1 < t.children.length := by omega
  have hle3 : l - 1 < 3 := by
    have := ComputeWalkLabel.fanoutComp_le_three (R.problem.exec.computePubAt i).state
    omega
  obtain ⟨c, hc⟩ : ∃ c, t.children[l - 1]? = some c :=
    ⟨t.children[l - 1], List.getElem?_eq_getElem hlt⟩
  have hlinkj' : (c.label.2.2.1.s, c.label.2.2.1.f, c.label.2.2.1.e) =
      sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩ := by
    have hlinkj := hlink ⟨l - 1, hle3⟩ (by
      show l - 1 < fanoutComp t.label.1
      rw [hst, ← hpub]; omega)
    simp only [Walk.NTree.childLabel, Walk.NTree.childOpt, hc, Option.map_some] at hlinkj
    exact Option.some.inj hlinkj
  have hcs : c.label.2.2.1.s = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).1 :=
    congrArg Prod.fst hlinkj'
  have hcf : c.label.2.2.1.f = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).2.1 :=
    congrArg (fun x => x.2.1) hlinkj'
  have hce : c.label.2.2.1.e = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).2.2 :=
    congrArg (fun x => x.2.2) hlinkj'
  have htag : ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) (l - 1) =
      stateTagField c.label.2.2.1.state := by
    simp [ComputeTable.childStateTagCol, ht, hc]
  simp only [Walk.chldCol, Nat.add_sub_cancel, ht, Option.bind_some, hc, Option.map_some,
    Option.getD_some, hEnc]
  congr 1
  rw [hpub]
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, (j : ℕ) = l - 1 := ⟨⟨l - 1, hle3⟩, rfl⟩
  rw [← hj, ComputeWalkLabel.childVecN_fin]
  funext k
  have hj' : (⟨l - 1, hle3⟩ : Fin 3) = j := Fin.ext hj.symm
  rw [hj'] at hcs hcf hce
  rw [← hj] at htag
  fin_cases k <;>
    simp [ComputeTable.labelVecOfPub, ComputeWalkLabel.childVec, htag, hcs, hcf, hce]

theorem walkCC_eq_childSum
    (hEnc : ∀ t, R.computeNodeVal t =
      Walk.rlc R.walkGamma (ComputeTable.labelVecOfPub t.label.2.2.1))
    (htopo : ∀ t ∈ R.computeWalkRows,
      t.label.1 = t.label.2.2.1.state ∧
        fanoutComp t.label.1 = t.children.length ∧
        childLinkComp t.label (fun j => t.childLabel j))
    (i : Fin R.problem.cfg.compRows) :
    Nock.Reified.Trans.walkCC (Walk.chldCol R.computeNodeVal R.computeWalkRows)
        (Walk.foCol R.computeWalkRows) R.computeWalkAlpha ((i : ℕ) + 1) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (R.problem.exec.computePubAt i).state),
        R.computeWalkAlpha ^ l *
          Walk.rlc R.walkGamma
            (ComputeWalkLabel.childVecN (R.problem.exec.computePubAt i)
              (fun j => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) j)
              (l - 1)) := by
  rw [Nock.Reified.Trans.walkCC, foCol_eq_fanout htopo i]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_Icc] at hl
  rw [chldCol_eq_childVec hEnc htopo i l hl.1 hl.2]

theorem walkCM_eq_pow
    (htopo : ∀ t ∈ R.computeWalkRows,
      t.label.1 = t.label.2.2.1.state ∧
        fanoutComp t.label.1 = t.children.length ∧
        childLinkComp t.label (fun j => t.childLabel j))
    (i : Fin R.problem.cfg.compRows) :
    Nock.Reified.Trans.walkCM (Walk.foCol R.computeWalkRows) R.computeWalkAlpha ((i : ℕ) + 1) =
      R.computeWalkAlpha ^ fanoutComp (R.problem.exec.computePubAt i).state := by
  rw [Nock.Reified.Trans.walkCM, foCol_eq_fanout htopo i]

/-- The exact walk certificate discharges all three production walk-transition sources at the
same compute row and successor. -/
theorem exact_finalWalk_transition_sources
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv = 0 ∧
      (Trans.walkCountStep.subst ComputeWalkLabel.finalWalkSubstInGate).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv = 0 ∧
      (Trans.walkAccStep.subst ComputeWalkLabel.finalWalkSubstInGate).eval
        (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  have hw := h.2.1.1
  have hlabel := h.2.2.2
  have hstep := (Nock.Reified.Trans.reified_walk_sound).1 hw |>.2.2.2.2
    ((i : ℕ) + 1) (by omega) (by omega)
  have hc0 := exactFinalTransitionEnv_walkOverlay_current A i hi (0 : Fin 5)
  have hc1 := exactFinalTransitionEnv_walkOverlay_current A i hi (1 : Fin 5)
  have hn0 := exactFinalTransitionEnv_walkOverlay_next A i hi (0 : Fin 5)
  have hn1 := exactFinalTransitionEnv_walkOverlay_next A i hi (1 : Fin 5)
  have hchal := exactFinalTransitionEnv_walkChallenge A i hi
  have hcur := exactFinalTransitionEnv_labelRLC_next A h i hi
  have hcc := exactFinalTransitionEnv_childSumCC_next A h i hi
  have hcm := exactFinalTransitionEnv_selectorCM_next A i hi
  have hcurW := curCol_eq_rlc_label hlabel.1 ⟨(i : ℕ) + 1, hi⟩
  have hccW := walkCC_eq_childSum hlabel.1 hlabel.2 ⟨(i : ℕ) + 1, hi⟩
  have hcmW := walkCM_eq_pow hlabel.2 ⟨(i : ℕ) + 1, hi⟩
  norm_num at hc0 hc1 hn0 hn1
  simp only [Expr.eval_subst, Trans.walkLnStep, Trans.walkCountStep, Trans.walkAccStep,
    Expr.eval, Env.ofSubst, Trans.tn, tc, chl, ComputeWalkLabel.finalWalkSubstInGate]
  rw [exactFinalTransitionEnv_walkLine_current,
    exactFinalTransitionEnv_walkLine_next, hchal,
    hc0, hc1, hn0, hn1, hcur, hcc, hcm, ← hcurW, ← hccW, ← hcmW]
  simpa [Trans.walkStep, Trans.walkRowEnv, Trans.twoRow, Trans.walkLnStep,
    Trans.walkCountStep, Trans.walkAccStep, Trans.tn, tc, chl, Expr.eval,
    Nat.add_assoc] using hstep

/-- The next physical row exposes the successor's `ln_prev` source column. -/
theorem exactFinalTransitionEnv_lnPrev_next
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (lnPrev .traceNext).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
      (R.problem.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev := by
  change (exactFinalTransitionEnv A i hi).toSourceEnv.traceNext (13 + (54 : Fin 58)) = _
  simp [exactFinalTransitionEnv, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalExtensionRow, coreExtensionValue, encodedRowAt, sampledEncode,
    sampledEncodeExtension, OptimizedComputeCodec.encodeExtension]

/-- Exact compute line-nonce chaining at the same adjacent row pair. -/
theorem exact_lnChain_source
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (Trans.lnChainExpr.subst computeSubst).eval
      (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  have hchain :=
    (computeTransitionSegment_iff R.problem.cfg R.problem.exec.computePubAt
      R.problem.exec.computeDecAt A.exact.computeTableAux).1 (h.1 .transition) i hi
  rw [Expr.eval_subst]
  simp [Trans.lnChainExpr, Expr.eval, Env.ofSubst, Trans.tn, tc,
    computeSubst, computeTraceSubst,
    exactFinalTransitionEnv_lnCur, exactFinalTransitionEnv_lnPrev_next, hchain]

/-- Main non-IO semantic encoder bridge: one exact same-execution assignment discharges every
source in all seventeen production families at the same physical row/successor environment. -/
theorem exact_finalNonIOSourceFamilies17
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ e ∈ finalNonIOSourceFamilies17.flatten,
      e.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  let env := (exactFinalTransitionEnv A i hi).toSourceEnv
  have hair := exact_computeAIR_row_substituted A h i hi
  have hrefold := exact_refoldedPerStateGates A h i hi
  have hcombined := exact_optimizedCombinedGate A h i hi
  have hln := exact_lnChain_source A h i hi
  have hwalk := exact_finalWalk_transition_sources A h i hi
  intro e hflat
  obtain ⟨es, hes, heEs⟩ := List.mem_flatten.mp hflat
  simp only [finalNonIOSourceFamilies17, nonIOSourceFamilies17With,
    List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [List.mem_append] at heEs
    rcases heEs with heEs | heEs
    · exact hrefold e (stateBlock_mem_refolded .s0 e heEs)
    · exact hrefold e (stateBlock_mem_refolded .s1 e heEs)
  · simp only [List.mem_append] at heEs
    rcases heEs with heEs | heEs
    · exact hrefold e (stateBlock_mem_refolded .s2 e heEs)
    · exact hrefold e (stateBlock_mem_refolded .s3 e heEs)
  · simp only [List.mem_append] at heEs
    rcases heEs with heEs | heEs
    · exact hrefold e (stateBlock_mem_refolded .s4 e heEs)
    · exact hrefold e (stateBlock_mem_refolded .s5 e heEs)
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hair ⟨.row, sv4Expr⟩ (by simp [computeAIR, svExprs])
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hair ⟨.row, sv5Expr⟩ (by simp [computeAIR, svExprs])
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hair ⟨.row, sv6Expr⟩ (by simp [computeAIR, svExprs])
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at heEs
    rcases heEs with ⟨src, hsrc, rfl⟩ | rfl
    · exact hair ⟨.row, src⟩ (by simp [computeAIR, hsrc])
    · exact hcombined
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hair ⟨.row, zZinvExpr⟩ (by simp [computeAIR])
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hln
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hwalk.1
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hwalk.2.1
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hwalk.2.2
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)

/-- Family-level form consumed by the 17-fold compiler. -/
theorem exact_finalNonIO_family_conjunction
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ es ∈ finalNonIOSourceFamilies17, ∀ e ∈ es,
      e.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  intro es hes e he
  exact exact_finalNonIOSourceFamilies17 A h i hi e
    (List.mem_flatten.mpr ⟨es, hes, he⟩)

/-- The honest same-execution row satisfies all seventeen compressed non-IO gates. -/
theorem exact_finalNonIOTransitionGates
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ g ∈ finalNonIOTransitionGates,
      g.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 :=
  finalNonIOTransitionGates_complete _ (exact_finalNonIOSourceFamilies17 A h i hi)

/-- Honest source satisfaction supplies the collision-free premise needed in the reverse
17-fold direction, without an independent witness or probabilistic assumption. -/
theorem exact_finalComputeCollisionFree
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    FinalComputeCollisionFree (exactFinalTransitionEnv A i hi).toSourceEnv := by
  intro es hes _ e he
  exact exact_finalNonIO_family_conjunction A h i hi es hes e he

theorem exactFinalCurrentEnv_lnPrev
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    (lnPrev .traceCur).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (R.problem.exec.computePubAt i).ln_prev := by
  simp [lnPrev, ext0, exactFinalCurrentEnv, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalExtensionRow, coreExtensionValue, encodedRowAt, sampledEncode,
    sampledEncodeExtension, OptimizedComputeCodec.encodeExtension, Expr.eval]

theorem exactFinalCurrentEnv_lnCur
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    (lnCur .traceCur).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (R.problem.exec.computePubAt i).ln := by
  simp [lnCur, ext0, exactFinalCurrentEnv, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalExtensionRow, coreExtensionValue, encodedRowAt, sampledEncode,
    sampledEncodeExtension, OptimizedComputeCodec.encodeExtension, Expr.eval]

theorem exactFinalCurrentEnv_consInv
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    (consInv .traceCur).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (A.exact.computeTableAux i).consInv := by
  simp [consInv, ext0, exactFinalCurrentEnv, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalExtensionRow, coreExtensionValue, encodedRowAt, sampledEncode,
    sampledEncodeExtension, OptimizedComputeCodec.encodeExtension, Expr.eval]

theorem exactFinalCurrentEnv_invGen
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    (invGen .traceCur).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (A.exact.computeTableAux i).invGen := by
  simp [invGen, ext0, exactFinalCurrentEnv, CorrectedFinalTypedEnv.toSourceEnv,
    exactFinalExtensionRow, coreExtensionValue, encodedRowAt, sampledEncode,
    sampledEncodeExtension, OptimizedComputeCodec.encodeExtension, Expr.eval]

theorem exactFinalCurrentEnv_chalAlpha
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    (exactFinalCurrentEnv A i).toSourceEnv.chal 0 =
      R.problem.cfg.challenges.computeInputs.α := by
  simp [exactFinalCurrentEnv, CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge]

theorem exactFinalCurrentEnv_chalZInv
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    (exactFinalCurrentEnv A i).toSourceEnv.chal 5 =
      R.problem.cfg.challenges.computeInputs.z⁻¹ := by
  simp [exactFinalCurrentEnv, CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge]

theorem exactFinalCurrentEnv_table_selectorSV
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hj : j < 11) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  interval_cases j
  all_goals norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull]
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s0
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s1
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s2
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s3
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s4
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s5
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s6
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s7
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s8
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .s9
  · simpa [Expr.eval, Nock.Reified.opCol, opSel, eq_comm] using
      exactFinalCurrentEnv_selectors A i .cons

theorem exactFinalCurrentEnv_table_pub_direct
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (r : Fin 12) (c : Fin 3) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace
        (11 + 3 * (r : ℕ) + c) =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace (11 + 3 * (r : ℕ) + c) := by
  rw [show (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace
      (11 + 3 * (r : ℕ) + c) =
      (semanticPub .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv by
    fin_cases r <;> fin_cases c <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst]]
  rw [exactFinalCurrentEnv_semanticPub_value A h i]
  fin_cases r <;> fin_cases c <;> rfl

theorem exactFinalCurrentEnv_table_pubFP
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hlo : 11 ≤ j) (hhi : j < 47) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  let r : Fin 12 := ⟨(j - 11) / 3, by omega⟩
  let c : Fin 3 := ⟨(j - 11) % 3, Nat.mod_lt _ (by omega)⟩
  have hidx : j = 11 + 3 * (r : ℕ) + c := by
    have hdiv := Nat.mod_add_div (j - 11) 3
    dsimp [r, c]
    omega
  rw [hidx]
  exact exactFinalCurrentEnv_table_pub_direct A h i r c

theorem exactFinalCurrentEnv_table_dec_direct
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (r : Fin 6) (c : Fin 3) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace
        (47 + 3 * (r : ℕ) + c) =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace (47 + 3 * (r : ℕ) + c) := by
  rw [show (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace
      (47 + 3 * (r : ℕ) + c) =
      (decFP .traceCur r c).eval (exactFinalCurrentEnv A i).toSourceEnv by
    fin_cases r <;> fin_cases c <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst]]
  rw [exactFinalCurrentEnv_decFP]
  fin_cases r <;> fin_cases c <;> rfl

theorem exactFinalCurrentEnv_table_decFP
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hlo : 47 ≤ j) (hhi : j < 65) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  let r : Fin 6 := ⟨(j - 47) / 3, by omega⟩
  let c : Fin 3 := ⟨(j - 47) % 3, Nat.mod_lt _ (by omega)⟩
  have hidx : j = 47 + 3 * (r : ℕ) + c := by
    have hdiv := Nat.mod_add_div (j - 47) 3
    dsimp [r, c]
    omega
  rw [hidx]
  exact exactFinalCurrentEnv_table_dec_direct A i r c

theorem exactFinalCurrentEnv_table_extras
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hlo : 65 ≤ j) (hhi : j < 67) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  interval_cases j <;>
    norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
    simpa [exactFinalCurrentEnv_lnPrev, exactFinalCurrentEnv_lnCur]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem exactFinalCurrentEnv_table_mr1
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hlo : 67 ≤ j) (hhi : j < 75) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  have hv := vcompAt_of_compute_obligations A h i
  have hrecords := OptimizedComputeCodec.records_eq_expected_of_vcomp hv
  interval_cases j <;>
    norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
    simp [Expr.eval, exactFinalCurrentEnv_pubFPNat,
      exactFinalCurrentEnv_semanticPubNat_value A h i,
      exactFinalCurrentEnv_decFPNat_value, exactFinalCurrentEnv_lnPrev,
      exactFinalCurrentEnv_chalAlpha, encodedRowAt, sampledEncode,
      sampledEncodeExtension, OptimizedComputeCodec.encodeExtension,
      OptimizedComputeCodec.pubFingerprint, OptimizedComputeCodec.decFingerprint,
      OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    (try simp [hs, overlayRoleA, overlayRoleB] at hrecords ⊢) <;>
    aesop

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem exactFinalCurrentEnv_table_mr2
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hlo : 75 ≤ j) (hhi : j < 83) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  have hv := vcompAt_of_compute_obligations A h i
  have hrecords := OptimizedComputeCodec.records_eq_expected_of_vcomp hv
  have h0 := exactFinalCurrentEnv_selectors A i .s0
  have h1 := exactFinalCurrentEnv_selectors A i .s1
  have h2 := exactFinalCurrentEnv_selectors A i .s2
  have h3 := exactFinalCurrentEnv_selectors A i .s3
  have h4 := exactFinalCurrentEnv_selectors A i .s4
  have h5 := exactFinalCurrentEnv_selectors A i .s5
  have h6 := exactFinalCurrentEnv_selectors A i .s6
  have h7 := exactFinalCurrentEnv_selectors A i .s7
  have h8 := exactFinalCurrentEnv_selectors A i .s8
  have h9 := exactFinalCurrentEnv_selectors A i .s9
  interval_cases j <;>
    norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull,
      mr2Field, mr2Group] <;>
    simp [Expr.eval, exactFinalCurrentEnv_selectors, exactFinalCurrentEnv_pubFPNat,
      exactFinalCurrentEnv_semanticPubNat_value A h i,
      exactFinalCurrentEnv_decFPNat_value, exactFinalCurrentEnv_lnPrev,
      exactFinalCurrentEnv_chalAlpha, encodedRowAt, sampledEncode,
      sampledEncodeExtension, OptimizedComputeCodec.encodeExtension,
      OptimizedComputeCodec.pubFingerprint, OptimizedComputeCodec.decFingerprint,
      OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [hs, overlayRoleA, overlayRoleB, OptimizedComputeCodec.expectedMr2,
      opSel, Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hrecords ⊢ <;>
    aesop

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem exactFinalCurrentEnv_table_mr3
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hlo : 83 ≤ j) (hhi : j < 91) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  have hv := vcompAt_of_compute_obligations A h i
  have hrecords := OptimizedComputeCodec.records_eq_expected_of_vcomp hv
  have h0 := exactFinalCurrentEnv_selectors A i .s0
  have h1 := exactFinalCurrentEnv_selectors A i .s1
  have h2 := exactFinalCurrentEnv_selectors A i .s2
  have h3 := exactFinalCurrentEnv_selectors A i .s3
  have h4 := exactFinalCurrentEnv_selectors A i .s4
  have h5 := exactFinalCurrentEnv_selectors A i .s5
  have h6 := exactFinalCurrentEnv_selectors A i .s6
  have h7 := exactFinalCurrentEnv_selectors A i .s7
  have h8 := exactFinalCurrentEnv_selectors A i .s8
  have h9 := exactFinalCurrentEnv_selectors A i .s9
  interval_cases j <;>
    norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull,
      mr3Field, mr3Group] <;>
    simp [Expr.eval, exactFinalCurrentEnv_selectors, exactFinalCurrentEnv_pubFPNat,
      exactFinalCurrentEnv_semanticPubNat_value A h i,
      exactFinalCurrentEnv_decFPNat_value, exactFinalCurrentEnv_lnPrev,
      exactFinalCurrentEnv_chalAlpha, encodedRowAt, sampledEncode,
      sampledEncodeExtension, OptimizedComputeCodec.encodeExtension,
      OptimizedComputeCodec.pubFingerprint, OptimizedComputeCodec.decFingerprint,
      OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [hs, overlayRoleA, overlayRoleB, OptimizedComputeCodec.expectedMr3,
      opSel, Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hrecords ⊢ <;>
    aesop

theorem exactFinalCurrentEnv_table_line
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hlo : 91 ≤ j) (hhi : j < 94) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  interval_cases j <;>
    norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
    simpa [Expr.eval, exactFinalCurrentEnv_consInv,
      exactFinalCurrentEnv_invGen, exactFinalCurrentEnv_chalZInv]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- Structural all-column current decoder.  It dispatches through semantic blocks instead of
enumerating all 94 source columns in one theorem. -/
theorem exactFinalCurrentEnv_table_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (j : ℕ) (hj : j < 94) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i)
        (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j := by
  by_cases h11 : j < 11
  · exact exactFinalCurrentEnv_table_selectorSV A i j h11
  by_cases h47 : j < 47
  · exact exactFinalCurrentEnv_table_pubFP A h i j (by omega) h47
  by_cases h65 : j < 65
  · exact exactFinalCurrentEnv_table_decFP A i j (by omega) h65
  by_cases h67 : j < 67
  · exact exactFinalCurrentEnv_table_extras A i j (by omega) h67
  by_cases h75 : j < 75
  · exact exactFinalCurrentEnv_table_mr1 A h i j (by omega) h75
  by_cases h83 : j < 83
  · exact exactFinalCurrentEnv_table_mr2 A h i j (by omega) h83
  by_cases h91 : j < 91
  · exact exactFinalCurrentEnv_table_mr3 A h i j (by omega) h91
  exact exactFinalCurrentEnv_table_line A i j (by omega) hj

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- Every ordinary compute-row source expression is current-only, so exact Vcomp/AIR row
satisfaction transports through the structural terminal decoder without a successor premise. -/
theorem exact_computeAIR_row_substituted_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) :
    ∀ c ∈ Nock.Reified.computeAIR.constraints,
      (c.expr.subst computeSubst).eval (exactFinalCurrentEnv A i).toSourceEnv = 0 := by
  intro c hc
  rw [eval_computeSubst]
  rw [CurrentComputeExpr.eval_eq (computeAIR_current_footprint c hc)
    (fun j hj => exactFinalCurrentEnv_table_current A h i j hj)
    (fun j hj => by
      interval_cases j <;>
        simp [Expr.eval, Env.ofSubst, computeSubst, exactFinalCurrentEnv,
          CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge, computeEnvFull])
    (fun j => by
      simp [Expr.eval, Env.ofSubst, computeSubst, exactFinalCurrentEnv,
        CorrectedFinalTypedEnv.toSourceEnv, computeEnvFull])]
  exact exact_computeAIR_row A h i c hc

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- Current-row counterpart of the two leaf-booleanity refolds. -/
theorem exact_refoldedPerStateGates_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) :
    ∀ e ∈ refoldedPerStateGates,
      e.eval (exactFinalCurrentEnv A i).toSourceEnv = 0 := by
  let env := (exactFinalCurrentEnv A i).toSourceEnv
  have hair := exact_computeAIR_row_substituted_current A h i
  have hmap :
      ∀ e ∈ Nock.Reified.perStateGated.map (fun e => e.subst computeSubst),
        e.eval env = 0 := by
    intro e he
    obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp he
    apply hair ⟨.row, src⟩
    simp [Nock.Reified.computeAIR, hsrc]
  have hfix := fixed_overlay_leaf_booleanity_degrees
  have hop3mem :
      op3ELeafBool.subst computeSubst ∈
        Nock.Reified.perStateGated.map (fun e => e.subst computeSubst) := by
    apply List.mem_map.mpr
    refine ⟨op3ELeafBool, ?_, rfl⟩
    rw [← hfix.1]
    exact List.get_mem _ _
  have hop5mem :
      op5ELeafBool.subst computeSubst ∈
        Nock.Reified.perStateGated.map (fun e => e.subst computeSubst) := by
    apply List.mem_map.mpr
    refine ⟨op5ELeafBool, ?_, rfl⟩
    rw [← hfix.2.1]
    exact List.get_mem _ _
  have hop3 : op3ELeafBoolRefold.eval env = 0 := by
    rw [← op3ELeafBool_refold_eval_oneHot env
      (R.problem.exec.computePubAt i).state (exactFinalCurrentEnv_selectors A i)]
    exact hmap _ hop3mem
  have hop5 : op5ELeafBoolRefold.eval env = 0 := by
    rw [← op5ELeafBool_refold_eval_oneHot env
      (R.problem.exec.computePubAt i).state (exactFinalCurrentEnv_selectors A i)]
    exact hmap _ hop5mem
  rw [refoldedPerStateGates]
  exact all_mem_set_zero env _ 270 op5ELeafBoolRefold
    (all_mem_set_zero env _ 177 op3ELeafBoolRefold hmap hop3) hop5

/-- The selector-activated nonlinear source is also entirely current-row. -/
theorem exact_optimizedCombinedGate_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) :
    optimizedCombinedGate.eval (exactFinalCurrentEnv A i).toSourceEnv = 0 := by
  rw [optimizedCombinedGate, eval_computeSubst]
  rw [CurrentComputeExpr.eval_eq combinedSourceExpr_current_footprint
    (fun j hj => exactFinalCurrentEnv_table_current A h i j hj)
    (fun j hj => by
      interval_cases j <;>
        simp [Expr.eval, Env.ofSubst, computeSubst, exactFinalCurrentEnv,
          CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge, computeEnvFull])
    (fun j => by
      simp [Expr.eval, Env.ofSubst, computeSubst, exactFinalCurrentEnv,
        CorrectedFinalTypedEnv.toSourceEnv, computeEnvFull])]
  rw [combinedSourceExpr_opSel_iff]
  have hair := exact_computeAIR_row A h i
  have hrap := (Nock.Reified.computeAIR_sound
    R.problem.cfg.challenges.computeInputs
    (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
    (A.exact.computeTableAux i)).1 hair |>.1
  obtain ⟨_, _, _, _, heval⟩ := hrap
  cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [Nock.ComputeTable.evalR, hs] at heval ⊢ <;>
    aesop

@[simp] theorem exactFinalCurrentEnv_sampled_gamma
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    (exactFinalCurrentEnv A i).toSourceEnv.chal 7 = A.sampled.coins.gamma := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv, exactFinalChallenge]

@[simp] theorem exactFinalCurrentEnv_sampled_pole
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    (exactFinalCurrentEnv A i).toSourceEnv.chal 8 = A.sampled.coins.pole := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv, exactFinalChallenge]

theorem exactFinalCurrentEnv_sampledActive
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : Fin 3) :
    (sampledActive .traceCur j).eval (exactFinalCurrentEnv A i).toSourceEnv =
      match j with
      | 0 => 1
      | 1 => secondRequestMask (R.problem.exec.computePubAt i).state
      | 2 => thirdRequestMask (R.problem.exec.computePubAt i).state := by
  have h0 := exactFinalCurrentEnv_selectors A i .s0
  have h1 := exactFinalCurrentEnv_selectors A i .s1
  have h2 := exactFinalCurrentEnv_selectors A i .s2
  have h3 := exactFinalCurrentEnv_selectors A i .s3
  have h4 := exactFinalCurrentEnv_selectors A i .s4
  have h5 := exactFinalCurrentEnv_selectors A i .s5
  have h6 := exactFinalCurrentEnv_selectors A i .s6
  have h7 := exactFinalCurrentEnv_selectors A i .s7
  have h8 := exactFinalCurrentEnv_selectors A i .s8
  have h9 := exactFinalCurrentEnv_selectors A i .s9
  fin_cases j <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [Nock.Reified.opCol, hs] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 <;>
    simp [sampledActive, Expr.eval, secondRequestMask, thirdRequestMask, hs,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem exactFinalCurrentEnv_sampledDenomWitness
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : Fin 3) :
    (sampledDenomWitness .traceCur j).eval (exactFinalCurrentEnv A i).toSourceEnv =
      match j with
      | 0 => (overlayAt A i).denom0
      | 1 => (overlayAt A i).denom1
      | 2 => (overlayAt A i).denom2 := by
  have h3 : ¬ 6 + (j : ℕ) < 3 := by omega
  have h5 : ¬ 6 + (j : ℕ) < 5 := by omega
  have heq : 6 + (j : ℕ) ≠ 5 := by omega
  simp only [sampledDenomWitness, overlayCoord, h3, h5, heq,
    if_false, Nat.add_sub_cancel_left]
  change (pubFP .traceCur 11 j).eval (exactFinalCurrentEnv A i).toSourceEnv = _
  rw [show (pubFP .traceCur 11 j).eval (exactFinalCurrentEnv A i).toSourceEnv =
      (encodedRowAt A i).extension (.inl ((11 : Fin 12), j)) by
    simpa using exactFinalCurrentEnv_pubFP A i (11 : Fin 12) j]
  fin_cases j <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [overlayAt, encodedRowAt, sampledEncode, sampledEncodeExtension,
      OptimizedComputeCodec.encodeExtension, sampledOverlayA, overlayDenoms,
      OptimizedComputeCodec.fpCoordinate, overlayRoleA, overlayRoleB,
      overlayANat, overlayBNat, hs]

set_option maxHeartbeats 8000000 in
/-- Successor-free twin of `exactFinalTransitionEnv_sampledDenom_current`. -/
theorem exactFinalCurrentEnv_sampledDenom
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F)
    (j : Fin 3)
    (hact : slotActive R i j = 1) :
    ((sampledDenom .traceCur j).subst finalSampledNamespace).eval
        (exactFinalCurrentEnv A i).toSourceEnv =
      A.compress10
        (NockVM.encRecFormR
          (slotRecord R i j) R.problem.cfg.challenges.lam) := by
  have hcol (c : Fin 8) :
      (computeTraceSubst .traceCur
        (67 + 8 * (j : ℕ) + (c : ℕ))).eval
          (Env.ofSubst finalSampledNamespace (exactFinalCurrentEnv A i).toSourceEnv) =
        NockVM.encRecC (slotRecord R i j) 1 c.castSucc := by
    have ht := exactFinalCurrentEnv_table_current A h i
      (67 + 8 * (j : ℕ) + (c : ℕ)) (by omega)
    fin_cases j <;> fin_cases c <;> exact ht
  have hx : (sampledSlotE .traceCur (67 + 8 * (j : ℕ))).eval
      (Env.ofSubst finalSampledNamespace (exactFinalCurrentEnv A i).toSourceEnv) =
        (((OptimizedComputeFinalTrace.honestS R i + (j : ℕ) + 1 : ℕ)) : K) := by
    fin_cases j <;>
      simp [sampledSlotE, Expr.eval, Env.ofSubst, finalSampledNamespace,
        CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv] <;> ring
  rw [SampledIOSameExecutionAssignment.compress10,
    ← withExp_honestS_eq_extRec A i j hact]
  refine sampledDenom_eq_formR A i hsmall hwidth (exactFinalCurrentEnv A i) j
    R.problem.cfg.challenges.lam
    (fun s => exactFinalCurrentEnv_selectors A i s) hcol
    (exactFinalCurrentEnv_sampled_gamma A i) (exactFinalCurrentEnv_sampled_pole A i)
    rfl rfl rfl
    (by simpa using exactFinalCurrentEnv_extension_current A i ⟨41, by decide⟩)
    (by simpa using exactFinalCurrentEnv_extension_current A i ⟨44, by decide⟩) hact _ hx

theorem exact_finalSampled_denom_pins_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F) :
    ∀ j : Fin 3,
      ((sampledDenomPin .traceCur j).subst finalSampledNamespace).eval
        (exactFinalCurrentEnv A i).toSourceEnv = 0 := by
  intro j
  rw [Expr.eval_subst]
  simp only [sampledDenomPin, Expr.eval]
  have hw :
      (sampledDenomWitness .traceCur j).eval
          (Env.ofSubst finalSampledNamespace (exactFinalCurrentEnv A i).toSourceEnv) =
        (sampledDenomWitness .traceCur j).eval (exactFinalCurrentEnv A i).toSourceEnv := by
    fin_cases j <;> rfl
  have hs :
      (sampledSafeDenom .traceCur j).eval
          (Env.ofSubst finalSampledNamespace (exactFinalCurrentEnv A i).toSourceEnv) =
        OptimizedComputeFiniteIOGates.SafeDenom
          ((sampledActive .traceCur j).eval (exactFinalCurrentEnv A i).toSourceEnv)
          (((sampledDenom .traceCur j).subst finalSampledNamespace).eval
            (exactFinalCurrentEnv A i).toSourceEnv) := by
    fin_cases j <;>
      simp [sampledSafeDenom, sampledActive,
        OptimizedComputeFiniteIOGates.SafeDenom,
        Expr.eval, Expr.eval_subst, Env.ofSubst, finalSampledNamespace]
  rw [sub_eq_zero, hw, exactFinalCurrentEnv_sampledDenomWitness, hs,
    exactFinalCurrentEnv_sampledActive]
  fin_cases j
  · have hd := exactFinalCurrentEnv_sampledDenom A h i hsmall hwidth 0 rfl
    simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero] at hd ⊢
    rw [hd]
    simp [overlayAt, slotRecord, OptimizedComputeFiniteIOGates.SafeDenom]
  · by_cases hm : secondRequestMask (K := K) (R.problem.exec.computePubAt i).state = 1
    · have hd := exactFinalCurrentEnv_sampledDenom A h i hsmall hwidth 1 hm
      simp only [Fin.mk_one, Fin.isValue, Fin.val_one] at hd ⊢
      rw [hd]
      simp [overlayAt, inactiveSafe, slotRecord, OptimizedComputeFiniteIOGates.SafeDenom, hm]
    · have hm0 : secondRequestMask (K := K) (R.problem.exec.computePubAt i).state = 0 := by
        cases hs : (R.problem.exec.computePubAt i).state <;>
          simp_all [secondRequestMask]
      simp [overlayAt, inactiveSafe, OptimizedComputeFiniteIOGates.SafeDenom, hm0]
  · by_cases hm : thirdRequestMask (K := K) (R.problem.exec.computePubAt i).state = 1
    · have hd := exactFinalCurrentEnv_sampledDenom A h i hsmall hwidth 2 hm
      simp only [Fin.reduceFinMk, Fin.isValue, Fin.val_two] at hd ⊢
      rw [hd]
      simp [overlayAt, inactiveSafe, slotRecord, OptimizedComputeFiniteIOGates.SafeDenom, hm]
    · have hm0 : thirdRequestMask (K := K) (R.problem.exec.computePubAt i).state = 0 := by
        cases hs : (R.problem.exec.computePubAt i).state <;>
          simp_all [thirdRequestMask]
      simp [overlayAt, inactiveSafe, OptimizedComputeFiniteIOGates.SafeDenom, hm0]

/-! ### The anchored accumulator step on the successor-free exact row (A-comp) -/

/-- The accumulator role `32` of the exact current row is the co-resident accumulator before
row `i`. -/
theorem exactFinalCurrentEnv_sampledAcc
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    (sampledIOSubst .traceCur 0).eval (exactFinalCurrentEnv A i).toSourceEnv =
      ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows i := by
  change (pubFP .traceCur (10 : Fin 12) (2 : Fin 3)).eval
    (exactFinalCurrentEnv A i).toSourceEnv = _
  rw [exactFinalCurrentEnv_pubFP]
  cases hs : (R.problem.exec.computePubAt i).state <;>
    simp [encodedRowAt, sampledEncode, sampledEncodeExtension,
      OptimizedComputeCodec.encodeExtension, sampledOverlayA, overlayRoleA,
      overlayRoleB, overlayANat, overlayBNat, overlayAt, hs]

/-- Witness role `60` of the exact current row is `acc_after(i)`. -/
theorem exactFinalCurrentEnv_accAfter
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    (exactFinalCurrentEnv A i).toSourceEnv.trace
        OptimizedComputeFiniteIOGates.accAfterIndex =
      ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows
        ((i : ℕ) + 1) := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv, exactFinalExtensionRow,
    OptimizedComputeFiniteIOGates.accAfterIndex]

/-- The semantic content of the sampled fold at **every** row, the last included: the
co-resident accumulator advances by the row's active reciprocals, in the inactive-safe form
.  Extracted from `exact_finalSampled_folded_step`, which needed a successor
only to *read* `acc(i+1)`. -/
theorem exact_folded_step_values
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    OptimizedComputeFiniteIOGates.FoldedProgStep3
      (ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows i)
      (ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1))
      (overlayAt A i).denom0 (overlayAt A i).denom1 (overlayAt A i).denom2
      1 (secondRequestMask (R.problem.exec.computePubAt i).state)
      (thirdRequestMask (R.problem.exec.computePubAt i).state) := by
  let row := R.problem.exec.computeRowAt i
  let a1 : K := secondRequestMask (R.problem.exec.computePubAt i).state
  let a2 : K := thirdRequestMask (R.problem.exec.computePubAt i).state
  let d0 := A.compress10
    (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr1 R.problem.cfg.challenges.lam)
  let d1 := A.compress10
    (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr2 R.problem.cfg.challenges.lam)
  let d2 := A.compress10
    (NockVM.encRecFormR (R.problem.exec.computePubAt i).mr3 R.problem.cfg.challenges.lam)
  have ha1 : a1 = 0 ∨ a1 = 1 := by
    cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [a1, secondRequestMask, hs]
  have ha2 : a2 = 0 ∨ a2 = 1 := by
    cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [a2, thirdRequestMask, hs]
  have hd0 : d0 ≠ 0 :=
    exact_active_request_nonzero A i (by
      apply List.mem_map_of_mem
      simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt]
      cases (R.problem.exec.computeRowAt i).2.2.1.state <;> simp)
  have hd1 : a1 = 1 → d1 ≠ 0 := by
    intro ha
    apply exact_active_request_nonzero A i
    apply List.mem_map_of_mem
    simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt,
      secondRequestMask, a1] at ha ⊢
    cases hst : (R.problem.exec.computeRowAt i).2.2.1.state <;> simp [hst] at ha ⊢
  have hd2 : a2 = 1 → d2 ≠ 0 := by
    intro ha
    apply exact_active_request_nonzero A i
    apply List.mem_map_of_mem
    simp only [NockVM.activeRequestRecords, ExactExecution.computePubAt,
      thirdRequestMask, a2] at ha ⊢
    cases hst : (R.problem.exec.computeRowAt i).2.2.1.state <;> simp [hst] at ha ⊢
  have hiRows : (i : ℕ) < R.problem.exec.computeRows.length := by
    simpa using i.isLt
  have hacc := ComputeSampledIO.coResidentAccC_succ A.compress10
    R.problem.cfg.challenges.lam R.problem.exec.computeRows hiRows
  rw [rowTermC_eq_fixed_slots] at hacc
  have hfoldSafe :
      OptimizedComputeFiniteIOGates.FoldedProgStep3
        (ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows i)
        (ComputeSampledIO.coResidentAccC A.compress10
          R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1))
        (OptimizedComputeFiniteIOGates.SafeDenom 1 d0)
        (OptimizedComputeFiniteIOGates.SafeDenom a1 d1)
        (OptimizedComputeFiniteIOGates.SafeDenom a2 d2)
        1 a1 a2 :=
    (OptimizedComputeFiniteIOGates.foldedProgStep3_safe_iff
      _ _ d0 d1 d2 1 a1 a2 (by simp) ha1 ha2
      (fun _ => hd0) hd1 hd2).2 (by
        simpa [row, a1, a2, d0, d1, d2,
          ComputeSampledIO.requestInv, ExactExecution.computePubAt,
          ExactExecution.computeRowAt, add_assoc] using hacc)
  simpa [a1, a2, d0, d1, d2, overlayAt, inactiveSafe,
    OptimizedComputeFiniteIOGates.SafeDenom] using hfoldSafe

/-- **The anchored step holds on every exact row**, the terminal one included: with role `60`
carrying `acc_after(i)`, `finalAccAfterStep` vanishes on the successor-free environment. -/
theorem exact_accAfterStep_current
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    finalAccAfterStep.eval (exactFinalCurrentEnv A i).toSourceEnv = 0 := by
  let env := (exactFinalCurrentEnv A i).toSourceEnv
  rw [finalAccAfterStep, Expr.eval_subst,
    OptimizedComputeFiniteIOGates.optimizedAccAfterStep_eval]
  have hc := exactFinalCurrentEnv_sampledAcc A i
  have hn := exactFinalCurrentEnv_accAfter A i
  have ha0 := exactFinalCurrentEnv_sampledActive A i 0
  have ha1 := exactFinalCurrentEnv_sampledActive A i 1
  have ha2 := exactFinalCurrentEnv_sampledActive A i 2
  have hw0 := exactFinalCurrentEnv_sampledDenomWitness A i 0
  have hw1 := exactFinalCurrentEnv_sampledDenomWitness A i 1
  have hw2 := exactFinalCurrentEnv_sampledDenomWitness A i 2
  have hc' :
      (sampledIOSubst .traceCur 0).eval (Env.ofSubst finalSampledNamespace env) =
        ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows i := by
    change (sampledIOSubst .traceCur 0).eval env = _
    exact hc
  have hn' :
      (Env.ofSubst finalSampledNamespace env).trace
          OptimizedComputeFiniteIOGates.accAfterIndex =
        ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows
          ((i : ℕ) + 1) := by
    change env.trace OptimizedComputeFiniteIOGates.accAfterIndex = _
    exact hn
  have hw0' :
      (sampledDenomWitness .traceCur 0).eval (Env.ofSubst finalSampledNamespace env) =
        (overlayAt A i).denom0 := by
    change (sampledDenomWitness .traceCur 0).eval env = _
    exact hw0
  have hw1' :
      (sampledDenomWitness .traceCur 1).eval (Env.ofSubst finalSampledNamespace env) =
        (overlayAt A i).denom1 := by
    change (sampledDenomWitness .traceCur 1).eval env = _
    exact hw1
  have hw2' :
      (sampledDenomWitness .traceCur 2).eval (Env.ofSubst finalSampledNamespace env) =
        (overlayAt A i).denom2 := by
    change (sampledDenomWitness .traceCur 2).eval env = _
    exact hw2
  have ha0' :
      (sampledActive .traceCur 0).eval (Env.ofSubst finalSampledNamespace env) = 1 := by
    change (sampledActive .traceCur 0).eval env = 1
    exact ha0
  have ha1' :
      (sampledActive .traceCur 1).eval (Env.ofSubst finalSampledNamespace env) =
        secondRequestMask (R.problem.exec.computePubAt i).state := by
    change (sampledActive .traceCur 1).eval env = _
    exact ha1
  have ha2' :
      (sampledActive .traceCur 2).eval (Env.ofSubst finalSampledNamespace env) =
        thirdRequestMask (R.problem.exec.computePubAt i).state := by
    change (sampledActive .traceCur 2).eval env = _
    exact ha2
  rw [hc', hn']
  simp only [sampledIOSubst]
  rw [hw0', hw1', hw2', ha0', ha1', ha2']
  exact exact_folded_step_values A i

/-- Exact non-IO source families behind terminal extension IDs
`0..7,12..16`, in ID order with the transitional gap removed. -/
def terminalCurrentNonIOSourceFamilies : List (List Expr) :=
  [(stateBlock .s0 ++ stateBlock .s1),
   (stateBlock .s2 ++ stateBlock .s3),
   (stateBlock .s4 ++ stateBlock .s5),
   [sv4Expr.subst computeSubst],
   [sv5Expr.subst computeSubst],
   [sv6Expr.subst computeSubst],
   (formulaExprs.map (fun e => e.subst computeSubst)) ++ [optimizedCombinedGate],
   [zZinvExpr.subst computeSubst],
   stateBlock .s6, stateBlock .s7, stateBlock .s8, stateBlock .s9,
   stateBlock .cons]

/-- Syntactic support predicate used by the terminal proof. -/
def CurrentRowOnly : Expr → Bool
  | .Var .traceCur _ => true
  | .Var .traceNext _ => false
  | .Var .challenge _ | .Var .publicVal _ | .Const _ => true
  | .Add x y | .Sub x y | .Mul x y => CurrentRowOnly x && CurrentRowOnly y
  | .Neg x | .Pow x _ => CurrentRowOnly x

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- Compiled support census: every source expression behind terminal IDs
`0..7,12..19` is current-row-only.  The final three families are the sampled denominator pins. -/
theorem terminalCurrentSourceFamilies_currentRowOnly :
    (∀ e ∈ terminalCurrentNonIOSourceFamilies.flatten, CurrentRowOnly e = true) ∧
      (∀ j : Fin 3,
        CurrentRowOnly ((sampledDenomPin .traceCur j).subst finalSampledNamespace) = true) := by
  decide

/-- Vcomp/AIR row satisfaction directly discharges every terminal-current non-IO source family. -/
theorem exact_terminalCurrentNonIOSourceFamilies
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) :
    ∀ e ∈ terminalCurrentNonIOSourceFamilies.flatten,
      e.eval (exactFinalCurrentEnv A i).toSourceEnv = 0 := by
  let env := (exactFinalCurrentEnv A i).toSourceEnv
  have hair := exact_computeAIR_row_substituted_current A h i
  have hrefold := exact_refoldedPerStateGates_current A h i
  have hcombined := exact_optimizedCombinedGate_current A h i
  intro e hflat
  obtain ⟨es, hes, heEs⟩ := List.mem_flatten.mp hflat
  simp only [terminalCurrentNonIOSourceFamilies, List.mem_cons,
    List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · simp only [List.mem_append] at heEs
    rcases heEs with heEs | heEs
    · exact hrefold e (stateBlock_mem_refolded .s0 e heEs)
    · exact hrefold e (stateBlock_mem_refolded .s1 e heEs)
  · simp only [List.mem_append] at heEs
    rcases heEs with heEs | heEs
    · exact hrefold e (stateBlock_mem_refolded .s2 e heEs)
    · exact hrefold e (stateBlock_mem_refolded .s3 e heEs)
  · simp only [List.mem_append] at heEs
    rcases heEs with heEs | heEs
    · exact hrefold e (stateBlock_mem_refolded .s4 e heEs)
    · exact hrefold e (stateBlock_mem_refolded .s5 e heEs)
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hair ⟨.row, sv4Expr⟩ (by simp [computeAIR, svExprs])
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hair ⟨.row, sv5Expr⟩ (by simp [computeAIR, svExprs])
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hair ⟨.row, sv6Expr⟩ (by simp [computeAIR, svExprs])
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at heEs
    rcases heEs with ⟨src, hsrc, rfl⟩ | rfl
    · exact hair ⟨.row, src⟩ (by simp [computeAIR, hsrc])
    · exact hcombined
  · simp only [List.mem_singleton] at heEs
    subst e
    exact hair ⟨.row, zZinvExpr⟩ (by simp [computeAIR])
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)
  · exact hrefold e (stateBlock_mem_refolded _ _ heEs)

/-- The 75 row-local terminal gates as source expressions, in production ID order:
packed row-local (`paperPackingRowLocal`, 72) plus the three sampled denominator pins. -/
def terminalCurrentExtGates : List Expr :=
  paperPackingRowLocal ++
    [((sampledDenomPin .traceCur 0).subst finalSampledNamespace),
     ((sampledDenomPin .traceCur 1).subst finalSampledNamespace),
     ((sampledDenomPin .traceCur 2).subst finalSampledNamespace)]

/-- The 75 unmasked terminal-row production IDs: packed row-local gates `0..71` and the three
sampled denominator pins `78..80`.  Excluded: cross-row `72..75` (F-E-2 `notLast`/residual),
the queue-witness pair `76..77` (last-row tiling, proved separately), and the IO chain `81`. -/
def terminalCurrentExtGateIds : List CorrectedCoreExtGateId :=
  List.ofFn (fun i : Fin 72 =>
      (⟨i.val, by have := i.isLt; omega⟩ : CorrectedCoreExtGateId)) ++
    [⟨78, by omega⟩, ⟨79, by omega⟩, ⟨80, by omega⟩]

theorem terminalCurrentExtGates_length : terminalCurrentExtGates.length = 75 := by
  simp [terminalCurrentExtGates, paperPackingRowLocal_length]

theorem terminalCurrentExtGateIds_length : terminalCurrentExtGateIds.length = 75 := by
  decide

set_option maxRecDepth 300000 in
/-- Exact production-ID lookup for the 77 terminal-current packed gates. -/
theorem finalExtGate_mem_terminalCurrent
    (gate : CorrectedCoreExtGateId) (hgate : gate ∈ terminalCurrentExtGateIds) :
    finalExtTransitionGates.get ⟨gate, by simp⟩ ∈ terminalCurrentExtGates := by
  simp only [terminalCurrentExtGateIds, List.mem_append] at hgate
  rcases hgate with h | h
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    have hj : (j : ℕ) < paperPackingRowLocal.length := by
      simpa [paperPackingRowLocal_length] using j.isLt
    have hget :
        finalExtTransitionGates.get ⟨j.val, by simp; have := j.isLt; omega⟩ =
          paperPackingRowLocal.get ⟨j.val, hj⟩ := by
      have hrow : paperPackingNonIOGates =
          paperPackingRowLocal ++ (crossRowSingletons ++
            OptimizedComputeGateBasis.queueWitnessGates) := by
        rw [paperPacking_eq_rowLocal_append, List.append_assoc]
      simp only [finalExtTransitionGates, hrow, List.append_assoc]
      exact List.getElem_append_left hj
    rw [hget]
    exact List.mem_append.mpr (Or.inl (List.get_mem _ _))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have hlen : paperPackingNonIOGates.length = 78 := paperPackingNonIOGates_length
    rcases h with h78 | h79 | h80
    · have hgval : (gate : ℕ) = 78 := congrArg Fin.val h78
      have hget : finalExtTransitionGates.get ⟨gate, by simp⟩ =
          (sampledDenomPin .traceCur 0).subst finalSampledNamespace := by
        simp [finalExtTransitionGates, hlen, finalSampledIOTransitionGates,
          OptimizedComputeFiniteIOGates.optimizedSampledIOTransitionGates,
          OptimizedComputeFiniteIOGates.optimizedDenomPinGates, hgval]
      rw [hget]
      simp [terminalCurrentExtGates]
    · have hgval : (gate : ℕ) = 79 := congrArg Fin.val h79
      have hget : finalExtTransitionGates.get ⟨gate, by simp⟩ =
          (sampledDenomPin .traceCur 1).subst finalSampledNamespace := by
        simp [finalExtTransitionGates, hlen, finalSampledIOTransitionGates,
          OptimizedComputeFiniteIOGates.optimizedSampledIOTransitionGates,
          OptimizedComputeFiniteIOGates.optimizedDenomPinGates, hgval]
      rw [hget]
      simp [terminalCurrentExtGates]
    · have hgval : (gate : ℕ) = 80 := congrArg Fin.val h80
      have hget : finalExtTransitionGates.get ⟨gate, by simp⟩ =
          (sampledDenomPin .traceCur 2).subst finalSampledNamespace := by
        simp [finalExtTransitionGates, hlen, finalSampledIOTransitionGates,
          OptimizedComputeFiniteIOGates.optimizedSampledIOTransitionGates,
          OptimizedComputeFiniteIOGates.optimizedDenomPinGates, hgval]
      rw [hget]
      simp [terminalCurrentExtGates]

/-- Direct terminal completeness for all 76 unmasked packed source gates. -/
theorem exact_terminalCurrentExtGates
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F) :
    ∀ g ∈ terminalCurrentExtGates,
      g.eval (exactFinalCurrentEnv A i).toSourceEnv = 0 := by
  intro g hg
  simp only [terminalCurrentExtGates, List.mem_append] at hg
  rcases hg with hg | hg
  · have hterm := exact_terminalCurrentNonIOSourceFamilies A h i
    have hsel : OneHotSelector (exactFinalCurrentEnv A i).toSourceEnv
        (R.problem.exec.computePubAt i).state :=
      fun s => exactFinalCurrentEnv_selectors A i s
    have hz : (zZinvExpr.subst computeSubst).eval
        (exactFinalCurrentEnv A i).toSourceEnv = 0 :=
      hterm _ (by decide)
    have hrefold := exact_refoldedPerStateGates_current A h i
    have hall : ∀ g ∈ alwaysOnOptimized,
        g ∈ terminalCurrentNonIOSourceFamilies.flatten := by decide
    rcases List.mem_append.mp hg with hg | hg
    · exact (paperPacking_iff_atomic _ _ hsel hz).2
        (fun s e he => hrefold e (stateBlock_mem_refolded s e he)) g hg
    · exact hterm g (hall g hg)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact exact_finalSampled_denom_pins_current A h i hsmall hwidth 0
    · exact exact_finalSampled_denom_pins_current A h i hsmall hwidth 1
    · exact exact_finalSampled_denom_pins_current A h i hsmall hwidth 2

theorem exact_correctedFinalExtGate_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F)
    (gate : CorrectedCoreExtGateId) (hgate : gate ∈ terminalCurrentExtGateIds) :
    (correctedFinalExtGate gate).eval (exactFinalCurrentEnv A i) = 0 := by
  rw [← correctedFinalExtGate_eval_source]
  exact exact_terminalCurrentExtGates A h i hsmall hwidth _
    (finalExtGate_mem_terminalCurrent gate hgate)

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem final_compute_source_families_compilerInputFree :
    (∀ e ∈ finalNonIOSourceFamilies17.flatten, CompilerInputFree e) ∧
      (∀ e ∈ finalSampledIOTransitionGates, CompilerInputFree e) ∧
      (∀ e ∈ terminalCurrentNonIOSourceFamilies.flatten, CompilerInputFree e) ∧
      (∀ j : Fin 3,
        CompilerInputFree ((sampledDenomPin .traceCur j).subst finalSampledNamespace)) := by
  constructor
  · intro e he
    rw [← compilerInputFreeB_iff]
    set_option maxRecDepth 300000 in
      exact (by
        have h : ∀ e ∈ finalNonIOSourceFamilies17.flatten, compilerInputFreeB e := by decide
        exact h e he)
  constructor
  · intro e he
    rw [← compilerInputFreeB_iff]
    have h : ∀ e ∈ finalSampledIOTransitionGates, compilerInputFreeB e := by decide
    exact h e he
  constructor
  · intro e he
    rw [← compilerInputFreeB_iff]
    set_option maxRecDepth 300000 in
      exact (by
        have h : ∀ e ∈ terminalCurrentNonIOSourceFamilies.flatten,
            compilerInputFreeB e := by decide
        exact h e he)
  · intro j
    rw [← compilerInputFreeB_iff]
    fin_cases j <;> decide

theorem paperPackingNonIOGates_compilerInputFree :
    ∀ e ∈ paperPackingNonIOGates, CompilerInputFree e := by
  intro e he
  rw [← compilerInputFreeB_iff]
  have h : ∀ e ∈ paperPackingNonIOGates, compilerInputFreeB e := by decide
  exact h e he

theorem paperPackingRowLocal_compilerInputFree :
    ∀ e ∈ paperPackingRowLocal, CompilerInputFree e := by
  intro e he
  have : e ∈ paperPackingNonIOGates := by
    rw [paperPacking_eq_rowLocal_append]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl he)))
  exact paperPackingNonIOGates_compilerInputFree e this

theorem queueWitnessGates_compilerInputFree :
    ∀ e ∈ OptimizedComputeGateBasis.queueWitnessGates, CompilerInputFree e := by
  intro e he
  have : e ∈ paperPackingNonIOGates := by
    rw [paperPacking_eq_rowLocal_append]
    exact List.mem_append.mpr (Or.inr he)
  exact paperPackingNonIOGates_compilerInputFree e this
theorem exact_finalExtTransitionGatesWith
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F) :
    ∀ g ∈ paperPackingCoreGates ++ finalSampledIOTransitionGates,
      g.eval (exactFinalTransitionEnvWith A c i hi).toSourceEnv = 0 := by
  intro g hg
  rcases List.mem_append.mp hg with hcore | hio
  · have hpk : g ∈ paperPackingNonIOGates := mem_nonIO_of_mem_core hcore
    rw [exactFinalTransitionEnvWith,
      eval_withFinalComputeChallenges_of_free A (exactFinalTransitionEnv A i hi) c g
        (paperPackingNonIOGates_compilerInputFree g hpk)]
    exact (paperPacking_iff_sources _
        (R.problem.exec.computePubAt i).state
        (fun s => exactFinalTransitionEnv_selectors A i hi s)
        (exact_finalNonIOSourceFamilies17 A h i hi _ zZinv_mem_finalNonIO)).2
      (exact_finalNonIOSourceFamilies17 A h i hi) g hcore
  · rw [exactFinalTransitionEnvWith,
      eval_withFinalComputeChallenges_of_free A (exactFinalTransitionEnv A i hi) c g
        (final_compute_source_families_compilerInputFree.2.1 g hio)]
    exact exact_finalSampledIOTransitionGates A h i hi hsmall hwidth g hio

/-- The 76 successor-free production gates remain zero for every verifier tuple. -/
theorem exact_correctedFinalExtGate_currentWith
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (i : Fin R.problem.cfg.compRows)
    (hsmall : FormRAxisSmall A) (hwidth : FormRWidth F)
    (gate : CorrectedCoreExtGateId) (hgate : gate ∈ terminalCurrentExtGateIds) :
    (correctedFinalExtGate gate).eval (exactFinalCurrentEnvWith A c i) = 0 := by
  rw [← correctedFinalExtGate_eval_source]
  have hmem := finalExtGate_mem_terminalCurrent gate hgate
  have hzero := exact_terminalCurrentExtGates A h i hsmall hwidth _
    hmem
  by_cases hrow : finalExtTransitionGates.get ⟨gate, by simp⟩ ∈ paperPackingRowLocal
  · rw [exactFinalCurrentEnvWith,
      eval_withFinalComputeChallenges_of_free A (exactFinalCurrentEnv A i) c
        (finalExtTransitionGates.get ⟨gate, by simp⟩)
        (paperPackingRowLocal_compilerInputFree _ hrow)]
    exact hzero
  · rw [exactFinalCurrentEnvWith,
      eval_withFinalComputeChallenges_of_free A (exactFinalCurrentEnv A i) c
        (finalExtTransitionGates.get ⟨gate, by simp⟩)
        (by
          simp only [terminalCurrentExtGates, List.mem_append] at hmem
          rcases hmem with hmem | hmem
          · exact (hrow hmem).elim
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with h0 | h1 | h2
            · rw [h0]; exact final_compute_source_families_compilerInputFree.2.2.2 0
            · rw [h1]; exact final_compute_source_families_compilerInputFree.2.2.2 1
            · rw [h2]; exact final_compute_source_families_compilerInputFree.2.2.2 2)]
    exact hzero

#print axioms exactFinalTransitionEnv_table_current
#print axioms exact_computeAIR_row_substituted
#print axioms exact_finalNonIOSourceFamilies17
#print axioms exact_finalComputeCollisionFree
#print axioms exactFinalCurrentEnv_table_current
#print axioms terminalCurrentSourceFamilies_currentRowOnly
#print axioms exact_correctedFinalExtGate_current

end

end OptimizedComputeSameExecution
end Nock.NockVMROM.Thm54
