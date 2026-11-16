import Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
import Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.NockVMROM.Thm54.ComputePaperPacking
import Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate

/-!
# Same-object semantic realization of the corrected final compute RAP

This module is the connective between the corrected `199/98` coordinate compiler and one semantic
`13/62` environment.  It keeps the seventeen challenge-9 families, four sampled-IO equations,
endpoint equations, selector/public equalities, and three residual witnesses as distinct named
obligations.  No environment or witness is independently quantified inside the decomposition.

Paper scope: the paper.
The `13/62` sharing map remains the author-approved correctness delta recorded by the frame lock.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeSemanticRealization

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

open Classical
open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open OptimizedComputeBaseGates
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId FinalExtensionColumn
open OptimizedComputeFinalTrace
open OptimizedComputeFinalTypedLowering
open OptimizedComputeGateBasis
open OptimizedComputeRangeCertificate
open ComputePaperPacking
open OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

theorem coord_sub'
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {e : ℕ} (b : Basis (Fin e) F K) (x y : K) (k : Fin e) :
    coord b (x - y) k = coord b x k - coord b y k := by
  simp [coord]

theorem coord_zero'
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {e : ℕ} (b : Basis (Fin e) F K) (k : Fin e) :
    coord b (0 : K) k = 0 := by
  simp [coord]

theorem coord_algebraMap_mul
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {e : ℕ} (b : Basis (Fin e) F K) (a : F) (x : K) (k : Fin e) :
    coord b (algebraMap F K a * x) k = a * coord b x k := by
  rw [← Algebra.smul_def, coord_smul]
  rfl

/-! ## Exact positional partition of all 310 gates -/

inductive FinalGateBucket where
  | base
  | extensionCore
  | residualAux
  | endpointDegreeTwo
  | endpointDegreeFour
  | selectorEquality
deriving DecidableEq, Repr

/-- Positional partition of the `310` committed gates.  The degree-two endpoint bucket is
eighteen coordinates: two walk-initial gates (W3 stage 2 unfolded `challenge11`), walk-out,
the two accumulator anchors, and the line-number origin. -/
def finalGateBucket (i : Fin 310) : FinalGateBucket :=
  if (i : ℕ) < 15 then .base
  else if (i : ℕ) < 258 then .extensionCore
  else if (i : ℕ) < 267 then .residualAux
  else if (i : ℕ) < 285 then .endpointDegreeTwo
  else if (i : ℕ) < 288 then .endpointDegreeFour
  else .selectorEquality

def finalGateBucketIndices (b : FinalGateBucket) : Finset (Fin 310) :=
  Finset.univ.filter fun i => finalGateBucket i = b

theorem finalGateBucket_cardinality :
    (finalGateBucketIndices .base).card = 15 ∧
      (finalGateBucketIndices .extensionCore).card = 243 ∧
      (finalGateBucketIndices .residualAux).card = 9 ∧
      (finalGateBucketIndices .endpointDegreeTwo).card = 18 ∧
      (finalGateBucketIndices .endpointDegreeFour).card = 3 ∧
      (finalGateBucketIndices .selectorEquality).card = 22 := by
  decide

theorem finalGateBucket_pairwise_disjoint :
    Set.Pairwise (Set.univ : Set FinalGateBucket)
      (fun a b => Disjoint (finalGateBucketIndices a) (finalGateBucketIndices b)) := by
  intro a _ b _ hab
  rw [Finset.disjoint_left]
  intro i hi hj
  simp only [finalGateBucketIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hab (hi.symm.trans hj)

theorem finalGateBucket_exhaustive :
    finalGateBucketIndices .base ∪
        finalGateBucketIndices .extensionCore ∪
        finalGateBucketIndices .residualAux ∪
        finalGateBucketIndices .endpointDegreeTwo ∪
        finalGateBucketIndices .endpointDegreeFour ∪
        finalGateBucketIndices .selectorEquality =
      Finset.univ := by
  ext i
  simp only [finalGateBucketIndices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, iff_true]
  unfold finalGateBucket
  split_ifs <;> trivial

theorem corrected_gate_list_exact_partition
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) :
    correctedFinalComputeAllGates n b =
      finalBaseTransitionGates n ++ correctedCore b ++ correctedAux b ++
        correctedCompileList b correctedEndpoint2 ++
        correctedCompileList b correctedEndpoint4 ++
        finalEndpointEqualityChecks ++
        OptimizedComputeRangeCertificate.formRCertificateGates ++
        correctedCompileList b formRLamPins ++ computeExpGates := by
  rfl

/-! ## One-object source obligation decomposition -/

def notLastScalar
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) : K :=
  algebraMap F K (1 - env.baseTrace 12)

/-- Semantic value represented by one of the 81 extension-core gate positions.  Positions
`73,74` (`lnChain`, `walkLn`) are directly last-row masked; positions `75,76,80` read the three
residual / chain slots (W3 stage 2; were `8,9` / `10,11,20`). -/
def correctedCoreSemanticValue
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (i : CorrectedCoreExtGateId) : K :=
  if i = packedWalkCountId then notLastScalar env * env.extTrace (residualWitnessRole 0)
  else if i = packedWalkAccId then notLastScalar env * env.extTrace (residualWitnessRole 1)
  else if i = packedChainId then accAfterChain.eval env
  else if i = packedLnChainId ∨ i = packedWalkLnId then
    notLastScalar env * (correctedFinalExtGate i).eval env
  else (correctedFinalExtGate i).eval env

/-- Positions `0, 1` are the two exact residual pins; position `2` is the unmasked anchored
accumulator step against `acc_after` (role `60`) — A-comp anchoring stage. -/
def correctedAuxSemanticValue
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (j : CorrectedResidualWitnessId) : K :=
  if j = 2 then correctedAccAfterStep.eval env
  else env.extTrace (residualWitnessRole j) - (correctedFinalResidualSource j).eval env

/-- Exact source-side decomposition of the corrected 98-gate object.  Every field refers to the
same `env`/`envF`; there are no independently quantified rows, records, coins, or witnesses. -/
structure CorrectedComputeSourceObligations
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (env : CorrectedFinalTypedEnv F K) (envF : Env F) : Prop where
  base15 :
    ∀ g ∈ finalBaseTransitionGates n, g.eval envF = 0
  extensionCore21 :
    ∀ i : CorrectedCoreExtGateId, correctedCoreSemanticValue env i = 0
  residualAux3 :
    ∀ j : CorrectedResidualWitnessId, correctedAuxSemanticValue env j = 0
  endpointDegreeTwo2 :
    ∀ t ∈ correctedEndpoint2, t.eval env = 0
  endpointDegreeFour1 :
    ∀ t ∈ correctedEndpoint4, t.eval env = 0
  selectorEquality2 :
    ∀ g ∈ finalEndpointEqualityChecks, g.eval envF = 0
  formR99 :
    ∀ g ∈ formRCertificateGates, g.eval envF = 0
  /-- The two Form R `𝕂` power pins at the `𝕂` coin `λ`. -/
  formRLam :
    ∀ t ∈ formRLamPins, t.eval env = 0
  /-- **The 31st:** the two exponent-carrier gates `isFirst · S = 0` and
  `(1 − isLast)·(S(i+1) − S(i) − arity(i)) = 0` (base field, column `302`). -/
  expGates :
    ∀ g ∈ computeExpGates (F := F), g.eval envF = 0

theorem correctedCoreCoord_eval
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF)
    (i : CorrectedCoreExtGateId) (k : Fin 3) :
    (correctedCoreCoord b i k).eval envF =
      coord b (correctedCoreSemanticValue env i) k := by
  by_cases h10 : i = packedWalkCountId
  · subst i
    have hb := henv.baseTrace (12 : Fin 13)
    have hb' : envF.trace 12 = env.baseTrace 12 := by simpa using hb
    have he := henv.extTrace (residualWitnessRole 0) k
    have he' :
        envF.trace ↑(OptimizedComputeFinal.finalExtCoordIndex
            (OptimizedComputeFinal.residualWitnessRole 0) k) =
          coord b (env.extTrace (residualWitnessRole 0)) k := by
      simpa [OptimizedComputeFinal.finalExtCoordIndex,
        OptimizedComputeFinal.residualWitnessRole, correctedFinalExtCoordIndex,
        residualWitnessRole] using he
    simp only [correctedCoreCoord, correctedCoreSemanticValue, notLastScalar,
      notLastCoeff, isLastVar, bv, residualWitnessCoord, CoeffExpr.eval,
      packedWalkCountId, packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId,
      if_pos, Fin.isValue]
    rw [hb', he']
    rw [coord_algebraMap_mul]
  by_cases h11 : i = packedWalkAccId
  · subst i
    have hb := henv.baseTrace (12 : Fin 13)
    have hb' : envF.trace 12 = env.baseTrace 12 := by simpa using hb
    have he := henv.extTrace (residualWitnessRole 1) k
    have he' :
        envF.trace ↑(OptimizedComputeFinal.finalExtCoordIndex
            (OptimizedComputeFinal.residualWitnessRole 1) k) =
          coord b (env.extTrace (residualWitnessRole 1)) k := by
      simpa [OptimizedComputeFinal.finalExtCoordIndex,
        OptimizedComputeFinal.residualWitnessRole, correctedFinalExtCoordIndex,
        residualWitnessRole] using he
    simp only [correctedCoreCoord, correctedCoreSemanticValue, notLastScalar,
      notLastCoeff, isLastVar, bv, residualWitnessCoord, CoeffExpr.eval,
      packedWalkCountId, packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId,
      h10, if_false, if_pos, Fin.isValue]
    rw [hb', he']
    rw [coord_algebraMap_mul]
  by_cases h20 : i = packedChainId
  · subst i
    simp only [correctedCoreCoord, correctedCoreSemanticValue,
      packedWalkCountId, packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId,
      h10, h11, if_false, if_pos rfl]
    exact (correctedFinalTypedCompile_eval b env envF henv accAfterChain k).symm
  by_cases h89 : i = packedLnChainId ∨ i = packedWalkLnId
  · simp only [correctedCoreCoord, correctedCoreSemanticValue,
      packedWalkCountId, packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId,
      h10, h11, h20, h89,
      if_false, if_true, notLastCoeff, isLastVar, bv, CoeffExpr.eval]
    have hb := henv.baseTrace (12 : Fin 13)
    have hb' : envF.trace 12 = env.baseTrace 12 := by simpa using hb
    rw [hb', ← correctedFinalTypedCompile_eval b env envF henv]
    change (1 - env.baseTrace 12) * coord b ((correctedFinalExtGate i).eval env) k =
      coord b (algebraMap F K (1 - env.baseTrace 12) *
        (correctedFinalExtGate i).eval env) k
    rw [
      coord_algebraMap_mul]
  · simp only [correctedCoreCoord, correctedCoreSemanticValue,
      packedWalkCountId, packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId,
      h10, h11, h20, h89,
      if_false]
    exact (correctedFinalTypedCompile_eval b env envF henv
      (correctedFinalExtGate i) k).symm

theorem correctedAuxCoord_eval
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF)
    (j : CorrectedResidualWitnessId) (k : Fin 3) :
    (correctedAuxCoord b j k).eval envF =
      coord b (correctedAuxSemanticValue env j) k := by
  by_cases h2 : j = 2
  · subst j
    simp only [correctedAuxCoord, correctedAuxSemanticValue, if_pos rfl]
    exact (correctedFinalTypedCompile_eval b env envF henv correctedAccAfterStep k).symm
  simp only [correctedAuxCoord, correctedAuxSemanticValue, h2, if_false, CoeffExpr.eval,
    coord_sub']
  have he := henv.extTrace (residualWitnessRole j) k
  have he' :
      envF.trace ↑(OptimizedComputeFinal.finalExtCoordIndex
          (OptimizedComputeFinal.residualWitnessRole j) k) =
        coord b (env.extTrace (residualWitnessRole j)) k := by
    simpa [OptimizedComputeFinal.finalExtCoordIndex,
      OptimizedComputeFinal.residualWitnessRole, correctedFinalExtCoordIndex,
      residualWitnessRole] using he
  simp only [residualWitnessCoord, CoeffExpr.eval]
  rw [he', ← correctedFinalTypedCompile_eval b env envF henv]

theorem correctedCompileList_eval_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF)
    (ts : List CorrectedFinalTypedExpr) :
    (∀ g ∈ correctedCompileList b ts, g.eval envF = 0) ↔
      ∀ t ∈ ts, t.eval env = 0 := by
  constructor
  · intro h t ht
    apply (correctedFinalTypedCompile_zero_iff b env envF henv t).1
    intro k
    apply h
    rw [correctedCompileList]
    exact List.mem_flatten.mpr
      ⟨List.ofFn (correctedFinalTypedCompile b t), List.mem_map.mpr ⟨t, ht, rfl⟩,
        List.mem_ofFn.mpr ⟨k, rfl⟩⟩
  · intro h g hg
    rw [correctedCompileList] at hg
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact (correctedFinalTypedCompile_zero_iff b env envF henv t).2 (h t ht) k

theorem correctedCore_eval_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF) :
    (∀ g ∈ correctedCore b, g.eval envF = 0) ↔
      ∀ i : CorrectedCoreExtGateId, correctedCoreSemanticValue env i = 0 := by
  constructor
  · intro h i
    rw [eq_iff_coords_eq b (correctedCoreSemanticValue env i) 0]
    intro k
    rw [coord_zero' b k, ← correctedCoreCoord_eval b env envF henv i k]
    apply h
    rw [correctedCore]
    exact List.mem_flatten.mpr
      ⟨List.ofFn (correctedCoreCoord b i), List.mem_ofFn.mpr ⟨i, rfl⟩,
        List.mem_ofFn.mpr ⟨k, rfl⟩⟩
  · intro h g hg
    rw [correctedCore] at hg
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    rw [correctedCoreCoord_eval b env envF henv, h i, coord_zero' b k]

theorem correctedAux_eval_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF) :
    (∀ g ∈ correctedAux b, g.eval envF = 0) ↔
      ∀ j : CorrectedResidualWitnessId, correctedAuxSemanticValue env j = 0 := by
  constructor
  · intro h j
    rw [eq_iff_coords_eq b (correctedAuxSemanticValue env j) 0]
    intro k
    rw [coord_zero' b k, ← correctedAuxCoord_eval b env envF henv j k]
    apply h
    rw [correctedAux]
    exact List.mem_flatten.mpr
      ⟨List.ofFn (correctedAuxCoord b j), List.mem_ofFn.mpr ⟨j, rfl⟩,
        List.mem_ofFn.mpr ⟨k, rfl⟩⟩
  · intro h g hg
    rw [correctedAux] at hg
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    rw [correctedAuxCoord_eval b env envF henv, h j, coord_zero' b k]

/-- Exact gate-compilation equivalence for all 98 constraints on one same-object environment. -/
theorem correctedFinalComputeAllGates_eval_iff_source
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (n : ℕ) (b : Basis (Fin 3) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF) :
    (∀ g ∈ correctedFinalComputeAllGates n b, g.eval envF = 0) ↔
      CorrectedComputeSourceObligations n env envF := by
  simp only [correctedFinalComputeAllGates, List.forall_mem_append]
  rw [correctedCore_eval_iff b env envF henv,
    correctedAux_eval_iff b env envF henv,
    correctedCompileList_eval_iff b env envF henv correctedEndpoint2,
    correctedCompileList_eval_iff b env envF henv correctedEndpoint4,
    correctedCompileList_eval_iff b env envF henv formRLamPins]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hb, hc⟩, ha⟩, h2⟩, h4⟩, heq⟩, hform⟩, hlam⟩, hexp⟩
    exact ⟨hb, hc, ha, h2, h4, heq, hform, hlam, hexp⟩
  · rintro ⟨hb, hc, ha, h2, h4, heq, hform, hlam, hexp⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hb, hc⟩, ha⟩, h2⟩, h4⟩, heq⟩, hform⟩, hlam⟩, hexp⟩

/-! ## Unconditional decoding from any physical trace -/

/-- Reassemble one corrected semantic environment from one physical `199`-column environment.
This is the arbitrary-trace decoder used by the B29-facing API. -/
def gatherCorrectedFinalTypedEnv
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (envF : Env F) : CorrectedFinalTypedEnv F K where
  baseTrace i := envF.trace i
  baseTraceNext i := envF.traceNext i
  extTrace i :=
    ∑ k : Fin 3, envF.trace (correctedFinalExtCoordIndex i k) • b k
  extTraceNext i :=
    ∑ k : Fin 3, envF.traceNext (correctedFinalExtCoordIndex i k) • b k
  chal i :=
    ∑ k : Fin 3, envF.chal (3 * (i : ℕ) + (k : ℕ)) • b k
  extensionPublic i :=
    ∑ k : Fin 3, envF.pub (3 * (i : ℕ) + (k : ℕ)) • b k
  scalarPublic i := envF.pub (20 + (i : ℕ))
  certBase i := envF.trace (202 + (i : ℕ))
  certExt i :=
    ∑ k : Fin 3, envF.trace (296 + 3 * (i : ℕ) + (k : ℕ)) • b k
  certBaseNext i := envF.traceNext (202 + (i : ℕ))
  certExtNext i :=
    ∑ k : Fin 3, envF.traceNext (296 + 3 * (i : ℕ) + (k : ℕ)) • b k
  expCol := envF.trace 302
  expColNext := envF.traceNext 302

theorem isCorrectedFinalCoordEnv_gather
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (envF : Env F) :
    IsCorrectedFinalCoordEnv b (gatherCorrectedFinalTypedEnv b envF) envF where
  baseTrace := fun _ => rfl
  baseTraceNext := fun _ => rfl
  extTrace := fun i k =>
    (coord_sum_smul b
      (fun j => envF.trace (correctedFinalExtCoordIndex i j)) k).symm
  extTraceNext := fun i k =>
    (coord_sum_smul b
      (fun j => envF.traceNext (correctedFinalExtCoordIndex i j)) k).symm
  chal := fun i k =>
    (coord_sum_smul b
      (fun j => envF.chal (3 * (i : ℕ) + (j : ℕ))) k).symm
  extensionPublic := fun i k =>
    (coord_sum_smul b
      (fun j => envF.pub (3 * (i : ℕ) + (j : ℕ))) k).symm
  scalarPublic := fun _ => rfl
  certBase := fun _ => rfl
  certExt := fun i k =>
    (coord_sum_smul b
      (fun j => envF.trace (296 + 3 * (i : ℕ) + (j : ℕ))) k).symm
  expCol := rfl

/-- Every arbitrary physical row satisfies the corrected 98 compiled equations iff its
unconditionally gathered same-object semantic environment satisfies the exact six-bucket source
decomposition. -/
theorem correctedFinalComputeAllGates_eval_iff_gathered_source
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (n : ℕ) (b : Basis (Fin 3) F K) (envF : Env F) :
    (∀ g ∈ correctedFinalComputeAllGates n b, g.eval envF = 0) ↔
      CorrectedComputeSourceObligations n
        (gatherCorrectedFinalTypedEnv b envF) envF :=
  correctedFinalComputeAllGates_eval_iff_source n b _ envF
    (isCorrectedFinalCoordEnv_gather b envF)

def CorrectedFinalComputeSourceLanguage
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) : Prop :=
  (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing P ∧
    ∀ x ∈ rowNodeSet nodes,
      let envF := envOfTrace P orbit.ω x chalVal pubVal
      CorrectedComputeSourceObligations n
        (gatherCorrectedFinalTypedEnv b envF) envF

/-- Corrected production satisfaction is exactly the gathered same-object source language, for
arbitrary traces. -/
theorem productionNamedComputeRAP_satisfies_iff_sourceLanguage
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit) P ↔
      CorrectedFinalComputeSourceLanguage hn nodes b chalVal pubVal orbit P := by
  rw [productionNamedComputeRAP_satisfies_iff_compiledLanguage]
  simp only [CorrectedFinalComputeCompiledLanguage, CorrectedFinalComputeSourceLanguage]
  apply and_congr Iff.rfl
  constructor
  · intro hall x hx
    exact (correctedFinalComputeAllGates_eval_iff_gathered_source n b _).1
      (hall x hx)
  · intro hall x hx
    exact (correctedFinalComputeAllGates_eval_iff_gathered_source n b _).2
      (hall x hx)

/-- Generic canonical-satisfaction constructor: once the one same-object assignment has discharged
the gathered source obligations at every encoded row, no further compiler or trace hypothesis is
needed. -/
theorem correctedCanonicalFinalTrace_satisfies_of_source
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (hsource : ∀ i : Fin R.problem.cfg.compRows,
      let envF := envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal
      CorrectedComputeSourceObligations R.problem.cfg.compRows
        (gatherCorrectedFinalTypedEnv b envF) envF) :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit)
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit) := by
  erw [productionNamedComputeRAP_satisfies_iff_sourceLanguage]
  refine ⟨correctedCanonicalFinalTrace_binds_preprocessing
    A hn nodes b chalVal pubVal orbit, ?_⟩
  intro x hx
  obtain ⟨i, ⟨_, hix⟩⟩ := Finset.mem_image.mp hx
  subst x
  exact hsource i

/-! ## Same-assignment canonical base block -/

theorem correctedCanonicalFinalTrace_base_eval
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (j : Fin 13) :
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal).trace j =
        finalBaseCell A hn i j := by
  simp only [envOfTrace, dif_pos (show (j : ℕ) < 303 by omega)]
  rw [correctedCanonicalFinalTrace_eval A hn nodes hnodes]
  have h296 : ¬ (296 ≤ (j : ℕ) ∧ (j : ℕ) < 299) := by omega
  have h299 : ¬ (299 ≤ (j : ℕ)) := by omega
  simp [preliminaryCell, h296, h299]

theorem eleven_lt_thirteen : 11 < 13 := by decide

theorem finalBaseCell_selector
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (i : Fin R.problem.cfg.compRows) (j : Fin 11) :
    finalBaseCell A hn i ⟨j, Nat.lt_trans j.isLt eleven_lt_thirteen⟩ =
      if j = OptimizedComputeCodec.stateIndex
          (R.problem.exec.computePubAt i).state then 1 else 0 := by
  simp [finalBaseCell, OptimizedComputeSampledTrace.encodedRowAt,
    OptimizedComputeOverlay.sampledEncode, OptimizedComputeCodec.encodeBase]

/-- Base15 is discharged directly by the selector and fixed-mask values of the same canonical
encoded row; neither a separately quantified base environment nor a collision hypothesis appears. -/
theorem correctedCanonicalFinalTrace_base15
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    ∀ g ∈ finalBaseTransitionGates R.problem.cfg.compRows, g.eval envF = 0 := by
  dsimp only
  intro g hg
  simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨j, hj, rfl⟩ | rfl | rfl | rfl | rfl
  · have htrace := correctedCanonicalFinalTrace_base_eval
      A hn nodes hnodes b chalVal pubVal orbit i ⟨j, by omega⟩
    have hsel := finalBaseCell_selector A hn i ⟨j, hj⟩
    rw [show (⟨j, by omega⟩ : Fin 13) = ⟨(⟨j, hj⟩ : Fin 11), by omega⟩ by rfl] at htrace
    rw [hsel] at htrace
    simp only [selectorBool, bv, CoeffExpr.eval]
    rw [htrace]
    by_cases heq : (⟨j, hj⟩ : Fin 11) =
        OptimizedComputeCodec.stateIndex (R.problem.exec.computePubAt i).state <;>
      simp [heq]
  · have htrace : ∀ (j : ℕ) (hj : j < 11),
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal).trace j =
          if (⟨j, hj⟩ : Fin 11) = OptimizedComputeCodec.stateIndex
              (R.problem.exec.computePubAt i).state then 1 else 0 := by
      intro j hj
      have hb := correctedCanonicalFinalTrace_base_eval
        A hn nodes hnodes b chalVal pubVal orbit i (⟨j, by omega⟩ : Fin 13)
      have hs := finalBaseCell_selector A hn i (⟨j, hj⟩ : Fin 11)
      simpa using hb.trans hs
    have h0 := htrace 0 (by omega); have h1 := htrace 1 (by omega)
    have h2 := htrace 2 (by omega); have h3 := htrace 3 (by omega)
    have h4 := htrace 4 (by omega); have h5 := htrace 5 (by omega)
    have h6 := htrace 6 (by omega); have h7 := htrace 7 (by omega)
    have h8 := htrace 8 (by omega); have h9 := htrace 9 (by omega)
    have h10 := htrace 10 (by omega)
    norm_num [selectorOneHot, selectorSum, CoeffExpr.sumList, bv, CoeffExpr.eval,
      List.range, List.range.loop]
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    cases hs : (R.problem.exec.computePubAt i).state <;>
      simp [OptimizedComputeCodec.stateIndex]
  · have hfirst := correctedCanonicalFinalTrace_base_eval
      A hn nodes hnodes b chalVal pubVal orbit i (11 : Fin 13)
    have hfirst' :
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal).trace 11 =
          finalBaseCell A hn i 11 := by simpa using hfirst
    simp only [firstMaskBoolean, isFirstVar, bv, CoeffExpr.eval]
    rw [hfirst']
    by_cases hi : (i : ℕ) = 0 <;>
      simp [finalBaseCell, hi]
  · have hlast := correctedCanonicalFinalTrace_base_eval
      A hn nodes hnodes b chalVal pubVal orbit i (12 : Fin 13)
    have hlast' :
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal).trace 12 =
          finalBaseCell A hn i 12 := by simpa using hlast
    simp only [lastMaskBoolean, isLastVar, bv, CoeffExpr.eval]
    rw [hlast']
    by_cases hi : i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ <;>
      simp [finalBaseCell, hi]
  · have hfirst := correctedCanonicalFinalTrace_base_eval
      A hn nodes hnodes b chalVal pubVal orbit i (11 : Fin 13)
    have hlast := correctedCanonicalFinalTrace_base_eval
      A hn nodes hnodes b chalVal pubVal orbit i (12 : Fin 13)
    have hfirst' :
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal).trace 11 =
          finalBaseCell A hn i 11 := by simpa using hfirst
    have hlast' :
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal).trace 12 =
          finalBaseCell A hn i 12 := by simpa using hlast
    by_cases hn1 : R.problem.cfg.compRows = 1
    · simp only [endpointOverlapConsistency, hn1, if_true, CoeffExpr.eval,
        isFirstVar, isLastVar, bv]
      rw [hfirst', hlast']
      have hnrows := hn1
      have hi0 : i = ⟨0, by omega⟩ := by
        apply Fin.ext
        omega
      subst i
      simp [hnrows, finalBaseCell]
    · simp only [endpointOverlapConsistency, hn1, if_false, CoeffExpr.eval,
        isFirstVar, isLastVar, bv]
      rw [hfirst', hlast']
      by_cases hzero : (i : ℕ) = 0
      · by_cases hlastEq :
          i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
        · exfalso
          apply hn1
          have hv := congrArg Fin.val hlastEq
          simp only at hv
          omega
        · simp [finalBaseCell, hzero, hlastEq]
      · simp [finalBaseCell, hzero]

/-! ## Collision-conditioned arbitrary-trace decoding -/


theorem finalExtTransitionGates_get20 :
    finalExtTransitionGates.get ⟨((packedChainId : CorrectedCoreExtGateId) : ℕ), by simp⟩ =
      OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3.subst finalSampledNamespace := by
  decide


theorem correctedAccAfterStep_eval_eq_fold
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K)
    (h : env.extTrace 60 = env.extTraceNext 32) :
    correctedAccAfterStep.eval env = (correctedFinalExtGate packedChainId).eval env := by
  rw [← correctedLowerFinal_eval env _ _ correctedLowerFinal_accAfterStep,
    ← correctedFinalExtGate_eval_source, finalExtTransitionGates_get20,
    finalAccAfterStep, Expr.eval_subst, Expr.eval_subst]
  apply OptimizedComputeFiniteIOGates.optimizedAccAfterStep_eval_eq_fold
  change (finalSampledNamespace .traceCur OptimizedComputeFiniteIOGates.accAfterIndex).eval
      env.toSourceEnv =
    (overlayCoord .traceNext 5).eval (Env.ofSubst finalSampledNamespace env.toSourceEnv)
  simp only [finalSampledNamespace, overlayCoord, pubFP, ext0, Expr.eval, Env.ofSubst,
    OptimizedComputeFiniteIOGates.accAfterIndex, CorrectedFinalTypedEnv.toSourceEnv]
  norm_num
  exact h

theorem corrected_ext_gate_zero_of_source_obligations
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF)
    (hnotLast : env.baseTrace 12 = 0)
    (i : CorrectedCoreExtGateId) :
    (correctedFinalExtGate i).eval env = 0 := by
  have hc := hsource.extensionCore21 i
  by_cases h10 : i = packedWalkCountId
  · subst i
    have ha := hsource.residualAux3 0
    simp [correctedCoreSemanticValue, notLastScalar, hnotLast, packedWalkCountId,
      packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId] at hc
    have heq : env.extTrace (residualWitnessRole 0) =
        (correctedFinalExtGate packedWalkCountId).eval env := by
      exact sub_eq_zero.mp (by simpa [correctedAuxSemanticValue,
        correctedFinalResidualSource] using ha)
    rw [← heq]
    exact hc
  by_cases h11 : i = packedWalkAccId
  · subst i
    have ha := hsource.residualAux3 1
    simp [correctedCoreSemanticValue, notLastScalar, hnotLast, packedWalkCountId,
      packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId] at hc
    have heq : env.extTrace (residualWitnessRole 1) =
        (correctedFinalExtGate packedWalkAccId).eval env := by
      exact sub_eq_zero.mp (by simpa [correctedAuxSemanticValue,
        correctedFinalResidualSource] using ha)
    rw [← heq]
    exact hc
  by_cases h20 : i = packedChainId
  · subst i
    have ha := hsource.residualAux3 2
    simp only [correctedAuxSemanticValue, if_pos rfl] at ha
    have hchain : env.extTrace 60 = env.extTraceNext 32 := by
      simpa [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
        packedLnChainId, packedWalkLnId, h10, h11, accAfterChain,
        CorrectedFinalTypedExpr.eval, hnotLast, sub_eq_zero] using hc
    rw [← correctedAccAfterStep_eval_eq_fold env hchain]
    exact ha
  by_cases h89 : i = packedLnChainId ∨ i = packedWalkLnId
  · simp only [correctedCoreSemanticValue] at hc
    simp only [h10, h11, h20, h89, ↓reduceIte, notLastScalar, hnotLast, sub_zero, map_one,
      one_mul] at hc
    exact hc
  · simp only [correctedCoreSemanticValue] at hc
    simp only [h10, h11, h20, h89, ↓reduceIte, notLastScalar, hnotLast] at hc
    exact hc

theorem corrected_extension_sources_of_source_obligations
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF)
    (hnotLast : env.baseTrace 12 = 0) :
    ∀ g ∈ finalExtTransitionGates, g.eval env.toSourceEnv = 0 := by
  intro g hg
  obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
  rw [← hget]; erw [correctedFinalExtGate_eval_source]
  exact corrected_ext_gate_zero_of_source_obligations hsource hnotLast i

structure CorrectedDecodedTransitionSources
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) : Prop where
  nonIO :
    ∀ e ∈ paperPackingCoreGates, e.eval env.toSourceEnv = 0
  sampledIOSafe4 :
    ∀ e ∈ finalSampledIOTransitionGates, e.eval env.toSourceEnv = 0

/-- On any nonterminal compiled row the packed (coin-free) non-IO gates and the four sampled-IO
source equations vanish.  No fold-collision hypothesis: the chip commits the packed set
directly (W3 stage 2).  Equivalence with the 511 atomic sources is `paperPacking_iff_sources`
at a one-hot selector (`ComputePaperPacking`). -/
theorem corrected_conditional_transition_soundness
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF)
    (hnotLast : env.baseTrace 12 = 0) :
    CorrectedDecodedTransitionSources env := by
  have hall := corrected_extension_sources_of_source_obligations hsource hnotLast
  have hnonIO : ∀ g ∈ paperPackingCoreGates, g.eval env.toSourceEnv = 0 := by
    intro g hg
    exact hall g (List.mem_append.mpr (Or.inl (mem_nonIO_of_mem_core hg)))
  have hio : ∀ g ∈ finalSampledIOTransitionGates, g.eval env.toSourceEnv = 0 := by
    intro g hg
    exact hall g (List.mem_append.mpr (Or.inr hg))
  exact { nonIO := hnonIO, sampledIOSafe4 := hio }

/-! ## Canonical residual pins -/

def CorrectedResidualFree : CorrectedFinalTypedExpr → Prop
  | .extCur i | .extNext i => (i : ℕ) < 58 ∨ (i : ℕ) = 61 ∨ (i : ℕ) = 62
  | .baseCur _ | .baseNext _ | .challenge _ | .extensionPublic _
  | .scalarPublic _ | .const _ | .lamPow _ => True
  | .certBase _ | .certExt _ | .expCur => False
  | .add x y | .sub x y | .mul x y =>
      CorrectedResidualFree x ∧ CorrectedResidualFree y
  | .neg x | .pow x _ => CorrectedResidualFree x

def correctedResidualFreeB : CorrectedFinalTypedExpr → Bool
  | .extCur i | .extNext i => (i : ℕ) < 58 || (i : ℕ) == 61 || (i : ℕ) == 62
  | .baseCur _ | .baseNext _ | .challenge _ | .extensionPublic _
  | .scalarPublic _ | .const _ | .lamPow _ => true
  | .certBase _ | .certExt _ | .expCur => false
  | .add x y | .sub x y | .mul x y =>
      correctedResidualFreeB x && correctedResidualFreeB y
  | .neg x | .pow x _ => correctedResidualFreeB x

theorem correctedResidualFreeB_iff (t : CorrectedFinalTypedExpr) :
    correctedResidualFreeB t ↔ CorrectedResidualFree t := by
  induction t <;>
    simp [correctedResidualFreeB, CorrectedResidualFree, or_assoc, *]

theorem correctedFinalResidualSource_residualFree :
    ∀ j : CorrectedResidualWitnessId,
      CorrectedResidualFree (correctedFinalResidualSource j) := by
  intro j
  rw [← correctedResidualFreeB_iff]
  fin_cases j <;> decide

theorem CorrectedFinalTypedExpr.eval_eq_of_residualFree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ i, a.baseTrace i = b.baseTrace i)
    (hbaseNext : ∀ i, a.baseTraceNext i = b.baseTraceNext i)
    (hext : ∀ i : Fin 63, (i : ℕ) < 58 ∨ (i : ℕ) = 61 ∨ (i : ℕ) = 62 →
      a.extTrace i = b.extTrace i)
    (hextNext : ∀ i : Fin 63, (i : ℕ) < 58 ∨ (i : ℕ) = 61 ∨ (i : ℕ) = 62 →
      a.extTraceNext i = b.extTraceNext i)
    (hchal : ∀ i, a.chal i = b.chal i)
    (hextPub : ∀ i, a.extensionPublic i = b.extensionPublic i)
    (hscalarPub : ∀ i, a.scalarPublic i = b.scalarPublic i)
    (t : CorrectedFinalTypedExpr) (ht : CorrectedResidualFree t) :
    t.eval a = t.eval b := by
  revert ht
  induction t with
  | baseCur i => intro; simp [CorrectedFinalTypedExpr.eval, hbase]
  | baseNext i => intro; simp [CorrectedFinalTypedExpr.eval, hbaseNext]
  | extCur i => intro ht; simpa [CorrectedFinalTypedExpr.eval] using hext i ht
  | extNext i => intro ht; simpa [CorrectedFinalTypedExpr.eval] using hextNext i ht
  | challenge i => intro; simp [CorrectedFinalTypedExpr.eval, hchal]
  | extensionPublic i => intro; simp [CorrectedFinalTypedExpr.eval, hextPub]
  | scalarPublic i => intro; simp [CorrectedFinalTypedExpr.eval, hscalarPub]
  | const c => intro; rfl
  | add x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· + ·)
        (ihx ht.1) (ihy ht.2)
  | sub x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· - ·)
        (ihx ht.1) (ihy ht.2)
  | mul x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· * ·)
        (ihx ht.1) (ihy ht.2)
  | neg x ih =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg Neg.neg (ih ht)
  | pow x m ih =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg (fun z => z ^ m) (ih ht)
  | certBase i => intro ht; exact ht.elim
  | certExt i => intro ht; exact ht.elim
  | lamPow d => intro; simp [CorrectedFinalTypedExpr.eval, hchal]
  | expCur => intro ht; exact ht.elim

theorem correctedCanonicalFinalTrace_eq_preliminary_of_role
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin 63) (hi : (i : ℕ) < 58 ∨ 60 ≤ (i : ℕ)) (k : Fin 3) :
    correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit
        ⟨correctedFinalExtCoordIndex i k, by
          simp [correctedFinalExtCoordIndex]
          omega⟩ =
      preliminaryTrace A hn nodes b
        ⟨correctedFinalExtCoordIndex i k, by
          simp [correctedFinalExtCoordIndex]
          omega⟩ := by
  simp only [correctedCanonicalFinalTrace]
  have h296 : ¬ (296 ≤ (correctedFinalExtCoordIndex i k : ℕ) ∧
      (correctedFinalExtCoordIndex i k : ℕ) < 299) := by
    simp [correctedFinalExtCoordIndex]; omega
  have h299 : ¬ (299 ≤ (correctedFinalExtCoordIndex i k : ℕ)) := by
    simp [correctedFinalExtCoordIndex]; omega
  rw [dif_neg h296, dif_neg h299]
  split_ifs with hres
  · simp [correctedFinalExtCoordIndex] at hres
    omega
  · rfl

/-- **Role `60` of the canonical trace is `acc_after`**: at row `i` it evaluates to the
co-resident request accumulator after row `i` (A-comp anchoring stage). -/
theorem correctedCanonicalFinalTrace_accAfter_eval
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (k : Fin 3) :
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit
        ⟨correctedFinalExtCoordIndex (60 : Fin 63) k, by
          simp [correctedFinalExtCoordIndex]; omega⟩).eval (nodes i) =
      coord b (ComputeSampledIO.coResidentAccC A.compress10
        R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1)) k := by
  rw [correctedCanonicalFinalTrace_eq_preliminary_of_role A hn nodes b chalVal pubVal orbit
    (60 : Fin 63) (Or.inr (by norm_num)) k, preliminaryTrace_eval A hn nodes hnodes b i]
  have hdiv : (correctedFinalExtCoordIndex (60 : Fin 63) k - 13) / 3 = 60 := by
    simp [correctedFinalExtCoordIndex]; omega
  have hmod : (correctedFinalExtCoordIndex (60 : Fin 63) k - 13) % 3 = (k : ℕ) := by
    simp [correctedFinalExtCoordIndex]; omega
  have h13 : ¬ correctedFinalExtCoordIndex (60 : Fin 63) k < 13 := by
    simp only [correctedFinalExtCoordIndex]; omega
  have hleaf : ¬ ((correctedFinalExtCoordIndex (60 : Fin 63) k : ℕ) = 136 ∨
      (correctedFinalExtCoordIndex (60 : Fin 63) k : ℕ) = 145) := by
    simp only [correctedFinalExtCoordIndex]; omega
  simp only [preliminaryCell, h13, hleaf, dif_neg, not_false_eq_true, hdiv, hmod]
  simp

theorem correctedCanonical_residualSource_eval_eq_preliminary
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (row : Fin R.problem.cfg.compRows) (j : CorrectedResidualWitnessId) :
    let envFinal := gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes row) chalVal pubVal)
    let envPre := gatherCorrectedFinalTypedEnv b
      (envOfTrace (preliminaryTrace A hn nodes b)
        orbit.ω (nodes row) chalVal pubVal)
    (correctedFinalResidualSource j).eval envFinal =
      (correctedFinalResidualSource j).eval envPre := by
  dsimp only
  apply CorrectedFinalTypedExpr.eval_eq_of_residualFree
  · intro q
    simp only [gatherCorrectedFinalTypedEnv, envOfTrace]
    have hq296 : ¬ (296 ≤ (q : ℕ) ∧ (q : ℕ) < 299) := by omega
    have hq299 : ¬ (299 ≤ (q : ℕ)) := by omega
    simp [correctedCanonicalFinalTrace, hq296, hq299,
      show (q : ℕ) < 303 by omega, show (q : ℕ) < 302 by omega]
  · intro q
    simp only [gatherCorrectedFinalTypedEnv, envOfTrace]
    have hq296 : ¬ (296 ≤ (q : ℕ) ∧ (q : ℕ) < 299) := by omega
    have hq299 : ¬ (299 ≤ (q : ℕ)) := by omega
    simp [correctedCanonicalFinalTrace, hq296, hq299,
      show (q : ℕ) < 303 by omega, show (q : ℕ) < 302 by omega]
  · intro role hrole
    simp only [gatherCorrectedFinalTypedEnv]
    apply Finset.sum_congr rfl
    intro k _
    simp only [envOfTrace, dif_pos (show correctedFinalExtCoordIndex role k < 302 by
      simp [correctedFinalExtCoordIndex]
      omega), dif_pos (show correctedFinalExtCoordIndex role k < 303 by
      simp [correctedFinalExtCoordIndex]
      omega)]
    rw [correctedCanonicalFinalTrace_eq_preliminary_of_role
      A hn nodes b chalVal pubVal orbit role (by rcases hrole with h | h | h <;> omega) k]
  · intro role hrole
    simp only [gatherCorrectedFinalTypedEnv]
    apply Finset.sum_congr rfl
    intro k _
    simp only [envOfTrace, dif_pos (show correctedFinalExtCoordIndex role k < 302 by
      simp [correctedFinalExtCoordIndex]
      omega), dif_pos (show correctedFinalExtCoordIndex role k < 303 by
      simp [correctedFinalExtCoordIndex]
      omega)]
    rw [correctedCanonicalFinalTrace_eq_preliminary_of_role
      A hn nodes b chalVal pubVal orbit role (by rcases hrole with h | h | h <;> omega) k]
  · intro q
    rfl
  · intro q
    rfl
  · intro q
    rfl
  · exact correctedFinalResidualSource_residualFree j

/-- The two exact residual pins (positions `0, 1`) vanish on the canonical trace by
construction.  Position `2` — the anchored step — is discharged semantically in
`OptimizedComputeCanonicalSatisfaction.canonical_accAfterStep` (A-comp anchoring stage). -/
theorem correctedCanonical_residualAux01
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (row : Fin R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes row) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    ∀ j : CorrectedResidualWitnessId, j ≠ 2 → correctedAuxSemanticValue env j = 0 := by
  dsimp only
  intro j hj
  rw [correctedAuxSemanticValue, if_neg hj, sub_eq_zero]
  rw [eq_iff_coords_eq b]
  intro k
  let envFinalF := envOfTrace
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes row) chalVal pubVal
  let envPreF := envOfTrace (preliminaryTrace A hn nodes b)
    orbit.ω (nodes row) chalVal pubVal
  let envFinal := gatherCorrectedFinalTypedEnv b envFinalF
  let envPre := gatherCorrectedFinalTypedEnv b envPreF
  have hcoord :
      coord b (envFinal.extTrace (residualWitnessRole j)) k =
        envFinalF.trace
          (correctedFinalExtCoordIndex (residualWitnessRole j) k) := by
    exact coord_sum_smul b
      (fun q => envFinalF.trace
        (correctedFinalExtCoordIndex (residualWitnessRole j) q)) k
  have hrow :
      envFinalF.trace
          (correctedFinalExtCoordIndex (residualWitnessRole j) k) =
        (correctedFinalTypedCompile b (correctedFinalResidualSource j) k).eval
          envPreF := by
    dsimp only [envFinalF]
    simp only [envOfTrace, dif_pos (show
      correctedFinalExtCoordIndex (residualWitnessRole j) k < 303 by
        simp [correctedFinalExtCoordIndex]
        omega)]
    rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes
      (hlt := by simp [correctedFinalExtCoordIndex]; omega)]
    fin_cases j
    · fin_cases k <;> norm_num [correctedFinalExtCoordIndex, residualWitnessRole] <;> rfl
    · fin_cases k <;> norm_num [correctedFinalExtCoordIndex, residualWitnessRole] <;> rfl
    · exact absurd rfl hj
  have hcompile :
      (correctedFinalTypedCompile b (correctedFinalResidualSource j) k).eval envPreF =
        coord b ((correctedFinalResidualSource j).eval envPre) k :=
    (correctedFinalTypedCompile_eval b envPre envPreF
      (isCorrectedFinalCoordEnv_gather b envPreF)
      (correctedFinalResidualSource j) k).symm
  have hsame :
      (correctedFinalResidualSource j).eval envFinal =
        (correctedFinalResidualSource j).eval envPre := by
    exact correctedCanonical_residualSource_eval_eq_preliminary
      A hn nodes b chalVal pubVal orbit row j
  change coord b (envFinal.extTrace (residualWitnessRole j)) k =
    coord b ((correctedFinalResidualSource j).eval envFinal) k
  rw [hcoord, hrow, hcompile, hsame]

theorem production_not_satisfies_of_source_failure
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hbad : let envF := envOfTrace P orbit.ω x chalVal pubVal
      ¬ CorrectedComputeSourceObligations n
        (gatherCorrectedFinalTypedEnv b envF) envF) :
    ¬ RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  intro hsat
  have hlang := (productionNamedComputeRAP_satisfies_iff_sourceLanguage
    hn nodes b chalVal pubVal orbit P).1 hsat
  exact hbad (hlang.2 x hx)

theorem production_satisfies_decodes_nonterminal_transition
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hsat : RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit) P)
    (hnotLast :
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace P orbit.ω x chalVal pubVal)).baseTrace 12 = 0) :
    CorrectedDecodedTransitionSources
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace P orbit.ω x chalVal pubVal)) := by
  have hsource :=
    (productionNamedComputeRAP_satisfies_iff_sourceLanguage
      hn nodes b chalVal pubVal orbit P).1 hsat |>.2 x hx
  exact corrected_conditional_transition_soundness hsource hnotLast

theorem final_extension_source_partition :
    finalExtTransitionGates =
      OptimizedComputeGateBasis.paperPackingNonIOGates ++ finalSampledIOTransitionGates ∧
      OptimizedComputeGateBasis.paperPackingNonIOGates.length = 78 ∧
      finalSampledIOTransitionGates.length = 4 ∧
      finalExtTransitionGates.length = 82 := by
  constructor
  · rfl
  · exact ⟨OptimizedComputeGateBasis.paperPackingNonIOGates_length, by decide,
      finalExtTransitionGates_length⟩

#print axioms correctedFinalComputeAllGates_eval_iff_source
#print axioms productionNamedComputeRAP_satisfies_iff_sourceLanguage
#print axioms correctedCanonicalFinalTrace_satisfies_of_source
#print axioms corrected_conditional_transition_soundness
#print axioms correctedCanonicalFinalTrace_eq_preliminary_of_role
#print axioms correctedCanonical_residualSource_eval_eq_preliminary
#print axioms correctedCanonical_residualAux01
#print axioms correctedCanonicalFinalTrace_accAfter_eval
#print axioms correctedAccAfterStep_eval_eq_fold
#print axioms production_not_satisfies_of_source_failure
#print axioms production_satisfies_decodes_nonterminal_transition
#print axioms finalGateBucket_pairwise_disjoint
#print axioms finalGateBucket_exhaustive

end
end OptimizedComputeSemanticRealization
end Nock.NockVMROM.Thm54
