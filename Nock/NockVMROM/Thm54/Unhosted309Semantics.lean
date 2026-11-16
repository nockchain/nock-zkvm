import Nock.NockVMROM.Thm54.Unhosted309Chip
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization

/-!
# The un-hosted 309 chip: the decode, the source language, and the conditional row decode

**.  Parallel definitions; nothing existing is edited.**

The width-309 counterpart of `OptimizedComputeSemanticRealization`:

* `gather309` reassembles one `Env309` from any physical 309-column row (the deployed
  `gatherCorrectedFinalTypedEnv` plus the two walk columns `W0 = 303..305`, `W1 = 306..308`);
* `SourceObligations309` is the exact semantic decomposition of the 418 compiled gates, and
  `allGates309_eval_iff_source` the equivalence on one same-object environment;
* `satisfies309_iff_sourceLanguage` is `arbitrary_trace_source_iff` at the 309 chip;
* `conditional_transition_soundness309` is `conditional_row_decode` at the 309 chip: on every
  nonterminal accepted row the 76 core coin-free sources — with the two walk recurrences now
  read off `W0`/`W1` (`crossRowSingletons309`) — and the four sampled-IO sources vanish.
-/

namespace Nock.NockVMROM.Thm54
namespace Unhosted309

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open OptimizedComputeBaseGates
open OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId FinalExtensionColumn
open OptimizedComputeFinalTypedLowering
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeRangeCertificate
open OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

/-! ## 1. Decoding any physical row -/

/-- **The width-309 decode.**  The deployed gathered environment plus `W0`/`W1`. -/
def gather309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (envF : Env F) : Env309 F K where
  base := gatherCorrectedFinalTypedEnv b envF
  walk j := ∑ k : Fin 3, envF.trace (walkLimb j k) • b k
  walkNext j := ∑ k : Fin 3, envF.traceNext (walkLimb j k) • b k

theorem isCoordEnv309_gather {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (envF : Env F) : IsCoordEnv309 b (gather309 b envF) envF where
  base := isCorrectedFinalCoordEnv_gather b envF
  walk := fun j k => (coord_sum_smul b (fun q => envF.trace (walkLimb j q)) k).symm
  walkNext := fun j k => (coord_sum_smul b (fun q => envF.traceNext (walkLimb j q)) k).symm

/-! ## 2. The semantic decomposition of the 418 gates -/

/-- Core position values at 309: positions `76`/`77` are the retargeted queue gates, every other
position is the deployed semantic value. -/
def coreSemValue309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : Env309 F K) (i : CorrectedCoreExtGateId) : K :=
  if i = packedQueueNonEmptyId then queueNonEmpty309.eval env
  else if i = packedQueueTilingId then queueTiling309.eval env
  else correctedCoreSemanticValue env.base i

/-- Aux position values at 309: positions `0`/`1` pin the residual roles `58`/`59` to the
retargeted walk recurrences, position `2` is the deployed anchored accumulator step. -/
def auxSemValue309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : Env309 F K) (j : CorrectedResidualWitnessId) : K :=
  if h : j = 2 then correctedAuxSemanticValue env.base j
  else env.base.extTrace (residualWitnessRole j) - (residualSource309 (aux309Idx j h)).eval env

/-- **The exact source-side decomposition of the 418-gate un-hosted chip.** -/
structure SourceObligations309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (env : Env309 F K) (envF : Env F) : Prop where
  base15 : ∀ g ∈ finalBaseTransitionGates n, g.eval envF = 0
  extensionCore : ∀ i : CorrectedCoreExtGateId, coreSemValue309 env i = 0
  residualAux : ∀ j : CorrectedResidualWitnessId, auxSemValue309 env j = 0
  endpointDegreeTwo : ∀ t ∈ endpoint2_309, t.eval env = 0
  endpointDegreeFour : ∀ t ∈ endpoint4_309, t.eval env = 0
  selectorEquality2 : ∀ g ∈ finalEndpointEqualityChecks, g.eval envF = 0
  formR99 : ∀ g ∈ formRCertificateGates, g.eval envF = 0
  formRLam : ∀ t ∈ formRLamPins, t.eval env.base = 0
  expGates : ∀ g ∈ computeExpGates (F := F), g.eval envF = 0

theorem coreCoord309_eval {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F) (henv : IsCoordEnv309 b env envF)
    (i : CorrectedCoreExtGateId) (k : Fin 3) :
    (correctedCoreCoord309 b i k).eval envF = coord b (coreSemValue309 env i) k := by
  unfold correctedCoreCoord309 coreSemValue309
  split_ifs
  · exact (compile309_eval b env envF henv _ k).symm
  · exact (compile309_eval b env envF henv _ k).symm
  · exact correctedCoreCoord_eval b env.base envF henv.base i k

theorem auxCoord309_eval {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F) (henv : IsCoordEnv309 b env envF)
    (j : CorrectedResidualWitnessId) (k : Fin 3) :
    (correctedAuxCoord309 b j k).eval envF = coord b (auxSemValue309 env j) k := by
  unfold correctedAuxCoord309 auxSemValue309
  split_ifs with h2
  · exact correctedAuxCoord_eval b env.base envF henv.base j k
  · simp only [CoeffExpr.eval, coord_sub']
    have he := henv.base.extTrace (residualWitnessRole j) k
    have he' :
        envF.trace ↑(OptimizedComputeFinal.finalExtCoordIndex
            (OptimizedComputeFinal.residualWitnessRole j) k) =
          coord b (env.base.extTrace (residualWitnessRole j)) k := by
      simpa [OptimizedComputeFinal.finalExtCoordIndex,
        OptimizedComputeFinal.residualWitnessRole, correctedFinalExtCoordIndex,
        residualWitnessRole] using he
    simp only [residualWitnessCoord, CoeffExpr.eval]
    rw [he', ← compile309_eval b env envF henv]

theorem core309_eval_iff {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F) (henv : IsCoordEnv309 b env envF) :
    (∀ g ∈ correctedCore309 b, g.eval envF = 0) ↔ ∀ i, coreSemValue309 env i = 0 := by
  constructor
  · intro h i
    rw [eq_iff_coords_eq b (coreSemValue309 env i) 0]
    intro k
    rw [coord_zero' b k, ← coreCoord309_eval b env envF henv i k]
    apply h
    rw [correctedCore309]
    exact List.mem_flatten.mpr
      ⟨List.ofFn (correctedCoreCoord309 b i), List.mem_ofFn.mpr ⟨i, rfl⟩,
        List.mem_ofFn.mpr ⟨k, rfl⟩⟩
  · intro h g hg
    rw [correctedCore309] at hg
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    rw [coreCoord309_eval b env envF henv, h i, coord_zero' b k]

theorem aux309_eval_iff {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F) (henv : IsCoordEnv309 b env envF) :
    (∀ g ∈ correctedAux309 b, g.eval envF = 0) ↔ ∀ j, auxSemValue309 env j = 0 := by
  constructor
  · intro h j
    rw [eq_iff_coords_eq b (auxSemValue309 env j) 0]
    intro k
    rw [coord_zero' b k, ← auxCoord309_eval b env envF henv j k]
    apply h
    rw [correctedAux309]
    exact List.mem_flatten.mpr
      ⟨List.ofFn (correctedAuxCoord309 b j), List.mem_ofFn.mpr ⟨j, rfl⟩,
        List.mem_ofFn.mpr ⟨k, rfl⟩⟩
  · intro h g hg
    rw [correctedAux309] at hg
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    rw [auxCoord309_eval b env envF henv, h j, coord_zero' b k]

/-- **Exact gate-compilation equivalence for all 418 constraints of the 309 chip.** -/
theorem allGates309_eval_iff_source {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K]
    (n : ℕ) (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F)
    (henv : IsCoordEnv309 b env envF) :
    (∀ g ∈ allGates309 n b, g.eval envF = 0) ↔ SourceObligations309 n env envF := by
  simp only [allGates309, List.forall_mem_append]
  rw [core309_eval_iff b env envF henv, aux309_eval_iff b env envF henv,
    compileList309_eval_iff b env envF henv endpoint2_309,
    compileList309_eval_iff b env envF henv endpoint4_309,
    correctedCompileList_eval_iff b env.base envF henv.base formRLamPins]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hb, hc⟩, ha⟩, h2⟩, h4⟩, heq⟩, hform⟩, hlam⟩, hexp⟩
    exact ⟨hb, hc, ha, h2, h4, heq, hform, hlam, hexp⟩
  · rintro ⟨hb, hc, ha, h2, h4, heq, hform, hlam, hexp⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hb, hc⟩, ha⟩, h2⟩, h4⟩, heq⟩, hform⟩, hlam⟩, hexp⟩

theorem allGates309_eval_iff_gathered {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (n : ℕ) (b : Basis (Fin 3) F K) (envF : Env F) :
    (∀ g ∈ allGates309 n b, g.eval envF = 0) ↔ SourceObligations309 n (gather309 b envF) envF :=
  allGates309_eval_iff_source n b _ envF (isCoordEnv309_gather b envF)

/-! ## 3. The language theorem at 309 (`arbitrary_trace_source_iff`) -/

/-- The gathered source language of the 309 chip. -/
def SourceLanguage309 {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit).rap.w → F[X]) : Prop :=
  (ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit).BindsPreprocessing P ∧
    ∀ x ∈ rowNodeSet nodes,
      let envF := envOfTrace P orbit.ω x chalVal pubVal
      SourceObligations309 n (gather309 b envF) envF

/-- **`arbitrary_trace_source_iff` at the 309 chip**: satisfaction is exactly the gathered
source language, for arbitrary traces. -/
theorem satisfies309_iff_sourceLanguage {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit) P ↔
      SourceLanguage309 hn nodes b chalVal pubVal orbit P := by
  let R := ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit
  have key : ∀ (i : Fin R.rap.s) (x : F),
      (R.rap.compose P i).eval x =
        ((allGates309 n b).get i).eval (envOfTrace P orbit.ω x chalVal pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalVal pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, ?_⟩
    intro x hx
    apply (allGates309_eval_iff_gathered n b _).1
    intro g hg
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact (allGates309_eval_iff_gathered n b _).2 (hall x hx) _ (List.get_mem _ _)

/-! ## 4. The conditional row decode at 309 (`conditional_row_decode`) -/

/-- The four cross-row singletons at 309: `lnChain`, `walkLn` (both untouched), and the two walk
recurrences on `W0`/`W1`. -/
def crossRowSingletons309 : List Expr :=
  [Trans.lnChainExpr.subst computeSubst,
   Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate,
   walkCountStep309, walkAccStep309]

/-- The 76 core coin-free sources at 309. -/
def paperPackingCoreGates309 : List Expr :=
  packedTableOptimized ++ alwaysOnOptimized ++ crossRowSingletons309

/-- **The decoded transition sources at 309**, on the width-309 source environment. -/
structure DecodedTransitionSources309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : Env309 F K) : Prop where
  nonIO : ∀ e ∈ paperPackingCoreGates309, e.eval env.toSourceEnv = 0
  sampledIOSafe4 : ∀ e ∈ finalSampledIOTransitionGates, e.eval env.toSourceEnv = 0

/-- `Expr` mentions neither walk column. -/
def noWalkVars : Expr → Bool
  | .Var .traceCur i => i != 303 && i != 306
  | .Var .traceNext i => i != 303 && i != 306
  | .Var _ _ => true
  | .Const _ => true
  | .Add a b | .Sub a b | .Mul a b => noWalkVars a && noWalkVars b
  | .Neg a | .Pow a _ => noWalkVars a

theorem eval_toSourceEnv309_of_noWalkVars {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : Env309 F K) : ∀ e : Expr, noWalkVars e = true →
      e.eval env.toSourceEnv = e.eval env.base.toSourceEnv
  | .Var .traceCur i, h => by
      simp only [noWalkVars, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      simp [Expr.eval, Env309.toSourceEnv, h.1, h.2]
  | .Var .traceNext i, h => by
      simp only [noWalkVars, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      simp [Expr.eval, Env309.toSourceEnv, h.1, h.2]
  | .Var .challenge i, _ => rfl
  | .Var .publicVal i, _ => rfl
  | .Const _, _ => rfl
  | .Add a b, h => by
      simp only [noWalkVars, Bool.and_eq_true] at h
      simp only [Expr.eval, eval_toSourceEnv309_of_noWalkVars env a h.1,
        eval_toSourceEnv309_of_noWalkVars env b h.2]
  | .Sub a b, h => by
      simp only [noWalkVars, Bool.and_eq_true] at h
      simp only [Expr.eval, eval_toSourceEnv309_of_noWalkVars env a h.1,
        eval_toSourceEnv309_of_noWalkVars env b h.2]
  | .Mul a b, h => by
      simp only [noWalkVars, Bool.and_eq_true] at h
      simp only [Expr.eval, eval_toSourceEnv309_of_noWalkVars env a h.1,
        eval_toSourceEnv309_of_noWalkVars env b h.2]
  | .Neg a, h => by
      simp only [noWalkVars] at h
      simp only [Expr.eval, eval_toSourceEnv309_of_noWalkVars env a h]
  | .Pow a _, h => by
      simp only [noWalkVars] at h
      simp only [Expr.eval, eval_toSourceEnv309_of_noWalkVars env a h]

/-- No deployed extension source reads `303`/`306`. -/
theorem finalExtTransitionGates_noWalkVars : ∀ e ∈ finalExtTransitionGates, noWalkVars e = true := by
  decide

theorem lower309_some (e : Expr) (h : (lower309 e).isSome) : lower309 e = some (lowerW e) := by
  unfold lowerW
  cases hl : lower309 e with
  | none => simp [hl] at h
  | some t => rfl

/-- On a nonterminal row, every untouched core position `i ∉ {74, 75, 76, 77}` evaluates to zero
(the deployed case analysis, minus the four retargeted positions). -/
theorem ext_gate_zero309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : SourceObligations309 n env envF) (hnotLast : env.base.baseTrace 12 = 0)
    (i : CorrectedCoreExtGateId)
    (h74 : i ≠ packedWalkCountId) (h75 : i ≠ packedWalkAccId)
    (h76 : i ≠ packedQueueNonEmptyId) (h77 : i ≠ packedQueueTilingId) :
    (correctedFinalExtGate i).eval env.base = 0 := by
  have hc := hsource.extensionCore i
  simp only [coreSemValue309, h76, h77, if_false] at hc
  by_cases h20 : i = packedChainId
  · subst i
    have ha := hsource.residualAux 2
    simp only [auxSemValue309, correctedAuxSemanticValue] at ha
    have hchain : env.base.extTrace 60 = env.base.extTraceNext 32 := by
      simpa [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
        packedLnChainId, packedWalkLnId, accAfterChain,
        CorrectedFinalTypedExpr.eval, hnotLast, sub_eq_zero] using hc
    rw [← correctedAccAfterStep_eval_eq_fold env.base hchain]
    exact ha
  by_cases h89 : i = packedLnChainId ∨ i = packedWalkLnId
  · simp only [correctedCoreSemanticValue] at hc
    simp only [h74, h75, h20, h89, ↓reduceIte, notLastScalar, hnotLast, sub_zero, map_one,
      one_mul] at hc
    exact hc
  · simp only [correctedCoreSemanticValue] at hc
    simp only [h74, h75, h20, h89, ↓reduceIte] at hc
    exact hc

theorem finalExtTransitionGates_split :
    finalExtTransitionGates =
      (packedTableOptimized ++ alwaysOnOptimized) ++
        crossRowSingletons ++ queueWitnessGates ++ finalSampledIOTransitionGates := rfl

/-- **`conditional_row_decode` at the 309 chip.**  On any nonterminal accepted row, the 76 core
coin-free sources at 309 and the four sampled-IO sources vanish on the width-309 decode. -/
theorem conditional_transition_soundness309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : SourceObligations309 n env envF) (hnotLast : env.base.baseTrace 12 = 0) :
    DecodedTransitionSources309 env := by
  -- the untouched sources, by position in the deployed list
  have hpos : ∀ (i : ℕ) (hi : i < 82), i ≠ 74 → i ≠ 75 → i ≠ 76 → i ≠ 77 →
      (finalExtTransitionGates.get ⟨i, by simpa using hi⟩).eval env.toSourceEnv = 0 := by
    intro i hi h74 h75 h76 h77
    rw [eval_toSourceEnv309_of_noWalkVars env _
      (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
    have := correctedFinalExtGate_eval_source env.base ⟨i, hi⟩
    simp only at this
    rw [this]
    exact ext_gate_zero309 hsource hnotLast ⟨i, hi⟩
      (fun h => h74 (congrArg Fin.val h)) (fun h => h75 (congrArg Fin.val h))
      (fun h => h76 (congrArg Fin.val h)) (fun h => h77 (congrArg Fin.val h))
  have hmem : ∀ e, (∃ (i : ℕ) (hi : i < 82), i ≠ 74 ∧ i ≠ 75 ∧ i ≠ 76 ∧ i ≠ 77 ∧
      finalExtTransitionGates.get ⟨i, by simpa using hi⟩ = e) → e.eval env.toSourceEnv = 0 := by
    rintro e ⟨i, hi, h74, h75, h76, h77, rfl⟩
    exact hpos i hi h74 h75 h76 h77
  -- the two retargeted recurrences, through the residual pins
  have hres : ∀ j : Fin 2, (residualSource309 j).eval env = 0 := by
    intro j
    have hj2 : (⟨j.val, by omega⟩ : CorrectedResidualWitnessId) ≠ 2 := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have ha := hsource.residualAux ⟨j.val, by omega⟩
    have hidx : aux309Idx ⟨j.val, by omega⟩ hj2 = j := Fin.ext rfl
    simp only [auxSemValue309, dif_neg hj2, hidx, sub_eq_zero] at ha
    have hc := hsource.extensionCore (if j = 0 then packedWalkCountId else packedWalkAccId)
    fin_cases j
    · simp [coreSemValue309, correctedCoreSemanticValue, notLastScalar, hnotLast,
        packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId] at hc
      rw [← ha]
      simpa [residualWitnessRole] using hc
    · simp [coreSemValue309, correctedCoreSemanticValue, notLastScalar, hnotLast,
        packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId] at hc
      rw [← ha]
      simpa [residualWitnessRole] using hc
  have hcount : walkCountStep309.eval env.toSourceEnv = 0 := by
    rw [lower309_eval env _ _ (lower309_some _ lower309_total.1)]
    exact hres 0
  have hacc : walkAccStep309.eval env.toSourceEnv = 0 := by
    rw [lower309_eval env _ _ (lower309_some _ lower309_total.2.1)]
    exact hres 1
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [paperPackingCoreGates309, List.mem_append] at he
    have hpl : packedTableOptimized.length = 66 := by decide
    have hlen : alwaysOnOptimized.length = 6 := by decide
    rcases he with (hrow | hon) | hcr
    · obtain ⟨i, hget⟩ := List.mem_iff_get.mp hrow
      have hi : i.val < 66 := by have := i.isLt; omega
      apply hmem e
      refine ⟨i.val, by omega, by omega, by omega, by omega, by omega, ?_⟩
      rw [← hget]
      simp only [List.get_eq_getElem, finalExtTransitionGates_split, List.append_assoc]
      rw [List.getElem_append_left (by omega)]
    · obtain ⟨i, hget⟩ := List.mem_iff_get.mp hon
      have hi : i.val < 6 := by have := i.isLt; omega
      apply hmem e
      refine ⟨66 + i.val, by omega, by omega, by omega, by omega, by omega, ?_⟩
      rw [← hget]
      simp only [List.get_eq_getElem, finalExtTransitionGates_split, List.append_assoc]
      rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
      simp [hpl]
    · simp only [crossRowSingletons309, List.mem_cons, List.not_mem_nil, or_false] at hcr
      rcases hcr with rfl | rfl | rfl | rfl
      · exact hmem _ ⟨72, by omega, by omega, by omega, by omega, by omega, by decide⟩
      · exact hmem _ ⟨73, by omega, by omega, by omega, by omega, by omega, by decide⟩
      · exact hcount
      · exact hacc
  · intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    have hlen : finalSampledIOTransitionGates.length = 4 := by decide
    have hpre : ((packedTableOptimized ++ alwaysOnOptimized) ++ crossRowSingletons ++
        queueWitnessGates).length = 78 := by decide
    apply hmem
    refine ⟨78 + j, by omega, by omega, by omega, by omega, by omega, ?_⟩
    simp only [List.get_eq_getElem, finalExtTransitionGates_split]
    rw [List.getElem_append_right (by omega)]
    congr 1
    omega

#print axioms allGates309_eval_iff_source
#print axioms satisfies309_iff_sourceLanguage
#print axioms conditional_transition_soundness309

end
end Unhosted309
end Nock.NockVMROM.Thm54
