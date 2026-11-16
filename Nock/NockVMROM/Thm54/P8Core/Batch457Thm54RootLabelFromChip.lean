/-
  Nock/NockVMROM/Thm54/P8Core/Batch457Thm54RootLabelFromChip.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch457Thm54RootLabelFromChip`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch457Thm54RootLabelFromChip.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch438Thm54InGateWalkReceipts
import Nock.NockVMROM.Thm54.P8Core.Batch453Thm54SeedWiring
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch457

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework.Reify
open Nock.RedTeam.Batch438
open Nock.RedTeam.Batch453
open Nock.Framework
open Module
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

/-- The physical `𝔽` row environment behind `rowEnvAt`. -/
abbrev envFAt (i : Fin (rows P)) : Env F :=
  envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
variable (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
variable (hbasis : FormRBasis P.optimized.basis)
variable (hwidth : FormRWidth F)
include hsat
include hax hbasis hwidth

/-- Base slots `11`/`12` of the family row are the fixed first/last-row masks.  Family
transcription of `OptimizedComputeHostileAccumulator.masks_at_row`: the preprocessing
binding of `computeChipAt c` is the same two columns. -/
theorem masks_at_row_at
    (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rowEnvAt P c Qc i).baseTrace 12 = (if i = lastRow P then 1 else 0) := by
  have hbind := ((productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)
    P.optimized.orbit Qc).1 hsat).1
  have hinj := (P.optimized.computeRealization hax hbasis hwidth).nodes_injective
  have h0 := hbind ⟨0, by change 0 < 2; norm_num⟩
  have h1 := hbind ⟨1, by change 1 < 2; norm_num⟩
  have h11 : 11 < (P.computeChipAt c).rap.w := by change 11 < 303; norm_num
  have h12 : 12 < (P.computeChipAt c).rap.w := by change 12 < 303; norm_num
  have hc0 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
      (P.familyComputePublic c) P.optimized.orbit).preprocessingColumn
        ⟨0, by change 0 < 2; norm_num⟩ = ⟨11, h11⟩ := rfl
  have hc1 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
      (P.familyComputePublic c) P.optimized.orbit).preprocessingColumn
        ⟨1, by change 1 < 2; norm_num⟩ = ⟨12, h12⟩ := rfl
  rw [hc0] at h0
  rw [hc1] at h1
  constructor
  · show (envFAt P c Qc i).trace 11 = _
    simp only [envFAt, envOfTrace, dif_pos h11]
    rw [show (Qc ⟨11, h11⟩) = Nock.Framework.firstRowMask P.optimized.computeNodes from h0,
      Nock.Framework.firstRowMask_eval _ hinj]
  · show (envFAt P c Qc i).trace 12 = _
    simp only [envFAt, envOfTrace, dif_pos h12]
    rw [show (Qc ⟨12, h12⟩) = Nock.Framework.lastRowMask
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes from h1,
      Nock.Framework.lastRowMask_eval _ _ hinj]

/-- `isFirst = 1` at the first family row (base slot `11`). -/
theorem baseTrace11_row0 :
    (rowEnvAt P c Qc (firstRow P)).baseTrace 11 = 1 := by
  have h := (masks_at_row_at P c Qc hsat hax hbasis hwidth (firstRow P)).1
  simpa using h

theorem initialMask_eq_selector_row0 (st : State) :
    (initialMaskExpr st).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
      (rowEnvAt P c Qc (firstRow P)).toSourceEnv.trace (opCol st) := by
  have hobl := row_obligations_at P c Qc hsat (firstRow P)
  have hlt : opCol st < 11 := by cases st <;> decide
  have hg := hobl.selectorEquality2 (endpointEqualityCheck isFirstVar 20 (opCol st)) (by
    simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨opCol st, hlt, rfl⟩)
  have hfirst : (envFAt P c Qc (firstRow P)).trace 11 = 1 := by
    have := baseTrace11_row0 P c Qc hsat hax hbasis hwidth
    exact this
  simp only [endpointEqualityCheck, isFirstVar, bv, CoeffExpr.eval, hfirst, one_mul,
    sub_eq_zero] at hg
  -- `hg : envF.trace (opCol st) = envF.pub (20 + opCol st)`
  have hpub : (rowEnvAt P c Qc (firstRow P)).toSourceEnv.pub (20 + opCol st) =
      algebraMap F K ((envFAt P c Qc (firstRow P)).pub (20 + opCol st)) := by
    have h1 : ¬ (20 + opCol st < 3) := by omega
    have h2 : 20 ≤ 20 + opCol st ∧ 20 + opCol st < 42 := by omega
    simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_neg h1, dif_pos h2]
    congr 1
    show (envFAt P c Qc (firstRow P)).pub (20 + (20 + opCol st - 20)) = _
    rw [Nat.add_sub_cancel_left]
  have htr : (rowEnvAt P c Qc (firstRow P)).toSourceEnv.trace (opCol st) =
      algebraMap F K ((envFAt P c Qc (firstRow P)).trace (opCol st)) := by
    rw [source_trace_base _ (opCol st) (by omega)]
    rfl
  simp only [initialMaskExpr, Expr.eval]
  rw [hpub, htr, hg]

omit hsat hax hbasis hwidth in
/-- Walk-`γ` at the family row is the tuple's `gamma` (compute `𝕂` slot `10`). -/
theorem walkGamma_at (i : Fin (rows P)) :
    walkGammaChallenge.eval (rowEnvAt P c Qc i).toSourceEnv = gamma c.1 := by
  have h := rowEnvAt_chal P c Qc i ⟨10, by decide⟩
  rw [show computeKOfTuple c 10 = gamma c.1 from rfl] at h
  simpa [walkGammaChallenge, walkGammaChallengeIndex, Expr.eval] using h

omit hsat hax hbasis hwidth in
/-- Walk-`α` at the family row is the tuple's `alphaC` (compute `𝕂` slot `6`). -/
theorem walkAlpha_at (i : Fin (rows P)) :
    (walkChallenge 0).eval (rowEnvAt P c Qc i).toSourceEnv = alphaC c.1 := by
  have h := rowEnvAt_chal P c Qc i ⟨6, by decide⟩
  rw [show computeKOfTuple c 6 = alphaC c.1 from rfl] at h
  simpa [walkChallenge, walkChallengeBase, Expr.eval] using h

omit hsat hax hbasis hwidth in
/-- The lowered `finalMaskedWalkAccInit` is the one member of `correctedEndpoint4`, obtained
by length (`corrected_lowered_counts`), not by `decide` on the in-gate expression. -/
theorem lower_walkAccInit_exists :
    ∃ t, correctedLowerFinal finalMaskedWalkAccInit = some t ∧ t ∈ correctedEndpoint4 := by
  have hlen : ([finalMaskedWalkAccInit].filterMap correctedLowerFinal).length =
      [finalMaskedWalkAccInit].length := by
    rw [show [finalMaskedWalkAccInit].filterMap correctedLowerFinal = correctedEndpoint4 from
      rfl, corrected_lowered_counts.2.2]
    rfl
  have h := get_filterMap_of_length_eq correctedLowerFinal [finalMaskedWalkAccInit] hlen 0
    (by simp)
  refine ⟨_, h, ?_⟩
  exact List.mem_filterMap.mpr ⟨finalMaskedWalkAccInit, by simp, h⟩

omit hsat hax hbasis hwidth in
theorem lower_walkLn1_exists :
    ∃ t, correctedLowerFinal finalMaskedWalkLn1 = some t ∧ t ∈ correctedEndpoint2 := by
  have hlen : ([finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
      finalAccTerminal, finalLnInit].filterMap correctedLowerFinal).length =
      [finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
        finalAccTerminal, finalLnInit].length := by
    rw [show [finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
      finalAccTerminal, finalLnInit].filterMap correctedLowerFinal = correctedEndpoint2 from
      rfl, corrected_lowered_counts.2.1]
    rfl
  have h := get_filterMap_of_length_eq correctedLowerFinal
    [finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
      finalAccTerminal, finalLnInit] hlen 0 (by simp)
  refine ⟨_, h, ?_⟩
  exact List.mem_filterMap.mpr ⟨finalMaskedWalkLn1, by simp, h⟩

omit hsat hax hbasis hwidth in
theorem lower_walkCount1_exists :
    ∃ t, correctedLowerFinal finalMaskedWalkCount1 = some t ∧ t ∈ correctedEndpoint2 := by
  have hlen : ([finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
      finalAccTerminal, finalLnInit].filterMap correctedLowerFinal).length =
      [finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
        finalAccTerminal, finalLnInit].length := by
    rw [show [finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
      finalAccTerminal, finalLnInit].filterMap correctedLowerFinal = correctedEndpoint2 from
      rfl, corrected_lowered_counts.2.1]
    rfl
  have h := get_filterMap_of_length_eq correctedLowerFinal
    [finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
      finalAccTerminal, finalLnInit] hlen 1 (by simp)
  refine ⟨_, h, ?_⟩
  exact List.mem_filterMap.mpr ⟨finalMaskedWalkCount1, by simp, h⟩

/-- The source-level `finalMaskedWalkAccInit` vanishes at row 0 of an accepted family trace. -/
theorem maskedWalkAccInit_source_zero :
    finalMaskedWalkAccInit.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 0 := by
  obtain ⟨t, ht, hmem⟩ := lower_walkAccInit_exists
  rw [correctedLowerFinal_eval _ _ _ ht]
  exact (row_obligations_at P c Qc hsat (firstRow P)).endpointDegreeFour1 t hmem

theorem maskedWalkLn1_source_zero :
    finalMaskedWalkLn1.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 0 := by
  obtain ⟨t, ht, hmem⟩ := lower_walkLn1_exists
  rw [correctedLowerFinal_eval _ _ _ ht]
  exact (row_obligations_at P c Qc hsat (firstRow P)).endpointDegreeTwo2 t hmem

theorem maskedWalkCount1_source_zero :
    finalMaskedWalkCount1.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 0 := by
  obtain ⟨t, ht, hmem⟩ := lower_walkCount1_exists
  rw [correctedLowerFinal_eval _ _ _ ht]
  exact (row_obligations_at P c Qc hsat (firstRow P)).endpointDegreeTwo2 t hmem

/-- **`ln(1) = αc`** at row 0 of an accepted family trace. -/
theorem walkLn_row0 :
    (finalWalkLine .traceCur).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = alphaC c.1 := by
  have h : finalMaskedWalkLn1.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 0 :=
    maskedWalkLn1_source_zero P c Qc hsat hax hbasis hwidth
  have hb1 : (rowEnvAt P c Qc (firstRow P)).baseTrace 11 = 1 :=
    baseTrace11_row0 P c Qc hsat hax hbasis hwidth
  have hm : fixedIsFirst.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 1 := by
    simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
  simp only [finalMaskedWalkLn1, Expr.eval] at h
  rw [hm, one_mul, finalOptimizedWalkLn1] at h
  have heq :
      (Trans.walkLn1.subst finalWalkInitialSubst).eval
        (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
        (finalWalkLine .traceCur).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv -
          (walkChallenge 0).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv := by
    rw [Expr.eval_subst]; rfl
  rw [heq, sub_eq_zero] at h
  have hα :
      (walkChallenge 0).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = alphaC c.1 :=
    walkAlpha_at P c Qc (firstRow P)
  rw [h, hα]

/-- **`count(1) = initial_count · cm(1)`** at row 0. -/
theorem walkCount_row0 :
    (initialOverlayCoord 0).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
      (rowEnvAt P c Qc (firstRow P)).toSourceEnv.pub 0 *
        (selectorCM firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv := by
  have h : finalMaskedWalkCount1.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 0 :=
    maskedWalkCount1_source_zero P c Qc hsat hax hbasis hwidth
  have hb1 : (rowEnvAt P c Qc (firstRow P)).baseTrace 11 = 1 :=
    baseTrace11_row0 P c Qc hsat hax hbasis hwidth
  have hm : fixedIsFirst.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 1 := by
    simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
  simp only [finalMaskedWalkCount1, Expr.eval] at h
  rw [hm, one_mul, finalOptimizedWalkCount1] at h
  have heq :
      (Trans.walkCount1.subst finalWalkInitialSubst).eval
        (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
        (initialOverlayCoord 0).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv -
          (rowEnvAt P c Qc (firstRow P)).toSourceEnv.pub 0 *
            (selectorCM firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv := by
    rw [Expr.eval_subst]; rfl
  rw [heq, sub_eq_zero] at h
  exact h

/-- **The row-0 walk identity, in the paper's operands**: with `ln(1) = αc`,
`αc · cur(1) + acc_walk(1) = initial_count · cc(1) + seed`. -/
theorem walkAccInit_row0 :
    alphaC c.1 * (labelRLC firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv +
        (initialOverlayCoord 1).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
      (rowEnvAt P c Qc (firstRow P)).toSourceEnv.pub 0 *
          (childSumCC firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv +
        (rowEnvAt P c Qc (firstRow P)).toSourceEnv.pub 1 := by
  have h : finalMaskedWalkAccInit.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 0 :=
    maskedWalkAccInit_source_zero P c Qc hsat hax hbasis hwidth
  have hb1 : (rowEnvAt P c Qc (firstRow P)).baseTrace 11 = 1 :=
    baseTrace11_row0 P c Qc hsat hax hbasis hwidth
  have hm : fixedIsFirst.eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = 1 := by
    simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
  simp only [finalMaskedWalkAccInit, Expr.eval] at h
  rw [hm, one_pow, finalOptimizedWalkAccInit] at h
  have heq :
      (Trans.walkAccInit.subst finalWalkInitialSubst).eval
        (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
        (finalWalkLine .traceCur).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv *
            (labelRLC firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv +
          (initialOverlayCoord 1).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv -
        ((rowEnvAt P c Qc (firstRow P)).toSourceEnv.pub 0 *
            (childSumCC firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv +
          (rowEnvAt P c Qc (firstRow P)).toSourceEnv.pub 1) := by
    rw [Expr.eval_subst]; rfl
  rw [heq, one_mul, sub_eq_zero, walkLn_row0 P c Qc hsat hax hbasis hwidth] at h
  exact h

omit hsat hax hbasis hwidth in
/-- Extension public `1` of every family row is the verifier's `seedOfClaim`. -/
theorem family_seed_at (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 1 =
      seedOfClaim P.optimized.verifier.raw.claim c := by
  have h1 : (1 : ℕ) < 3 := by norm_num
  simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos h1]
  change (∑ k : Fin 3, P.familyComputePublic c (3 * 1 + (k : ℕ)) • P.optimized.basis k) = _
  have hcoord : ∀ k : Fin 3, P.familyComputePublic c (3 * 1 + (k : ℕ)) =
      coord P.optimized.basis (seedOfClaim P.optimized.verifier.raw.claim c) k := by
    intro k
    have := family_seed_slots P c k
    simpa [show 3 * 1 + (k : ℕ) = 3 + (k : ℕ) by ring] using this
  simp_rw [hcoord]
  exact reconstruct_coord P.optimized.basis _

omit hsat hax hbasis hwidth in
theorem family_initialCount_at (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 0 = alphaC c.1 := by
  have h0 : (0 : ℕ) < 3 := by norm_num
  simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos h0]
  change (∑ k : Fin 3, P.familyComputePublic c (3 * 0 + (k : ℕ)) • P.optimized.basis k) = _
  have hcoord : ∀ k : Fin 3, P.familyComputePublic c (3 * 0 + (k : ℕ)) =
      coord P.optimized.basis (alphaC c.1) k := by
    intro k
    have := computePublicOfTuple_alpha_coord P.optimized.basis P.optimized.verifier.raw.claim
      P.optimized.computePublic c k
    simpa using this
  simp_rw [hcoord]
  exact reconstruct_coord P.optimized.basis _

end

end Nock.RedTeam.Batch457


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch457

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework.Reify
open Nock.RedTeam.Batch438
open Nock.RedTeam.Batch453
open Nock.Framework
open Module
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

theorem rowEnvAt_eq_gather (i : Fin (rows P)) :
    rowEnvAt P c Qc i = gatherCorrectedFinalTypedEnv P.optimized.basis (envFAt P c Qc i) :=
  rfl

end

end Nock.RedTeam.Batch457
