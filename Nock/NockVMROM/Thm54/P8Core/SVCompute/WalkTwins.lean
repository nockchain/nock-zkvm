/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/WalkTwins.lean

  Every twin is the
  live proof with the package replaced by `(D : ChipData) (L : ChipLayout)`, `rowEnvAt P c Qc` by
  `rowEnvAtD D c Q`, `row_obligations_at` / `masks_at_row_at` by the row facts `RF : RowFacts D L c Q`,
  and the Form R premises `hax hbasis hwidth` (used only for `computeRealization.adjacent_orbit` and
  `nodes_injective`) by `hadj : D.Adjacent` (injectivity is inside `RF`).  The walk-gate
  source lemmas that never read the package (`overlay*_eval_oneHot`, `lower_walkOut_exists`,
  `finalExtTransitionGates_get_walk*`, `termReader`) are used from `Batch459` / `Batch457` as they stand.
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.ChainTwins
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.WrapFixesVcomp
import Nock.NockVMROM.Thm54.P8Core.Batch438Thm54InGateWalkReceipts

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open Nock.Framework.Reify
open Module
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open Nock.RedTeam.Batch438

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}
  (D : ChipData F K h) (L : ChipLayout F K h)
  (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOf D L c).rap.w → F[X])
  (RF : RowFacts D L c Q)

/-- `FamilyComputeRows.row_obligations_at`, from the row facts. -/
theorem row_obligations_atD (RF : RowFacts D L c Q) (i : Fin D.N) :
    CorrectedComputeSourceObligations D.N (rowEnvAtD D c Q i)
      (envOfTrace Q D.orbit.ω (D.nodes i) (computeChalValOfTuple D.basis c)
        (computePublicOfTuple D.basis D.claim D.pub c)) :=
  RF.obl i

/-- `Batch457.masks_at_row_at`, from the row facts. -/
theorem masks_at_row_atD (RF : RowFacts D L c Q) (i : Fin D.N) :
    (rowEnvAtD D c Q i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rowEnvAtD D c Q i).baseTrace 12 = (if i = lastRowD D then 1 else 0) := by
  refine ⟨(RF.masks i).1, ?_⟩
  have := (RF.masks i).2
  rw [this]
  simp only [lastRowD, Fin.ext_iff]

variable (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

/-- `FamilyComputeRows.deployed_row_one_hot_at`: an accepted row has a one-hot state. -/
theorem deployed_row_one_hot_atD (RF : RowFacts D L c Q) (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin D.N) :
    ∃ st : State, OneHotSelector (rowEnvAtD D c Q i).toSourceEnv st := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot_atD RF hchar i
  refine ⟨s, fun t => ?_⟩
  have ht : (rowEnvAtD D c Q i).toSourceEnv.trace (opCol t) = opSel s t := by
    rw [source_trace_base _ (opCol t) (by cases t <;> decide)]
    simpa [rowSelector] using congrFun hs t
  simpa [OneHotSelector, opSel] using ht

include RF hchar

/-- `isFirst = 1` at the first family row (base slot `11`). -/
theorem baseTrace11_row0D :
    (rowEnvAtD D c Q (firstRowD D)).baseTrace 11 = 1 := by
  have h := (masks_at_row_atD D L c Q RF (firstRowD D)).1
  simpa using h

theorem initialMask_eq_selector_row0D (st : State) :
    (initialMaskExpr st).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv =
      (rowEnvAtD D c Q (firstRowD D)).toSourceEnv.trace (opCol st) := by
  have hobl := row_obligations_atD D L c Q RF (firstRowD D)
  have hlt : opCol st < 11 := by cases st <;> decide
  have hg := hobl.selectorEquality2 (endpointEqualityCheck isFirstVar 20 (opCol st)) (by
    simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨opCol st, hlt, rfl⟩)
  have hfirst : (envFAtD D c Q (firstRowD D)).trace 11 = 1 := by
    have := baseTrace11_row0D D L c Q RF hchar
    exact this
  simp only [endpointEqualityCheck, isFirstVar, bv, CoeffExpr.eval, hfirst, one_mul,
    sub_eq_zero] at hg
  -- `hg : envF.trace (opCol st) = envF.pub (20 + opCol st)`
  have hpub : (rowEnvAtD D c Q (firstRowD D)).toSourceEnv.pub (20 + opCol st) =
      algebraMap F K ((envFAtD D c Q (firstRowD D)).pub (20 + opCol st)) := by
    have h1 : ¬ (20 + opCol st < 3) := by omega
    have h2 : 20 ≤ 20 + opCol st ∧ 20 + opCol st < 42 := by omega
    simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_neg h1, dif_pos h2]
    congr 1
    show (envFAtD D c Q (firstRowD D)).pub (20 + (20 + opCol st - 20)) = _
    rw [Nat.add_sub_cancel_left]
  have htr : (rowEnvAtD D c Q (firstRowD D)).toSourceEnv.trace (opCol st) =
      algebraMap F K ((envFAtD D c Q (firstRowD D)).trace (opCol st)) := by
    rw [source_trace_base _ (opCol st) (by omega)]
    rfl
  simp only [initialMaskExpr, Expr.eval]
  rw [hpub, htr, hg]

omit RF hchar in
/-- Walk-`γ` at the family row is the tuple's `gamma` (compute `𝕂` slot `10`). -/
theorem walkGamma_atD (i : Fin (D.N)) :
    walkGammaChallenge.eval (rowEnvAtD D c Q i).toSourceEnv = gamma c.1 := by
  have h := rowEnvAtD_chal D L c Q i ⟨10, by decide⟩
  rw [show computeKOfTuple c 10 = gamma c.1 from rfl] at h
  simpa [walkGammaChallenge, walkGammaChallengeIndex, Expr.eval] using h

omit RF hchar in
/-- Walk-`α` at the family row is the tuple's `alphaC` (compute `𝕂` slot `6`). -/
theorem walkAlpha_atD (i : Fin (D.N)) :
    (walkChallenge 0).eval (rowEnvAtD D c Q i).toSourceEnv = alphaC c.1 := by
  have h := rowEnvAtD_chal D L c Q i ⟨6, by decide⟩
  rw [show computeKOfTuple c 6 = alphaC c.1 from rfl] at h
  simpa [walkChallenge, walkChallengeBase, Expr.eval] using h

omit RF hchar in
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

omit RF hchar in
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

omit RF hchar in
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
theorem maskedWalkAccInit_source_zeroD :
    finalMaskedWalkAccInit.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 0 := by
  obtain ⟨t, ht, hmem⟩ := lower_walkAccInit_exists
  rw [correctedLowerFinal_eval _ _ _ ht]
  exact (row_obligations_atD D L c Q RF (firstRowD D)).endpointDegreeFour1 t hmem

theorem maskedWalkLn1_source_zeroD :
    finalMaskedWalkLn1.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 0 := by
  obtain ⟨t, ht, hmem⟩ := lower_walkLn1_exists
  rw [correctedLowerFinal_eval _ _ _ ht]
  exact (row_obligations_atD D L c Q RF (firstRowD D)).endpointDegreeTwo2 t hmem

theorem maskedWalkCount1_source_zeroD :
    finalMaskedWalkCount1.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 0 := by
  obtain ⟨t, ht, hmem⟩ := lower_walkCount1_exists
  rw [correctedLowerFinal_eval _ _ _ ht]
  exact (row_obligations_atD D L c Q RF (firstRowD D)).endpointDegreeTwo2 t hmem

/-- **`ln(1) = αc`** at row 0 of an accepted family trace. -/
theorem walkLn_row0D :
    (finalWalkLine .traceCur).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = alphaC c.1 := by
  have h : finalMaskedWalkLn1.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 0 :=
    maskedWalkLn1_source_zeroD D L c Q RF hchar
  have hb1 : (rowEnvAtD D c Q (firstRowD D)).baseTrace 11 = 1 :=
    baseTrace11_row0D D L c Q RF hchar
  have hm : fixedIsFirst.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 1 := by
    simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
  simp only [finalMaskedWalkLn1, Expr.eval] at h
  rw [hm, one_mul, finalOptimizedWalkLn1] at h
  have heq :
      (Trans.walkLn1.subst finalWalkInitialSubst).eval
        (rowEnvAtD D c Q (firstRowD D)).toSourceEnv =
        (finalWalkLine .traceCur).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv -
          (walkChallenge 0).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv := by
    rw [Expr.eval_subst]; rfl
  rw [heq, sub_eq_zero] at h
  have hα :
      (walkChallenge 0).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = alphaC c.1 :=
    walkAlpha_atD D L c Q (firstRowD D)
  rw [h, hα]

/-- **`count(1) = initial_count · cm(1)`** at row 0. -/
theorem walkCount_row0D :
    (initialOverlayCoord 0).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv =
      (rowEnvAtD D c Q (firstRowD D)).toSourceEnv.pub 0 *
        (selectorCM firstReader).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv := by
  have h : finalMaskedWalkCount1.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 0 :=
    maskedWalkCount1_source_zeroD D L c Q RF hchar
  have hb1 : (rowEnvAtD D c Q (firstRowD D)).baseTrace 11 = 1 :=
    baseTrace11_row0D D L c Q RF hchar
  have hm : fixedIsFirst.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 1 := by
    simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
  simp only [finalMaskedWalkCount1, Expr.eval] at h
  rw [hm, one_mul, finalOptimizedWalkCount1] at h
  have heq :
      (Trans.walkCount1.subst finalWalkInitialSubst).eval
        (rowEnvAtD D c Q (firstRowD D)).toSourceEnv =
        (initialOverlayCoord 0).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv -
          (rowEnvAtD D c Q (firstRowD D)).toSourceEnv.pub 0 *
            (selectorCM firstReader).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv := by
    rw [Expr.eval_subst]; rfl
  rw [heq, sub_eq_zero] at h
  exact h

/-- **The row-0 walk identity, in the paper's operands**: with `ln(1) = αc`,
`αc · cur(1) + acc_walk(1) = initial_count · cc(1) + seed`. -/
theorem walkAccInit_row0D :
    alphaC c.1 * (labelRLC firstReader).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv +
        (initialOverlayCoord 1).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv =
      (rowEnvAtD D c Q (firstRowD D)).toSourceEnv.pub 0 *
          (childSumCC firstReader).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv +
        (rowEnvAtD D c Q (firstRowD D)).toSourceEnv.pub 1 := by
  have h : finalMaskedWalkAccInit.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 0 :=
    maskedWalkAccInit_source_zeroD D L c Q RF hchar
  have hb1 : (rowEnvAtD D c Q (firstRowD D)).baseTrace 11 = 1 :=
    baseTrace11_row0D D L c Q RF hchar
  have hm : fixedIsFirst.eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv = 1 := by
    simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
  simp only [finalMaskedWalkAccInit, Expr.eval] at h
  rw [hm, one_pow, finalOptimizedWalkAccInit] at h
  have heq :
      (Trans.walkAccInit.subst finalWalkInitialSubst).eval
        (rowEnvAtD D c Q (firstRowD D)).toSourceEnv =
        (finalWalkLine .traceCur).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv *
            (labelRLC firstReader).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv +
          (initialOverlayCoord 1).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv -
        ((rowEnvAtD D c Q (firstRowD D)).toSourceEnv.pub 0 *
            (childSumCC firstReader).eval (rowEnvAtD D c Q (firstRowD D)).toSourceEnv +
          (rowEnvAtD D c Q (firstRowD D)).toSourceEnv.pub 1) := by
    rw [Expr.eval_subst]; rfl
  rw [heq, one_mul, sub_eq_zero, walkLn_row0D D L c Q RF hchar] at h
  exact h

omit RF hchar in
/-- Extension public `1` of every family row is the verifier's `seedOfClaim`. -/
theorem family_seed_atD (i : Fin (D.N)) :
    (rowEnvAtD D c Q i).toSourceEnv.pub 1 =
      seedOfClaim D.claim c := by
  have h1 : (1 : ℕ) < 3 := by norm_num
  simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos h1]
  change (∑ k : Fin 3, (computePublicOfTuple D.basis D.claim D.pub c) (3 * 1 + (k : ℕ)) • D.basis k) = _
  have hcoord : ∀ k : Fin 3, (computePublicOfTuple D.basis D.claim D.pub c) (3 * 1 + (k : ℕ)) =
      coord D.basis (seedOfClaim D.claim c) k := by
    intro k
    have := computePublicOfTuple_seed_coord D.basis D.claim D.pub c k
    simpa [show 3 * 1 + (k : ℕ) = 3 + (k : ℕ) by ring] using this
  simp_rw [hcoord]
  exact reconstruct_coord D.basis _

omit RF hchar in
theorem family_initialCount_atD (i : Fin (D.N)) :
    (rowEnvAtD D c Q i).toSourceEnv.pub 0 = alphaC c.1 := by
  have h0 : (0 : ℕ) < 3 := by norm_num
  simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos h0]
  change (∑ k : Fin 3, (computePublicOfTuple D.basis D.claim D.pub c) (3 * 0 + (k : ℕ)) • D.basis k) = _
  have hcoord : ∀ k : Fin 3, (computePublicOfTuple D.basis D.claim D.pub c) (3 * 0 + (k : ℕ)) =
      coord D.basis (alphaC c.1) k := by
    intro k
    have := computePublicOfTuple_alpha_coord D.basis D.claim
      D.pub c k
    simpa using this
  simp_rw [hcoord]
  exact reconstruct_coord D.basis _


variable (hadj : D.Adjacent)

section Assembly

include hadj

/-- The source environment of family row `i`. -/
noncomputable abbrev envRD (i : Fin (D.N)) : Env K := (rowEnvAtD D c Q i).toSourceEnv


omit hadj in
/-- The one-hot state of row `i` (chosen; `deployed_row_one_hot_atD`). -/
noncomputable def stAtD (i : Fin (D.N)) : ComputeTable.State :=
  Classical.choose (deployed_row_one_hot_atD D L c Q RF hchar i)

omit hadj in
theorem stAt_specD (i : Fin (D.N)) : OneHotSelector (envRD D L c Q i) (stAtD D L c Q RF hchar i) :=
  Classical.choose_spec (deployed_row_one_hot_atD D L c Q RF hchar i)

omit hadj in
/-- The decoded row label (the `lblCAt` payload at the one-hot state). -/
noncomputable def pubAtD (i : Fin (D.N)) : Pub K :=
  decodePub (rowEnvAtD D c Q i) (stAtD D L c Q RF hchar i)

omit hadj in
/-- The three hosted child state tags of row `i` (Option A). -/
noncomputable def tagsAtD (i : Fin (D.N)) : Fin 3 → K :=
  fun j => (childTagHost curReader (stAtD D L c Q RF hchar i) j).eval (envRD D L c Q i)

omit hadj in
theorem hsel_atD (i : Fin (D.N)) :
    ∀ st, (envRD D L c Q i).trace (opCol st) =
      if st = (pubAtD D L c Q RF hchar i).state then 1 else 0 :=
  fun st => stAt_specD D L c Q RF hchar i st

omit hadj in
/-- Restored sources are the decoded
fingerprints. -/
theorem hsrc_atD (i : Fin (D.N)) :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR curReader (pubAtD D L c Q RF hchar i).state role cc).eval (envRD D L c Q i) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAtD D L c Q RF hchar i) ⟨role, hr⟩) ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_cur,
    OptimizedComputeSameExecution.sourcePubAt_eval_eq_semanticPub _ _ (hsel_atD D L c Q RF hchar i)
      role cc hr hc,
    show pubAtD D L c Q RF hchar i =
      pubOfState (Env.ofSubst computeSubst (envRD D L c Q i)) (stAtD D L c Q RF hchar i) from rfl,
    pubFingerprint_pubOfState, fpCoordinate_fpOf]
  exact (decoded_source_trace (envRD D L c Q i) ⟨role, hr⟩ ⟨cc, hc⟩).symm

omit RF hchar hadj in
theorem hγ_atD (i : Fin (D.N)) : walkGammaChallenge.eval (envRD D L c Q i) = gamma c.1 :=
  walkGamma_atD D L c Q i

omit RF hchar hadj in
theorem hα_atD (i : Fin (D.N)) : walkAlphaChallenge.eval (envRD D L c Q i) = alphaC c.1 :=
  walkAlpha_atD D L c Q i

omit RF hchar in
theorem envF_traceNext_eqD
    (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) :
    (envFAtD D c Q i).traceNext j = (envFAtD D c Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  have hadj := hadj i hi
  simp only [envOfTrace]
  split_ifs with h
  · rw [hadj]
  · rfl

omit RF hchar in
theorem shift_traceD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) :
    (envRD D L c Q i).traceNext j = (envRD D L c Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [envRD, CorrectedFinalTypedEnv.toSourceEnv]
  split_ifs with h13 h76 hcb h296 h299 h302
  · simp only [rowEnvAtD_eq_gather, gatherCorrectedFinalTypedEnv]
    rw [envF_traceNext_eqD D L c Q hadj i hi]
  · simp only [rowEnvAtD_eq_gather, gatherCorrectedFinalTypedEnv]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [envF_traceNext_eqD D L c Q hadj i hi]
  · simp only [rowEnvAtD_eq_gather, gatherCorrectedFinalTypedEnv]
    rw [envF_traceNext_eqD D L c Q hadj i hi]
  · simp only [rowEnvAtD_eq_gather, gatherCorrectedFinalTypedEnv]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [envF_traceNext_eqD D L c Q hadj i hi]
  · simp only [rowEnvAtD_eq_gather, gatherCorrectedFinalTypedEnv]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [envF_traceNext_eqD D L c Q hadj i hi]
  ·
    simp only [rowEnvAtD_eq_gather, gatherCorrectedFinalTypedEnv]
    rw [envF_traceNext_eqD D L c Q hadj i hi]
  · rfl

omit RF hchar in
theorem shift_trace71D (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    ∀ j, j < 71 → (shiftNext (envRD D L c Q i)).trace j = (envRD D L c Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  fun j _ => shift_traceD D L c Q hadj i hi j

theorem hsel_shiftD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    ∀ st, (curReader.sel st).eval (shiftNext (envRD D L c Q i)) =
      if st = (pubAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state then 1 else 0 := by
  intro st
  show (envRD D L c Q i).traceNext (opCol st) = _
  rw [shift_traceD D L c Q hadj i hi]
  exact hsel_atD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩ st

theorem hsrc_shiftD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR curReader (pubAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state role cc).eval
          (shiftNext (envRD D L c Q i)) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
            ⟨role, hr⟩) ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_cur_eval_congr (shift_trace71D D L c Q hadj i hi) _ role cc hr hc]
  exact hsrc_atD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩ role cc hr hc

theorem htag_shiftD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    ∀ j, (childTagHost curReader (pubAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state j).eval
        (shiftNext (envRD D L c Q i)) = tagsAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩ j := by
  intro j
  exact childTagHost_cur_eval_congr (shift_trace71D D L c Q hadj i hi) _ j

omit RF hchar hadj in
theorem hγ_shiftD (i : Fin (D.N)) :
    walkGammaChallenge.eval (shiftNext (envRD D L c Q i)) = gamma c.1 := by
  rw [gamma_eval_shift]; exact walkGamma_atD D L c Q i

omit RF hchar hadj in
theorem hα_shiftD (i : Fin (D.N)) :
    walkAlphaChallenge.eval (shiftNext (envRD D L c Q i)) = alphaC c.1 := by
  rw [alpha_eval_shift]; exact walkAlpha_atD D L c Q i

theorem nextLabel_evalD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    (labelRLC nextReader).eval (envRD D L c Q i) =
      Walk.rlc (gamma c.1) (labelVecOfPub (pubAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)) := by
  rw [labelRLC_next_eval]
  exact labelRLC_eval curReader _ _ _ (hsel_shiftD D L c Q RF hchar hadj i hi) (hsrc_shiftD D L c Q RF hchar hadj i hi)
    (hγ_shiftD D L c Q i)

theorem nextCC_evalD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    (childSumCC nextReader).eval (envRD D L c Q i) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)),
        alphaC c.1 ^ l * Walk.rlc (gamma c.1)
          (childVecN (pubAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
            (tagsAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩) (l - 1)) := by
  rw [childSumCC_next_eval]
  exact childSumCC_eval curReader _ _ _ _ _ (hsel_shiftD D L c Q RF hchar hadj i hi)
    (hsrc_shiftD D L c Q RF hchar hadj i hi) (hα_shiftD D L c Q i) (hγ_shiftD D L c Q i)
    (htag_shiftD D L c Q RF hchar hadj i hi)

theorem nextCM_evalD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    (selectorCM nextReader).eval (envRD D L c Q i) =
      alphaC c.1 ^ fanoutComp (stAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩) := by
  rw [selectorCM_next_eval]
  exact selectorCM_eval curReader _ _ _ (hsel_shiftD D L c Q RF hchar hadj i hi) (hα_shiftD D L c Q i)

omit RF hchar in
theorem nextLine_evalD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    (finalWalkLine .traceNext).eval (envRD D L c Q i) =
      (finalWalkLine .traceCur).eval (envRD D L c Q ⟨(i : ℕ) + 1, hi⟩) := by
  simp only [finalWalkLine, Expr.eval]
  exact shift_traceD D L c Q hadj i hi _

omit RF hchar hadj in
theorem overlayCur_eval_oneHot (env : Env K) (st : ComputeTable.State)
    (hone : OneHotSelector env st) (k : ℕ) (hk : k < 3) :
    (overlayCoord .traceCur k).eval env = (pubFP .traceCur (overlayANat st) k).eval env := by
  unfold overlayCoord
  rw [if_pos hk]
  exact selSum_eval curReader (fun s => pubFP .traceCur (overlayANat s) k) env st
    (fun s => hone s)

omit RF hchar hadj in
theorem overlayNext_eval_oneHot (env : Env K) (st : ComputeTable.State)
    (hone : ∀ s, env.traceNext (opCol s) = if s = st then 1 else 0) (k : ℕ) (hk : k < 3) :
    (overlayCoord .traceNext k).eval env = (pubFP .traceNext (overlayANat st) k).eval env := by
  unfold overlayCoord
  rw [if_pos hk]
  exact selSum_eval nextReader (fun s => pubFP .traceNext (overlayANat s) k) env st
    (fun s => hone s)

omit RF hchar hadj in
theorem initialOverlay_eval_oneHot (env : Env K) (st : ComputeTable.State)
    (hmask : ∀ s, (initialMaskExpr s).eval env = if s = st then 1 else 0) (k : ℕ) (hk : k < 3) :
    (initialOverlayCoord k).eval env = (pubFP .traceCur (overlayANat st) k).eval env := by
  unfold initialOverlayCoord
  rw [if_pos hk]
  exact selSum_eval firstReader (fun s => pubFP .traceCur (overlayANat s) k) env st hmask

/-- The terminal row through the public terminal masks (`OptimizedComputeTemplate.terminalMask`). -/
def termReader : RowReader := ⟨fun i => .Var .traceCur i, terminalMask⟩

omit RF hchar hadj in
theorem terminalOverlay_eval_oneHot (env : Env K) (st : ComputeTable.State)
    (hmask : ∀ s, (terminalMask s).eval env = if s = st then 1 else 0) (k : ℕ) (hk : k < 3) :
    (terminalOverlayCoord k).eval env = (pubFP .traceCur (overlayANat st) k).eval env := by
  unfold terminalOverlayCoord
  rw [if_pos hk]
  exact selSum_eval termReader (fun s => pubFP .traceCur (overlayANat s) k) env st hmask

theorem nextOverlay_evalD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) (k : ℕ) (hk : k < 3) :
    (overlayCoord .traceNext k).eval (envRD D L c Q i) =
      (overlayCoord .traceCur k).eval (envRD D L c Q ⟨(i : ℕ) + 1, hi⟩) := by
  rw [overlayNext_eval_oneHot (envRD D L c Q i) (stAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
      (fun s => hsel_shiftD D L c Q RF hchar hadj i hi s) k hk,
    overlayCur_eval_oneHot (envRD D L c Q ⟨(i : ℕ) + 1, hi⟩) (stAtD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
      (stAt_specD D L c Q RF hchar ⟨(i : ℕ) + 1, hi⟩) k hk]
  simp only [pubFP, Expr.eval]
  exact shift_traceD D L c Q hadj i hi _

theorem hmask_firstD :
    ∀ st, (firstReader.sel st).eval (envRD D L c Q (firstRowD D)) =
      if st = (pubAtD D L c Q RF hchar (firstRowD D)).state then 1 else 0 := by
  intro st
  show (initialMaskExpr st).eval _ = _
  rw [initialMask_eq_selector_row0D D L c Q RF hchar st]
  exact hsel_atD D L c Q RF hchar (firstRowD D) st

omit hadj in
theorem hsrc_firstD :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR firstReader (pubAtD D L c Q RF hchar (firstRowD D)).state role cc).eval
          (envRD D L c Q (firstRowD D)) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAtD D L c Q RF hchar (firstRowD D)) ⟨role, hr⟩)
          ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_first]
  exact hsrc_atD D L c Q RF hchar (firstRowD D) role cc hr hc

theorem firstLabel_evalD :
    (labelRLC firstReader).eval (envRD D L c Q (firstRowD D)) =
      Walk.rlc (gamma c.1) (labelVecOfPub (pubAtD D L c Q RF hchar (firstRowD D))) :=
  labelRLC_eval firstReader _ _ _ (hmask_firstD D L c Q RF hchar hadj) (hsrc_firstD D L c Q RF hchar)
    (hγ_atD D L c Q (firstRowD D))

theorem firstCC_evalD :
    (childSumCC firstReader).eval (envRD D L c Q (firstRowD D)) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAtD D L c Q RF hchar (firstRowD D))),
        alphaC c.1 ^ l * Walk.rlc (gamma c.1)
          (childVecN (pubAtD D L c Q RF hchar (firstRowD D)) (tagsAtD D L c Q RF hchar (firstRowD D)) (l - 1)) :=
  childSumCC_eval firstReader _ _ _ _ _ (hmask_firstD D L c Q RF hchar hadj) (hsrc_firstD D L c Q RF hchar)
    (hα_atD D L c Q (firstRowD D)) (hγ_atD D L c Q (firstRowD D))
    (fun j => by rw [childTagHost_first]; rfl)

theorem firstCM_evalD :
    (selectorCM firstReader).eval (envRD D L c Q (firstRowD D)) =
      alphaC c.1 ^ fanoutComp (stAtD D L c Q RF hchar (firstRowD D)) :=
  selectorCM_eval firstReader _ _ _ (hmask_firstD D L c Q RF hchar hadj) (hα_atD D L c Q (firstRowD D))

/-- Public-mask overlay reads at row 0 are the selector overlay reads. -/
theorem initialOverlay_eval_row0D (k : ℕ) (hk : k < 3) :
    (initialOverlayCoord k).eval (envRD D L c Q (firstRowD D)) =
      (overlayCoord .traceCur k).eval (envRD D L c Q (firstRowD D)) := by
  rw [initialOverlay_eval_oneHot _ (stAtD D L c Q RF hchar (firstRowD D)) (hmask_firstD D L c Q RF hchar hadj) k hk,
    overlayCur_eval_oneHot _ (stAtD D L c Q RF hchar (firstRowD D)) (stAt_specD D L c Q RF hchar (firstRowD D))
      k hk]

theorem terminalMask_eq_selector_lastD (st : ComputeTable.State) :
    (terminalMask st).eval (envRD D L c Q (lastRowD D)) =
      (envRD D L c Q (lastRowD D)).trace (opCol st) := by
  have hobl := row_obligations_atD D L c Q RF (lastRowD D)
  have hlt : opCol st < 11 := by cases st <;> decide
  have hg := hobl.selectorEquality2 (endpointEqualityCheck isLastVar 31 (opCol st)) (by
    simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨opCol st, hlt, rfl⟩)
  have hlast : (envFAtD D c Q (lastRowD D)).trace 12 = 1 := by
    have := (masks_at_row_atD D L c Q RF (lastRowD D)).2
    rw [if_pos rfl] at this
    exact this
  simp only [endpointEqualityCheck, isLastVar, bv, CoeffExpr.eval, hlast, one_mul,
    sub_eq_zero] at hg
  have hpub : (envRD D L c Q (lastRowD D)).pub (31 + opCol st) =
      algebraMap F K ((envFAtD D c Q (lastRowD D)).pub (31 + opCol st)) := by
    have h1 : ¬ (31 + opCol st < 3) := by omega
    have h2 : 20 ≤ 31 + opCol st ∧ 31 + opCol st < 42 := by omega
    simp only [envRD, CorrectedFinalTypedEnv.toSourceEnv, dif_neg h1, dif_pos h2]
    congr 1
    show (envFAtD D c Q (lastRowD D)).pub (20 + (31 + opCol st - 20)) = _
    congr 1
    omega
  have htr : (envRD D L c Q (lastRowD D)).trace (opCol st) =
      algebraMap F K ((envFAtD D c Q (lastRowD D)).trace (opCol st)) := by
    rw [envRD, source_trace_base _ (opCol st) (by omega)]
    rfl
  simp only [terminalMask, Expr.eval]
  rw [hpub, htr, hg]

theorem terminalOverlay_eval_lastD (k : ℕ) (hk : k < 3) :
    (terminalOverlayCoord k).eval (envRD D L c Q (lastRowD D)) =
      (overlayCoord .traceCur k).eval (envRD D L c Q (lastRowD D)) := by
  rw [terminalOverlay_eval_oneHot _ (stAtD D L c Q RF hchar (lastRowD D))
      (fun s => by
        rw [terminalMask_eq_selector_lastD D L c Q RF hchar hadj s]
        exact stAt_specD D L c Q RF hchar (lastRowD D) s) k hk,
    overlayCur_eval_oneHot _ (stAtD D L c Q RF hchar (lastRowD D)) (stAt_specD D L c Q RF hchar (lastRowD D))
      k hk]

omit RF hchar hadj in
theorem lower_walkOut_exists :
    ∃ t, correctedLowerFinal finalMaskedWalkOut = some t ∧ t ∈ correctedEndpoint2 := by
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
      finalAccTerminal, finalLnInit] hlen 2 (by simp)
  refine ⟨_, h, ?_⟩
  exact List.mem_filterMap.mpr ⟨finalMaskedWalkOut, by simp, h⟩

theorem isLast_source_lastD : (envRD D L c Q (lastRowD D)).trace 12 = 1 := by
  rw [envRD, source_trace_base _ 12 (by norm_num)]
  change algebraMap F K ((rowEnvAtD D c Q (lastRowD D)).baseTrace 12) = 1
  rw [(masks_at_row_atD D L c Q RF (lastRowD D)).2, if_pos rfl, map_one]

/-- **`out_walk = 0`**: the walk accumulator (overlay coordinate `1`) vanishes at the last row. -/
theorem walkOut_lastD :
    (overlayCoord .traceCur 1).eval (envRD D L c Q (lastRowD D)) = 0 := by
  obtain ⟨t, ht, hmem⟩ := lower_walkOut_exists
  have h := (row_obligations_atD D L c Q RF (lastRowD D)).endpointDegreeTwo2 t hmem
  rw [← correctedLowerFinal_eval _ _ _ ht] at h
  simp only [finalMaskedWalkOut, finalOptimizedWalkOut, Expr.eval, fixedIsLast,
    isLast_source_lastD D L c Q RF hchar hadj, one_mul] at h
  rw [Expr.eval_subst] at h
  change (terminalOverlayCoord 1).eval (envRD D L c Q (lastRowD D)) = 0 at h
  rw [terminalOverlay_eval_lastD D L c Q RF hchar hadj 1 (by norm_num)] at h
  exact h

omit RF hchar hadj in
theorem finalExtTransitionGates_get_walkLn :
    finalExtTransitionGates.get ⟨(packedWalkLnId : ℕ), by simp⟩ =
      Trans.walkLnStep.subst finalWalkSubstInGate := by
  simp [finalExtTransitionGates,
    OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append,
    OptimizedComputeGateBasis.paperPackingRowLocal_length,
    OptimizedComputeGateBasis.crossRowSingletons, List.getElem_append_right, List.append_assoc]

omit RF hchar hadj in
theorem finalExtTransitionGates_get_walkCount :
    finalExtTransitionGates.get ⟨(packedWalkCountId : ℕ), by simp⟩ =
      Trans.walkCountStep.subst finalWalkSubstInGate := by
  simp [finalExtTransitionGates,
    OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append,
    OptimizedComputeGateBasis.paperPackingRowLocal_length,
    OptimizedComputeGateBasis.crossRowSingletons, List.getElem_append_right, List.append_assoc]

omit RF hchar hadj in
theorem finalExtTransitionGates_get_walkAcc :
    finalExtTransitionGates.get ⟨(packedWalkAccId : ℕ), by simp⟩ =
      Trans.walkAccStep.subst finalWalkSubstInGate := by
  simp [finalExtTransitionGates,
    OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append,
    OptimizedComputeGateBasis.paperPackingRowLocal_length,
    OptimizedComputeGateBasis.crossRowSingletons, List.getElem_append_right, List.append_assoc]

theorem notLast_walkD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    (rowEnvAtD D c Q i).baseTrace 12 = 0 := by
  rw [(masks_at_row_atD D L c Q RF i).2, if_neg]
  intro heq
  have hv : (i : ℕ) = D.N - 1 := congrArg Fin.val heq
  omega

theorem walkLn_gate_zeroD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    (Trans.walkLnStep.subst finalWalkSubstInGate).eval (envRD D L c Q i) = 0 := by
  have hc := (row_obligations_atD D L c Q RF i).extensionCore21 packedWalkLnId
  have h75 : packedWalkLnId ≠ packedWalkCountId := by decide
  have h76 : packedWalkLnId ≠ packedWalkAccId := by decide
  have h80 : packedWalkLnId ≠ packedChainId := by decide
  have hnl := notLast_walkD D L c Q RF hchar hadj i hi
  have hgate : (correctedFinalExtGate packedWalkLnId).eval (rowEnvAtD D c Q i) = 0 := by
    simp only [correctedCoreSemanticValue, h75, h76, h80, ↓reduceIte, notLastScalar,
      hnl, map_one, sub_zero, one_mul] at hc
    exact hc
  have h2 := (correctedFinalExtGate_eval_source (rowEnvAtD D c Q i) packedWalkLnId).trans hgate
  rw [finalExtTransitionGates_get_walkLn] at h2
  exact h2

theorem walkCount_gate_zeroD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    (Trans.walkCountStep.subst finalWalkSubstInGate).eval (envRD D L c Q i) = 0 := by
  have hc := (row_obligations_atD D L c Q RF i).extensionCore21 packedWalkCountId
  have ha := (row_obligations_atD D L c Q RF i).residualAux3 0
  have hnl := notLast_walkD D L c Q RF hchar hadj i hi
  have hres : (rowEnvAtD D c Q i).extTrace (residualWitnessRole 0) = 0 := by
    simp only [correctedCoreSemanticValue, ↓reduceIte, notLastScalar, hnl, map_one, sub_zero,
      one_mul] at hc
    exact hc
  have hgate : (correctedFinalExtGate packedWalkCountId).eval (rowEnvAtD D c Q i) = 0 := by
    simp only [correctedAuxSemanticValue, correctedFinalResidualSource, hres] at ha
    have : (0 : Fin 3) = 2 ↔ False := by decide
    simp only [this, if_false, zero_sub, neg_eq_zero] at ha
    exact ha
  have h2 :=
    (correctedFinalExtGate_eval_source (rowEnvAtD D c Q i) packedWalkCountId).trans hgate
  rw [finalExtTransitionGates_get_walkCount] at h2
  exact h2

theorem walkAcc_gate_zeroD (i : Fin (D.N)) (hi : (i : ℕ) + 1 < D.N) :
    (Trans.walkAccStep.subst finalWalkSubstInGate).eval (envRD D L c Q i) = 0 := by
  have hc := (row_obligations_atD D L c Q RF i).extensionCore21 packedWalkAccId
  have ha := (row_obligations_atD D L c Q RF i).residualAux3 1
  have hnl := notLast_walkD D L c Q RF hchar hadj i hi
  have h74 : packedWalkAccId ≠ packedWalkCountId := by decide
  have hres : (rowEnvAtD D c Q i).extTrace (residualWitnessRole 1) = 0 := by
    simp only [correctedCoreSemanticValue, h74, ↓reduceIte, notLastScalar, hnl, map_one,
      sub_zero, one_mul] at hc
    exact hc
  have hgate : (correctedFinalExtGate packedWalkAccId).eval (rowEnvAtD D c Q i) = 0 := by
    simp only [correctedAuxSemanticValue, correctedFinalResidualSource, hres] at ha
    have : (1 : Fin 3) = 2 ↔ False := by decide
    simp only [this, if_false, zero_sub, neg_eq_zero] at ha
    exact ha
  have h2 :=
    (correctedFinalExtGate_eval_source (rowEnvAtD D c Q i) packedWalkAccId).trans hgate
  rw [finalExtTransitionGates_get_walkAcc] at h2
  exact h2

omit RF hchar hadj in
theorem walkLnStep_inGate_eval (env : Env K) :
    (Trans.walkLnStep.subst finalWalkSubstInGate).eval env =
      (finalWalkLine .traceNext).eval env - (walkChallenge 0).eval env *
        (finalWalkLine .traceCur).eval env := by
  rw [Expr.eval_subst]; rfl

omit RF hchar hadj in
theorem walkCountStep_inGate_eval (env : Env K) :
    (Trans.walkCountStep.subst finalWalkSubstInGate).eval env =
      (overlayCoord .traceNext 0).eval env -
        (overlayCoord .traceCur 0).eval env * (selectorCM nextReader).eval env := by
  rw [Expr.eval_subst]; rfl

omit RF hchar hadj in
/-- Row `i − 1` for `1 ≤ i ≤ D.N`; row 0 out of range (mirrors `lblC`). -/
def rowOfD (i : ℕ) : Fin (D.N) :=
  if h : i - 1 < D.N then ⟨i - 1, h⟩ else firstRowD D

omit RF hchar hadj in
theorem rowOf_succD (k : ℕ) (hk : k < D.N) : rowOfD D (k + 1) = ⟨k, hk⟩ := by
  simp [rowOfD, hk]

omit RF hchar hadj in
theorem rowOf_oneD : rowOfD D 1 = firstRowD D := by
  rw [rowOf_succD D 0 D.hN]

omit RF hchar hadj in
theorem rowOf_rowsD : rowOfD D (D.N) = lastRowD D := by
  have hpos : 0 < D.N := D.hN
  have h : D.N - 1 < D.N := Nat.sub_lt hpos (by omega)
  apply Fin.ext
  simp [rowOfD, h]

omit RF hchar hadj in
noncomputable def lnWD (i : ℕ) : K := (finalWalkLine .traceCur).eval (envRD D L c Q (rowOfD D i))

omit RF hchar hadj in
noncomputable def countWD (i : ℕ) : K := (overlayCoord .traceCur 0).eval (envRD D L c Q (rowOfD D i))

omit RF hchar hadj in
noncomputable def accWD (i : ℕ) : K := (overlayCoord .traceCur 1).eval (envRD D L c Q (rowOfD D i))

omit hadj in
noncomputable def curWD (i : ℕ) : K :=
  Walk.rlc (gamma c.1) (labelVecOfPub (pubAtD D L c Q RF hchar (rowOfD D i)))

omit hadj in
noncomputable def chldWD (i l : ℕ) : K :=
  Walk.rlc (gamma c.1)
    (childVecN (pubAtD D L c Q RF hchar (rowOfD D i)) (tagsAtD D L c Q RF hchar (rowOfD D i)) (l - 1))

omit hadj in
noncomputable def foWD (i : ℕ) : ℕ := fanoutComp (stAtD D L c Q RF hchar (rowOfD D i))

theorem deployed_walkSatD :
    WalkSat (curWD D L c Q RF hchar) (chldWD D L c Q RF hchar) (foWD D L c Q RF hchar) (lnWD D L c Q)
      (countWD D L c Q) (accWD D L c Q) (alphaC c.1)
      (seedOfClaim D.claim c)
      (alphaC c.1) (D.N) := by
  have hpos : 1 ≤ D.N := D.hN
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ln1
    show (finalWalkLine .traceCur).eval (envRD D L c Q (rowOfD D 1)) = alphaC c.1
    rw [rowOf_oneD]
    exact walkLn_row0D D L c Q RF hchar
  · -- lnInc
    intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (finalWalkLine .traceCur).eval (envRD D L c Q (rowOfD D (k + 1 + 1))) =
      alphaC c.1 * (finalWalkLine .traceCur).eval (envRD D L c Q (rowOfD D (k + 1)))
    rw [rowOf_succD D (k + 1) hk1, rowOf_succD D k hk]
    have h := walkLn_gate_zeroD D L c Q RF hchar hadj ⟨k, hk⟩ hk1
    rw [walkLnStep_inGate_eval, sub_eq_zero, nextLine_evalD D L c Q hadj ⟨k, hk⟩ hk1,
      walkAlpha_atD] at h
    exact h
  · -- count1
    show (overlayCoord .traceCur 0).eval (envRD D L c Q (rowOfD D 1)) =
      alphaC c.1 * alphaC c.1 ^ fanoutComp (stAtD D L c Q RF hchar (rowOfD D 1))
    rw [rowOf_oneD, ← initialOverlay_eval_row0D D L c Q RF hchar hadj 0 (by norm_num),
      walkCount_row0D D L c Q RF hchar, family_initialCount_atD,
      firstCM_evalD D L c Q RF hchar hadj]
  · -- countInc
    intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (overlayCoord .traceCur 0).eval (envRD D L c Q (rowOfD D (k + 1 + 1))) =
      (overlayCoord .traceCur 0).eval (envRD D L c Q (rowOfD D (k + 1))) *
        alphaC c.1 ^ fanoutComp (stAtD D L c Q RF hchar (rowOfD D (k + 1 + 1)))
    rw [rowOf_succD D (k + 1) hk1, rowOf_succD D k hk]
    have h := walkCount_gate_zeroD D L c Q RF hchar hadj ⟨k, hk⟩ hk1
    rw [walkCountStep_inGate_eval, sub_eq_zero,
      nextOverlay_evalD D L c Q RF hchar hadj ⟨k, hk⟩ hk1 0 (by norm_num),
      nextCM_evalD D L c Q RF hchar hadj] at h
    exact h
  · -- accInit
    show (finalWalkLine .traceCur).eval (envRD D L c Q (rowOfD D 1)) *
        Walk.rlc (gamma c.1) (labelVecOfPub (pubAtD D L c Q RF hchar (rowOfD D 1))) +
        (overlayCoord .traceCur 1).eval (envRD D L c Q (rowOfD D 1)) =
      (∑ l ∈ Finset.Icc 1 (fanoutComp (stAtD D L c Q RF hchar (rowOfD D 1))),
        alphaC c.1 ^ l * alphaC c.1 *
          Walk.rlc (gamma c.1)
            (childVecN (pubAtD D L c Q RF hchar (rowOfD D 1)) (tagsAtD D L c Q RF hchar (rowOfD D 1)) (l - 1)))
        + seedOfClaim D.claim c
    rw [rowOf_oneD]
    have h := walkAccInit_row0D D L c Q RF hchar
    rw [firstLabel_evalD D L c Q RF hchar hadj, initialOverlay_eval_row0D D L c Q RF hchar hadj 1 (by norm_num),
      firstCC_evalD D L c Q RF hchar hadj, family_seed_atD, family_initialCount_atD, Finset.mul_sum] at h
    rw [walkLn_row0D D L c Q RF hchar, h]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  · -- accStep
    intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (finalWalkLine .traceCur).eval (envRD D L c Q (rowOfD D (k + 1 + 1))) *
        Walk.rlc (gamma c.1) (labelVecOfPub (pubAtD D L c Q RF hchar (rowOfD D (k + 1 + 1)))) +
        (overlayCoord .traceCur 1).eval (envRD D L c Q (rowOfD D (k + 1 + 1))) -
        (overlayCoord .traceCur 1).eval (envRD D L c Q (rowOfD D (k + 1))) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAtD D L c Q RF hchar (rowOfD D (k + 1 + 1)))),
        alphaC c.1 ^ l * (overlayCoord .traceCur 0).eval (envRD D L c Q (rowOfD D (k + 1))) *
          Walk.rlc (gamma c.1)
            (childVecN (pubAtD D L c Q RF hchar (rowOfD D (k + 1 + 1)))
              (tagsAtD D L c Q RF hchar (rowOfD D (k + 1 + 1))) (l - 1))
    rw [rowOf_succD D (k + 1) hk1, rowOf_succD D k hk]
    have h := walkAcc_gate_zeroD D L c Q RF hchar hadj ⟨k, hk⟩ hk1
    rw [walkAccStep_inGate_eval, nextLine_evalD D L c Q hadj ⟨k, hk⟩ hk1,
      nextLabel_evalD D L c Q RF hchar hadj ⟨k, hk⟩ hk1, nextOverlay_evalD D L c Q RF hchar hadj ⟨k, hk⟩ hk1 1 (by norm_num),
      nextCC_evalD D L c Q RF hchar hadj ⟨k, hk⟩ hk1, Finset.mul_sum] at h
    have h' := sub_eq_zero.mp h
    rw [h']
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/-- **`out_walk = 0`** in the `ℕ`-indexed form. -/
theorem deployed_walk_outD : accWD D L c Q (D.N) = 0 := by
  show (overlayCoord .traceCur 1).eval (envRD D L c Q (rowOfD D (D.N))) = 0
  rw [rowOf_rowsD]
  exact walkOut_lastD D L c Q RF hchar hadj

omit hadj in
/-- The chosen one-hot state is `computeStateOf` of the decoded source (what `lblCAt` reads). -/
theorem stAt_eq_computeStateOfD (i : Fin (D.N)) :
    StrategyOfTraces.computeStateOf (decodeSource (rowEnvAtD D c Q i)) = stAtD D L c Q RF hchar i :=
  WrapFixesVcomp.computeStateOf_of_oneHot
    (oneHot_ofSubst _ _ (stAt_specD D L c Q RF hchar i))

    end Assembly
    
    end
    
    end Nock.NockVMROM.Thm54.SVCompute
    