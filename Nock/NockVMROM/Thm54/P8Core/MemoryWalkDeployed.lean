/-
  Nock/NockVMROM/Thm54/P8Core/MemoryWalkDeployed.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.MemoryWalkDeployed`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/MemoryWalkDeployed.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch475Thm54MemoryWalkAlphaInitialCount
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.MemoryWalkDeployed

open scoped Classical
open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.FixedPreprocessingRAP
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler.MixedExpr (ofExpr)
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.RedTeam.Batch475
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
  (hchar : MemStateTagChar F)

abbrev memRows : ℕ := P.optimized.family.problem.cfg.memRows

abbrev kMem : ℕ := P.optimized.family.problem.cfg.kMem

omit hsat hchar in
theorem memRows_pos : 1 ≤ memRows P :=
  Nat.succ_le_of_lt P.optimized.family.problem.cfg.memRows_pos

omit hsat hchar in
def firstMem : Fin (memRows P) := ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩

omit hsat hchar in
def lastMem : Fin (memRows P) :=
  ⟨memRows P - 1, Nat.sub_lt P.optimized.family.problem.cfg.memRows_pos (by omega)⟩

omit hsat hchar in
def Qmh : Fin P.memoryChip.rap.w → F[X] := honestQm P c Qm

omit hsat hchar in
def envF (i : Fin (memRows P)) : Env F := memoryBaseEnvAt P c (Qmh P c Qm) i

omit hsat hchar in
def envK (i : Fin (memRows P)) : Env K := memorySourceEnvAt P c (Qmh P c Qm) i

omit hsat hchar in
abbrev sourceAt : FixedPreprocessingRAP F :=
  namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis
    (memoryChalValOfTuple P.optimized.basis c)
    (P.familyMemoryPublic c) P.optimized.orbit
    P.optimized.family.problem.cfg.kMem

include hsat in
theorem projAt_firstMask :
    projAt P c Qm ⟨4, by norm_num⟩ =
      OptimizedMemoryCanonicalTrace.firstRowMask P.optimized.memoryNodes := by
  have hbind := (source_sat_at P c Qm hsat).2
  have hw : (sourceAt P c).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis
      (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  have h4 : 4 < (sourceAt P c).rap.w := by rw [hw]; norm_num
  have h0 := hbind ⟨0, by change (0 : ℕ) < 4; norm_num⟩
  have hc0 : (sourceAt P c).preprocessingColumn ⟨0, by change (0 : ℕ) < 4; norm_num⟩ =
      ⟨4, h4⟩ := rfl
  rw [hc0] at h0
  change projAt P c Qm ⟨4, h4⟩ = (sourceAt P c).preprocessing ⟨0, by change (0 : ℕ) < 4; norm_num⟩ at h0
  simpa [sourceAt, namedSourceMemoryRAP] using h0

include hsat in
theorem projAt_lastMask :
    projAt P c Qm ⟨5, by norm_num⟩ =
      OptimizedMemoryCanonicalTrace.lastRowMask P.optimized.memoryNodes := by
  have hbind := (source_sat_at P c Qm hsat).2
  have hw : (sourceAt P c).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis
      (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  have h5 : 5 < (sourceAt P c).rap.w := by rw [hw]; norm_num
  have h1 := hbind ⟨1, by change (1 : ℕ) < 4; norm_num⟩
  have hc1 : (sourceAt P c).preprocessingColumn ⟨1, by change (1 : ℕ) < 4; norm_num⟩ =
      ⟨5, h5⟩ := rfl
  rw [hc1] at h1
  change projAt P c Qm ⟨5, h5⟩ = (sourceAt P c).preprocessing ⟨1, by change (1 : ℕ) < 4; norm_num⟩ at h1
  simpa [sourceAt, namedSourceMemoryRAP] using h1

include hsat in
theorem projAt_dequeueMask :
    projAt P c Qm ⟨154, by norm_num⟩ =
      OptimizedMemoryCanonicalTrace.dequeueRowMask P.optimized.memoryNodes
        (kMem P) := by
  have hbind := (source_sat_at P c Qm hsat).2
  have hw : (sourceAt P c).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis
      (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  have h154 : 154 < (sourceAt P c).rap.w := by rw [hw]; norm_num
  have h3 := hbind ⟨3, by change (3 : ℕ) < 4; norm_num⟩
  have hc3 : (sourceAt P c).preprocessingColumn ⟨3, by change (3 : ℕ) < 4; norm_num⟩ =
      ⟨154, h154⟩ := rfl
  rw [hc3] at h3
  change projAt P c Qm ⟨154, h154⟩ =
    (sourceAt P c).preprocessing ⟨3, by change (3 : ℕ) < 4; norm_num⟩ at h3
  simpa [sourceAt, namedSourceMemoryRAP] using h3

include hsat in
theorem envF_trace4 (i : Fin (memRows P)) :
    (envF P c Qm i).trace 4 = (if (i : ℕ) = 0 then 1 else 0) := by
  have h4 : (4 : ℕ) < 182 := by norm_num
  simp only [envF, Qmh]
  rw [← envF_eq_base P c Qm i]
  simp only [envOfTrace, dif_pos h4]
  rw [projAt_firstMask P c Qm hsat,
    OptimizedMemoryCanonicalTrace.firstRowMask_eval _
      P.optimized.memoryNodes_injective]

include hsat in
theorem envF_trace5 (i : Fin (memRows P)) :
    (envF P c Qm i).trace 5 = (if (i : ℕ) + 1 = memRows P then 1 else 0) := by
  have h5 : (5 : ℕ) < 182 := by norm_num
  simp only [envF, Qmh]
  rw [← envF_eq_base P c Qm i]
  simp only [envOfTrace, dif_pos h5]
  rw [projAt_lastMask P c Qm hsat,
    OptimizedMemoryCanonicalTrace.lastRowMask_eval _
      P.optimized.memoryNodes_injective]

include hsat in
theorem envF_trace154 (i : Fin (memRows P)) :
    (envF P c Qm i).trace 154 =
      (if (i : ℕ) + 1 = memRows P then 0
       else if (i : ℕ) + 1 < kMem P then 0
       else 1) := by
  have h154 : (154 : ℕ) < 182 := by norm_num
  simp only [envF, Qmh]
  rw [← envF_eq_base P c Qm i]
  simp only [envOfTrace, dif_pos h154]
  rw [projAt_dequeueMask P c Qm hsat,
    OptimizedMemoryCanonicalTrace.dequeueRowMask_eval _
      (kMem P) P.optimized.memoryNodes_injective]

omit hsat hchar in
theorem envF_traceNext (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P) (j : ℕ) :
    (envF P c Qm i).traceNext j = (envF P c Qm ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [envF, Qmh, memoryBaseEnvAt, envOfTrace]
  rw [P.optimized.memoryOrbitAligned i hi]
  split_ifs <;> simp [mul_comm]

omit hsat hchar in
theorem envK_traceNext (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P) (r : ℕ) :
    (envK P c Qm i).traceNext r = (envK P c Qm ⟨(i : ℕ) + 1, hi⟩).trace r := by
  simp only [envK, Qmh, memorySourceEnvAt, gatherEnv, memorySourceTemplate_col0,
    memoryCol0]
  apply Finset.sum_congr rfl
  intro k _
  have h := envF_traceNext P c Qm i hi (6 + 3 * r + (k : ℕ))
  simp only [envF, Qmh] at h
  rw [h]

omit hsat hchar in
theorem envK_chal (i : Fin (memRows P)) (q : Fin 9) :
    (envK P c Qm i).chal q = memoryKOfTuple c q := by
  have hcol :
      (memorySourceTemplate P.optimized.basis).col0 3 = memoryCol0 :=
    memorySourceTemplate_col0 P.optimized.basis
  simp only [envK, Qmh, memorySourceEnvAt, hcol, gatherEnv, memoryCol0,
    memoryBaseEnvAt, envOfTrace]
  simp_rw [memoryChalValOfTuple_slot P.optimized.basis c q]
  change reconstruct P.optimized.basis (coord P.optimized.basis (memoryKOfTuple c q)) =
    memoryKOfTuple c q
  exact reconstruct_coord P.optimized.basis (memoryKOfTuple c q)

omit hsat hchar in
theorem envK_alpha (i : Fin (memRows P)) :
    (envK P c Qm i).chal 3 = alphaM c.1 := by
  rw [envK_chal P c Qm i ⟨3, by decide⟩]; rfl

omit hsat hchar in
theorem envK_gamma (i : Fin (memRows P)) :
    (envK P c Qm i).chal 7 = gamma c.1 := by
  rw [envK_chal P c Qm i ⟨7, by decide⟩]; rfl

omit hsat hchar in
theorem envK_pub0 (i : Fin (memRows P)) :
    (envK P c Qm i).pub 0 = alphaM c.1 ^ kMem P := by
  have hcol :
      (memorySourceTemplate P.optimized.basis).col0 3 = memoryCol0 :=
    memorySourceTemplate_col0 P.optimized.basis
  simp only [envK, Qmh, memorySourceEnvAt, hcol, gatherEnv, memoryCol0,
    memoryBaseEnvAt, envOfTrace]
  simpa using memory_initialCount_is_coin P c

include hsat hchar in
theorem oneHot_at (i : Fin (memRows P)) :
    ∃ st, MemoryPaperFactorization.BaseOneHot (envF P c Qm i) st :=
  baseOneHot_at_family P c Qm hsat i hchar

omit hsat in
def stAt (i : Fin (memRows P)) : MState :=
  memoryStateOf (envF P c Qm i)

omit hsat in
def pubAt (i : Fin (memRows P)) : Pub K :=
  decodeMemPub P (Qmh P c Qm) c i

omit hsat in
def tagsAt (i : Fin (memRows P)) : Fin 2 → K :=
  fun j => (envK P c Qm i).trace (childTagHostRole j)

include hchar in
theorem stAt_eq_oneHot (i : Fin (memRows P))
    (st : MState) (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm i) st) :
    stAt P c Qm i = st := by
  simp only [stAt, envF, Qmh]
  exact memoryStateOf_eq_of_baseOneHot _ _ hone

omit hsat in
theorem pubAt_st (i : Fin (memRows P)) :
    (pubAt P c Qm i).st = stAt P c Qm i := by
  simp only [pubAt, stAt, decodeMemPub, envF, Qmh]

include hchar in
theorem hsel_cur (i : Fin (memRows P))
    (st : MState) (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm i) st) :
    ∀ st', ((curReader (F := F)).sel st').eval (envF P c Qm i) =
      if st' = st then 1 else 0 :=
  fun st' => hone st'

include hchar in
theorem hsel_next (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P)
    (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm ⟨(i : ℕ) + 1, hi⟩) st) :
    ∀ st', ((nextReader (F := F)).sel st').eval (envF P c Qm i) =
      if st' = st then 1 else 0 := by
  intro st'
  simp only [nextReader_sel_eval]
  rw [envF_traceNext P c Qm i hi]
  exact hone st'

omit hsat hchar in
theorem cur_cell (i : Fin (memRows P)) (k : Fin 5) :
    ((curReader (F := F)).col k).eval (envK P c Qm i) (envF P c Qm i) =
      cellCoord (pubAt P c Qm i).pt k := by
  fin_cases k <;> simp [curReader_col_eval, pubAt, decodeMemPub, envK, Qmh,
    cellCoord, memoryPtNoun]

omit hsat hchar in
theorem next_cell (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P)
    (k : Fin 5) :
    ((nextReader (F := F)).col k).eval (envK P c Qm i) (envF P c Qm i) =
      cellCoord (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).pt k := by
  have h := cur_cell P c Qm ⟨(i : ℕ) + 1, hi⟩ k
  fin_cases k <;>
    (simp only [nextReader_col_eval, curReader_col_eval] at h ⊢
     rw [envK_traceNext P c Qm i hi]
     exact h)

omit hsat hchar in
theorem cur_child_cell (i : Fin (memRows P)) (j : Fin 2) (k : Fin 5) :
    ((curReader (F := F)).col (cellBase j + (k : ℕ))).eval
        (envK P c Qm i) (envF P c Qm i) =
      cellCoord (childCell (pubAt P c Qm i) j) k := by
  fin_cases j <;> fin_cases k <;>
    simp [curReader_col_eval, cellBase, childCell, pubAt, decodeMemPub, cellCoord,
      envK, Qmh]

omit hsat hchar in
theorem next_child_cell (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P)
    (j : Fin 2) (k : Fin 5) :
    ((nextReader (F := F)).col (cellBase j + (k : ℕ))).eval
        (envK P c Qm i) (envF P c Qm i) =
      cellCoord (childCell (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩) j) k := by
  have h := cur_child_cell P c Qm ⟨(i : ℕ) + 1, hi⟩ j k
  simp only [nextReader_col_eval, curReader_col_eval] at h ⊢
  rw [envK_traceNext P c Qm i hi]
  exact h

omit hsat hchar in
theorem walkGamma_eval (i : Fin (memRows P)) :
    (walkGammaChallenge (F := F)).eval (envK P c Qm i) (envF P c Qm i) =
      gamma c.1 := by
  simpa [walkGammaChallenge, walkGammaChallengeIndex, MixedExpr.eval]
    using envK_gamma P c Qm i

omit hsat hchar in
theorem walkAlpha_eval (i : Fin (memRows P)) :
    (walkAlphaChallenge (F := F)).eval (envK P c Qm i) (envF P c Qm i) =
      alphaM c.1 := by
  simpa [walkAlphaChallenge, walkAlphaChallengeIndex, MixedExpr.eval]
    using envK_alpha P c Qm i

include hsat hchar in
theorem labelRLC_next (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P)
    (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm ⟨(i : ℕ) + 1, hi⟩) st) :
    (labelRLC (nextReader (F := F))).eval (envK P c Qm i) (envF P c Qm i) =
      Walk.rlc (gamma c.1) (memoryLabelVec (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩)) := by
  have hst : (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P c Qm hchar _ st hone]
  have hsel : ∀ st', ((nextReader (F := F)).sel st').eval (envF P c Qm i) =
      if st' = (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st then 1 else 0 := by
    intro st'; rw [hst]; exact hsel_next P c Qm hchar i hi st hone st'
  refine labelRLC_eval (nextReader (F := F)) _ _ (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩)
    (gamma c.1) hsel (next_cell P c Qm i hi) ?_
  simpa [walkGammaChallenge, walkGammaChallengeIndex, MixedExpr.eval]
    using envK_gamma P c Qm i

include hsat hchar in
theorem childSum_cur (i : Fin (memRows P))
    (st : MState) (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm i) st) :
    (childSumCC (curReader (F := F))).eval (envK P c Qm i) (envF P c Qm i) =
      ∑ l ∈ Finset.Icc 1 (fanoutMem (pubAt P c Qm i).st),
        alphaM c.1 ^ l *
          Walk.rlc (gamma c.1) (childVecN (pubAt P c Qm i) (tagsAt P c Qm i) (l - 1)) := by
  have hst : (pubAt P c Qm i).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P c Qm hchar i st hone]
  have hsel : ∀ st', ((curReader (F := F)).sel st').eval (envF P c Qm i) =
      if st' = (pubAt P c Qm i).st then 1 else 0 := by
    intro st'; rw [hst]; exact hsel_cur P c Qm hchar i st hone st'
  exact childSumCC_eval (curReader (F := F)) _ _ (pubAt P c Qm i) (alphaM c.1)
    (gamma c.1) (tagsAt P c Qm i) hsel (cur_child_cell P c Qm i)
    (walkAlpha_eval P c Qm i) (walkGamma_eval P c Qm i)
    (fun j => by simp [childTagHost, curReader_col_eval, tagsAt])

include hsat hchar in
theorem childSum_next (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P)
    (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm ⟨(i : ℕ) + 1, hi⟩) st) :
    (childSumCC (nextReader (F := F))).eval (envK P c Qm i) (envF P c Qm i) =
      ∑ l ∈ Finset.Icc 1 (fanoutMem (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st),
        alphaM c.1 ^ l *
          Walk.rlc (gamma c.1)
            (childVecN (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩)
              (tagsAt P c Qm ⟨(i : ℕ) + 1, hi⟩) (l - 1)) := by
  have hst : (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P c Qm hchar _ st hone]
  have hsel : ∀ st', ((nextReader (F := F)).sel st').eval (envF P c Qm i) =
      if st' = (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st then 1 else 0 := by
    intro st'; rw [hst]; exact hsel_next P c Qm hchar i hi st hone st'
  refine childSumCC_eval (nextReader (F := F)) _ _ (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩)
    (alphaM c.1) (gamma c.1) (tagsAt P c Qm ⟨(i : ℕ) + 1, hi⟩) hsel
    (next_child_cell P c Qm i hi) ?_ ?_ ?_
  · simpa [walkAlphaChallenge, walkAlphaChallengeIndex, MixedExpr.eval]
      using envK_alpha P c Qm i
  · simpa [walkGammaChallenge, walkGammaChallengeIndex, MixedExpr.eval]
      using envK_gamma P c Qm i
  · intro j
    simp [childTagHost, nextReader_col_eval, tagsAt, envK_traceNext P c Qm i hi]

include hsat hchar in
theorem selectorCM_cur (i : Fin (memRows P))
    (st : MState) (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm i) st) :
    (selectorCM (curReader (F := F))).eval (envK P c Qm i) (envF P c Qm i) =
      alphaM c.1 ^ fanoutMem (pubAt P c Qm i).st := by
  have hst : (pubAt P c Qm i).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P c Qm hchar i st hone]
  have hsel : ∀ st', ((curReader (F := F)).sel st').eval (envF P c Qm i) =
      if st' = (pubAt P c Qm i).st then 1 else 0 := by
    intro st'; rw [hst]; exact hsel_cur P c Qm hchar i st hone st'
  exact selectorCM_eval (curReader (F := F)) _ _ (pubAt P c Qm i) (alphaM c.1)
    hsel (walkAlpha_eval P c Qm i)

include hsat hchar in
theorem selectorCM_next (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P)
    (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm ⟨(i : ℕ) + 1, hi⟩) st) :
    (selectorCM (nextReader (F := F))).eval (envK P c Qm i) (envF P c Qm i) =
      alphaM c.1 ^ fanoutMem (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st := by
  have hst : (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P c Qm hchar _ st hone]
  have hsel : ∀ st', ((nextReader (F := F)).sel st').eval (envF P c Qm i) =
      if st' = (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st then 1 else 0 := by
    intro st'; rw [hst]; exact hsel_next P c Qm hchar i hi st hone st'
  refine selectorCM_eval (nextReader (F := F)) _ _ (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩)
    (alphaM c.1) hsel ?_
  simpa [walkAlphaChallenge, walkAlphaChallengeIndex, MixedExpr.eval]
    using envK_alpha P c Qm i

omit hchar in
theorem walkLn1InGate_mem :
    (.Scale (bcur 4) (ofExpr (Trans.walkLn1.subst walkBoundarySubst)) : MixedExpr F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, paperKGatesCore, walkGates, walkInitGates]

omit hchar in
theorem walkLnStepInGate_mem :
    (.Scale (.sub (.const 1) (bcur 5))
        (ofExpr (Trans.walkLnStep.subst walkSubst)) : MixedExpr F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, paperKGatesCore, walkGates, walkStepGates]

omit hchar in
theorem walkCount1InGate_mem :
    walkCount1InGate (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, paperKGatesCore, walkGates, walkInitGates]

omit hchar in
theorem walkCountStepInGate_mem :
    walkCountStepInGate (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, paperKGatesCore, walkGates, walkStepGates]

omit hchar in
theorem walkAccInitInGate_mem :
    walkAccInitInGate (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, paperKGatesCore, walkGates, walkInitGates]

omit hchar in
theorem walkAccStepInGate_mem :
    walkAccStepInGate (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, paperKGatesCore, walkGates, walkStepGates]

omit hchar in
theorem walkTerminal_mem :
    walkTerminal (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, paperKGatesCore, walkGates]

omit hchar in
theorem walkQueueNonEmpty_mem :
    walkQueueNonEmpty (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, MemoryWalkLabel.queueWitnessGates]

omit hchar in
theorem walkQueueTiling_mem :
    walkQueueTiling (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
  change _ ∈ paperKGates (F := F) ++ [haltAtomMixed]
  simp [paperKGates, MemoryWalkLabel.queueWitnessGates]

include hsat in
theorem mixed_zero (i : Fin (memRows P)) {g : MixedExpr F}
    (hg : g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis) :
    g.eval (envK P c Qm i) (envF P c Qm i) = 0 := by
  simpa [envK, envF, Qmh] using mixed_at_family P c Qm hsat i g hg

omit hsat hchar in
theorem walkLn1_subst_eval (eK : Env K) :
    (Trans.walkLn1.subst walkBoundarySubst).eval eK =
      eK.trace lnRole - eK.chal 3 := by
  simp [Trans.walkLn1, Reified.tc, Reified.chl, Expr.subst, Expr.eval,
    walkBoundarySubst, extVar, lnRole]

omit hsat hchar in
theorem walkLn1InGate_eval (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (bcur 4) (ofExpr (Trans.walkLn1.subst walkBoundarySubst)) :
        MixedExpr F).eval eK eF =
      algebraMap F K (eF.trace 4) * (eK.trace lnRole - eK.chal 3) := by
  rw [MixedExpr.eval, MixedExpr.ofExpr_eval, walkLn1_subst_eval]
  simp [CoeffExpr.eval, bcur]

omit hsat hchar in
theorem walkLnStep_subst_eval (eK : Env K) :
    (Trans.walkLnStep.subst walkSubst).eval eK =
      eK.traceNext lnRole - eK.chal 3 * eK.trace lnRole := by
  simp [Trans.walkLnStep, Trans.tn, Reified.tc, Reified.chl, Expr.subst, Expr.eval,
    walkSubst, extVar, lnRole]

omit hsat hchar in
theorem walkLnStepInGate_eval (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (.sub (.const 1) (bcur 5))
        (ofExpr (Trans.walkLnStep.subst walkSubst)) : MixedExpr F).eval eK eF =
      algebraMap F K (1 - eF.trace 5) *
        (eK.traceNext lnRole - eK.chal 3 * eK.trace lnRole) := by
  rw [MixedExpr.eval, MixedExpr.ofExpr_eval, walkLnStep_subst_eval]
  simp [CoeffExpr.eval, bcur]

include hsat in
theorem walkLn_row0 :
    (envK P c Qm (firstMem P)).trace lnRole = alphaM c.1 := by
  have h := mixed_zero P c Qm hsat (firstMem P) (walkLn1InGate_mem P)
  rw [walkLn1InGate_eval, envF_trace4 P c Qm hsat (firstMem P)] at h
  have h0 : (firstMem P : ℕ) = 0 := rfl
  simp only [h0, ↓reduceIte, map_one, one_mul] at h
  rw [sub_eq_zero] at h
  rw [h, envK_alpha]

include hsat in
theorem walkLn_step (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    (envK P c Qm ⟨(i : ℕ) + 1, hi⟩).trace lnRole =
      alphaM c.1 * (envK P c Qm i).trace lnRole := by
  have h := mixed_zero P c Qm hsat i (walkLnStepInGate_mem P)
  rw [walkLnStepInGate_eval, envF_trace5 P c Qm hsat i] at h
  simp only [show (i : ℕ) + 1 ≠ memRows P by omega, ↓reduceIte, sub_zero, map_one,
    one_mul] at h
  rw [envK_traceNext P c Qm i hi, envK_alpha, sub_eq_zero] at h
  exact h

include hsat hchar in
theorem walkCount_row0 :
    (envK P c Qm (firstMem P)).trace countRole =
      alphaM c.1 ^ kMem P *
        alphaM c.1 ^ fanoutMem (pubAt P c Qm (firstMem P)).st := by
  obtain ⟨st, hone⟩ := oneHot_at P c Qm hsat hchar (firstMem P)
  have h := mixed_zero P c Qm hsat (firstMem P) (walkCount1InGate_mem P)
  rw [walkCount1InGate_eval, envF_trace4 P c Qm hsat (firstMem P)] at h
  have h0 : (firstMem P : ℕ) = 0 := rfl
  simp only [h0, ↓reduceIte, map_one, one_mul] at h
  rw [sub_eq_zero, envK_pub0] at h
  rw [h, selectorCM_cur P c Qm hsat hchar (firstMem P) st hone]

include hsat hchar in
theorem walkCount_step (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    (envK P c Qm ⟨(i : ℕ) + 1, hi⟩).trace countRole =
      (envK P c Qm i).trace countRole *
        alphaM c.1 ^ fanoutMem (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st := by
  obtain ⟨st, hone⟩ := oneHot_at P c Qm hsat hchar ⟨(i : ℕ) + 1, hi⟩
  have h := mixed_zero P c Qm hsat i (walkCountStepInGate_mem P)
  rw [walkCountStepInGate_eval, envF_trace5 P c Qm hsat i] at h
  simp only [show (i : ℕ) + 1 ≠ memRows P by omega, ↓reduceIte, sub_zero, map_one,
    one_mul] at h
  rw [envK_traceNext P c Qm i hi, sub_eq_zero] at h
  rw [h, selectorCM_next P c Qm hsat hchar i hi st hone]

include hsat hchar in
/-- First row is a root (`kMem ≥ 1`): `acc(1) = initial_count·cc(1)` (`WalkSatInGate.accInit`). -/
theorem walkAcc_row0 :
    (envK P c Qm (firstMem P)).trace accRole =
      (envK P c Qm (firstMem P)).pub 0 *
        ∑ l ∈ Finset.Icc 1 (fanoutMem (pubAt P c Qm (firstMem P)).st),
          alphaM c.1 ^ l *
            Walk.rlc (gamma c.1)
              (childVecN (pubAt P c Qm (firstMem P)) (tagsAt P c Qm (firstMem P))
                (l - 1)) := by
  obtain ⟨st, hone⟩ := oneHot_at P c Qm hsat hchar (firstMem P)
  have h := mixed_zero P c Qm hsat (firstMem P) (walkAccInitInGate_mem P)
  rw [walkAccInitInGate_eval, envF_trace4 P c Qm hsat (firstMem P)] at h
  have h0 : (firstMem P : ℕ) = 0 := rfl
  simp only [h0, ↓reduceIte, map_one, one_mul] at h
  rw [sub_eq_zero] at h
  rw [childSum_cur P c Qm hsat hchar (firstMem P) st hone] at h
  exact h

include hsat hchar in
/-- Masked step: `dequeueMask · ln · RLC + Δacc = count · cc` (`WalkSatInGate.accStep`). -/
theorem walkAcc_step (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    algebraMap F K ((envF P c Qm i).trace 154) *
        ((envK P c Qm ⟨(i : ℕ) + 1, hi⟩).trace lnRole *
          Walk.rlc (gamma c.1) (memoryLabelVec (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩))) +
      (envK P c Qm ⟨(i : ℕ) + 1, hi⟩).trace accRole -
        (envK P c Qm i).trace accRole =
      (envK P c Qm i).trace countRole *
        ∑ l ∈ Finset.Icc 1 (fanoutMem (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩).st),
          alphaM c.1 ^ l *
            Walk.rlc (gamma c.1)
              (childVecN (pubAt P c Qm ⟨(i : ℕ) + 1, hi⟩)
                (tagsAt P c Qm ⟨(i : ℕ) + 1, hi⟩) (l - 1)) := by
  obtain ⟨st, hone⟩ := oneHot_at P c Qm hsat hchar ⟨(i : ℕ) + 1, hi⟩
  have h := mixed_zero P c Qm hsat i (walkAccStepInGate_mem P)
  rw [walkAccStepInGate_eval, envF_trace5 P c Qm hsat i] at h
  simp only [show (i : ℕ) + 1 ≠ memRows P by omega, ↓reduceIte, sub_zero, map_one,
    one_mul] at h
  rw [envK_traceNext P c Qm i hi, envK_traceNext P c Qm i hi] at h
  have h' := h
  rw [labelRLC_next P c Qm hsat hchar i hi st hone,
    childSum_next P c Qm hsat hchar i hi st hone] at h'
  linear_combination h'

include hsat in
theorem walkOut_last :
    (envK P c Qm (lastMem P)).trace accRole = 0 := by
  have h := mixed_zero P c Qm hsat (lastMem P) (walkTerminal_mem P)
  simp only [walkTerminal, MixedExpr.eval, CoeffExpr.eval, bcur] at h
  rw [envF_trace5 P c Qm hsat (lastMem P)] at h
  have hlast : (lastMem P : ℕ) + 1 = memRows P := by
    change memRows P - 1 + 1 = memRows P
    exact Nat.sub_add_cancel (memRows_pos P)
  simp only [hlast, ↓reduceIte, map_one, one_mul] at h
  exact h

omit hsat hchar in
def rowOf (i : ℕ) : Fin (memRows P) :=
  if h : i - 1 < memRows P then ⟨i - 1, h⟩ else firstMem P

omit hsat hchar in
theorem rowOf_succ (k : ℕ) (hk : k < memRows P) : rowOf P (k + 1) = ⟨k, hk⟩ := by
  simp [rowOf, hk]

omit hsat hchar in
theorem rowOf_one : rowOf P 1 = firstMem P := by
  rw [rowOf_succ P 0 P.optimized.family.problem.cfg.memRows_pos]; rfl

omit hsat hchar in
theorem rowOf_rows : rowOf P (memRows P) = lastMem P := by
  have h : memRows P - 1 < memRows P :=
    Nat.sub_lt P.optimized.family.problem.cfg.memRows_pos (by omega)
  apply Fin.ext
  simp [rowOf, lastMem, h]

omit hsat hchar in
def lnW (i : ℕ) : K := (envK P c Qm (rowOf P i)).trace lnRole

omit hsat hchar in
def countW (i : ℕ) : K := (envK P c Qm (rowOf P i)).trace countRole

omit hsat hchar in
def accW (i : ℕ) : K := (envK P c Qm (rowOf P i)).trace accRole

omit hsat in
def curW (i : ℕ) : K :=
  Walk.rlc (gamma c.1) (memoryLabelVec (pubAt P c Qm (rowOf P i)))

omit hsat in
def chldW (i l : ℕ) : K :=
  Walk.rlc (gamma c.1)
    (childVecN (pubAt P c Qm (rowOf P i)) (tagsAt P c Qm (rowOf P i)) (l - 1))

omit hsat in
def foW (i : ℕ) : ℕ := fanoutMem (pubAt P c Qm (rowOf P i)).st

omit hsat hchar in
theorem kMem_pos : 1 ≤ kMem P := by
  have hpos : 0 < P.objects.cfg.kMem := P.objects.exec.memoryRootCount_pos
  have hk := congrArg ExactConfig.kMem P.optimized.family_cfg
  rw [← hk] at hpos
  exact Nat.succ_le_of_lt hpos

omit hsat hchar in
theorem kMem_le : kMem P ≤ memRows P := by
  have hkObj : P.objects.cfg.kMem ≤ P.objects.cfg.memRows :=
    P.objects.exec.kMem_le_memRows
  have hk := congrArg ExactConfig.kMem P.optimized.family_cfg
  have hm := congrArg ExactConfig.memRows P.optimized.family_cfg
  rwa [← hk, ← hm] at hkObj

include hsat in
theorem dequeue_eq_deqCoeff (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P) :
    algebraMap F K ((envF P c Qm i).trace 154) =
      deqCoeff (K := K) (kMem P) ((i : ℕ) + 2) := by
  rw [envF_trace154 P c Qm hsat i]
  have hnl : (i : ℕ) + 1 ≠ memRows P := Nat.ne_of_lt hi
  simp only [hnl, ↓reduceIte]
  unfold deqCoeff Walk.rootMask
  by_cases hroot : (i : ℕ) + 1 < kMem P
  · have hle : (i : ℕ) + 2 ≤ kMem P := Nat.succ_le_of_lt hroot
    simp [hroot, hle]
  · have hn : ¬ ((i : ℕ) + 2 ≤ kMem P) := fun h => hroot (Nat.lt_of_succ_le h)
    simp [hroot, hn]

include hsat hchar in
/-- **`WalkSatInGate` of the deployed memory chip's walk columns**, for every `c`
and every accepted `Qm`: mask-form acc, no seed
public.  `α = alphaM c.1`, `initial_count = α ^ kMem`. -/
theorem deployed_walkSat :
    WalkSatInGate (curW P c Qm) (chldW P c Qm) (foW P c Qm) (lnW P c Qm)
      (countW P c Qm) (accW P c Qm) (alphaM c.1)
      (alphaM c.1 ^ kMem P) (kMem P) (memRows P) := by
  refine ⟨memRows_pos P, kMem_pos P, kMem_le P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (envK P c Qm (rowOf P 1)).trace lnRole = alphaM c.1
    rw [rowOf_one]; exact walkLn_row0 P c Qm hsat
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < memRows P := by omega
    have hk1 : k + 1 < memRows P := by omega
    show (envK P c Qm (rowOf P (k + 1 + 1))).trace lnRole =
      alphaM c.1 * (envK P c Qm (rowOf P (k + 1))).trace lnRole
    rw [rowOf_succ P (k + 1) hk1, rowOf_succ P k hk]
    exact walkLn_step P c Qm hsat ⟨k, hk⟩ hk1
  · show (envK P c Qm (rowOf P 1)).trace countRole =
      alphaM c.1 ^ kMem P * alphaM c.1 ^ fanoutMem (pubAt P c Qm (rowOf P 1)).st
    rw [rowOf_one]; exact walkCount_row0 P c Qm hsat hchar
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < memRows P := by omega
    have hk1 : k + 1 < memRows P := by omega
    show (envK P c Qm (rowOf P (k + 1 + 1))).trace countRole =
      (envK P c Qm (rowOf P (k + 1))).trace countRole *
        alphaM c.1 ^ fanoutMem (pubAt P c Qm (rowOf P (k + 1 + 1))).st
    rw [rowOf_succ P (k + 1) hk1, rowOf_succ P k hk]
    exact walkCount_step P c Qm hsat hchar ⟨k, hk⟩ hk1
  · show (envK P c Qm (rowOf P 1)).trace accRole =
      ∑ l ∈ Finset.Icc 1 (fanoutMem (pubAt P c Qm (rowOf P 1)).st),
        alphaM c.1 ^ l * (alphaM c.1 ^ kMem P) *
          Walk.rlc (gamma c.1)
            (childVecN (pubAt P c Qm (rowOf P 1)) (tagsAt P c Qm (rowOf P 1)) (l - 1))
    rw [rowOf_one]
    have h := walkAcc_row0 P c Qm hsat hchar
    rw [envK_pub0] at h
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < memRows P := by omega
    have hk1 : k + 1 < memRows P := by omega
    simp only [accW, lnW, countW, curW, chldW, foW]
    rw [rowOf_succ P (k + 1) hk1, rowOf_succ P k hk]
    have hdeq := dequeue_eq_deqCoeff P c Qm hsat ⟨k, hk⟩ hk1
    have h := walkAcc_step P c Qm hsat hchar ⟨k, hk⟩ hk1
    rw [← hdeq]
    convert h using 1
    · ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring

include hsat in
theorem deployed_walk_out : accW P c Qm (memRows P) = 0 := by
  simp only [accW, rowOf_rows]
  exact walkOut_last P c Qm hsat

omit hsat in
theorem foW_eq_foM_all (i : ℕ) :
    foW P c Qm i = foM P (Qmh P c Qm) c i := by
  simp only [foW, foM, lblM, pubAt, Qmh, rowOf]
  split_ifs <;> rfl

end

end Nock.NockVMROM.Thm54.MemoryWalkDeployed
