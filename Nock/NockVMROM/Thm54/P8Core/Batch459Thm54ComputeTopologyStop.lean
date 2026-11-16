/-
  Nock/NockVMROM/Thm54/P8Core/Batch459Thm54ComputeTopologyStop.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch459Thm54ComputeTopologyStop`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch459Thm54ComputeTopologyStop.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch457Thm54RootLabelFromChip
import Nock.NockVMROM.Thm54.P8Core.WrapFixesVcomp
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch459

open Lean Meta Elab Command
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
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open Nock.RedTeam.Batch438
open Nock.RedTeam.Batch457

section Assembly

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

/-- The source environment of family row `i`. -/
noncomputable abbrev envR (i : Fin (rows P)) : Env K := (rowEnvAt P c Qc i).toSourceEnv

include hsat
include hax hbasis hwidth

omit hax hbasis hwidth in
/-- The one-hot state of row `i` (chosen; `deployed_row_one_hot_at`). -/
noncomputable def stAt (i : Fin (rows P)) : ComputeTable.State :=
  Classical.choose (deployed_row_one_hot_at P c Qc hsat i)

omit hax hbasis hwidth in
theorem stAt_spec (i : Fin (rows P)) : OneHotSelector (envR P c Qc i) (stAt P c Qc hsat i) :=
  Classical.choose_spec (deployed_row_one_hot_at P c Qc hsat i)

omit hax hbasis hwidth in
/-- The decoded row label (the `lblCAt` payload at the one-hot state). -/
noncomputable def pubAt (i : Fin (rows P)) : Pub K :=
  decodePub (rowEnvAt P c Qc i) (stAt P c Qc hsat i)

omit hax hbasis hwidth in
/-- The three hosted child state tags of row `i` (Option A). -/
noncomputable def tagsAt (i : Fin (rows P)) : Fin 3 → K :=
  fun j => (childTagHost curReader (stAt P c Qc hsat i) j).eval (envR P c Qc i)

omit hax hbasis hwidth in
theorem hsel_at (i : Fin (rows P)) :
    ∀ st, (envR P c Qc i).trace (opCol st) =
      if st = (pubAt P c Qc hsat i).state then 1 else 0 :=
  fun st => stAt_spec P c Qc hsat i st

omit hax hbasis hwidth in
/-- Restored sources are the decoded
fingerprints. -/
theorem hsrc_at (i : Fin (rows P)) :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR curReader (pubAt P c Qc hsat i).state role cc).eval (envR P c Qc i) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt P c Qc hsat i) ⟨role, hr⟩) ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_cur,
    OptimizedComputeSameExecution.sourcePubAt_eval_eq_semanticPub _ _ (hsel_at P c Qc hsat i)
      role cc hr hc,
    show pubAt P c Qc hsat i =
      pubOfState (Env.ofSubst computeSubst (envR P c Qc i)) (stAt P c Qc hsat i) from rfl,
    pubFingerprint_pubOfState, fpCoordinate_fpOf]
  exact (decoded_source_trace (envR P c Qc i) ⟨role, hr⟩ ⟨cc, hc⟩).symm

omit hsat hax hbasis hwidth in
theorem hγ_at (i : Fin (rows P)) : walkGammaChallenge.eval (envR P c Qc i) = gamma c.1 :=
  walkGamma_at P c Qc i

omit hsat hax hbasis hwidth in
theorem hα_at (i : Fin (rows P)) : walkAlphaChallenge.eval (envR P c Qc i) = alphaC c.1 :=
  walkAlpha_at P c Qc i

omit hsat in
theorem envF_traceNext_eq
    (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) (j : ℕ) :
    (envFAt P c Qc i).traceNext j = (envFAt P c Qc ⟨(i : ℕ) + 1, hi⟩).trace j := by
  have hadj := (P.optimized.computeRealization hax hbasis hwidth).adjacent_orbit i hi
  simp only [envFAt, envOfTrace]
  split_ifs with h
  · rw [hadj]
  · rfl

omit hsat in
theorem shift_trace (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) (j : ℕ) :
    (envR P c Qc i).traceNext j = (envR P c Qc ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [envR, CorrectedFinalTypedEnv.toSourceEnv]
  split_ifs with h13 h76 hcb h296 h299 h302
  · simp only [rowEnvAt_eq_gather, gatherCorrectedFinalTypedEnv]
    rw [envF_traceNext_eq P c Qc hax hbasis hwidth i hi]
  · simp only [rowEnvAt_eq_gather, gatherCorrectedFinalTypedEnv]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [envF_traceNext_eq P c Qc hax hbasis hwidth i hi]
  · simp only [rowEnvAt_eq_gather, gatherCorrectedFinalTypedEnv]
    rw [envF_traceNext_eq P c Qc hax hbasis hwidth i hi]
  · simp only [rowEnvAt_eq_gather, gatherCorrectedFinalTypedEnv]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [envF_traceNext_eq P c Qc hax hbasis hwidth i hi]
  · simp only [rowEnvAt_eq_gather, gatherCorrectedFinalTypedEnv]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [envF_traceNext_eq P c Qc hax hbasis hwidth i hi]
  ·
    simp only [rowEnvAt_eq_gather, gatherCorrectedFinalTypedEnv]
    rw [envF_traceNext_eq P c Qc hax hbasis hwidth i hi]
  · rfl

omit hsat in
theorem shift_trace71 (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    ∀ j, j < 71 → (shiftNext (envR P c Qc i)).trace j = (envR P c Qc ⟨(i : ℕ) + 1, hi⟩).trace j :=
  fun j _ => shift_trace P c Qc hax hbasis hwidth i hi j

theorem hsel_shift (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    ∀ st, (curReader.sel st).eval (shiftNext (envR P c Qc i)) =
      if st = (pubAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩).state then 1 else 0 := by
  intro st
  show (envR P c Qc i).traceNext (opCol st) = _
  rw [shift_trace P c Qc hax hbasis hwidth i hi]
  exact hsel_at P c Qc hsat ⟨(i : ℕ) + 1, hi⟩ st

theorem hsrc_shift (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR curReader (pubAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩).state role cc).eval
          (shiftNext (envR P c Qc i)) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩)
            ⟨role, hr⟩) ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_cur_eval_congr (shift_trace71 P c Qc hax hbasis hwidth i hi) _ role cc hr hc]
  exact hsrc_at P c Qc hsat ⟨(i : ℕ) + 1, hi⟩ role cc hr hc

theorem htag_shift (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    ∀ j, (childTagHost curReader (pubAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩).state j).eval
        (shiftNext (envR P c Qc i)) = tagsAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩ j := by
  intro j
  exact childTagHost_cur_eval_congr (shift_trace71 P c Qc hax hbasis hwidth i hi) _ j

omit hsat hax hbasis hwidth in
theorem hγ_shift (i : Fin (rows P)) :
    walkGammaChallenge.eval (shiftNext (envR P c Qc i)) = gamma c.1 := by
  rw [gamma_eval_shift]; exact walkGamma_at P c Qc i

omit hsat hax hbasis hwidth in
theorem hα_shift (i : Fin (rows P)) :
    walkAlphaChallenge.eval (shiftNext (envR P c Qc i)) = alphaC c.1 := by
  rw [alpha_eval_shift]; exact walkAlpha_at P c Qc i

theorem nextLabel_eval (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (labelRLC nextReader).eval (envR P c Qc i) =
      Walk.rlc (gamma c.1) (labelVecOfPub (pubAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩)) := by
  rw [labelRLC_next_eval]
  exact labelRLC_eval curReader _ _ _ (hsel_shift P c Qc hsat hax hbasis hwidth i hi) (hsrc_shift P c Qc hsat hax hbasis hwidth i hi)
    (hγ_shift P c Qc i)

theorem nextCC_eval (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (childSumCC nextReader).eval (envR P c Qc i) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩)),
        alphaC c.1 ^ l * Walk.rlc (gamma c.1)
          (childVecN (pubAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩)
            (tagsAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩) (l - 1)) := by
  rw [childSumCC_next_eval]
  exact childSumCC_eval curReader _ _ _ _ _ (hsel_shift P c Qc hsat hax hbasis hwidth i hi)
    (hsrc_shift P c Qc hsat hax hbasis hwidth i hi) (hα_shift P c Qc i) (hγ_shift P c Qc i)
    (htag_shift P c Qc hsat hax hbasis hwidth i hi)

theorem nextCM_eval (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (selectorCM nextReader).eval (envR P c Qc i) =
      alphaC c.1 ^ fanoutComp (stAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩) := by
  rw [selectorCM_next_eval]
  exact selectorCM_eval curReader _ _ _ (hsel_shift P c Qc hsat hax hbasis hwidth i hi) (hα_shift P c Qc i)

omit hsat in
theorem nextLine_eval (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (finalWalkLine .traceNext).eval (envR P c Qc i) =
      (finalWalkLine .traceCur).eval (envR P c Qc ⟨(i : ℕ) + 1, hi⟩) := by
  simp only [finalWalkLine, Expr.eval]
  exact shift_trace P c Qc hax hbasis hwidth i hi _

omit hsat hax hbasis hwidth in
theorem overlayCur_eval_oneHot (env : Env K) (st : ComputeTable.State)
    (hone : OneHotSelector env st) (k : ℕ) (hk : k < 3) :
    (overlayCoord .traceCur k).eval env = (pubFP .traceCur (overlayANat st) k).eval env := by
  unfold overlayCoord
  rw [if_pos hk]
  exact selSum_eval curReader (fun s => pubFP .traceCur (overlayANat s) k) env st
    (fun s => hone s)

omit hsat hax hbasis hwidth in
theorem overlayNext_eval_oneHot (env : Env K) (st : ComputeTable.State)
    (hone : ∀ s, env.traceNext (opCol s) = if s = st then 1 else 0) (k : ℕ) (hk : k < 3) :
    (overlayCoord .traceNext k).eval env = (pubFP .traceNext (overlayANat st) k).eval env := by
  unfold overlayCoord
  rw [if_pos hk]
  exact selSum_eval nextReader (fun s => pubFP .traceNext (overlayANat s) k) env st
    (fun s => hone s)

omit hsat hax hbasis hwidth in
theorem initialOverlay_eval_oneHot (env : Env K) (st : ComputeTable.State)
    (hmask : ∀ s, (initialMaskExpr s).eval env = if s = st then 1 else 0) (k : ℕ) (hk : k < 3) :
    (initialOverlayCoord k).eval env = (pubFP .traceCur (overlayANat st) k).eval env := by
  unfold initialOverlayCoord
  rw [if_pos hk]
  exact selSum_eval firstReader (fun s => pubFP .traceCur (overlayANat s) k) env st hmask

/-- The terminal row through the public terminal masks (`OptimizedComputeTemplate.terminalMask`). -/
def termReader : RowReader := ⟨fun i => .Var .traceCur i, terminalMask⟩

omit hsat hax hbasis hwidth in
theorem terminalOverlay_eval_oneHot (env : Env K) (st : ComputeTable.State)
    (hmask : ∀ s, (terminalMask s).eval env = if s = st then 1 else 0) (k : ℕ) (hk : k < 3) :
    (terminalOverlayCoord k).eval env = (pubFP .traceCur (overlayANat st) k).eval env := by
  unfold terminalOverlayCoord
  rw [if_pos hk]
  exact selSum_eval termReader (fun s => pubFP .traceCur (overlayANat s) k) env st hmask

theorem nextOverlay_eval (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) (k : ℕ) (hk : k < 3) :
    (overlayCoord .traceNext k).eval (envR P c Qc i) =
      (overlayCoord .traceCur k).eval (envR P c Qc ⟨(i : ℕ) + 1, hi⟩) := by
  rw [overlayNext_eval_oneHot (envR P c Qc i) (stAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩)
      (fun s => hsel_shift P c Qc hsat hax hbasis hwidth i hi s) k hk,
    overlayCur_eval_oneHot (envR P c Qc ⟨(i : ℕ) + 1, hi⟩) (stAt P c Qc hsat ⟨(i : ℕ) + 1, hi⟩)
      (stAt_spec P c Qc hsat ⟨(i : ℕ) + 1, hi⟩) k hk]
  simp only [pubFP, Expr.eval]
  exact shift_trace P c Qc hax hbasis hwidth i hi _

theorem hmask_first :
    ∀ st, (firstReader.sel st).eval (envR P c Qc (firstRow P)) =
      if st = (pubAt P c Qc hsat (firstRow P)).state then 1 else 0 := by
  intro st
  show (initialMaskExpr st).eval _ = _
  rw [initialMask_eq_selector_row0 P c Qc hsat hax hbasis hwidth st]
  exact hsel_at P c Qc hsat (firstRow P) st

omit hax hbasis hwidth in
theorem hsrc_first :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR firstReader (pubAt P c Qc hsat (firstRow P)).state role cc).eval
          (envR P c Qc (firstRow P)) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt P c Qc hsat (firstRow P)) ⟨role, hr⟩)
          ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_first]
  exact hsrc_at P c Qc hsat (firstRow P) role cc hr hc

theorem firstLabel_eval :
    (labelRLC firstReader).eval (envR P c Qc (firstRow P)) =
      Walk.rlc (gamma c.1) (labelVecOfPub (pubAt P c Qc hsat (firstRow P))) :=
  labelRLC_eval firstReader _ _ _ (hmask_first P c Qc hsat hax hbasis hwidth) (hsrc_first P c Qc hsat)
    (hγ_at P c Qc (firstRow P))

theorem firstCC_eval :
    (childSumCC firstReader).eval (envR P c Qc (firstRow P)) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt P c Qc hsat (firstRow P))),
        alphaC c.1 ^ l * Walk.rlc (gamma c.1)
          (childVecN (pubAt P c Qc hsat (firstRow P)) (tagsAt P c Qc hsat (firstRow P)) (l - 1)) :=
  childSumCC_eval firstReader _ _ _ _ _ (hmask_first P c Qc hsat hax hbasis hwidth) (hsrc_first P c Qc hsat)
    (hα_at P c Qc (firstRow P)) (hγ_at P c Qc (firstRow P))
    (fun j => by rw [childTagHost_first]; rfl)

theorem firstCM_eval :
    (selectorCM firstReader).eval (envR P c Qc (firstRow P)) =
      alphaC c.1 ^ fanoutComp (stAt P c Qc hsat (firstRow P)) :=
  selectorCM_eval firstReader _ _ _ (hmask_first P c Qc hsat hax hbasis hwidth) (hα_at P c Qc (firstRow P))

/-- Public-mask overlay reads at row 0 are the selector overlay reads. -/
theorem initialOverlay_eval_row0 (k : ℕ) (hk : k < 3) :
    (initialOverlayCoord k).eval (envR P c Qc (firstRow P)) =
      (overlayCoord .traceCur k).eval (envR P c Qc (firstRow P)) := by
  rw [initialOverlay_eval_oneHot _ (stAt P c Qc hsat (firstRow P)) (hmask_first P c Qc hsat hax hbasis hwidth) k hk,
    overlayCur_eval_oneHot _ (stAt P c Qc hsat (firstRow P)) (stAt_spec P c Qc hsat (firstRow P))
      k hk]

theorem terminalMask_eq_selector_last (st : ComputeTable.State) :
    (terminalMask st).eval (envR P c Qc (lastRow P)) =
      (envR P c Qc (lastRow P)).trace (opCol st) := by
  have hobl := row_obligations_at P c Qc hsat (lastRow P)
  have hlt : opCol st < 11 := by cases st <;> decide
  have hg := hobl.selectorEquality2 (endpointEqualityCheck isLastVar 31 (opCol st)) (by
    simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨opCol st, hlt, rfl⟩)
  have hlast : (envFAt P c Qc (lastRow P)).trace 12 = 1 := by
    have := (masks_at_row_at P c Qc hsat hax hbasis hwidth (lastRow P)).2
    rw [if_pos rfl] at this
    exact this
  simp only [endpointEqualityCheck, isLastVar, bv, CoeffExpr.eval, hlast, one_mul,
    sub_eq_zero] at hg
  have hpub : (envR P c Qc (lastRow P)).pub (31 + opCol st) =
      algebraMap F K ((envFAt P c Qc (lastRow P)).pub (31 + opCol st)) := by
    have h1 : ¬ (31 + opCol st < 3) := by omega
    have h2 : 20 ≤ 31 + opCol st ∧ 31 + opCol st < 42 := by omega
    simp only [envR, CorrectedFinalTypedEnv.toSourceEnv, dif_neg h1, dif_pos h2]
    congr 1
    show (envFAt P c Qc (lastRow P)).pub (20 + (31 + opCol st - 20)) = _
    congr 1
    omega
  have htr : (envR P c Qc (lastRow P)).trace (opCol st) =
      algebraMap F K ((envFAt P c Qc (lastRow P)).trace (opCol st)) := by
    rw [envR, source_trace_base _ (opCol st) (by omega)]
    rfl
  simp only [terminalMask, Expr.eval]
  rw [hpub, htr, hg]

theorem terminalOverlay_eval_last (k : ℕ) (hk : k < 3) :
    (terminalOverlayCoord k).eval (envR P c Qc (lastRow P)) =
      (overlayCoord .traceCur k).eval (envR P c Qc (lastRow P)) := by
  rw [terminalOverlay_eval_oneHot _ (stAt P c Qc hsat (lastRow P))
      (fun s => by
        rw [terminalMask_eq_selector_last P c Qc hsat hax hbasis hwidth s]
        exact stAt_spec P c Qc hsat (lastRow P) s) k hk,
    overlayCur_eval_oneHot _ (stAt P c Qc hsat (lastRow P)) (stAt_spec P c Qc hsat (lastRow P))
      k hk]

omit hsat hax hbasis hwidth in
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

theorem isLast_source_last : (envR P c Qc (lastRow P)).trace 12 = 1 := by
  rw [envR, source_trace_base _ 12 (by norm_num)]
  change algebraMap F K ((rowEnvAt P c Qc (lastRow P)).baseTrace 12) = 1
  rw [(masks_at_row_at P c Qc hsat hax hbasis hwidth (lastRow P)).2, if_pos rfl, map_one]

/-- **`out_walk = 0`**: the walk accumulator (overlay coordinate `1`) vanishes at the last row. -/
theorem walkOut_last :
    (overlayCoord .traceCur 1).eval (envR P c Qc (lastRow P)) = 0 := by
  obtain ⟨t, ht, hmem⟩ := lower_walkOut_exists
  have h := (row_obligations_at P c Qc hsat (lastRow P)).endpointDegreeTwo2 t hmem
  rw [← correctedLowerFinal_eval _ _ _ ht] at h
  simp only [finalMaskedWalkOut, finalOptimizedWalkOut, Expr.eval, fixedIsLast,
    isLast_source_last P c Qc hsat hax hbasis hwidth, one_mul] at h
  rw [Expr.eval_subst] at h
  change (terminalOverlayCoord 1).eval (envR P c Qc (lastRow P)) = 0 at h
  rw [terminalOverlay_eval_last P c Qc hsat hax hbasis hwidth 1 (by norm_num)] at h
  exact h

omit hsat hax hbasis hwidth in
theorem finalExtTransitionGates_get_walkLn :
    finalExtTransitionGates.get ⟨(packedWalkLnId : ℕ), by simp⟩ =
      Trans.walkLnStep.subst finalWalkSubstInGate := by
  simp [finalExtTransitionGates,
    OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append,
    OptimizedComputeGateBasis.paperPackingRowLocal_length,
    OptimizedComputeGateBasis.crossRowSingletons, List.getElem_append_right, List.append_assoc]

omit hsat hax hbasis hwidth in
theorem finalExtTransitionGates_get_walkCount :
    finalExtTransitionGates.get ⟨(packedWalkCountId : ℕ), by simp⟩ =
      Trans.walkCountStep.subst finalWalkSubstInGate := by
  simp [finalExtTransitionGates,
    OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append,
    OptimizedComputeGateBasis.paperPackingRowLocal_length,
    OptimizedComputeGateBasis.crossRowSingletons, List.getElem_append_right, List.append_assoc]

omit hsat hax hbasis hwidth in
theorem finalExtTransitionGates_get_walkAcc :
    finalExtTransitionGates.get ⟨(packedWalkAccId : ℕ), by simp⟩ =
      Trans.walkAccStep.subst finalWalkSubstInGate := by
  simp [finalExtTransitionGates,
    OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append,
    OptimizedComputeGateBasis.paperPackingRowLocal_length,
    OptimizedComputeGateBasis.crossRowSingletons, List.getElem_append_right, List.append_assoc]

theorem notLast_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvAt P c Qc i).baseTrace 12 = 0 := by
  rw [(masks_at_row_at P c Qc hsat hax hbasis hwidth i).2, if_neg]
  intro heq
  have hv : (i : ℕ) = rows P - 1 := congrArg Fin.val heq
  omega

theorem walkLn_gate_zero (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (Trans.walkLnStep.subst finalWalkSubstInGate).eval (envR P c Qc i) = 0 := by
  have hc := (row_obligations_at P c Qc hsat i).extensionCore21 packedWalkLnId
  have h75 : packedWalkLnId ≠ packedWalkCountId := by decide
  have h76 : packedWalkLnId ≠ packedWalkAccId := by decide
  have h80 : packedWalkLnId ≠ packedChainId := by decide
  have hnl := notLast_at P c Qc hsat hax hbasis hwidth i hi
  have hgate : (correctedFinalExtGate packedWalkLnId).eval (rowEnvAt P c Qc i) = 0 := by
    simp only [correctedCoreSemanticValue, h75, h76, h80, ↓reduceIte, notLastScalar,
      hnl, map_one, sub_zero, one_mul] at hc
    exact hc
  have h2 := (correctedFinalExtGate_eval_source (rowEnvAt P c Qc i) packedWalkLnId).trans hgate
  rw [finalExtTransitionGates_get_walkLn] at h2
  exact h2

theorem walkCount_gate_zero (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (Trans.walkCountStep.subst finalWalkSubstInGate).eval (envR P c Qc i) = 0 := by
  have hc := (row_obligations_at P c Qc hsat i).extensionCore21 packedWalkCountId
  have ha := (row_obligations_at P c Qc hsat i).residualAux3 0
  have hnl := notLast_at P c Qc hsat hax hbasis hwidth i hi
  have hres : (rowEnvAt P c Qc i).extTrace (residualWitnessRole 0) = 0 := by
    simp only [correctedCoreSemanticValue, ↓reduceIte, notLastScalar, hnl, map_one, sub_zero,
      one_mul] at hc
    exact hc
  have hgate : (correctedFinalExtGate packedWalkCountId).eval (rowEnvAt P c Qc i) = 0 := by
    simp only [correctedAuxSemanticValue, correctedFinalResidualSource, hres] at ha
    have : (0 : Fin 3) = 2 ↔ False := by decide
    simp only [this, if_false, zero_sub, neg_eq_zero] at ha
    exact ha
  have h2 :=
    (correctedFinalExtGate_eval_source (rowEnvAt P c Qc i) packedWalkCountId).trans hgate
  rw [finalExtTransitionGates_get_walkCount] at h2
  exact h2

theorem walkAcc_gate_zero (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (Trans.walkAccStep.subst finalWalkSubstInGate).eval (envR P c Qc i) = 0 := by
  have hc := (row_obligations_at P c Qc hsat i).extensionCore21 packedWalkAccId
  have ha := (row_obligations_at P c Qc hsat i).residualAux3 1
  have hnl := notLast_at P c Qc hsat hax hbasis hwidth i hi
  have h74 : packedWalkAccId ≠ packedWalkCountId := by decide
  have hres : (rowEnvAt P c Qc i).extTrace (residualWitnessRole 1) = 0 := by
    simp only [correctedCoreSemanticValue, h74, ↓reduceIte, notLastScalar, hnl, map_one,
      sub_zero, one_mul] at hc
    exact hc
  have hgate : (correctedFinalExtGate packedWalkAccId).eval (rowEnvAt P c Qc i) = 0 := by
    simp only [correctedAuxSemanticValue, correctedFinalResidualSource, hres] at ha
    have : (1 : Fin 3) = 2 ↔ False := by decide
    simp only [this, if_false, zero_sub, neg_eq_zero] at ha
    exact ha
  have h2 :=
    (correctedFinalExtGate_eval_source (rowEnvAt P c Qc i) packedWalkAccId).trans hgate
  rw [finalExtTransitionGates_get_walkAcc] at h2
  exact h2

omit hsat hax hbasis hwidth in
theorem walkLnStep_inGate_eval (env : Env K) :
    (Trans.walkLnStep.subst finalWalkSubstInGate).eval env =
      (finalWalkLine .traceNext).eval env - (walkChallenge 0).eval env *
        (finalWalkLine .traceCur).eval env := by
  rw [Expr.eval_subst]; rfl

omit hsat hax hbasis hwidth in
theorem walkCountStep_inGate_eval (env : Env K) :
    (Trans.walkCountStep.subst finalWalkSubstInGate).eval env =
      (overlayCoord .traceNext 0).eval env -
        (overlayCoord .traceCur 0).eval env * (selectorCM nextReader).eval env := by
  rw [Expr.eval_subst]; rfl

omit hsat hax hbasis hwidth in
/-- Row `i − 1` for `1 ≤ i ≤ rows P`; row 0 out of range (mirrors `lblC`). -/
def rowOf (i : ℕ) : Fin (rows P) :=
  if h : i - 1 < rows P then ⟨i - 1, h⟩ else firstRow P

omit hsat hax hbasis hwidth in
theorem rowOf_succ (k : ℕ) (hk : k < rows P) : rowOf P (k + 1) = ⟨k, hk⟩ := by
  simp [rowOf, hk]

omit hsat hax hbasis hwidth in
theorem rowOf_one : rowOf P 1 = firstRow P := by
  rw [rowOf_succ P 0 P.optimized.family.problem.cfg.compRows_pos]

omit hsat hax hbasis hwidth in
theorem rowOf_rows : rowOf P (rows P) = lastRow P := by
  have hpos : 0 < rows P := P.optimized.family.problem.cfg.compRows_pos
  have h : rows P - 1 < rows P := Nat.sub_lt hpos (by omega)
  apply Fin.ext
  simp [rowOf, h]

omit hsat hax hbasis hwidth in
noncomputable def lnW (i : ℕ) : K := (finalWalkLine .traceCur).eval (envR P c Qc (rowOf P i))

omit hsat hax hbasis hwidth in
noncomputable def countW (i : ℕ) : K := (overlayCoord .traceCur 0).eval (envR P c Qc (rowOf P i))

omit hsat hax hbasis hwidth in
noncomputable def accW (i : ℕ) : K := (overlayCoord .traceCur 1).eval (envR P c Qc (rowOf P i))

omit hax hbasis hwidth in
noncomputable def curW (i : ℕ) : K :=
  Walk.rlc (gamma c.1) (labelVecOfPub (pubAt P c Qc hsat (rowOf P i)))

omit hax hbasis hwidth in
noncomputable def chldW (i l : ℕ) : K :=
  Walk.rlc (gamma c.1)
    (childVecN (pubAt P c Qc hsat (rowOf P i)) (tagsAt P c Qc hsat (rowOf P i)) (l - 1))

omit hax hbasis hwidth in
noncomputable def foW (i : ℕ) : ℕ := fanoutComp (stAt P c Qc hsat (rowOf P i))

theorem deployed_walkSat :
    WalkSat (curW P c Qc hsat) (chldW P c Qc hsat) (foW P c Qc hsat) (lnW P c Qc)
      (countW P c Qc) (accW P c Qc) (alphaC c.1)
      (seedOfClaim P.optimized.verifier.raw.claim c)
      (alphaC c.1) (rows P) := by
  have hpos : 1 ≤ rows P := P.optimized.family.problem.cfg.compRows_pos
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ln1
    show (finalWalkLine .traceCur).eval (envR P c Qc (rowOf P 1)) = alphaC c.1
    rw [rowOf_one]
    exact walkLn_row0 P c Qc hsat hax hbasis hwidth
  · -- lnInc
    intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < rows P := by omega
    have hk1 : k + 1 < rows P := by omega
    show (finalWalkLine .traceCur).eval (envR P c Qc (rowOf P (k + 1 + 1))) =
      alphaC c.1 * (finalWalkLine .traceCur).eval (envR P c Qc (rowOf P (k + 1)))
    rw [rowOf_succ P (k + 1) hk1, rowOf_succ P k hk]
    have h := walkLn_gate_zero P c Qc hsat hax hbasis hwidth ⟨k, hk⟩ hk1
    rw [walkLnStep_inGate_eval, sub_eq_zero, nextLine_eval P c Qc hax hbasis hwidth ⟨k, hk⟩ hk1,
      walkAlpha_at] at h
    exact h
  · -- count1
    show (overlayCoord .traceCur 0).eval (envR P c Qc (rowOf P 1)) =
      alphaC c.1 * alphaC c.1 ^ fanoutComp (stAt P c Qc hsat (rowOf P 1))
    rw [rowOf_one, ← initialOverlay_eval_row0 P c Qc hsat hax hbasis hwidth 0 (by norm_num),
      walkCount_row0 P c Qc hsat hax hbasis hwidth, family_initialCount_at,
      firstCM_eval P c Qc hsat hax hbasis hwidth]
  · -- countInc
    intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < rows P := by omega
    have hk1 : k + 1 < rows P := by omega
    show (overlayCoord .traceCur 0).eval (envR P c Qc (rowOf P (k + 1 + 1))) =
      (overlayCoord .traceCur 0).eval (envR P c Qc (rowOf P (k + 1))) *
        alphaC c.1 ^ fanoutComp (stAt P c Qc hsat (rowOf P (k + 1 + 1)))
    rw [rowOf_succ P (k + 1) hk1, rowOf_succ P k hk]
    have h := walkCount_gate_zero P c Qc hsat hax hbasis hwidth ⟨k, hk⟩ hk1
    rw [walkCountStep_inGate_eval, sub_eq_zero,
      nextOverlay_eval P c Qc hsat hax hbasis hwidth ⟨k, hk⟩ hk1 0 (by norm_num),
      nextCM_eval P c Qc hsat hax hbasis hwidth] at h
    exact h
  · -- accInit
    show (finalWalkLine .traceCur).eval (envR P c Qc (rowOf P 1)) *
        Walk.rlc (gamma c.1) (labelVecOfPub (pubAt P c Qc hsat (rowOf P 1))) +
        (overlayCoord .traceCur 1).eval (envR P c Qc (rowOf P 1)) =
      (∑ l ∈ Finset.Icc 1 (fanoutComp (stAt P c Qc hsat (rowOf P 1))),
        alphaC c.1 ^ l * alphaC c.1 *
          Walk.rlc (gamma c.1)
            (childVecN (pubAt P c Qc hsat (rowOf P 1)) (tagsAt P c Qc hsat (rowOf P 1)) (l - 1)))
        + seedOfClaim P.optimized.verifier.raw.claim c
    rw [rowOf_one]
    have h := walkAccInit_row0 P c Qc hsat hax hbasis hwidth
    rw [firstLabel_eval P c Qc hsat hax hbasis hwidth, initialOverlay_eval_row0 P c Qc hsat hax hbasis hwidth 1 (by norm_num),
      firstCC_eval P c Qc hsat hax hbasis hwidth, family_seed_at, family_initialCount_at, Finset.mul_sum] at h
    rw [walkLn_row0 P c Qc hsat hax hbasis hwidth, h]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  · -- accStep
    intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < rows P := by omega
    have hk1 : k + 1 < rows P := by omega
    show (finalWalkLine .traceCur).eval (envR P c Qc (rowOf P (k + 1 + 1))) *
        Walk.rlc (gamma c.1) (labelVecOfPub (pubAt P c Qc hsat (rowOf P (k + 1 + 1)))) +
        (overlayCoord .traceCur 1).eval (envR P c Qc (rowOf P (k + 1 + 1))) -
        (overlayCoord .traceCur 1).eval (envR P c Qc (rowOf P (k + 1))) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt P c Qc hsat (rowOf P (k + 1 + 1)))),
        alphaC c.1 ^ l * (overlayCoord .traceCur 0).eval (envR P c Qc (rowOf P (k + 1))) *
          Walk.rlc (gamma c.1)
            (childVecN (pubAt P c Qc hsat (rowOf P (k + 1 + 1)))
              (tagsAt P c Qc hsat (rowOf P (k + 1 + 1))) (l - 1))
    rw [rowOf_succ P (k + 1) hk1, rowOf_succ P k hk]
    have h := walkAcc_gate_zero P c Qc hsat hax hbasis hwidth ⟨k, hk⟩ hk1
    rw [walkAccStep_inGate_eval, nextLine_eval P c Qc hax hbasis hwidth ⟨k, hk⟩ hk1,
      nextLabel_eval P c Qc hsat hax hbasis hwidth ⟨k, hk⟩ hk1, nextOverlay_eval P c Qc hsat hax hbasis hwidth ⟨k, hk⟩ hk1 1 (by norm_num),
      nextCC_eval P c Qc hsat hax hbasis hwidth ⟨k, hk⟩ hk1, Finset.mul_sum] at h
    have h' := sub_eq_zero.mp h
    rw [h']
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/-- **`out_walk = 0`** in the `ℕ`-indexed form. -/
theorem deployed_walk_out : accW P c Qc (rows P) = 0 := by
  show (overlayCoord .traceCur 1).eval (envR P c Qc (rowOf P (rows P))) = 0
  rw [rowOf_rows]
  exact walkOut_last P c Qc hsat hax hbasis hwidth

omit hsat hax hbasis hwidth in
/-- The chosen one-hot state is `computeStateOf` of the decoded source (what `lblCAt` reads). -/
theorem stAt_eq_computeStateOf (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin (rows P)) :
    StrategyOfTraces.computeStateOf (decodeSource (rowEnvAt P c Qc i)) = stAt P c Qc hsat i :=
  WrapFixesVcomp.computeStateOf_of_oneHot
    (oneHot_ofSubst _ _ (stAt_spec P c Qc hsat i))

end Assembly

end Nock.RedTeam.Batch459
