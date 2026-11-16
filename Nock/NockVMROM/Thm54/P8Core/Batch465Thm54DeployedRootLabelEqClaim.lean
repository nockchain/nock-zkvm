/-
  Nock/NockVMROM/Thm54/P8Core/Batch465Thm54DeployedRootLabelEqClaim.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch465Thm54DeployedRootLabelEqClaim.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch458Thm54StrategyBindsStop
import Nock.NockVMROM.Thm54.P8Core.Batch459Thm54ComputeTopologyStop
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch465

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.RedTeam.Batch457
open Nock.RedTeam.Batch458
open Nock.RedTeam.Batch459
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Framework.Reify
open MonolithicRAP
open OptimizedHostileTimestamps
open Module

noncomputable section

section Congr

variable {K : Type} [Field K] [DecidableEq K]

theorem nodeListP_congr {cur cur' : ℕ → K} {k : ℕ}
    (h : ∀ i, 1 ≤ i → i ≤ k → cur i = cur' i) :
    nodeListP cur k = nodeListP cur' k := by
  unfold nodeListP
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2]

theorem Sf_congr {fo fo' : ℕ → ℕ} {k : ℕ} (h : ∀ i, 1 ≤ i → i ≤ k → fo i = fo' i) :
    Sf fo k = Sf fo' k := by
  unfold Sf
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2]

theorem queueTerm_congr {chld chld' : ℕ → ℕ → K} {fo fo' : ℕ → ℕ} {i : ℕ}
    (hfo : ∀ j, 1 ≤ j → j ≤ i → fo j = fo' j)
    (hchld : ∀ l, 1 ≤ l → l ≤ fo i → chld i l = chld' i l) (hi : 1 ≤ i) :
    queueTerm chld fo i = queueTerm chld' fo' i := by
  unfold queueTerm
  have hfi : fo i = fo' i := hfo i hi le_rfl
  have hS : Sf fo (i - 1) = Sf fo' (i - 1) :=
    Sf_congr fun j hj1 hj2 => hfo j hj1 (by omega)
  rw [← hfi, hS]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [hchld l (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2]

theorem nodeQueueP_congr {cur cur' : ℕ → K} {chld chld' : ℕ → ℕ → K} {fo fo' : ℕ → ℕ} {k : ℕ}
    (hcur : cur 1 = cur' 1)
    (hfo : ∀ j, 1 ≤ j → j ≤ k → fo j = fo' j)
    (hchld : ∀ i l, 1 ≤ i → i ≤ k → 1 ≤ l → l ≤ fo i → chld i l = chld' i l) :
    nodeQueueP cur chld fo k = nodeQueueP cur' chld' fo' k := by
  unfold nodeQueueP
  rw [hcur]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hik := (Finset.mem_Icc.mp hi).2
  exact queueTerm_congr (fun j hj1 hj2 => hfo j hj1 (by omega))
    (fun l hl1 hl2 => hchld i l hi1 hik hl1 hl2) hi1

/-- `rootDiffP` reads `cur`/`fo` on `1..h` and `chld i l` on `1 ≤ i ≤ h`, `1 ≤ l ≤ fo i` only. -/
theorem rootDiffP_congr {cur cur' : ℕ → K} {chld chld' : ℕ → ℕ → K} {fo fo' : ℕ → ℕ}
    {root : K} {h : ℕ}
    (hcur : ∀ i, 1 ≤ i → i ≤ h → cur i = cur' i)
    (hfo : ∀ j, 1 ≤ j → j ≤ h → fo j = fo' j)
    (hchld : ∀ i l, 1 ≤ i → i ≤ h → 1 ≤ l → l ≤ fo i → chld i l = chld' i l) :
    rootDiffP cur chld fo root h = rootDiffP cur' chld' fo' root h := by
  unfold rootDiffP
  rw [nodeListP_congr hcur, nodeQueueP_congr rfl hfo hchld]

/-- `computeStateOf` on the decoded source reads the same selector columns as on the source
(`computeTraceSubst` is the identity below `11`). -/
theorem computeStateOf_ofSubst (E : Env K) :
    computeStateOf (Env.ofSubst computeSubst E) = computeStateOf E := by
  have h : ∀ k, k < 11 → (Env.ofSubst computeSubst E).trace k = E.trace k := by
    intro k hk
    simp [Env.ofSubst, computeSubst, computeTraceSubst, hk, Expr.eval]
  simp only [computeStateOf, h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num),
    h 8 (by norm_num), h 9 (by norm_num), h 10 (by norm_num)]

/-- `rowStateOf` and `computeStateOf` have the same body. -/
theorem rowStateOf_eq_computeStateOf (E : Env K) : rowStateOf E = computeStateOf E := by
  unfold rowStateOf computeStateOf
  congr

end Congr

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])

/-- The physical row of the family trace `familyQc P c Qc₀` reads the same polynomials as the
honest-width row: `familyQc` is `Fin.cast` on the same `Qc₀`. -/
theorem envOfTrace_familyQc_trace (x : F) (chal pub chal' pub' : ℕ → F) (j : ℕ) :
    (envOfTrace (familyQc P c Qc₀) P.optimized.orbit.ω x chal pub).trace j =
      (envOfTrace Qc₀ P.optimized.orbit.ω x chal' pub').trace j := by
  simp only [envOfTrace]
  by_cases h : j < P.computeChip.rap.w
  · have h' : j < (P.computeChipAt c).rap.w := by rw [computeChipAt_width]; exact h
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ j < (P.computeChipAt c).rap.w := by rw [computeChipAt_width]; exact h
    rw [dif_neg h', dif_neg h]

theorem envOfTrace_familyQc_traceNext (x : F) (chal pub chal' pub' : ℕ → F) (j : ℕ) :
    (envOfTrace (familyQc P c Qc₀) P.optimized.orbit.ω x chal pub).traceNext j =
      (envOfTrace Qc₀ P.optimized.orbit.ω x chal' pub').traceNext j := by
  simp only [envOfTrace]
  by_cases h : j < P.computeChip.rap.w
  · have h' : j < (P.computeChipAt c).rap.w := by rw [computeChipAt_width]; exact h
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ j < (P.computeChipAt c).rap.w := by rw [computeChipAt_width]; exact h
    rw [dif_neg h', dif_neg h]

set_option maxRecDepth 4000 in
/-- **Trace columns of the family row are those of the `c`-free `computeSourceEnv`.** -/
theorem familyRow_trace_eq (i : Fin (rows P)) :
    (rowEnvAt P c (familyQc P c Qc₀) i).toSourceEnv.trace = (P.computeSourceEnv Qc₀ i).trace := by
  funext j
  simp only [rowEnvAt, OptimizedFullStrictNockVMROMPackage.computeSourceEnv,
    OptimizedFullStrictNockVMROMPackage.computeBaseEnv, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv]
  split_ifs with h13 h76 hcb h296 h299 h302
  · rw [envOfTrace_familyQc_trace]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_familyQc_trace]
  · rw [envOfTrace_familyQc_trace]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_familyQc_trace]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_familyQc_trace]
  · rw [envOfTrace_familyQc_trace]
  · rfl

set_option maxRecDepth 4000 in
theorem familyRow_traceNext_eq (i : Fin (rows P)) :
    (rowEnvAt P c (familyQc P c Qc₀) i).toSourceEnv.traceNext =
      (P.computeSourceEnv Qc₀ i).traceNext := by
  funext j
  simp only [rowEnvAt, OptimizedFullStrictNockVMROMPackage.computeSourceEnv,
    OptimizedFullStrictNockVMROMPackage.computeBaseEnv, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv]
  split_ifs with h13 h76 hcb h296 h299 h302
  · rw [envOfTrace_familyQc_traceNext]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_familyQc_traceNext]
  · rw [envOfTrace_familyQc_traceNext]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_familyQc_traceNext]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_familyQc_traceNext]
  · rw [envOfTrace_familyQc_traceNext]
  · rfl

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsat
include hax hbasis hwidth

omit hax hbasis hwidth in
/-- `rowStateOf` of the family row is the chosen one-hot state. -/
theorem rowStateOf_envR (i : Fin (rows P)) :
    rowStateOf (rowEnvAt P c (familyQc P c Qc₀) i).toSourceEnv =
      stAt P c (familyQc P c Qc₀) hsat i := by
  rw [rowStateOf_eq_computeStateOf, ← computeStateOf_ofSubst]
  exact stAt_eq_computeStateOf P c (familyQc P c Qc₀) hsat i

omit hax hbasis hwidth in
theorem rowLabelVec_family (i : Fin (rows P)) :
    rowLabelVec (P.computeSourceEnv Qc₀ i) =
      labelVecOfPub (pubAt P c (familyQc P c Qc₀) hsat i) := by
  rw [← rowLabelVec_congr (familyRow_trace_eq P c Qc₀ i) (familyRow_traceNext_eq P c Qc₀ i)]
  show labelVecOfPub (pubOfState _ (rowStateOf (rowEnvAt P c (familyQc P c Qc₀) i).toSourceEnv)) = _
  rw [rowStateOf_envR P c Qc₀ hsat i]
  rfl

omit hax hbasis hwidth in
theorem rowChildVec_family (i : Fin (rows P)) (l : ℕ) :
    rowChildVec (P.computeSourceEnv Qc₀ i) l =
      childVecN (pubAt P c (familyQc P c Qc₀) hsat i) (tagsAt P c (familyQc P c Qc₀) hsat i) l := by
  rw [← rowChildVec_congr (familyRow_trace_eq P c Qc₀ i) (familyRow_traceNext_eq P c Qc₀ i)]
  show childVecN (pubOfState _ (rowStateOf (rowEnvAt P c (familyQc P c Qc₀) i).toSourceEnv))
    (fun j => (childTagHost curReader
      (rowStateOf (rowEnvAt P c (familyQc P c Qc₀) i).toSourceEnv) j).eval _) l = _
  rw [rowStateOf_envR P c Qc₀ hsat i]
  rfl

omit hax hbasis hwidth in
theorem rowFanout_family (i : Fin (rows P)) :
    rowFanout (P.computeSourceEnv Qc₀ i) = fanoutComp (stAt P c (familyQc P c Qc₀) hsat i) := by
  rw [rowFanout, rowStateOf_congr (familyRow_trace_eq P c Qc₀ i).symm, rowStateOf_envR]

omit hax hbasis hwidth in
theorem curOf_eq_curW (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    curOf (P.computeSourceEnv Qc₀) (gamma c.1) i = curW P c (familyQc P c Qc₀) hsat i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < rows P := by omega
  rw [curOf_succ _ _ k hk, curW, rowOf_succ P k hk, rowLabelVec_family P c Qc₀ hsat ⟨k, hk⟩]

omit hax hbasis hwidth in
theorem chldOf_eq_chldW (i l : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    chldOf (P.computeSourceEnv Qc₀) (gamma c.1) i l = chldW P c (familyQc P c Qc₀) hsat i l := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < rows P := by omega
  rw [chldOf_succ _ _ k l hk, chldW, rowOf_succ P k hk, rowChildVec_family P c Qc₀ hsat ⟨k, hk⟩]

omit hax hbasis hwidth in
theorem foOf_eq_foW (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    foOf (P.computeSourceEnv Qc₀) i = foW P c (familyQc P c Qc₀) hsat i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < rows P := by omega
  rw [foOf_succ _ k hk, foW, rowOf_succ P k hk, rowFanout_family P c Qc₀ hsat ⟨k, hk⟩]

omit hax hbasis hwidth in
/-- The event's polynomial IS the chip's walk polynomial. -/
theorem rootDiffP_family (root : K) :
    rootDiffP (curOf (P.computeSourceEnv Qc₀) (gamma c.1)) (chldOf (P.computeSourceEnv Qc₀) (gamma c.1))
        (foOf (P.computeSourceEnv Qc₀)) root (rows P) =
      rootDiffP (curW P c (familyQc P c Qc₀) hsat) (chldW P c (familyQc P c Qc₀) hsat)
        (foW P c (familyQc P c Qc₀) hsat) root (rows P) :=
  rootDiffP_congr (fun i h1 h2 => curOf_eq_curW P c Qc₀ hsat i h1 h2)
    (fun j h1 h2 => foOf_eq_foW P c Qc₀ hsat j h1 h2)
    (fun i l h1 h2 _ _ => chldOf_eq_chldW P c Qc₀ hsat i l h1 h2)

/-- **`cur(1) = RLC^γ(rvt_root)` outside the `α`-event**. -/
theorem deployed_root_cur_eq_claim
    (hα : c.1 ∉ alphaRootEvent (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim)) :
    Walk.rlc (gamma c.1) (labelVecOfPub (pubAt P c (familyQc P c Qc₀) hsat (firstRow P))) =
      Walk.rlc (gamma c.1) (claimLabelVec (nprSeed c.1) P.optimized.verifier.raw.claim) := by
  rw [mem_alphaRootEvent_iff, rootDiffP_family P c Qc₀ hsat] at hα
  have h := cur_one_eq_root_of_walkSat (deployed_walkSat P c (familyQc P c Qc₀) hsat hax hbasis hwidth)
    (deployed_walk_out P c (familyQc P c Qc₀) hsat hax hbasis hwidth) hα
  rw [curW, rowOf_one] at h
  exact h

/-- **`deployed_root_label_eq_claim`.**  For every `c` outside the compute walk's root events
and every `Qc₀` whose family trace is accepted at `computeChipAt c`, the decoded row-0
`(s, f, e)` are `enc (nprSeed c.1)` of the claim's `(subject, formula, result)`
(`Batch458::ChipRootBinding`). -/
theorem deployed_root_label_eq_claim
    (hwalk : c.1 ∉ P.computeWalkRootEvent Qc₀)
    (hα : c.1 ∉ alphaRootEvent (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim)) :
    ChipRootBinding P c (familyQc P c Qc₀) := by
  have hγ := ((notMem_rootEvent_iff _ _ _ _).1 hwalk).2
  have hcur := deployed_root_cur_eq_claim P c Qc₀ hsat hax hbasis hwidth hα
  rw [mem_gammaRootEvent_iff, rowLabelVec_family P c Qc₀ hsat] at hγ
  have hlab := eq_of_rlc_eq_of_not_mem hγ hcur.symm
  exact ⟨stAt P c (familyQc P c Qc₀) hsat (firstRow P),
    stAt_spec P c (familyQc P c Qc₀) hsat (firstRow P),
    bindFP_of_labelVec_eq _ _ _ hlab.symm⟩

/-- The same at the consumed event, plus the (now separately priced) `α`-root
polynomial event.  `hgood` gives the walk-root and tiling exclusions;
`hα` is the paper's degree-`h` root set, which the consumed union prices
only on a tiled table. -/
theorem deployed_root_label_eq_claim_of_good
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm)
    (hα : c.1 ∉ alphaRootEvent (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim)) :
    ChipRootBinding P c (familyQc P c Qc₀) :=
  deployed_root_label_eq_claim P c Qc₀ hsat hax hbasis hwidth
    (P.optimizedFailureEvent_good_components Qc₀ Qm c hgood).2.2.2.2.1 hα

end

end Nock.RedTeam.Batch465
