/-
  Nock/NockVMROM/Thm54/P8Core/WalkQueueDeployed.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.WalkQueueDeployed`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/WalkQueueDeployed.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch471Thm54ComputeTopologyPrefix
import Nock.NockVMROM.Thm54.P8Core.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.P8Core.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.WalkQueueDeployed
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.WalkQueueDeployed

open scoped Classical
open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.RedTeam.Batch459
open Nock.RedTeam.Batch471
open Nock.RedTeam.Batch478

noncomputable section

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

omit hsat in
theorem finalExtTransitionGates_get_queueNonEmpty :
    finalExtTransitionGates.get ⟨(packedQueueNonEmptyId : ℕ), by simp⟩ =
      walkQueueNonEmpty := by
  simp [finalExtTransitionGates, paperPacking_eq_rowLocal_append,
    paperPackingRowLocal_length, crossRowSingletons, queueWitnessGates,
    List.getElem_append_left, List.getElem_append_right, List.append_assoc]

omit hsat in
theorem finalExtTransitionGates_get_queueTiling :
    finalExtTransitionGates.get ⟨(packedQueueTilingId : ℕ), by simp⟩ =
      walkQueueTiling := by
  simp [finalExtTransitionGates, paperPacking_eq_rowLocal_append,
    paperPackingRowLocal_length, crossRowSingletons, queueWitnessGates,
    List.getElem_append_left, List.getElem_append_right, List.append_assoc]

include hsat
include hax hbasis hwidth

omit hax hbasis hwidth in
theorem queueNonEmpty_gate_zero (i : Fin (rows P)) :
    walkQueueNonEmpty.eval (envR P c Qc i) = 0 := by
  have hc := (row_obligations_at P c Qc hsat i).extensionCore21 packedQueueNonEmptyId
  have hsem : correctedCoreSemanticValue (rowEnvAt P c Qc i) packedQueueNonEmptyId =
      (correctedFinalExtGate packedQueueNonEmptyId).eval (rowEnvAt P c Qc i) := by
    simp [correctedCoreSemanticValue]
  have hsrc :=
    (correctedFinalExtGate_eval_source (rowEnvAt P c Qc i) packedQueueNonEmptyId).trans
      (hsem.symm.trans hc)
  rw [finalExtTransitionGates_get_queueNonEmpty] at hsrc
  exact hsrc

omit hax hbasis hwidth in
theorem queueTiling_gate_zero (i : Fin (rows P)) :
    walkQueueTiling.eval (envR P c Qc i) = 0 := by
  have hc := (row_obligations_at P c Qc hsat i).extensionCore21 packedQueueTilingId
  have hsem : correctedCoreSemanticValue (rowEnvAt P c Qc i) packedQueueTilingId =
      (correctedFinalExtGate packedQueueTilingId).eval (rowEnvAt P c Qc i) := by
    simp [correctedCoreSemanticValue]
  have hsrc :=
    (correctedFinalExtGate_eval_source (rowEnvAt P c Qc i) packedQueueTilingId).trans
      (hsem.symm.trans hc)
  rw [finalExtTransitionGates_get_queueTiling] at hsrc
  exact hsrc

omit hsat hax hbasis hwidth in
theorem walkQueueTiling_eval (env : Env K) :
    walkQueueTiling.eval env =
      env.trace 12 *
        ((overlayCoord .traceCur 0).eval env - (finalWalkLine .traceCur).eval env) := by
  unfold walkQueueTiling
  simp only [Expr.eval]

theorem count_ne_ln_of_queue (i : Fin (rows P))
    (hi : (i : ℕ) + 1 < rows P) :
    countW P c Qc ((i : ℕ) + 1) ≠ lnW P c Qc ((i : ℕ) + 1) := by
  have hgate := queueNonEmpty_gate_zero P c Qc hsat i
  have hnl := notLast_at P c Qc hsat hax hbasis hwidth i hi
  have h12 : (envR P c Qc i).trace 12 = 0 := by
    rw [envR, CorrectedFinalTypedEnv.toSourceEnv]
    change algebraMap F K ((rowEnvAt P c Qc i).baseTrace 12) = 0
    rw [hnl, map_zero]
  have hrow : rowOf P ((i : ℕ) + 1) = i := rowOf_succ P (i : ℕ) i.isLt
  rw [countW, lnW, hrow]
  rw [walkQueueNonEmpty_eval] at hgate
  simp only [h12, sub_zero, one_mul, Int.cast_one] at hgate
  intro heq
  have : (walkInv .traceCur).eval (envR P c Qc i) * (0 : K) - (1 : K) = 0 := by
    simpa [heq, sub_self] using hgate
  simp at this

theorem count_eq_ln_last :
    countW P c Qc (rows P) = lnW P c Qc (rows P) := by
  have hgate := queueTiling_gate_zero P c Qc hsat (lastRow P)
  have hlast := isLast_source_last P c Qc hsat hax hbasis hwidth
  have hrow : rowOf P (rows P) = lastRow P := rowOf_rows P
  rw [countW, lnW, hrow]
  rw [walkQueueTiling_eval, hlast, one_mul] at hgate
  exact sub_eq_zero.mp hgate

/-- Queue-validity, no condition on `α`.  `Batch478::bfsValid_of_ratio_gate`. -/
theorem deployed_bfsValid :
    BFSValid (foW P c Qc hsat) (rows P) := by
  have hw := deployed_walkSat P c Qc hsat hax hbasis hwidth
  refine bfsValid_of_ratio_gate (K := K) (α := alphaC c.1) ?_
  intro i hi1 hih
  have hk : i - 1 < rows P := by omega
  let k : Fin (rows P) := ⟨i - 1, hk⟩
  have hki : (k : ℕ) + 1 = i := Nat.sub_add_cancel hi1
  have hne := count_ne_ln_of_queue P c Qc hsat hax hbasis hwidth k (by omega)
  have hcnt := Walk.count_closed hw i hi1 (le_of_lt hih)
  have hln := Walk.ln_closed hw i hi1 (le_of_lt hih)
  rw [hki] at hne
  rw [hcnt, hln] at hne
  rw [pow_add, pow_one]
  exact hne

/-- Last-row gate forces the tiling outside the priced event. -/
theorem deployed_tiling
    (hα : c.1 ∉ computeTilingEvent (foW P c Qc hsat) (rows P)) :
    Sf (foW P c Qc hsat) (rows P) + 1 = rows P := by
  have hw := deployed_walkSat P c Qc hsat hax hbasis hwidth
  have hterm := count_eq_ln_last P c Qc hsat hax hbasis hwidth
  have hcnt := Walk.count_closed hw (rows P) hw.hpos (le_rfl)
  have hln := Walk.ln_closed hw (rows P) hw.hpos (le_rfl)
  have hpow : alphaC c.1 ^ (1 + Sf (foW P c Qc hsat) (rows P)) =
      alphaC c.1 ^ rows P := by
    rw [pow_add, pow_one, ← hcnt, ← hln]
    exact hterm
  by_contra hne
  exact hα ((mem_computeTilingEvent_iff (foW P c Qc hsat) (rows P) c.1).2
    ⟨hpow, by omega⟩)

end

section AtFamily

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hax hbasis hwidth

/-- Compute half of `TracesWalkHyps` at the family remapping. -/
theorem tracesWalkHyps_compute
    (hα : c.1 ∉ computeTilingEvent (foW P c (familyQc P c Qc₀) hsat) (rows P)) :
    Sf (ExecOfTraces.foC P Qc₀ c) (rows P) + 1 = rows P ∧
      BFSValid (ExecOfTraces.foC P Qc₀ c) (rows P) := by
  have hfo := foW_eq_foC_all P c Qc₀ hsat
  have htile := deployed_tiling P c (familyQc P c Qc₀) hsat hax hbasis hwidth (by
    simpa [hfo] using hα)
  have hv := deployed_bfsValid P c (familyQc P c Qc₀) hsat hax hbasis hwidth
  exact ⟨by simpa [hfo] using htile, by simpa [hfo] using hv⟩

end AtFamily

/-- Terminal-accepting coins on a non-tiling committed forest fanout column. -/
abbrev memoryTilingEvent {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (k h : ℕ) : Finset (JointCoins K) :=
  WalkTilingEvents.memoryTilingEvent fo k h

theorem mem_memoryTilingEvent_iff {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (k h : ℕ) (ω : JointCoins K) :
    ω ∈ memoryTilingEvent fo k h ↔
      alphaM ω ^ (k + Sf fo h) = alphaM ω ^ h ∧ k + Sf fo h ≠ h :=
  WalkTilingEvents.mem_memoryTilingEvent_iff fo k h ω

section MemoryChip

open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
  (hchar : MemStateTagChar F)
include hsat

theorem queueNonEmpty_memory_zero (i : Fin (memRows P)) :
    (walkQueueNonEmpty (F := F)).eval (envK P c Qm i) (envF P c Qm i) = 0 :=
  mixed_zero P c Qm hsat i (walkQueueNonEmpty_mem P)

theorem queueTiling_memory_zero (i : Fin (memRows P)) :
    (walkQueueTiling (F := F)).eval (envK P c Qm i) (envF P c Qm i) = 0 :=
  mixed_zero P c Qm hsat i (walkQueueTiling_mem P)

theorem count_ne_ln_of_queue_memory (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P) :
    MemoryWalkDeployed.countW P c Qm ((i : ℕ) + 1) ≠
      MemoryWalkDeployed.lnW P c Qm ((i : ℕ) + 1) := by
  have hgate := queueNonEmpty_memory_zero P c Qm hsat i
  have hmask := envF_trace5 P c Qm hsat i
  have hrow : MemoryWalkDeployed.rowOf P ((i : ℕ) + 1) = i :=
    MemoryWalkDeployed.rowOf_succ P (i : ℕ) i.isLt
  rw [MemoryWalkDeployed.countW, MemoryWalkDeployed.lnW, hrow]
  rw [MemoryWalkLabel.walkQueueNonEmpty_eval] at hgate
  simp only [hmask, show (i : ℕ) + 1 ≠ memRows P by omega, ↓reduceIte, sub_zero,
    map_one, one_mul] at hgate
  intro heq
  have : (envK P c Qm i).trace MemoryWalkLabel.walkInvRole * (0 : K) - (1 : K) = 0 := by
    simpa [heq, sub_self] using hgate
  simp at this

theorem count_eq_ln_last_memory :
    MemoryWalkDeployed.countW P c Qm (memRows P) =
      MemoryWalkDeployed.lnW P c Qm (memRows P) := by
  have hgate := queueTiling_memory_zero P c Qm hsat (lastMem P)
  have hmask := envF_trace5 P c Qm hsat (lastMem P)
  have hlast : (lastMem P : ℕ) + 1 = memRows P :=
    Nat.sub_add_cancel (memRows_pos P)
  have hrow : MemoryWalkDeployed.rowOf P (memRows P) = lastMem P :=
    MemoryWalkDeployed.rowOf_rows P
  rw [MemoryWalkDeployed.countW, MemoryWalkDeployed.lnW, hrow]
  rw [MemoryWalkLabel.walkQueueTiling_eval, hmask, hlast] at hgate
  simp only [↓reduceIte, map_one, one_mul] at hgate
  exact sub_eq_zero.mp hgate

omit hsat hchar in
theorem kMem_pos : 1 ≤ kMem P := by
  have hpos : 0 < P.objects.cfg.kMem := P.objects.exec.memoryRootCount_pos
  have hk := congrArg ExactConfig.kMem P.optimized.family_cfg
  rw [← hk] at hpos
  exact Nat.succ_le_of_lt hpos

include hsat hchar

/-- Queue-validity of the forest, no condition on `α`. -/
theorem deployed_bfsValid_memory :
    BFSValidF (kMem P) (MemoryWalkDeployed.foW P c Qm) (memRows P) := by
  have hw := deployed_walkSat P c Qm hsat hchar
  refine bfsValidF_of_ratio_gate (k := kMem P) (α := alphaM c.1) (kMem_pos P) ?_
  intro i hi1 hih
  have hk : i - 1 < memRows P := by omega
  let k : Fin (memRows P) := ⟨i - 1, hk⟩
  have hki : (k : ℕ) + 1 = i := Nat.sub_add_cancel hi1
  have hne := count_ne_ln_of_queue_memory P c Qm hsat k (by omega)
  have hcnt := WalkSatInGate.count_closed hw i hi1 (le_of_lt hih)
  have hln := WalkSatInGate.ln_closed hw i hi1 (le_of_lt hih)
  rw [hki] at hne
  rw [hcnt, hln] at hne
  rw [pow_add]
  exact hne

/-- Last-row gate forces the forest tiling outside the priced event. -/
theorem deployed_tiling_memory
    (hα : c.1 ∉ memoryTilingEvent (MemoryWalkDeployed.foW P c Qm) (kMem P) (memRows P)) :
    kMem P + Sf (MemoryWalkDeployed.foW P c Qm) (memRows P) = memRows P := by
  have hw := deployed_walkSat P c Qm hsat hchar
  have hterm := count_eq_ln_last_memory P c Qm hsat
  have hcnt := WalkSatInGate.count_closed hw (memRows P) hw.hpos (le_rfl)
  have hln := WalkSatInGate.ln_closed hw (memRows P) hw.hpos (le_rfl)
  have hpow : alphaM c.1 ^ (kMem P + Sf (MemoryWalkDeployed.foW P c Qm) (memRows P)) =
      alphaM c.1 ^ memRows P := by
    rw [pow_add, ← hcnt, ← hln]
    exact hterm
  by_contra hne
  exact hα ((mem_memoryTilingEvent_iff (MemoryWalkDeployed.foW P c Qm)
      (kMem P) (memRows P) c.1).2 ⟨hpow, hne⟩)

end MemoryChip

section AtFamilyBoth

open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.ExecOfTraces
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatC hsatM hchar
include hax hbasis hwidth

omit hsatC hsatM hchar hax hbasis hwidth in
theorem honestQm_familyQm :
    honestQm P c (familyQm P c Qm₀) = Qm₀ := by
  funext j
  unfold honestQm familyQm
  apply congrArg Qm₀
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

/-- Both halves of `TracesWalkHyps` at the family remapping. -/
theorem tracesWalkHyps_of_chips
    (hαC : c.1 ∉ computeTilingEvent
      (foW P c (familyQc P c Qc₀) hsatC) (rows P))
    (hαM : c.1 ∉ memoryTilingEvent
      (MemoryWalkDeployed.foW P c (familyQm P c Qm₀)) (kMem P) (memRows P)) :
    ExecOfTraces.TracesWalkHyps P Qc₀ Qm₀ c where
  sfCompute := (tracesWalkHyps_compute P c Qc₀ hsatC hax hbasis hwidth hαC).1
  validCompute := (tracesWalkHyps_compute P c Qc₀ hsatC hax hbasis hwidth hαC).2
  sfMemory := by
    have hfo : MemoryWalkDeployed.foW P c (familyQm P c Qm₀) = foM P Qm₀ c := by
      funext i
      have h := MemoryWalkDeployed.foW_eq_foM_all P c (familyQm P c Qm₀) i
      simpa [MemoryWalkDeployed.Qmh, honestQm_familyQm P c Qm₀] using h
    have htile := deployed_tiling_memory P c (familyQm P c Qm₀) hsatM hchar (by
      simpa [hfo] using hαM)
    simpa [hfo] using htile
  validMemory := by
    have hfo : MemoryWalkDeployed.foW P c (familyQm P c Qm₀) = foM P Qm₀ c := by
      funext i
      have h := MemoryWalkDeployed.foW_eq_foM_all P c (familyQm P c Qm₀) i
      simpa [MemoryWalkDeployed.Qmh, honestQm_familyQm P c Qm₀] using h
    have hv := deployed_bfsValid_memory P c (familyQm P c Qm₀) hsatM hchar
    simpa [hfo] using hv

end AtFamilyBoth

end Nock.NockVMROM.Thm54.WalkQueueDeployed
