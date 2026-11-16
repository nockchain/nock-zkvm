/-
  Nock/RedTeam/Batch501Thm54MemoryTopology.lean

  Memory topology in mask
  form: `hγ` from the priced forest prefix-γ event, whole-table
  `ForestVecBFT` from `WalkSatInGate` + `exists_walkSat_agree_ge` +
  forest prefix + `deployed_bfsValid_memory` / `deployed_tiling_memory`,
  per-row `FmemTopo` from `hFcommit_memory` (no residual).

  The production `MemoryExactTopology` is NOT
  concluded.  From `DeployedAcceptanceAt` +
  `c ∉ optimizedFailureEvent`, outside the forest prefix-α event
  (`walkForestPrefixAlphaEvent`).  That α-event is the paper's
  `:1008` `h/|K|` and is not a component of `optimizedFailureEvent`
  (priced walk-α is compute's root event only).

  Seed public slots 9..11 remain in `ExactMemoryCoordinatePins.walkSeed`
  / `seedW`; `memoryPublicOfTuple` already pass-throughs them.
-/
import Nock.WalkPrefix
import Nock.WalkInGate
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.WalkQueueDeployed
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.HostilePoleAlignment
import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch489Thm54FoOfEqFoW
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch500Thm54GammaTransport
import Nock.NockVMROM.Thm54.P8Core.Batch501Thm54MemoryTopology
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch501

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.HostilePoleAlignment
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch489
open Nock.RedTeam.Batch490
open Nock.RedTeam.Batch500
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree (FmemTopo mem_stateSep_topo respects_pt_topo memPtOf)

noncomputable section


def openAfterMemoryTopology : List String :=
  openConjunctsAfterVer

theorem openAfterMemoryTopology_length :
    openAfterMemoryTopology.length = 7 :=
  openConjunctsAfterVer_length

theorem topology_names_still_on_ledger :
    "computeTopology" ∈ openAfterMemoryTopology ∧
      "memoryTopology" ∈ openAfterMemoryTopology := by
  decide

def seedPublicStillPresent : String :=
  "memoryPublicOfTuple slots 9..11 / ExactMemoryCoordinatePins.walkSeed / seedW"

theorem seedPublicStillPresent_nonempty :
    seedPublicStillPresent ≠ "" := by
  decide

/-! ## A. -/

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-! ## B. Priced memory `hγ` is `forestPrefixBadGammas` of the committed table -/

section PricedForestGamma
variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

end PricedForestGamma

/-! ## C. -/

section Projection
variable {K : Type} [Field K]

/-- `Fmem` reads children only through `ptOf` (and `none`/`some`). -/
theorem respects_pt : RespectsChildLabels (Fmem (K := K)) ptOf := by
  intro lbl xout xout' hx hF
  obtain ⟨hst, hV, hslot, hlink⟩ := hF
  refine ⟨hst, hV, ?_, ?_⟩
  · intro i
    rw [hslot i]
    have := hx i
    constructor
    · intro hne hnone; rw [hnone] at this; cases h : xout i
      · exact hne h
      · rw [h] at this; simp at this
    · intro hne hnone; rw [hnone] at this; cases h : xout' i
      · exact hne h
      · rw [h] at this; simp at this
  · intro i hi
    have hli := hlink i hi
    have hj := hx i
    cases hxout : xout i with
    | none => rw [hxout] at hli; simp at hli
    | some child =>
      cases hxout' : xout' i with
      | none =>
        rw [hxout, hxout'] at hj; simp at hj
      | some child' =>
        rw [hxout] at hli
        simp only [Option.map_some, Option.some.injEq] at hli
        rw [hxout, hxout'] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        simp only [Option.map_some, Option.some.injEq]
        exact hj.symm.trans hli

end Projection

/-! ## D. `ForestVecBFT` under projection and congruence -/

section ForestMap
variable {K : Type*} [Field K] {n m : ℕ}

end ForestMap

/-! ## E. Hosted memory walk vectors and pole discharge -/

section MemoryVectors
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)

theorem memRowPred {i : ℕ} (h1 : 1 ≤ i) (hle : i ≤ memRowsP P) :
    i - 1 < P.optimized.family.problem.cfg.memRows := by
  have hle' : i ≤ P.optimized.family.problem.cfg.memRows := by
    simpa [memRowsP] using hle
  exact Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_succ_le h1) Nat.one_pos) hle'

include hz

theorem hpole_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (i : Fin (memRowsP P)) :
    (OptimizedMemoryGateBasis.poleSourceMixed (F := F)).eval
      (memorySourceEnvAt P c (honestQm P c (familyQm P c Qm₀)) i)
      (memoryBaseEnvAt P c (honestQm P c (familyQm P c Qm₀)) i) ≠ 0 := by
  have hinter :=
    (P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood).2.2.2.1
  have hQ : honestQm P c (familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  rw [hQ]
  have hps := poleSource_eval_at P c Qm₀ i
  have hmix := FamilyMemoryRows.poleSourceMixed_eval_at P c Qm₀ i
  intro h0
  apply hinter
  refine Finset.mem_union.mpr (Or.inr ?_)
  simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm₀ i)
    (P.memoryBaseEnv Qm₀ i), ?_, ?_⟩
  · refine List.mem_append_left _ ?_
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · have htr := memorySourceEnv_trace_eq P c Qm₀ i
    have hF := memoryBaseEnv_trace_eq P c Qm₀ i
    have hrec : memRowRecord (memorySourceEnvAt P c Qm₀ i) =
        memRowRecord (P.memorySourceEnv Qm₀ i) := by
      funext t; simp [memRowRecord, htr]
    have h181 : (P.memoryBaseEnv Qm₀ i).trace 181 = (memoryBaseEnvAt P c Qm₀ i).trace 181 := by
      rw [hF]
    have h0' : (MemoryPaperFactorization.poleSourceMixed (F := F)).eval
        (memorySourceEnvAt P c Qm₀ i) (memoryBaseEnvAt P c Qm₀ i) = 0 := h0
    rw [hmix, show MemoryPaperFactorization.poleSource.eval (memorySourceEnvAt P c Qm₀ i) =
      poleSource.eval (memorySourceEnvAt P c Qm₀ i) from rfl, hps] at h0'
    rw [OptimizedMemoryHostileAccumulator.rowRecord_eq_memRowRecord10,
      OptimizedMemoryHostileAccumulator.memRowRecord10, RecordCarrier.rlc_withExp, ← hrec, h181]
    simp only [FamilyMemoryRows.rowExpTerm, OptimizedMemoryGateBasis.reqIdxCol] at h0'
    linear_combination h0'

include hsatM hchar

end MemoryVectors

/-! ## F. Whole-table `ForestVecBFT` from in-gate + prefix + queue -/

section ForestVecBFT
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)

include hsatM hchar

end ForestVecBFT

/-! ## G. `ForestReconGoal` / β-free memory topology of `execOfTraces` (M′) -/

section MemoryTopology
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
  (hz : nprSeed c.1 ≠ 0)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hsatM hchar hz

/-- Whole-table `ForestReconGoal` at `lblM`, on the β-free predicate (M′: no `hexp0`). -/
theorem deployed_forestReconGoal
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hα : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P)) :
    ForestReconGoal (mem_stateSep_topo (K := K)) (lblM P Qm₀ c)
      (kMemP P) (memRowsP P) := by
  have hfo : foW P c (familyQm P c Qm₀) = foM P Qm₀ c := by
    funext i
    have h := foW_eq_foM_all P c (familyQm P c Qm₀) i
    rw [MemoryWalkDeployed.Qmh, WalkQueueDeployed.honestQm_familyQm P c Qm₀] at h
    exact h
  have hv : BFSValidF (kMemP P) (foM P Qm₀ c) (memRowsP P) := by
    rw [← hfo]
    exact deployed_bfsValid_memory P c (familyQm P c Qm₀) hsatM hchar
  have htile : kMemP P + Sf (foM P Qm₀ c) (memRowsP P) = memRowsP P := by
    rw [← hfo]
    exact deployed_tiling_memory P c (familyQm P c Qm₀) hsatM hchar
      (htileαM_of_good P c Qc₀ Qm₀ hsatM hchar hgood)
  have hγ : gamma c.1 ∉ forestPrefixBadGammas (VdM P c Qm₀) (CvdM P c Qm₀)
      (foM P Qm₀ c) (kMemP P) (memRowsP P) := by
    rw [← forestPrefixBadGammas_VdM_eq_committed P c Qm₀]
    exact hγM_of_good P c Qc₀ Qm₀ hgood
  have hb' := deployed_forestVecBFT_pt P c Qm₀ hsatM hchar hγ hα
    (htileαM_of_good P c Qc₀ Qm₀ hsatM hchar hgood)
  have harity : ∀ i, foM P Qm₀ c i ≤ 2 :=
    fun i => fanoutMem_le_two (lblM P Qm₀ c i).1
  refine reconForest_ForestReconGoal_of_label (mem_stateSep_topo (K := K)) memPtOf
    respects_pt_topo encPT encPT_label (lblM P Qm₀ c)
    (clabOfMem (lblM P Qm₀ c)) (foM P Qm₀ c)
    (MemoryWalkDeployed.kMem_pos P) htile hv harity (fun i _ _ => rfl)
    (fun i hi1 hih => hFcommit_memory_of_good P c Qm₀ hsatM hchar hz i hi1 hih) hb'

include hsatC
include hax hbasis hwidth

end MemoryTopology

end

end Nock.RedTeam.Batch501

#print axioms Nock.RedTeam.Batch501.forestPrefixBadGammas_congr_on
#print axioms Nock.RedTeam.Batch501.hγM_of_good
#print axioms Nock.RedTeam.Batch501.hFcommit_memory_of_good
#print axioms Nock.RedTeam.Batch501.deployed_forestVecBFT
#print axioms Nock.RedTeam.Batch501.execOfTraces_memoryTopology
#print axioms Nock.RedTeam.Batch501.memoryTopology_of_deployed
#print axioms Nock.RedTeam.Batch501.hαM_of_good
#print axioms Nock.RedTeam.Batch501.memoryTopology_of_deployed_of_good
#print axioms Nock.RedTeam.Batch501.openAfterMemoryTopology_length
