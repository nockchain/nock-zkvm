/-
  Nock/NockVMROM/Thm54/P8Core/Batch490Thm54TopologyAssembly.lean

  The
  remaining declarations stay in `Nock/RedTeam/Batch490Thm54TopologyAssembly.lean`, which imports this module. This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`. -/
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.NockVMROM.Thm54.P8Core.Batch489Thm54FoOfEqFoW
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch490Thm54TopologyAssembly

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch490

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch471
open Nock.RedTeam.Batch489
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

section ComputeFcommit

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hz : nprSeed c.1 ≠ 0)

omit hsat hz in
/-- 1-indexed `lblC` is the 0-indexed `lblCAt` on `1..N`. -/
theorem lblC_of_pos (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.compRows) :
    lblC P Qc₀ c i = lblCAt P Qc₀ c ⟨i - 1, by omega⟩ := by
  have h : i - 1 < P.optimized.family.problem.cfg.compRows := by omega
  simp only [lblC, dif_pos h]

include hsat hz

/-- Decoded `Vcomp` at a 1-indexed compute row. -/
theorem deployed_lblC_vcomp (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.compRows) :
    Vcomp (lblC P Qc₀ c i).2.1 (lblC P Qc₀ c i).2.2.1 (lblC P Qc₀ c i).2.2.2 := by
  have hi : i - 1 < P.optimized.family.problem.cfg.compRows := by omega
  have hv := deployed_row_vcomp_at P c (familyQc P c Qc₀) hsat hz ⟨i - 1, hi⟩
  have hV := lblCAt_vcomp_of_vcompAt P Qc₀ c ⟨i - 1, hi⟩ hv
  rw [lblC_of_pos P c Qc₀ i hi1 hih]
  simpa [lblCAt] using hV

/-- **`hFcommit` at the deployed chip.**  No `RawTopologyBindingResidual`.
`clabOf` is the 1-indexed `clabC`-shaped child; `childLinkComp`
reads only `(s, f, e)`. -/
theorem hFcommit_deployed (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.compRows) :
    Fcomp (lblC P Qc₀ c i)
      (fun j : Fin 3 =>
        if (j : ℕ) < foC P Qc₀ c i then
          some (clabOf (lblC P Qc₀ c) i ((j : ℕ) + 1))
        else none) := by
  refine ⟨lblC_state P c Qc₀ i, deployed_lblC_vcomp P c Qc₀ hsat hz i hi1 hih, ?_, ?_⟩
  · intro j
    simp only [foC]
    constructor
    · intro hj; simp [hj]
    · intro hne; by_contra hj; simp [hj] at hne
  · intro j hj
    simp only [foC] at hj ⊢
    simp only [hj, ↓reduceIte]
    simp only [Option.map_some, clabOf, childOfSlot]
    have hm : ((j : ℕ) + 1 - 1) % 3 = j := by
      rw [show (j : ℕ) + 1 - 1 = (j : ℕ) by omega]; exact Nat.mod_eq_of_lt j.isLt
    have hfin : (⟨((j : ℕ) + 1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = j :=
      Fin.ext hm
    rw [hfin]

end ComputeFcommit

section ComputeVecBFT

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
include hsat
include hax hbasis hwidth

/-- `hseed` of `deployed_prefixBFT` from the priced walk-root `α`-event
(`Batch465::deployed_root_cur_eq_claim`). -/
theorem hseed_of_alphaRoot
    (hα : c.1 ∉ alphaRootEvent (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim)) :
    seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1 := by
  have hcur := deployed_root_cur_eq_claim P c Qc₀ hsat hax hbasis hwidth hα
  have hpub := pubAt_rowOf P c Qc₀ hsat 1
  have hrow : Batch459.rowOf P 1 = OptimizedComputeHostileAccumulator.firstRow P :=
    Batch459.rowOf_one P
  simp only [Vd, seedOfClaim]
  rw [hrow] at hpub
  rw [hpub] at hcur
  exact congrArg (fun x => x * alphaC c.1) hcur.symm

/-- Whole-table `VecBFT` at the hosted vectors, from `PrefixBFT` + queue
validity + tiling.  `hic` of `deployed_prefixBFT` is unused after walk-α
(`initial_count` is the coin). -/
theorem deployed_vecBFT
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1)
    (hα : alphaC c.1 ∉ walkPrefixAlphaEvent
      (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsat i l))
      (foC P Qc₀ c) (rows P))
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsat)
      (foC P Qc₀ c) (rows P))
    (htileα : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsat) (rows P)) :
    VecBFT (Vd P c Qc₀) (Cvd P c Qc₀ hsat) (foC P Qc₀ c) (rows P) := by
  have hw := deployed_walkSat_lblC P c Qc₀ hsat hax hbasis hwidth
  have hout : Batch459.accW P c (familyQc P c Qc₀) (rows P) = 0 :=
    Batch459.deployed_walk_out P c (familyQc P c Qc₀) hsat hax hbasis hwidth
  have hh : 1 ≤ rows P := Nat.succ_le_of_lt P.optimized.family.problem.cfg.compRows_pos
  rcases isFullBFT_or_mem_alphaEvent hw hseed (rfl : alphaC c.1 = alphaC c.1) hout
    with hbft | hmem
  · have hpre := prefixBFT_of_isFullBFT (Vd P c Qc₀) (Cvd P c Qc₀ hsat)
      (foC P Qc₀ c) hh hγ hbft
    have hfo := foW_eq_foC_all P c Qc₀ hsat
    have hv : BFSValid (foC P Qc₀ c) (rows P) := by
      simpa [hfo] using deployed_bfsValid P c (familyQc P c Qc₀) hsat hax hbasis hwidth
    have hlen : prefixLen (foC P Qc₀ c) (rows P) = rows P :=
      prefixLen_eq_of_bfsValid _ hv
    have htile : Sf (foC P Qc₀ c) (rows P) + 1 = rows P := by
      simpa [hfo] using deployed_tiling P c (familyQc P c Qc₀) hsat hax hbasis hwidth htileα
    obtain ⟨_, hcase⟩ := hpre
    rw [hlen] at hcase
    rcases hcase with ⟨_, hb⟩ | ⟨_, hgt, _⟩
    · exact hb
    · omega
  · exact absurd hmem hα

/-- Projected whole-table `VecBFT` at `encSFE` / `clabOf`. -/
theorem deployed_vecBFT_sfe
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1)
    (hα : alphaC c.1 ∉ walkPrefixAlphaEvent
      (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsat i l))
      (foC P Qc₀ c) (rows P))
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsat)
      (foC P Qc₀ c) (rows P))
    (htileα : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsat) (rows P)) :
    VecBFT (fun i => encSFE (lblC P Qc₀ c i))
      (fun i l => encSFE (clabOf (lblC P Qc₀ c) i l))
      (foC P Qc₀ c) (rows P) := by
  have hbft := deployed_vecBFT P c Qc₀ hsat hax hbasis hwidth hseed hα hγ htileα
  have hproj := vecBFT_map sfeProj hbft
  refine vecBFT_congr_children (fun i l hl => ?_) hproj
  have hl3 : l < 3 := lt_of_lt_of_le hl ((comp_stateSep (K := K)).fanout_le _)
  show sfeProj (Cvd P c Qc₀ hsat i (l + 1)) =
    sfeProj (labelVecOfPub (childOfSlot (lblC P Qc₀ c i).2.2.1
      ⟨(l + 1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩))
  have hl' : l + 1 - 1 = l := by omega
  have hm : (l + 1 - 1) % 3 = l := by rw [hl']; exact Nat.mod_eq_of_lt hl3
  have hfin : (⟨(l + 1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = ⟨l, hl3⟩ :=
    Fin.ext hm
  simp only [Cvd]
  rw [hfin, encSFE_clab (lblC P Qc₀ c i).2.2.1
    (Batch459.tagsAt P c (familyQc P c Qc₀) hsat (Batch459.rowOf P i)) ⟨l, hl3⟩]
  congr 1
  rw [hl']
  exact childVecN_fin (lblC P Qc₀ c i).2.2.1
    (Batch459.tagsAt P c (familyQc P c Qc₀) hsat (Batch459.rowOf P i)) ⟨l, hl3⟩

end ComputeVecBFT

section ComputeTopology

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hz : nprSeed c.1 ≠ 0)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatC hz
include hax hbasis hwidth

/-- `RVT Fcomp` of `execOfTraces.computeTree`. -/
theorem execOfTraces_compute_rvt
    (h : TracesWalkHyps P Qc₀ Qm₀ c)
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1)
    (hα : alphaC c.1 ∉ walkPrefixAlphaEvent
      (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsatC i l))
      (foC P Qc₀ c) (rows P))
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P))
    (htileα : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P)) :
    RVT (Fcomp (K := K)) (execOfTraces P Qc₀ Qm₀ c h).computeTree := by
  have hfo := foW_eq_foC_all P c Qc₀ hsatC
  have hv : BFSValid (foC P Qc₀ c) (rows P) := by
    simpa [hfo] using deployed_bfsValid P c (familyQc P c Qc₀) hsatC hax hbasis hwidth
  have htile : Sf (foC P Qc₀ c) (rows P) + 1 = rows P := by
    simpa [hfo] using deployed_tiling P c (familyQc P c Qc₀) hsatC hax hbasis hwidth htileα
  have hb' := deployed_vecBFT_sfe P c Qc₀ hsatC hax hbasis hwidth hseed hα hγ htileα
  have harity : ∀ i, foC P Qc₀ c i ≤ 3 :=
    fun i => (comp_stateSep (K := K)).fanout_le _
  have hrvt := VecBFT_reconstruct_of_label (comp_stateSep (K := K)) sfeOf respects_sfe
    encSFE encSFE_label (lblC P Qc₀ c) (clabOf (lblC P Qc₀ c)) (foC P Qc₀ c)
    htile hv harity (fun i _ _ => rfl)
    (fun i hi1 hih => hFcommit_deployed P c Qc₀ hsatC hz i hi1 hih) hb'
  simpa [execOfTraces, rows] using hrvt

/-- Arity of the reconstructed compute tree. -/
theorem execOfTraces_compute_arity
    (h : TracesWalkHyps P Qc₀ Qm₀ c)
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1)
    (hα : alphaC c.1 ∉ walkPrefixAlphaEvent
      (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsatC i l))
      (foC P Qc₀ c) (rows P))
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P))
    (htileα : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P)) :
    ProperArity 3 (execOfTraces P Qc₀ Qm₀ c h).computeTree := by
  have hfo := foW_eq_foC_all P c Qc₀ hsatC
  have hv : BFSValid (foC P Qc₀ c) (rows P) := by
    simpa [hfo] using deployed_bfsValid P c (familyQc P c Qc₀) hsatC hax hbasis hwidth
  have htile : Sf (foC P Qc₀ c) (rows P) + 1 = rows P := by
    simpa [hfo] using deployed_tiling P c (familyQc P c Qc₀) hsatC hax hbasis hwidth htileα
  have harity : ∀ i, foC P Qc₀ c i ≤ 3 :=
    fun i => (comp_stateSep (K := K)).fanout_le _
  have hrvt := execOfTraces_compute_rvt P c Qc₀ Qm₀ hsatC hz hax hbasis hwidth h hseed hα hγ htileα
  have hbind := reconTree_bindings (comp_stateSep (K := K)) (foC P Qc₀ c)
    (lblC P Qc₀ c) (rows P) htile hv harity (by simpa [execOfTraces, rows] using hrvt)
  intro s hs
  have hs' : s ∈ bfsForest [execOfTraces P Qc₀ Qm₀ c h |>.computeTree] :=
    (mem_bfsForest _ s).mpr ⟨_, List.mem_singleton.mpr rfl, hs⟩
  have hlen := hbind.1 s (by simpa [execOfTraces, rows] using hs')
  exact hlen.symm.trans_le ((comp_stateSep (K := K)).fanout_le _)

/-- **`ComputeExactTopology` of `execOfTraces`.** -/
theorem execOfTraces_computeTopology
    (h : TracesWalkHyps P Qc₀ Qm₀ c)
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1)
    (hα : alphaC c.1 ∉ walkPrefixAlphaEvent
      (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsatC i l))
      (foC P Qc₀ c) (rows P))
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P))
    (htileα : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P)) :
    ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c h) :=
  ⟨execOfTraces_compute_rvt P c Qc₀ Qm₀ hsatC hz hax hbasis hwidth h hseed hα hγ htileα,
    execOfTraces_compute_arity P c Qc₀ Qm₀ hsatC hz hax hbasis hwidth h hseed hα hγ htileα⟩

end ComputeTopology

section AlphaEventEq

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end AlphaEventEq

section PricedDischarge

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
  (hz : nprSeed c.1 ≠ 0)
  (hchar : MemStateTagChar F)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatC
include hax hbasis hwidth

/-- Tiling of the consumed `foOf` table, from the priced tiling event. -/
theorem foOf_tiles_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    Sf (foOf (P.computeSourceEnv Qc₀)) (rows P) + 1 = rows P := by
  have htileC : c.1 ∉ P.computeTilingEventOf Qc₀ :=
    (P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood).2.2.2.2.2.1
  have htileW : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) := by
    rwa [← computeTilingEventOf_eq_foW P c Qc₀ hsatC]
  have hSfW : Sf (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) + 1 = rows P :=
    deployed_tiling P c (familyQc P c Qc₀) hsatC hax hbasis hwidth htileW
  rw [Sf_foOf_eq_foW P c Qc₀ hsatC]
  exact hSfW

/-- Priced walk-root + tiling ⇒ outside `alphaRootEvent`. -/
theorem not_mem_alphaRoot_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    c.1 ∉ alphaRootEvent (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim) := by
  have hwalk : c.1 ∉ P.computeWalkRootEvent Qc₀ :=
    (P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood).2.2.2.2.1
  have htile : Sf (foOf (P.computeSourceEnv Qc₀)) (rows P) + 1 = rows P :=
    foOf_tiles_of_good P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood
  have hcons : c.1 ∉ alphaRootEventConsumed (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim) :=
    ((notMem_rootEvent_iff (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim)
      (rowLabelVec (P.computeSourceEnv Qc₀
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩)) c.1).1
      (by simpa [OptimizedFullStrictNockVMROMPackage.computeWalkRootEvent] using hwalk)).1
  simp only [alphaRootEventConsumed, htile, ↓reduceIte] at hcons
  exact hcons

/-- `hseed` of `deployed_prefixBFT` from `c ∉ optimizedFailureEvent`. -/
theorem hseed_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1 :=
  hseed_of_alphaRoot P c Qc₀ hsatC hax hbasis hwidth
    (not_mem_alphaRoot_of_good P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood)

omit hax hbasis hwidth in
/-- Chip walk columns agree with the projected `Vd`/`Cvd` RLCs. -/
theorem curW_eq_rlc_Vd (i : ℕ) :
    Batch459.curW P c (familyQc P c Qc₀) hsatC i =
      rlc (gamma c.1) (Vd P c Qc₀ i) := by
  simp only [Batch459.curW, Vd]
  rw [pubAt_rowOf P c Qc₀ hsatC i]

omit hax hbasis hwidth in
theorem chldW_eq_rlc_Cvd (i l : ℕ) :
    Batch459.chldW P c (familyQc P c Qc₀) hsatC i l =
      rlc (gamma c.1) (Cvd P c Qc₀ hsatC i l) := by
  simp only [Batch459.chldW, Cvd]
  rw [pubAt_rowOf P c Qc₀ hsatC i]

/-- Prefix `α`-event ⊆ priced `alphaRootEvent` after the root binding. -/
theorem walkPrefixAlpha_of_alphaRoot
    (hα : c.1 ∉ alphaRootEvent (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim)) :
    alphaC c.1 ∉ walkPrefixAlphaEvent
      (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsatC i l))
      (foC P Qc₀ c) (rows P) := by
  have hcur1 : Batch459.curW P c (familyQc P c Qc₀) hsatC 1 =
      rlc (gamma c.1)
        (claimLabelVec (nprSeed c.1) P.optimized.verifier.raw.claim) := by
    have h := deployed_root_cur_eq_claim P c Qc₀ hsatC hax hbasis hwidth hα
    have hrow : Batch459.rowOf P 1 = OptimizedComputeHostileAccumulator.firstRow P :=
      Batch459.rowOf_one P
    simp only [Batch459.curW]
    rw [hrow]
    exact h
  have hfun : (fun i => rlc (gamma c.1) (Vd P c Qc₀ i)) =
      Batch459.curW P c (familyQc P c Qc₀) hsatC := by
    funext i; exact (curW_eq_rlc_Vd P c Qc₀ hsatC i).symm
  have hch : (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsatC i l)) =
      Batch459.chldW P c (familyQc P c Qc₀) hsatC := by
    funext i l; exact (chldW_eq_rlc_Cvd P c Qc₀ hsatC i l).symm
  have hfo : foC P Qc₀ c = Batch459.foW P c (familyQc P c Qc₀) hsatC :=
    (foW_eq_foC_all P c Qc₀ hsatC).symm
  rw [hfun, hch, hfo, walkPrefixAlphaEvent_eq_alphaBadOf hcur1]
  have hD : rootDiffP (Batch459.curW P c (familyQc P c Qc₀) hsatC)
      (Batch459.chldW P c (familyQc P c Qc₀) hsatC)
      (Batch459.foW P c (familyQc P c Qc₀) hsatC)
      (rlc (gamma c.1)
        (claimLabelVec (nprSeed c.1) P.optimized.verifier.raw.claim)) (rows P) =
      rootDiffP (curOf (P.computeSourceEnv Qc₀) (gamma c.1))
        (chldOf (P.computeSourceEnv Qc₀) (gamma c.1))
        (foOf (P.computeSourceEnv Qc₀))
        (rlc (gamma c.1)
          (claimLabelVec (nprSeed c.1) P.optimized.verifier.raw.claim)) (rows P) :=
    (rootDiffP_family P c Qc₀ hsatC _).symm
  rw [hD]
  intro hmem
  exact hα ((mem_alphaRootEvent_iff _ _ c.1).2 hmem)

/-- Tiling exclusion the chip theorem takes, from the priced event. -/
theorem htileα_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) := by
  have htileC : c.1 ∉ P.computeTilingEventOf Qc₀ :=
    (P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood).2.2.2.2.2.1
  rwa [← computeTilingEventOf_eq_foW P c Qc₀ hsatC]

include hz hchar hsatM

/-- **Exact failing statement.**  `DeployedAcceptanceAt` + priced events give
`ComputeExactTopology` of `execOfTraces` once `γ ∉ prefixBadGammas`.  That
event is not a component of `optimizedFailureEvent` (priced `γ` is the
root/claim collision only). -/
theorem computeTopology_of_deployed
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P)) :
    ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c
      (tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)) :=
  execOfTraces_computeTopology P c Qc₀ Qm₀ hsatC hz hax hbasis hwidth
    (tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)
    (hseed_of_good P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood)
    (walkPrefixAlpha_of_alphaRoot P c Qc₀ hsatC hax hbasis hwidth
      (not_mem_alphaRoot_of_good P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood))
    hγ
    (htileα_of_good P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood)

end PricedDischarge

section MemoryFcommit

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)

omit hsatM hchar hz in
/-- 1-indexed `lblM` is the 0-indexed `lblMAt` on `1..M`. -/
theorem lblM_of_pos (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    lblM P Qm₀ c i = lblMAt P Qm₀ c ⟨i - 1, by omega⟩ := by
  have h : i - 1 < P.optimized.family.problem.cfg.memRows := by omega
  simp only [lblM, dif_pos h]

omit hsatM hchar hz in
/-- `Fmem`'s state conjunct: `Pub.st` is the decoded one-hot. -/
theorem lblM_state (i : ℕ) :
    (lblM P Qm₀ c i).2.2.st = (lblM P Qm₀ c i).1 := by
  unfold lblM
  split <;> rfl

/-- The `clabM`-shaped child of slot `l` (1-indexed) of row `i`. -/
def clabOfMem (lbl : ℕ → MState × DTmem K) (i l : ℕ) : MState × DTmem K :=
  ((lbl i).1, ((lbl i).2.1,
    { (lbl i).2.2 with
      pt := memCell (lbl i) ⟨(l - 1) % 2, Nat.mod_lt _ (by norm_num)⟩ }))

include hsatM hchar hz

/-- Decoded `eqBlk` at a 1-indexed memory row (M′, `m-prime-topo`).  Restates the former
`deployed_lblM_vmem`, which concluded the paper's uniform-β `Vmem` and so needed `hpole` and, since
the 31st, `hexp` (unsatisfiable on record rows whenever `γ ≠ 0`, `Batch679.rowExpTerm_eq_zero_iff`).  The β-free
conjunct needs neither: the chip's acceptance, `MemStateTagChar` and `z ≠ 0` only
(`FamilyMemoryRows.eqBlk_of_paper_classes`). -/
theorem deployed_lblM_eqBlk
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    eqBlk (lblM P Qm₀ c i).2.1 (lblM P Qm₀ c i).2.2 := by
  have hi : i - 1 < P.optimized.family.problem.cfg.memRows := by omega
  obtain ⟨st, hone⟩ :=
    baseOneHot_at_family P c (familyQm P c Qm₀) hsatM ⟨i - 1, hi⟩ hchar
  have hst : (decodeMemPub P (honestQm P c (familyQm P c Qm₀)) c ⟨i - 1, hi⟩).st = st := by
    simp only [decodeMemPub]
    exact memoryStateOf_eq_of_baseOneHot _ _ hone
  have he := eqBlk_of_paper_classes P c (familyQm P c Qm₀) hsatM ⟨i - 1, hi⟩ st hone hst hz
  have hQ : honestQm P c (familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  rw [lblM_of_pos P c Qm₀ i hi1 hih]
  rw [hQ] at he
  exact he

/-- **`hFcommit` at the deployed memory chip (no residual).**  M′:
the per-row predicate is the β-free `MemoryTopoBetaFree.FmemTopo` (state, `eqBlk`, fanout, child
link), from the chip's acceptance, `MemStateTagChar` and `z ≠ 0` alone — no `hpole`, no `hexp0`,
and nothing about `γ`, `β` or `reqIdx`.  `clabOfMem` is the 1-indexed `clabM`-shaped child;
`childLinkMem` reads only the child's `pt`. -/
theorem hFcommit_memory
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    MemoryTopoBetaFree.FmemTopo (lblM P Qm₀ c i)
      (fun j : Fin 2 =>
        if (j : ℕ) < foM P Qm₀ c i then
          some (clabOfMem (lblM P Qm₀ c) i ((j : ℕ) + 1))
        else none) := by
  refine ⟨lblM_state P c Qm₀ i,
    deployed_lblM_eqBlk P c Qm₀ hsatM hchar hz i hi1 hih,
    ?_, ?_⟩
  · intro j
    simp only [foM]
    constructor
    · intro hj; simp [hj]
    · intro hne; by_contra hj; simp [hj] at hne
  · intro j hj
    simp only [foM] at hj ⊢
    simp only [hj, ↓reduceIte]
    simp only [Option.map_some, clabOfMem]
    have hm : ((j : ℕ) + 1 - 1) % 2 = j := by
      rw [show (j : ℕ) + 1 - 1 = (j : ℕ) by omega]; exact Nat.mod_eq_of_lt j.isLt
    have hfin : (⟨((j : ℕ) + 1 - 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = j :=
      Fin.ext hm
    rw [hfin]

end MemoryFcommit

end Nock.RedTeam.Batch490
