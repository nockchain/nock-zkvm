/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch974Thm54Round0WrapJoinForestEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch974Thm54Round0WrapJoinForest
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch489Thm54FoOfEqFoWEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch490Thm54TopologyAssemblyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch500Thm54GammaTransportEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch501Thm54MemoryTopologyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch822Thm54R4BridgeMemoryEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.FamilyIOChainRouteBEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch824Thm54R4BridgeEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.UniqueExponentsBridgeEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch973Thm54Round0WrapJoinEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch974

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.RedTeam.Batch973
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch516 (ServedFingerprint)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

theorem hio_of_hgood_ev (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    FamilyIOGood P c Qc Qm := by
  have h2 := (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P _ _ c hgood).2.1
  have := Nock.RedTeam.Batch884.familyIOGood_of_not_mem P (honestQc P c Qc) (honestQm P c Qm) c h2
  have hm : Nock.RedTeam.Batch884.famQm P c (honestQm P c Qm) = Qm := by
    funext j; unfold Nock.RedTeam.Batch884.famQm honestQm
    exact congrArg Qm (Fin.ext (by rw [Fin.val_cast, Fin.val_cast]))
  rwa [Nock.RedTeam.Batch824.familyQc_honestQc, hm] at this

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

/-- The decoded forest's β-free topology, at the reindexed traces. -/
theorem decoded_topology_ev :
    ∀ t ∈ (ExecOfTraces.execOfTraces P (honestQc P c Qc) (honestQm P c Qm) c
      (Batch489.tracesWalkHyps_of_deployed_ev P c (honestQc P c Qc) (honestQm P c Qm)
        (by rw [Batch824.familyQc_honestQc]; exact hacc.compute_satisfies)
        (by rw [Batch824.familyQm_honestQm]; exact hacc.memory_satisfies)
        (Batch824.memStateTagChar_of_package P) hax hbasis hwidth
        (by rw [Batch824.familyQc_honestQc, Batch824.familyQm_honestQm]; exact hacc)
        hgood)).memoryForest,
      RVTWithArity (FmemTopo (K := K)) t :=
  Batch501.memoryTopology_of_deployed_of_good_ev P c (honestQc P c Qc) (honestQm P c Qm)
    (by rw [Batch824.familyQc_honestQc]; exact hacc.compute_satisfies)
    (by rw [Batch824.familyQm_honestQm]; exact hacc.memory_satisfies)
    (Batch824.memStateTagChar_of_package P)
    (FamilyIOChain.nprSeed_ne_of_good_at_ev P c Qc Qm hgood) hax hbasis hwidth
    (by rw [Batch824.familyQc_honestQc, Batch824.familyQm_honestQm]; exact hacc) hgood

include hacc hgood hax hbasis hwidth

/-- **The per-row identity** at every 0-indexed memory row `k`. -/
theorem row_identity_ev (k : Fin P.optimized.family.problem.cfg.memRows) :
    (wrapR0OfEnvs (computeEnvsR0 P.optimized (honestQc P c Qc) c)
        (memoryEnvsR0 P.optimized (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows_pos
        (k.val + 1) (ExecOfTraces.lblMAt P (honestQm P c Qm) c k)).specialize
        (alphaM c.1) c.2.2.2.lambda =
      ExecOfTraces.lblMAt P (honestQm P c Qm) c k := by
  have hio := hio_of_hgood_ev P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hE : memRowExpOfEnvs (memoryEnvsR0 P.optimized (honestQm P c Qm) c)
      P.optimized.family.problem.cfg.memRows_pos (k.val + 1) = expR P c Qm k := by
    unfold memRowExpOfEnvs
    rw [dif_pos (by simp)]
    rfl
  have hfam : FamilyEnvCore.familyQc P.optimized c (honestQc P c Qc) = Qc :=
    Batch824.familyQc_honestQc P c Qc
  have hC : certAxisOfEnvs (computeEnvsR0 P.optimized (honestQc P c Qc) c) =
      certAxisOfEnvs (Batch824.envsCR P c Qc) := by
    refine Batch970.certAxisOfEnvs_congr fun i col _ => ?_
    have htr : (computeEnvsR0 P.optimized (honestQc P c Qc) c i).trace =
        (Batch824.envsCR P c Qc i).trace := by
      unfold computeEnvsR0
      rw [hfam]
      exact (Batch823.envsC_trace P c Qc i).symm
    rw [htr]
  unfold wrapR0OfEnvs
  rw [hE, hC]
  apply specialize_wrapR0_eq_self
  · rfl
  · exact congrArg some (HostilePoleAlignment.memorySourceEnvAt_chal8 P c (honestQm P c Qm) k)
  · intro hk
    have htop := decoded_topology_ev P c Qc Qm hacc hgood hax hbasis hwidth
    have hF := Batch509.fmem_of_topology P c (honestQc P c Qc) (honestQm P c Qm) _ htop
      (k.val + 1) (by omega) k.isLt
    rw [ExecOfTraces.lblM_succ] at hF
    have hst : (ExecOfTraces.lblMAt P (honestQm P c Qm) c k).2.2.st =
        (ExecOfTraces.lblMAt P (honestQm P c Qm) c k).1 := hF.1
    exact Batch509.eqBlk_padding_mem_zero hF.2.1 (by rw [hst]; exact hk)
  · intro hk
    have hstate : (ExecOfTraces.lblMAt P (honestQm P c Qm) c k).1 =
        memRowStateOf (memEnvF P c Qm k) := Batch844.memoryStateOf_eq_memRowStateOf _
    rw [hstate] at hk
    rcases hs : memRowStateOf (memEnvF P c Qm k) with _ | _ | _ | _
    · rw [hs] at hk; exact absurd hk (by decide)
    · rw [hs] at hk; exact absurd hk (by decide)
    · obtain ⟨h25, h57, h26⟩ := read_row_facts_ev P c Qc Qm hacc hgood hio hrb hb1 hwidth k hs
      exact ⟨h26, h25, congrArg some h57⟩
    · obtain ⟨h25, h57, h26⟩ := verify_row_facts_ev P c Qc Qm hacc hgood hio hrb hb1 hwidth k hs
      exact ⟨h26, h25, congrArg some h57⟩

/-- **The round-0 wrap then specialize is the identity on every decoded memory row**
(`lblMR0`, every index, `lblM`'s off-range convention). -/
theorem wrapR0_identity_ev (i : ℕ) :
    (lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c i).specialize
        (alphaM c.1) c.2.2.2.lambda =
      StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c i := by
  have hM := P.optimized.family.problem.cfg.memRows_pos
  have hreduce : ∀ k : Fin P.optimized.family.problem.cfg.memRows,
      (lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c (k.val + 1)).specialize
          (alphaM c.1) c.2.2.2.lambda =
        StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c (k.val + 1) := by
    intro k
    have hl : StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c (k.val + 1) =
        ExecOfTraces.lblMAt P (honestQm P c Qm) c k := ExecOfTraces.lblM_succ P _ c k
    show (wrapR0OfEnvs _ _ _ (k.val + 1)
      (StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c (k.val + 1))).specialize _ _ = _
    rw [hl]
    exact row_identity_ev P c Qc Qm hacc hgood hax hbasis hwidth k
  by_cases hi : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact hreduce ⟨k, by omega⟩
  · have hoff : StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c i =
        StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c 1 :=
      Batch509.lblM_off_eq_root P c (honestQm P c Qm) i hi
    have hexp : memRowExpOfEnvs (memoryEnvsR0 P.optimized (honestQm P c Qm) c) hM i =
        memRowExpOfEnvs (memoryEnvsR0 P.optimized (honestQm P c Qm) c) hM 1 := by
      unfold memRowExpOfEnvs
      by_cases h0 : i - 1 < P.optimized.family.problem.cfg.memRows
      · have : i = 0 := by omega
        subst this
        rfl
      · rw [dif_neg h0, dif_pos (by omega)]
    have hrow : lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c i =
        lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c 1 := by
      unfold lblMR0 wrapR0OfEnvs
      rw [hexp, hoff]
    rw [hrow, hoff]
    exact hreduce ⟨0, hM⟩

/-- **The round-0 strategy's specialized memory forest IS the decoded forest.** -/
theorem specialized_memoryForest_R0_eq_ev
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTracesR0 P.optimized P.stateTagChar (honestQc P c Qc) (honestQm P c Qm) c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest =
      (StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc) (honestQm P c Qm) c h).memoryForest := by
  rw [specializedExec_R0_eq]
  change (reconForest P.optimized.family.problem.cfg.kMem
      (StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c)
      (lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
      P.optimized.family.problem.cfg.memRows).map
      (mapNTree (fun row : MemoryRowTemplate (K := K) => row.specialize (alphaM c.1) c.2.2.2.lambda)) =
    reconForest P.optimized.family.problem.cfg.kMem
      (StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c)
      (StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c)
      P.optimized.family.problem.cfg.memRows
  rw [Batch509.mapNTree_reconForest]
  exact Batch509.reconForest_eq_of_lbl _ _ _
    (wrapR0_identity_ev P c Qc Qm hacc hgood hax hbasis hwidth)

/-- **`wrapJoin_ev`.**  Every tree of the round-0 strategy's specialized memory forest — the forest
`ProductionStrategy.BindsAtCoin` reads at `(nprSeed c.1, alphaM c.1, c.λ)` — is in
`L_RVT^{FmemTopo,2}`: the `eqBlk` / `FmemTopo` premise of the `BindsAtCoin` chain, on accepted
family traces outside the event. -/
theorem wrapJoin_ev
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (hz : nprSeed c.1 ≠ 0) :
    ∀ t ∈ ((strategyOfTracesR0 P.optimized P.stateTagChar (honestQc P c Qc) (honestQm P c Qm) c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest,
      RVTWithArity (FmemTopo (K := K)) t := by
  rw [specialized_memoryForest_R0_eq_ev P c Qc Qm hacc hgood hax hbasis hwidth h hz]
  exact decoded_topology_ev P c Qc Qm hacc hgood hax hbasis hwidth

end

end Nock.RedTeam.Batch974

