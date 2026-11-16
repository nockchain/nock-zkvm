/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch1173Thm54C2CombinedServedRecordsEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1173Thm54C2CombinedServedRecords
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
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch974Thm54Round0WrapJoinForestEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1011Thm54AxisViewBindsAtCoinEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1024Thm54C2BindsAtCoinEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1090Thm54C2ReadyFuelEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1111Thm54C2CombinedAtTracesEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1140Thm54CertAxesAtTracesEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1172Thm54ServedRecordsAtTracesEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1173

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1024
open Nock.RedTeam.Batch1110
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
set_option quotPrecheck false
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

open Nock.RedTeam.Batch1111 (root_binds_ev rowFacts_core_ev censusOK_of_ev windowOK_of_ev
  skeletonEv_computeTree_eq hacc_at)
open Nock.RedTeam.Batch1142 (hΛ1_of_hgen hα0_of_goodEv)

section Assembly

/-- **The context at the traces, certificate axes discharged.** -/
theorem ctx_of_traces_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {G : NTree (GenComputeRow K)}
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ) (hΛ1 : 1 ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    Batch1171.Ctx (sv := svF P c Qm) (ax := axF P c Qc) (nprSeed c.1) (ringChar K) P.optimized.Λ G
      (treeS P c Qc) P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula := by
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P
  have hz := FamilyIOChain.nprSeed_ne_of_good_at_ev P c Qc Qm hgood
  have hα0 := hα0_of_goodEv P c Qc Qm hgoodEv
  have haxc := Batch1140.certAxesOK0_of_traces_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 h
  have hrec := Batch1172.servedRecordsPos_of_traces_ev P c Qc Qm hacc hgood hax hbasis hwidth hgoodEv h hF
  refine ⟨hz, by omega, by omega, ?_, hΛ1, hΛG, ?_, hrec, ?_, ?_⟩
  · exact CharP.natCast_injOn_Iio K (ringChar K)
  · intro u hu
    obtain ⟨hst, hz', hV, har, hl⟩ := rowFacts_core_ev P c Qc Qm hacc hgood hax hbasis hwidth h u hu
    exact ⟨hst, hz', hV, har, hl, (haxc u hu).1, (haxc u hu).2⟩
  · intro u s f _ hreach
    exact censusOK_of_ev P c Qc Qm hgoodEv hreach
  · intro u s f _ hreach
    exact windowOK_of_ev P c Qc Qm hgoodEv hz hreach

/-- **`C2ChipReady` and `C2Aligned` at the traces** (certificate axes discharged; `hΛ1` derived). -/
theorem chipReady_aligned_of_traces_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    Batch1090.C2ChipReady (sv := svF P c Qm) (ax := axF P c Qc) (nprSeed c.1) (ringChar K) (treeS P c Qc)
        P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula ∧
      Batch1091.C2Aligned (sv := svF P c Qm) (ax := axF P c Qc) (treeS P c Qc)
        P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula := by
  have hroot := root_binds_ev P c Qc Qm hacc hgood hax hbasis hwidth
  exact Batch1171.root_good (ctx_of_traces_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hΛG
      (hΛ1_of_hgen hgen hΛG) hF)
    (honestCall_root hgen) ⟨fuel, r, hG⟩ bs bf hroot.1 hroot.2.1

theorem bindsAtCoin_C2_combined_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    (TC P c Qc Qm h).BindsAtCoin c.1 c.2.2.2.lambda :=
  Batch1090.bindsAtCoin_C2_of_chipReady_ev P c Qc Qm h hacc hgood hax hbasis hwidth hF
    (hα0_of_goodEv P c Qc Qm hgoodEv)
    (chipReady_aligned_of_traces_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
      hF).1
    (root_binds_ev P c Qc Qm hacc hgood hax hbasis hwidth).1

theorem census_window_combined_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) P.optimized.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) P.optimized.Λ :=
  Batch1091.c2_aligned_census_window (hΛ1_of_hgen hgen hΛG)
    (chipReady_aligned_of_traces_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
      hF).2
    hG hgen hΛG _ (skeletonEv_computeTree_eq P c Qc Qm)

theorem not_mem_FailureUnion_combined_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    c.1 ∉ ProductionP8Containment.FailureUnion (TC P c Qc Qm h)
      (ConsumerObligationsEv.census_C2_of_Ev P c (honestQc P c Qc) (honestQm P c Qm) h
        (census_window_combined_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
          hF).1)
      c.2.2.2.lambda :=
  ConsumerObligationsEv.not_mem_FailureUnion_C2 P c (honestQc P c Qc) (honestQm P c Qm) h
    (hacc_at P c Qc Qm hacc) hgoodEv hbasis
    (census_window_combined_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
      hF).1
    (census_window_combined_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
      hF).2

end Assembly

end Nock.RedTeam.Batch1173

