/-
  Nock/NockVMROM/Thm54/P8Core/PlacementAEvOnly.lean

  Imports P8Core only; never
  the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.EvOnly.RootResultBridgeEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace Nock.NockVMROM.Thm54.PlacementA

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
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1024
open Nock.RedTeam.Batch1173
open Nock.NockVMROM.Thm54.RootResultBridge (claimInputs_bounded)
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


/-! Each is the `_ev` twin (`P8Core/EvOnly/`) at `hgood := hgoodEv`: the twin chain reads its former
`hgood` slot only through `PlacementA.good_components_of_Ev`, so one hypothesis
`c ∉ optimizedFailureEventEv …` serves both slots. -/

/-- **`bindsAtCoin_C2_combined` with no `hgood`.** -/
theorem bindsAtCoin_C2_combined_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
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
  Nock.RedTeam.Batch1173.bindsAtCoin_C2_combined_ev P c Qc Qm hacc hgoodEv hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG hF

/-- **`census_window_combined` with no `hgood`.** -/
theorem census_window_combined_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
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
  Nock.RedTeam.Batch1173.census_window_combined_ev P c Qc Qm hacc hgoodEv hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG hF

/-- **`not_mem_FailureUnion_combined` with no `hgood`.** -/
theorem not_mem_FailureUnion_combined_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
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
        (census_window_combined_evOnly P c Qc Qm hacc hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG hF).1)
      c.2.2.2.lambda :=
  Nock.RedTeam.Batch1173.not_mem_FailureUnion_combined_ev P c Qc Qm hacc hgoodEv hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG hF

/-- **`rootResult_bridge` with no `hgood`**: the C2 join's root evaluation at the family traces is
the package claim's result. -/
theorem rootResult_bridge_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
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
    (JT).label.evaluation = P.optimized.verifier.raw.claim.result :=
  Nock.NockVMROM.Thm54.RootResultBridge.rootResult_bridge_ev P c Qc Qm hacc hgoodEv hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG hF

/-- **THE SEMANTIC `p8` with no `hgood`** (`holds_of_traces`): the claimed result is the guarded
and the Nock evaluation of the claim's own program. -/
theorem holds_of_traces_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
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
    evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result ∧
      Nock.evalN fuel P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula =
        some P.optimized.verifier.raw.claim.result :=
  Nock.NockVMROM.Thm54.RootResultBridge.holds_of_traces_ev P c Qc Qm hacc hgoodEv hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG hF

/-- **`holds_exists` with no `hgood`.** -/
theorem holds_exists_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
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
    (∃ fuel', evalGBy (ringChar K) fuel' P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result) ∧
      ∃ fuel', Nock.evalN fuel' P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result := by
  have H := holds_of_traces_evOnly P c Qc Qm hacc hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG hF
  exact ⟨⟨fuel, H.1⟩, ⟨fuel, H.2⟩⟩

/-- The walk hypotheses at the family traces from acceptance and `c ∉ optimizedFailureEventEv`
(`Batch489.tracesWalkHyps_of_deployed_ev`, repacked field by field as `tracesWalkHyps_of_acc`). -/
theorem tracesWalkHyps_of_acc_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c := by
  have hacc' : DeployedAcceptanceAt P c (familyQc P c (honestQc P c Qc))
      (familyQm P c (honestQm P c Qm)) := by
    rw [Nock.RedTeam.Batch824.familyQc_honestQc, Nock.RedTeam.Batch824.familyQm_honestQm]
    exact hacc
  have h0 := Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed_ev P c (honestQc P c Qc)
    (honestQm P c Qm) hacc'.compute_satisfies hacc'.memory_satisfies
    (Nock.RedTeam.Batch824.memStateTagChar_of_package P) hax hbasis hwidth hacc' hgoodEv
  exact ⟨h0.sfCompute, h0.validCompute, h0.sfMemory, h0.validMemory⟩

/-- **The semantic `p8` from acceptance, with no `hgood`**: acceptance at the family chips,
`c ∉ optimizedFailureEventEv`, `of_package`'s Form R hypotheses, the compiler's generator run and
window, the program's guarded termination, and `hF`.  `h`, `bs`, `bf` are derived. -/
theorem holds_of_acceptance_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result ∧
      Nock.evalN fuel P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula =
        some P.optimized.verifier.raw.claim.result :=
  holds_of_traces_evOnly P c Qc Qm hacc hgoodEv hax hbasis hwidth
    (tracesWalkHyps_of_acc_evOnly P c Qc Qm hacc hax hbasis hwidth hgoodEv) hgen hG
    (claimInputs_bounded P).1 (claimInputs_bounded P).2 hΛG hF

theorem wrong_claim_rejected_evOnly
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (hwrong : r ≠ P.optimized.verifier.raw.claim.result)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    c ∈ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm) := by
  by_contra hgoodEv
  have H := holds_of_acceptance_evOnly P c Qc Qm hacc hgoodEv hax hbasis hwidth hgen hG hΛG hF
  rw [hG] at H
  exact hwrong (Option.some.inj H.1)

end Nock.NockVMROM.Thm54.PlacementA
