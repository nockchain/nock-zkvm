/-
  Nock/RedTeam/Batch1111Thm54C2CombinedAtTraces.lean

  * `ServedRecordsOK` — gap (ii), the served-record oracle (`RecOK` at every reached node);
  * `CertAxesOK` — the certificate axes of OP0 / OP9 rows cast to the row's leaf and lie below the
    characteristic (S1 axis validity at the family chips).

  Discharged here:
-/
import Nock.RedTeam.Batch1110Thm54C2CombinedInduction
import Nock.RedTeam.Batch1024Thm54C2BindsAtCoin
import Nock.RedTeam.Batch500Thm54GammaTransport
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch974Thm54Round0WrapJoinForest
import Nock.NockVMROM.Thm54.ConsumerObligationsEv
import Nock.NockVMROM.Thm54.OptimizedFailureEventEv
import Nock.NockVMROM.Thm54.P8Core.Batch1111Thm54C2CombinedAtTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1111

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
open Nock.NockVMROM.Thm54.DeployedAcceptance
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

/-- The C2 join on the family traces at `c`, rooted at the package claim. -/
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

/-! ## §A  The census and size-window oracles from the 2b-ii event -/

section Census

variable (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
include hgoodEv

end Census

/-! ## §B  The row facts from the compute topology  and the seed -/

section Rows

end Rows


section Root

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hacc hgood hax hbasis hwidth

end Root

/-! ## §D  The context at the traces, the induction at the traces, and the assembly -/

section Assembly

def ServedRecordsOK : Prop :=
  ∀ (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun), InTree (treeS P c Qc) u →
    InTree JT (c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1) (fun l => l.2)
      (svF P c Qm) (axF P c Qc) u.size u s f) →
    RecOK (nprSeed c.1) (ringChar K) P.optimized.Λ u.label
      (c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1) (fun l => l.2)
        (svF P c Qm) (axF P c Qc) u.size u s f).label

def CertAxesOK : Prop :=
  ∀ u : NTree ((State × DTcomp K) × ℕ), InTree (treeS P c Qc) u →
    (u.label.1.1 = .s0 →
      ((axF P c Qc (u.label.2 + 2) : ℕ) : K) = u.label.1.2.2.2.f_t.leaf ∧
        axF P c Qc (u.label.2 + 2) < ringChar K) ∧
    (u.label.1.1 = .s9 →
      ((axF P c Qc (u.label.2 + 3) : ℕ) : K) = u.label.1.2.2.2.f_th.leaf ∧
        axF P c Qc (u.label.2 + 3) < ringChar K)

/-- **The context at the traces.** -/
theorem ctx_of_traces
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {G : NTree (GenComputeRow K)}
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ) (hΛ1 : 1 ≤ P.optimized.Λ)
    (hrec : ServedRecordsOK P c Qc Qm) (haxc : CertAxesOK P c Qc) :
    Ctx (sv := svF P c Qm) (ax := axF P c Qc) (nprSeed c.1) (ringChar K) P.optimized.Λ G
      (treeS P c Qc) P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula := by
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P
  have hz := FamilyIOChain.nprSeed_ne_of_good_at P c Qc Qm hgood
  refine ⟨hz, by omega, by omega, ?_, hΛ1, hΛG, ?_, hrec, ?_, ?_⟩
  · exact CharP.natCast_injOn_Iio K (ringChar K)
  · intro u hu
    obtain ⟨hst, hz', hV, har, hl⟩ := rowFacts_core P c Qc Qm hacc hgood hax hbasis hwidth h u hu
    exact ⟨hst, hz', hV, har, hl, (haxc u hu).1, (haxc u hu).2⟩
  · intro u s f _ hreach
    exact censusOK_of_ev P c Qc Qm hgoodEv hreach
  · intro u s f _ hreach
    exact windowOK_of_ev P c Qc Qm hgoodEv hz hreach

theorem chipReady_aligned_of_traces
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
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
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ) (hΛ1 : 1 ≤ P.optimized.Λ)
    (hrec : ServedRecordsOK P c Qc Qm) (haxc : CertAxesOK P c Qc) :
    Batch1090.C2ChipReady (sv := svF P c Qm) (ax := axF P c Qc) (nprSeed c.1) (ringChar K) (treeS P c Qc)
        P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula ∧
      Batch1091.C2Aligned (sv := svF P c Qm) (ax := axF P c Qc) (treeS P c Qc)
        P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula := by
  have hroot := root_binds P c Qc Qm hacc hgood hax hbasis hwidth
  exact root_good (ctx_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hΛG hΛ1 hrec haxc)
    (honestCall_root hgen) ⟨fuel, r, hG⟩ bs bf hroot.1 hroot.2.1

theorem bindsAtCoin_C2_combined
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (hα0 : alphaM c.1 ≠ 0)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ) (hΛ1 : 1 ≤ P.optimized.Λ)
    (hrec : ServedRecordsOK P c Qc Qm) (haxc : CertAxesOK P c Qc) :
    (TC P c Qc Qm h).BindsAtCoin c.1 c.2.2.2.lambda :=
  Batch1090.bindsAtCoin_C2_of_chipReady P c Qc Qm h hacc hgood hax hbasis hwidth hF hα0
    (chipReady_aligned_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
      hΛ1 hrec haxc).1
    (root_binds P c Qc Qm hacc hgood hax hbasis hwidth).1

theorem census_window_combined
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
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
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ) (hΛ1 : 1 ≤ P.optimized.Λ)
    (hrec : ServedRecordsOK P c Qc Qm) (haxc : CertAxesOK P c Qc) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) P.optimized.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) P.optimized.Λ :=
  Batch1091.c2_aligned_census_window hΛ1
    (chipReady_aligned_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
      hΛ1 hrec haxc).2
    hG hgen hΛG _ (skeletonEv_computeTree_eq P c Qc Qm)

theorem not_mem_FailureUnion_combined
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
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
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ) (hΛ1 : 1 ≤ P.optimized.Λ)
    (hrec : ServedRecordsOK P c Qc Qm) (haxc : CertAxesOK P c Qc) :
    c.1 ∉ ProductionP8Containment.FailureUnion (TC P c Qc Qm h)
      (ConsumerObligationsEv.census_C2_of_Ev P c (honestQc P c Qc) (honestQm P c Qm) h
        (census_window_combined P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
          hΛ1 hrec haxc).1)
      c.2.2.2.lambda :=
  ConsumerObligationsEv.not_mem_FailureUnion_C2 P c (honestQc P c Qc) (honestQm P c Qm) h
    (hacc_at P c Qc Qm hacc) hgoodEv hbasis
    (census_window_combined P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
      hΛ1 hrec haxc).1
    (census_window_combined P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG
      hΛ1 hrec haxc).2

end Assembly

end Nock.RedTeam.Batch1111

#print axioms Nock.RedTeam.Batch1111.censusOK_of_ev
#print axioms Nock.RedTeam.Batch1111.windowOK_of_ev
#print axioms Nock.RedTeam.Batch1111.rowFacts_core
#print axioms Nock.RedTeam.Batch1111.root_binds
#print axioms Nock.RedTeam.Batch1111.chipReady_aligned_of_traces
#print axioms Nock.RedTeam.Batch1111.bindsAtCoin_C2_combined
#print axioms Nock.RedTeam.Batch1111.census_window_combined
#print axioms Nock.RedTeam.Batch1111.not_mem_FailureUnion_combined
