/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/RootResultBridgeEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.RootResultBridge
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
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1173Thm54C2CombinedServedRecordsEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace Nock.NockVMROM.Thm54.RootResultBridge

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

/-- **THE ROOT-RESULT BRIDGE.**  `Batch1173`'s premise list (with `c ∉ optimizedFailureEventEv`)
gives: the C2 join's root evaluation at the family traces is the package claim's result. -/
theorem rootResult_bridge_ev
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
    (JT).label.evaluation = P.optimized.verifier.raw.claim.result := by
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P
  have hq1 : 1 < ringChar K := by omega
  have hz := FamilyIOChain.nprSeed_ne_of_good_at_ev P c Qc Qm hgood
  have hready := chipReady_aligned_of_traces_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen
    hG bs bf hΛG hF
  have hroot := Nock.RedTeam.Batch1111.root_binds_ev P c Qc Qm hacc hgood hax hbasis hwidth
  -- (0) the built root evaluation is the guarded run's result
  have hev : (JT).label.evaluation = r :=
    Nock.RedTeam.Batch1091.c2_aligned_eval (sv := svF P c Qm) (ax := axF P c Qc) (ringChar K)
      hready.2 fuel _ r hG le_rfl
  -- (1) `henc`: the join root binds the S-tree root; `root_binds_ev` binds the claim result there
  have hb := Nock.RedTeam.Batch1090.computeTreeBinds_of_chipReady (sv := svF P c Qm)
    (ax := axF P c Qc) hz (le_refl (treeS P c Qc).size) hready.1 hroot.1
  have hrow := hb.root
  rw [mapNTree_label] at hrow
  have he1 : bindFP (nprSeed c.1) (JT).label.evaluation (treeS P c Qc).label.1.2.2.1.e :=
    hrow.2.2.2.2.2.1
  have henc : GlobalCarryRecognizer.enc (nprSeed c.1) (JT).label.evaluation =
      GlobalCarryRecognizer.enc (nprSeed c.1) P.optimized.verifier.raw.claim.result := by
    have e2 := hroot.2.2
    unfold bindFP at he1 e2
    rw [← he1, ← e2]
  -- (2) leaf bounds, at the window `Λg = memRows ⊔ Λ`
  have hgen' := Nock.RedTeam.Batch1091.c2_aligned_genuine (sv := svF P c Qm) (ax := axF P c Qc)
    (ringChar K) hready.2 fuel (treeS P c Qc).size r hG le_rfl
  obtain ⟨-, -, hrows⟩ := genuine_rows_le_programLeafBound hgen hgen'
    (Nock.RedTeam.Batch1021.J_subject _ _ _ _) (Nock.RedTeam.Batch1021.J_formula _ _ _ _)
  have hΛ1 : (JT).label.evaluation.leaves ≤ Λg P :=
    ((hrows _ (Walk.InTree.here _)).2.2.trans hΛG).trans le_sup_right
  have hΛ2 : P.optimized.verifier.raw.claim.result.leaves ≤ Λg P :=
    (claimResult_leaves_le P).trans le_sup_right
  -- (3) outside the root-result event: field-noun equality
  have hout : c.1 ∉ rootResultEv P (honestQc P c Qc) (honestQm P c Qm) :=
    (optimizedFailureEventEv_good_components P _ _ c hgoodEv).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpub : (builtSkeletonEv P (honestQc P c Qc) (honestQm P c Qm)).publicClaim.result =
      (JT).label.evaluation := by
    show (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)).computeTree.label.evaluation = _
    rw [Nock.RedTeam.Batch1173.skeletonEv_computeTree_eq P c Qc Qm]
  have hzs : nprSeed c.1 ∉ PreSeedCensus.pairBadSeeds (K := K) (Λg P)
      [((builtSkeletonEv P (honestQc P c Qc) (honestQm P c Qm)).publicClaim.result,
        P.optimized.verifier.raw.claim.result)] := by
    intro hmem
    exact hout (by rw [rootResultEv, mem_liftSeed_iff]; exact hmem)
  rw [hpub] at hzs
  have hfn := PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hzs (by simp) hΛ1 hΛ2 henc
  -- (4) atoms below the characteristic: noun equality
  have hbr : BoundedBy (ringChar K) (JT).label.evaluation := by
    rw [hev]; exact Nock.RedTeam.Batch1091.evalGBy_bounded hq1 bs bf hG
  exact PreSeedCensus.noun_eq_of_fieldNoun_eq (bounded_leafList hbr)
    (bounded_leafList (claimResult_bounded P)) hfn

/-- **THE SEMANTIC `p8`** at the family traces: `Batch1173`'s premise list and nothing else; the
package claim's result is the guarded evaluation of its own program, and (through
`evalGBy_le_evalN`) its Nock evaluation.  No `hbridge`, no `TC.Accepts`, no `GenuineTargetAt`. -/
theorem holds_of_traces_ev
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
    evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result ∧
      Nock.evalN fuel P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula =
        some P.optimized.verifier.raw.claim.result := by
  have hal := (chipReady_aligned_of_traces_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG
    bs bf hΛG hF).2
  have he : (JT).label.evaluation = r :=
    Nock.RedTeam.Batch1091.c2_aligned_eval (sv := svF P c Qm) (ax := axF P c Qc) (ringChar K) hal
      fuel _ r hG le_rfl
  have hr : r = P.optimized.verifier.raw.claim.result :=
    he.symm.trans (rootResult_bridge_ev P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf
      hΛG hF)
  subst hr
  refine ⟨hG, ?_⟩
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P
  exact evalGBy_le_evalN (by omega) bs bf hG

end Nock.NockVMROM.Thm54.RootResultBridge

