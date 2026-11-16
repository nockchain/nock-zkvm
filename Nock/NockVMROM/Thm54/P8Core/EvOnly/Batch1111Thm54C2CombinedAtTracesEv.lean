/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch1111Thm54C2CombinedAtTracesEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1111Thm54C2CombinedAtTraces
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
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
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

section Census

variable (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
include hgoodEv

end Census

section Rows

theorem fcomp_of_inTree_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    ∀ v, InTree (StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc)
        (honestQm P c Qm) c h).computeTree v →
      Fcomp (K := K) v.label (fun i => v.childLabel i) ∧ v.children.length ≤ 3 := by
  have htopo := Batch500.computeTopology_of_deployed_of_good_ev P c (honestQc P c Qc) (honestQm P c Qm)
    (hsatC_at P c Qc Qm hacc) (hsatM_at P c Qc Qm hacc)
    (FamilyIOChain.nprSeed_ne_of_good_at_ev P c Qc Qm hgood)
    (Batch824.memStateTagChar_of_package P) hax hbasis hwidth (hacc_at P c Qc Qm hacc) hgood
  unfold ComputeExactTopology at htopo
  have hrvt := htopo.1
  have har := htopo.2
  intro v hv
  have hv' : InTree (ExecOfTraces.execOfTraces P (honestQc P c Qc) (honestQm P c Qm) c
      (Batch489.tracesWalkHyps_of_deployed_ev P c (honestQc P c Qc) (honestQm P c Qm)
        (hsatC_at P c Qc Qm hacc) (hsatM_at P c Qc Qm hacc)
        (Batch824.memStateTagChar_of_package P) hax hbasis hwidth (hacc_at P c Qc Qm hacc)
        hgood)).computeTree v := hv
  exact ⟨((RVT_iff_forall_InTree (Fcomp (K := K)) _).mp hrvt v hv').1, har v hv'⟩

/-- **The row facts, except the certificate axes, at every node of the S-carrying tree.** -/
theorem rowFacts_core_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    ∀ u, InTree (treeS P c Qc) u →
      u.label.1.2.2.1.state = u.label.1.1 ∧ u.label.1.2.1.z = nprSeed c.1 ∧
      Vcomp u.label.1.2.1 u.label.1.2.2.1 u.label.1.2.2.2 ∧
      u.children.length = fanoutComp u.label.1.1 ∧
      ∀ (k : Fin 3) (c' : NTree ((State × DTcomp K) × ℕ)), u.children[(k : ℕ)]? = some c' →
        (c'.label.1.2.2.1.s, c'.label.1.2.2.1.f, c'.label.1.2.2.1.e) =
          sfTriple u.label.1.2.2.1 k := by
  intro u hu
  obtain ⟨hF, hlen⟩ := fcomp_of_inTree_ev P c Qc Qm hacc hgood hax hbasis hwidth h _
    (inTree_exec_of_inTree P c Qc Qm h hu)
  obtain ⟨i, hi⟩ := label_of_inTree_S P c Qc Qm h hu
  have hz : u.label.1.2.1.z = nprSeed c.1 := by rw [hi]; exact lblCS_z P c Qc i
  rw [mapNTree_label] at hF
  have hcl : ∀ j : ℕ, (mapNTree Prod.fst u).childLabel j =
      u.children[j]?.map (fun c' => c'.label.1) := by
    intro j
    simp only [NTree.childLabel, NTree.childOpt, mapNTree_children, List.getElem?_map,
      Option.map_map]
    cases u.children[j]? <;> simp [mapNTree_label]
  rw [mapNTree_children, List.length_map] at hlen
  obtain ⟨hst, hV, hiff, hlink⟩ := hF
  have key : ∀ j, j < 3 → (j < fanoutComp u.label.1.1 ↔ j < u.children.length) := by
    intro j hj
    have hj' := hiff ⟨j, hj⟩
    dsimp only at hj'
    rw [hcl j, ne_eq, Option.map_eq_none_iff, List.getElem?_eq_none_iff, not_le] at hj'
    exact hj'
  refine ⟨hst, hz, hV, ?_, ?_⟩
  · -- arity: the iff at `i < 3` plus `length ≤ 3`
    have hfan : fanoutComp u.label.1.1 ≤ 3 := by cases u.label.1.1 <;> decide
    rcases Nat.lt_trichotomy u.children.length (fanoutComp u.label.1.1) with hlt | heq | hgt
    · exfalso
      have := (key u.children.length (by omega)).1 hlt
      omega
    · exact heq
    · exfalso
      have := (key (fanoutComp u.label.1.1) (by omega)).2 hgt
      omega
  · intro k c' hc
    have hk : (k : ℕ) < fanoutComp u.label.1.1 := by
      rw [key k k.isLt]
      exact (List.getElem?_eq_some_iff.1 hc).1
    have hl := hlink k hk
    dsimp only at hl
    rw [hcl k, hc] at hl
    simpa using hl

end Rows

section Root

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hacc hgood hax hbasis hwidth

/-- **`hsRoot` (and the formula / result twins)**: the root row of the S-carrying tree binds the
package claim's subject, formula and result — `Batch465.deployed_root_label_eq_claim_of_good_ev` with
`hα` from `Batch490.not_mem_alphaRoot_of_good_ev` (priced walk-root + tiling), bridged to `treeS`'s
root label (row `1` of the inverse BFS is `lblCAt 0`, whose `Pub` is `decodePub` of the first row
at any state). -/
theorem root_binds_ev :
    bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.subject (treeS P c Qc).label.1.2.2.1.s ∧
      bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.formula (treeS P c Qc).label.1.2.2.1.f ∧
      bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.result (treeS P c Qc).label.1.2.2.1.e := by
  have hsatC := hsatC_at P c Qc Qm hacc
  have hα := Batch490.not_mem_alphaRoot_of_good_ev P c (honestQc P c Qc) (honestQm P c Qm) hsatC
    hax hbasis hwidth hgood
  have hroot := Batch465.deployed_root_label_eq_claim_of_good_ev P c (honestQc P c Qc) hsatC hax hbasis
    hwidth (honestQm P c Qm) hgood hα
  rw [Batch824.familyQc_honestQc] at hroot
  obtain ⟨st0, -, hs, hf, he⟩ := hroot
  have h0 : 1 - 1 < P.optimized.family.problem.cfg.compRows :=
    P.optimized.family.problem.cfg.compRows_pos
  have hlab : (treeS P c Qc).label = lblCS P.optimized (honestQc P c Qc) c 1 := by
    simp only [treeS, c2TreeOfTraces, reconTree, buildT_label]
  have hpub : (treeS P c Qc).label.1.2.2.1 =
      StrategyOfTracesLift.decodePub (FamilyComputeRows.rowEnvAt P c Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩)
        (computeStateOf (StrategyOfTracesLift.decodeSource
          (FamilyComputeRows.rowEnvAt P c Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩))) := by
    rw [hlab]
    show (lblC P.optimized (honestQc P c Qc) c 1).2.2.1 = _
    unfold lblC
    rw [dif_pos h0]
    show (StrategyOfTracesLift.decodePub (FamilyComputeRows.rowEnvAt P c
      (familyQc P c (honestQc P c Qc)) ⟨1 - 1, h0⟩) _) = _
    rw [Batch824.familyQc_honestQc]
    rfl
  rw [hpub]
  exact ⟨hs, hf, he⟩

end Root

end Nock.RedTeam.Batch1111

