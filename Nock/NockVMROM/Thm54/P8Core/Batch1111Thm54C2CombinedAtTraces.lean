/-
  Nock/NockVMROM/Thm54/P8Core/Batch1111Thm54C2CombinedAtTraces.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1111Thm54C2CombinedAtTraces`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1111Thm54C2CombinedAtTraces.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1024Thm54C2BindsAtCoin
import Nock.NockVMROM.Thm54.P8Core.Batch1110Thm54C2CombinedInduction
import Nock.NockVMROM.Thm54.P8Core.ConsumerObligationsEv
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTierAMemAccept
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
/-- The C2 join on the family traces at `c`, rooted at the package claim. -/
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

/-- The event skeleton's compute tree is the C2 join at `c` (`c2ComputeTree_eq`). -/
theorem skeletonEv_computeTree_eq :
    (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)).computeTree = JT := by
  show c2ComputeTree P.optimized (honestQc P c Qc) (honestQm P c Qm) coinFree = _
  rw [c2ComputeTree_eq P.optimized (honestQc P c Qc) (honestQm P c Qm) coinFree c]
  rfl

section Census

variable (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
include hgoodEv

/-- The coin is outside the guarded census collisions and the guarded size windows of the event
skeleton. -/
theorem not_mem_census_window :
    c.1 ∉ collisionFailureEvent (guardedCensusEv K
        (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) P.optimized.Λ) ∧
      c.1 ∉ guardedSizeWindowFailure (K := K)
        (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) P.optimized.Λ := by
  have hp8 := (optimizedFailureEventEv_good_components P _ _ c hgoodEv).1
  unfold evFailureUnion at hp8
  simp only [Finset.mem_union, not_or] at hp8
  exact ⟨hp8.1.1.1.2, hp8.2⟩

omit hgoodEv in
/-- A node of the C2 join is a row of the event skeleton. -/
theorem row_of_inTree {v : NTree ComputeRowSkeleton} (hv : InTree JT v) :
    v.label ∈ computeSkeletonRows (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) := by
  unfold computeSkeletonRows
  rw [skeletonEv_computeTree_eq]
  exact List.mem_map.2 ⟨v, (mem_bfsForest _ _).2 ⟨_, List.mem_singleton_self _, hv⟩, rfl⟩

omit hgoodEv in
theorem pair_mem_combined {v : NTree ComputeRowSkeleton} (hv : InTree JT v)
    {cmp : SemanticTrace.ComparisonUse} (hc : cmp ∈ P8Census.skeletonComparisons (K := K) v.label) :
    cmp.pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K
      (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) := by
  unfold EdgeComparisonCensus.combinedSkeletonPairs
  apply List.mem_append_left
  unfold BoundSemanticTrace.skeletonPairs
  apply List.mem_append_right
  refine List.mem_map.2 ⟨cmp, ?_, rfl⟩
  unfold P8Census.skeletonComparisonCensus
  rw [List.mem_flatMap]
  exact ⟨v.label, row_of_inTree P c Qc Qm hv, hc⟩

/-- **`CensusOK` at every reached node.** -/
theorem censusOK_of_ev {v : NTree ComputeRowSkeleton} (hv : InTree JT v) :
    CensusOK (nprSeed c.1) P.optimized.Λ v.label := by
  intro cmp hc hl hr
  have hcol := (not_mem_census_window P c Qc Qm hgoodEv).1
  by_contra hsep
  apply hcol
  unfold collisionFailureEvent guardedCensusEv
  rw [mem_liftSeed_iff]
  show nprSeed c.1 ∈ PreSeedCensus.pairBadSeeds _ _
  rw [PreSeedCensus.mem_pairBadSeeds_iff]
  exact ⟨cmp.pair, pair_mem_combined P c Qc Qm hv hc, hl, hr, hsep⟩

/-- **`WindowOK` at every reached node.** -/
theorem windowOK_of_ev (hz : nprSeed c.1 ≠ 0) {v : NTree ComputeRowSkeleton} (hv : InTree JT v) :
    WindowOK (nprSeed c.1) P.optimized.Λ v.label := by
  intro n hn hΛ
  have hw := (not_mem_census_window P c Qc Qm hgoodEv).2
  refine window_of_not_mem_guardedSizeWindowFailure _ _ c.1 hz hw n ?_ hΛ
  unfold SizeWindowCounting.skeletonSizeWindowNouns
  rw [List.mem_flatMap]
  exact ⟨v.label, row_of_inTree P c Qc Qm hv, hn⟩

end Census

section Rows

theorem hsatC_at (hacc : DeployedAcceptanceAt P c Qc Qm) :
    Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c)
      (familyQc P c (honestQc P c Qc)) := by
  rw [Batch824.familyQc_honestQc]; exact hacc.compute_satisfies

theorem hsatM_at (hacc : DeployedAcceptanceAt P c Qc Qm) :
    Framework.RAP.SatisfiesWithPreprocessing (P.memoryChipAt c)
      (WrapMemoryConjuncts.familyQm P c (honestQm P c Qm)) := by
  rw [Batch824.familyQm_honestQm]; exact hacc.memory_satisfies

theorem hacc_at (hacc : DeployedAcceptanceAt P c Qc Qm) :
    DeployedAcceptanceAt P c (familyQc P c (honestQc P c Qc))
      (WrapMemoryConjuncts.familyQm P c (honestQm P c Qm)) := by
  rw [Batch824.familyQc_honestQc, Batch824.familyQm_honestQm]; exact hacc

theorem fcomp_of_inTree
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    ∀ v, InTree (StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc)
        (honestQm P c Qm) c h).computeTree v →
      Fcomp (K := K) v.label (fun i => v.childLabel i) ∧ v.children.length ≤ 3 := by
  have htopo := Batch500.computeTopology_of_deployed_of_good P c (honestQc P c Qc) (honestQm P c Qm)
    (hsatC_at P c Qc Qm hacc) (hsatM_at P c Qc Qm hacc)
    (FamilyIOChain.nprSeed_ne_of_good_at P c Qc Qm hgood)
    (Batch824.memStateTagChar_of_package P) hax hbasis hwidth (hacc_at P c Qc Qm hacc) hgood
  unfold ComputeExactTopology at htopo
  have hrvt := htopo.1
  have har := htopo.2
  intro v hv
  have hv' : InTree (ExecOfTraces.execOfTraces P (honestQc P c Qc) (honestQm P c Qm) c
      (Batch489.tracesWalkHyps_of_deployed P c (honestQc P c Qc) (honestQm P c Qm)
        (hsatC_at P c Qc Qm hacc) (hsatM_at P c Qc Qm hacc)
        (Batch824.memStateTagChar_of_package P) hax hbasis hwidth (hacc_at P c Qc Qm hacc)
        hgood)).computeTree v := hv
  exact ⟨((RVT_iff_forall_InTree (Fcomp (K := K)) _).mp hrvt v hv').1, har v hv'⟩

/-- Every node of the S-carrying tree projects to a node of the exec tree. -/
theorem inTree_exec_of_inTree
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {u : NTree ((State × DTcomp K) × ℕ)} (hu : InTree (treeS P c Qc) u) :
    InTree (StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc)
        (honestQm P c Qm) c h).computeTree (mapNTree Prod.fst u) := by
  rw [← c2TreeOfTraces_fst P.optimized (honestQc P c Qc) (honestQm P c Qm) c h]
  exact TraceGen.mapNTree_inTree Prod.fst hu

/-- Every node of the S-carrying tree is a committed row label `lblCS … i`. -/
theorem label_of_inTree_S
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {u : NTree ((State × DTcomp K) × ℕ)} (hu : InTree (treeS P c Qc) u) :
    ∃ i, u.label = lblCS P.optimized (honestQc P c Qc) c i := by
  have hmem : u ∈ bfsForest [treeS P c Qc] := (mem_bfsForest _ _).2 ⟨_, List.mem_singleton_self _, hu⟩
  change u ∈ bfsForest [reconTree (foC P.optimized (honestQc P c Qc) c)
    (lblCS P.optimized (honestQc P c Qc) c) P.optimized.family.problem.cfg.compRows] at hmem
  rw [bfsForest_reconTree _ _ _ h.sfCompute h.validCompute] at hmem
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hmem
  exact ⟨i, buildT_label _ _ _ _⟩

/-- The seed of every committed compute label is `nprSeed c.1`. -/
theorem lblCS_z (i : ℕ) : (lblCS P.optimized (honestQc P c Qc) c i).1.2.1.z = nprSeed c.1 := by
  show (lblC P.optimized (honestQc P c Qc) c i).2.1.z = nprSeed c.1
  rw [lblC_inputs]
  show (FamilyComputeRows.rowEnvAt P c (familyQc P c (honestQc P c Qc))
    ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).toSourceEnv.chal 1 = nprSeed c.1
  have := rowEnvAt_chal P c (familyQc P c (honestQc P c Qc))
    ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩ ⟨1, by decide⟩
  simp only at this
  rw [this]
  rfl

/-- **The row facts, except the certificate axes, at every node of the S-carrying tree.** -/
theorem rowFacts_core
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
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
  obtain ⟨hF, hlen⟩ := fcomp_of_inTree P c Qc Qm hacc hgood hax hbasis hwidth h _
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
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hacc hgood hax hbasis hwidth

/-- **`hsRoot` (and the formula / result twins)**: the root row of the S-carrying tree binds the
package claim's subject, formula and result — `Batch465.deployed_root_label_eq_claim_of_good` with
`hα` from `Batch490.not_mem_alphaRoot_of_good` (priced walk-root + tiling), bridged to `treeS`'s
root label (row `1` of the inverse BFS is `lblCAt 0`, whose `Pub` is `decodePub` of the first row
at any state). -/
theorem root_binds :
    bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.subject (treeS P c Qc).label.1.2.2.1.s ∧
      bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.formula (treeS P c Qc).label.1.2.2.1.f ∧
      bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.result (treeS P c Qc).label.1.2.2.1.e := by
  have hsatC := hsatC_at P c Qc Qm hacc
  have hα := Batch490.not_mem_alphaRoot_of_good P c (honestQc P c Qc) (honestQm P c Qm) hsatC
    hax hbasis hwidth hgood
  have hroot := Batch465.deployed_root_label_eq_claim_of_good P c (honestQc P c Qc) hsatC hax hbasis
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
