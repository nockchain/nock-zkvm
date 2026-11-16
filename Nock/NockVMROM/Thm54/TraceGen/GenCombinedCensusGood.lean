/-
  Nock/NockVMROM/Thm54/TraceGen/GenCombinedCensusGood.lean

  Three of the five `FailureUnion` summands, discharged on the generated
  path from premises `nockCompiles_of_accepted_accepting` already carries.

  SCOPE.  `FailureUnion T C` (`ProductionP8Containment.lean:539`) is a
  five-way union.  This module owns exactly three of them:

  1. `zeroSeedFailureEvent` -- from `hz : z ≠ 0`.
  2. `collisionFailureEvent C.census` at the **combined** census -- from
     the p8-census premise `hbad`, via step 1 below.
  5. `SizeWindowFailure T.skeleton` -- from
     `hout : z ∉ sizeWindowFailureSeeds …`.

  Summands 3 (`specializedTopologyFailureEvent`) and 4
  (`guardedAxisFailureEvent`) are **out of scope here** and are owned by
  another lane; every theorem below that mentions the full
  `FailureUnion` takes them as explicit hypotheses and proves nothing
  about them.

  ## The `bfsAssign` scope of the edge sub-census

  `GenEdgeSelfCensus.lean` proves the edge summand of
  `combinedSkeletonPairs` carries no bad seed on the generated path, but
  states it at `genSemanticSkeleton (airReorder t) mf`.  Every live
  configuration commits `genSemanticSkeleton (bfsAssign (airReorder t)) mf`
  (`genSkeletonP8Census`, `GenSemanticDataParts.lean:132`), so the
  argument has to survive the inverse-BFS restamping.  It does, and
  cheaply: `bfsAssign` is `buildTF`/`reconForest` over the *same*
  fan-out column and `childrenMatchSf`
  reads only `.skel`, which `bfsLabelAt` copies -- exactly the content of
  `childrenMatchSf_bfsAssign` (`GenAirOrderBinding.lean:141`), which
  already existed.  So proving the
  skel-projected trees equal is not needed: the per-node predicate
  transports directly, and no new fact about `buildTF` is required.

  The objects compared are the parent's `subformula_i` triples
  `(child_i_subject, child_i_formula, sf_evaluation_i)` of
  the paper the census that separates them is the collision
  census whose per-occurrence error is `lem:ion_univariate_sec`.

  ## The seed-side summands

  All three are `liftSeed` events (`JointCoins.lean:98`), so each reduces
  to a bare-seed statement at `nprSeed ω`.  Nothing here is about
  acceptance; these are set-membership projections feeding
  `accepted_outside_failureUnion`'s `hout`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenEdgeSelfCensus
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderBinding
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.EdgeComparisonCensus
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment

variable {K : Type} [Field K]

/-! ## Edge self-pairing survives `bfsAssign`

`GenEdgeSelfCensus.edgePairs_self_of_airLinked` consumes `AirLinked`, an
everywhere-recursive predicate.  The `bfsAssign` transport
(`childrenMatchSf_bfsAssign`) delivers the *BFS-pointwise* form instead, so the
first job is to restate the edge conclusion against that weaker hypothesis. -/

/-- Every edge comparison of `t`'s skeleton is a self-pair as soon as every BFS node of
`t` matches its children's `sf` slots.  The BFS-pointwise form of
`edgePairs_self_of_airLinked`. -/
theorem edgePairs_self_of_bfs_childrenMatchSf
    {t : NTree (GenComputeRow K)}
    (h : ∀ n ∈ bfsForest [t], childrenMatchSf n)
    {pair : Noun × Noun}
    (hp : pair ∈ edgePairs (mapNTree (fun g : GenComputeRow K => g.skel) t)) :
    pair.1 = pair.2 := by
  rw [edgePairs, List.mem_flatMap] at hp
  obtain ⟨node, hnode, hpn⟩ := hp
  rw [show [mapNTree (fun g : GenComputeRow K => g.skel) t] =
        [t].map (mapNTree (fun g : GenComputeRow K => g.skel)) from rfl,
    bfsForest_mapNTree, List.mem_map] at hnode
  obtain ⟨s, hs, hseq⟩ := hnode
  subst hseq
  exact rowEdgePairs_self_of_childrenMatchSf (h s hs) hpn

/-- **The scope fix.**  `bfsAssign` restamps but does not reshape, and `childrenMatchSf`
reads only `.skel`, so the AIR-order child matching of an accepted program's tree survives
the inverse-BFS reconstruction at every BFS node -/
theorem bfs_childrenMatchSf_bfsAssign_of_gen
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (hgen : genComputeSkeleton (K := K) fuel subject formula = .ok p) :
    ∀ n ∈ bfsForest [bfsAssign (airReorder p.1)], childrenMatchSf n :=
  fun _ hn =>
    childrenMatchSf_bfsAssign
      (fun _ hm =>
        childrenMatchSf_bfs_of_AirLinked (airLinked_airReorder_of_gen hgen) hm)
      hn

/-- `genSemanticSkeleton`'s compute tree is the `.skel` projection of its argument — a field
of the structure literal (`Gen.lean:2021`), stated so downstream rewriting need not `change`. -/
theorem genSemanticSkeleton_computeTree_eq (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genSemanticSkeleton t mf).computeTree =
      mapNTree (fun g : GenComputeRow K => g.skel) t :=
  rfl

/-- Every edge comparison of the skeleton live configurations actually commit is a
self-pair. -/
theorem edgePairs_self_of_gen_bfsAssign
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (hgen : genComputeSkeleton (K := K) fuel subject formula = .ok p)
    (mf : List (NTree (GenMemoryRow K)))
    {pair : Noun × Noun}
    (hp : pair ∈ edgePairs
      (genSemanticSkeleton (bfsAssign (airReorder p.1)) mf).computeTree) :
    pair.1 = pair.2 := by
  rw [genSemanticSkeleton_computeTree_eq] at hp
  exact edgePairs_self_of_bfs_childrenMatchSf (bfs_childrenMatchSf_bfsAssign_of_gen hgen) hp

section Finite
variable [Fintype K] [DecidableEq K]

/-- On the generated path, at the `bfsAssign` spelling, the combined census needs no premise
beyond p8. -/
theorem combined_good_of_p8_good_gen_bfsAssign {Λ : ℕ}
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (hgen : genComputeSkeleton (K := K) fuel subject formula = .ok p)
    (mf : List (NTree (GenMemoryRow K)))
    (C : CombinedSkeletonCensus K
      (genSemanticSkeleton (bfsAssign (airReorder p.1)) mf) Λ)
    (z : K) (hgood : z ∉ C.p8.census.badSeeds (K := K)) :
    z ∉ C.census.badSeeds (K := K) :=
  combined_good_of_p8_good C
    (fun _ hedge => edgePairs_self_of_gen_bfsAssign hgen mf hedge) z hgood

/-- **Step 1's deliverable.**  The p8-census premise `nockCompiles_of_accepted_accepting`
carries (`GenAcceptingCoin.lean:156`) discharges the *combined* census at the very census
object `genComputeSkeleton_census_gen` produces. -/
theorem combined_good_of_p8_good_bfsAssign {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K))) (z : K)
    (hgood : z ∉ (genSkeletonP8Census hΛ h hconf mf).census.badSeeds (K := K)) :
    z ∉ (genComputeSkeleton_census_gen hΛ h hconf mf).census.badSeeds (K := K) :=
  combined_good_of_p8_good_gen_bfsAssign (p := (t, result)) h mf
    (genComputeSkeleton_census_gen hΛ h hconf mf) z hgood

end Finite

/-! ## Summands 1, 2 and 5

Each is a `liftSeed` of a bare-seed condition, so each is a one-line projection once the
coin's seed is named.  Summands 3 and 4 are not touched. -/

section Failure
variable [Fintype K] [DecidableEq K]

/-- Summand 1, from `hz : z ≠ 0`. -/
theorem not_mem_zeroSeedFailureEvent {z : K} (hz : z ≠ 0)
    {ω : JointCoins K} (hseed : nprSeed ω = z) :
    ω ∉ (zeroSeedFailureEvent : Finset (JointCoins K)) := by
  intro hmem
  rw [mem_zeroSeedFailureEvent_iff, hseed] at hmem
  exact hz hmem

/-- Summand 2, from goodness of the seed at whatever census is committed. -/
theorem not_mem_collisionFailureEvent {Λ : ℕ} (C : ComparisonCensus Λ)
    {z : K} {ω : JointCoins K} (hseed : nprSeed ω = z)
    (hgood : z ∉ C.badSeeds (K := K)) :
    ω ∉ collisionFailureEvent (K := K) C := by
  intro hmem
  rw [mem_collisionFailureEvent_iff, hseed] at hmem
  exact hgood ((ComparisonCensus.mem_badSeeds_iff C z).2 hmem)

/-- Summand 5, from `hout : z ∉ sizeWindowFailureSeeds …`. -/
theorem not_mem_sizeWindowFailure {S : SemanticSkeleton}
    {z : K} {ω : JointCoins K} (hseed : nprSeed ω = z)
    (hout : z ∉ sizeWindowFailureSeeds (K := K) S) :
    ω ∉ SizeWindowFailure (K := K) S := by
  intro hmem
  rw [SizeWindowFailure, mem_liftSeed_iff, hseed] at hmem
  exact hout hmem

/-- **The three summands this module owns, packaged.**  `hz`, combined-census goodness and
the size-window seed condition put `ω` outside summands 1, 2 and 5 simultaneously. -/
theorem not_mem_seedFailureTriple {Λ : ℕ} {S : SemanticSkeleton}
    (C : CombinedSkeletonCensus K S Λ) {z : K} (hz : z ≠ 0)
    {ω : JointCoins K} (hseed : nprSeed ω = z)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hout : z ∉ sizeWindowFailureSeeds (K := K) S) :
    ω ∉ ((zeroSeedFailureEvent ∪ collisionFailureEvent (K := K) C.census) ∪
      SizeWindowFailure (K := K) S) := by
  intro hmem
  rcases Finset.mem_union.1 hmem with hmem | hmem
  · rcases Finset.mem_union.1 hmem with hmem | hmem
    · exact not_mem_zeroSeedFailureEvent hz hseed hmem
    · exact not_mem_collisionFailureEvent C.census hseed hgood hmem
  · exact not_mem_sizeWindowFailure hseed hout hmem

/-- **Steps 1 and 2 composed, on the generated path.**  Premises are exactly three that
`nockCompiles_of_accepted_accepting` already carries — `hz`, `hbad` at the *p8* census, and
`hout` — and the conclusion is the three-summand sub-union of `FailureUnion` at the
*combined* census. -/
theorem not_mem_seedFailureTriple_of_gen {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K)))
    {z : K} (hz : z ≠ 0) {lmb : K} {ω : JointCoins K} (hseed : nprSeed ω = z)
    (hbad : z ∉ (genSkeletonP8Census hΛ h hconf mf).census.badSeeds (K := K))
    (hout : z ∉ sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf)) :
    ω ∉ ((zeroSeedFailureEvent ∪
        collisionFailureEvent (K := K)
          (genComputeSkeleton_census_gen hΛ h hconf mf).census) ∪
      SizeWindowFailure (K := K)
        (genSemanticSkeleton (bfsAssign (airReorder t)) mf)) :=
  not_mem_seedFailureTriple (genComputeSkeleton_census_gen hΛ h hconf mf) hz hseed
    (combined_good_of_p8_good_bfsAssign hΛ h hconf mf z hbad) hout

end Failure

/-! ## Assembling `FailureUnion`

Summands 3 and 4 stay hypotheses: they are another lane's, and nothing below asserts
anything about them. -/

section Union
variable {F : Type} [Field F] [Algebra F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- `FailureUnion`'s five summands, split.  Three arguments are what this module proves; the
topology and axis arguments are carried, not proved. -/
theorem not_mem_failureUnion_of_summands
    (T : ProductionStrategy F K) {Λ : ℕ}
    (C : CombinedSkeletonCensus K T.skeleton Λ) {lmb : K} {ω : JointCoins K}
    (h1 : ω ∉ (zeroSeedFailureEvent : Finset (JointCoins K)))
    (h2 : ω ∉ collisionFailureEvent (K := K) C.census)
    (h3 : ω ∉ specializedTopologyFailureEvent T.verifier.raw lmb)
    (h4 : ω ∉ guardedAxisFailureEvent T lmb)
    (h5 : ω ∉ SizeWindowFailure (K := K) T.skeleton) :
    ω ∉ ProductionP8Containment.FailureUnion T C lmb := by
  intro hmem
  unfold ProductionP8Containment.FailureUnion at hmem
  simp only [Finset.mem_union] at hmem
  rcases hmem with (((h | h) | h) | h) | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h
  · exact h5 h

/-- `accepted_outside_failureUnion`'s `hout`, with summands 1, 2 and 5 discharged from the
seed conditions and only the topology and axis summands left to the caller. -/
theorem not_mem_failureUnion_of_seed
    (T : ProductionStrategy F K) {Λ : ℕ}
    (C : CombinedSkeletonCensus K T.skeleton Λ)
    {z : K} (hz : z ≠ 0) {lmb : K} {ω : JointCoins K} (hseed : nprSeed ω = z)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hout : z ∉ sizeWindowFailureSeeds (K := K) T.skeleton)
    (h3 : ω ∉ specializedTopologyFailureEvent T.verifier.raw lmb)
    (h4 : ω ∉ guardedAxisFailureEvent T lmb) :
    ω ∉ ProductionP8Containment.FailureUnion T C lmb :=
  not_mem_failureUnion_of_summands T C
    (not_mem_zeroSeedFailureEvent hz hseed)
    (not_mem_collisionFailureEvent C.census hseed hgood)
    h3 h4
    (not_mem_sizeWindowFailure hseed hout)

end Union

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.edgePairs_self_of_bfs_childrenMatchSf
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfs_childrenMatchSf_bfsAssign_of_gen
#print axioms Nock.NockVMROM.Thm54.TraceGen.edgePairs_self_of_gen_bfsAssign
#print axioms Nock.NockVMROM.Thm54.TraceGen.combined_good_of_p8_good_bfsAssign
#print axioms Nock.NockVMROM.Thm54.TraceGen.not_mem_seedFailureTriple
#print axioms Nock.NockVMROM.Thm54.TraceGen.not_mem_seedFailureTriple_of_gen
#print axioms Nock.NockVMROM.Thm54.TraceGen.not_mem_failureUnion_of_summands
#print axioms Nock.NockVMROM.Thm54.TraceGen.not_mem_failureUnion_of_seed

