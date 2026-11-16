/-
  Nock/RedTeam/Batch956Thm54HonestP8Union.lean

  The generated package of the `nockCompiles` chain (`nockCompiles_p61` and successors,
  `GenNockCompilesBounded.lean`) is `buildFullPackage E I (commitmentResidualOfZero D)..` with
  `E = genBuildableOfProgram..`, `D = genDataOfProgram..`: the ZERO later-round arrays, not the
  honest arrays of `GenericHonestPackage.packageOf`.  `GenGenuineTarget.honestCoin_not_mem_failureUnion`
  is stated for `packageOf` only; this file restates it at `commitmentResidualOfZero`, for every
  buildable carrier `E` and every `D : Data E`:

  * summands 1, 2, 5 (`zeroSeed`, census collision, size window) read only `nprSeed`, which at the
    honest tuple is the carrier's committed seed `E.cfg.challenges.z`; they are the seed hypotheses
    `hgood` / `hwin`, i.e. the generator's good-seed choice (`hbad` / `hout`; at the generated `D`,
    `GenCombinedCensusGood.combined_good_of_p8_good_bfsAssign` turns `hbad` into `hgood`);
  * summand 3 (topology) is EMPTY at the honest `(z, α)` for every `γ`: the zero arrays do not
    enter `topologyBadGammas`, which reads only the specialized execution, and that is `E.exec`
    (`Data.honest_exec`, `E.traversal`);
  * summand 4 (guarded axis) is empty at the honest `α`: served axis validity
    (`GenGenuineTarget.honestAlpha_not_mem_verifierGuardedRootUnion`).

  Status: **proved-by-choice** for summands 1, 2, 5 (the honest tuple's seed is the generator's
  chosen good seed `romSeed`, an existence-by-counting choice, `GenGoodSeedExists`; it is not an
  arbitrary seed), **proved** (honest-trace identity, every coin) for summands 3, 4.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenuineTarget
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch956

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
variable {E : BuildableNockExecution F K}

/-- The zero-array raw strategy's base family at the honest sample is bound (topology). -/
theorem zeroBase_topologyBinding (D : Data E) (hz : E.cfg.challenges.z ≠ 0) :
    RawTopologyBindingResidual
      ((zeroAlphaM D.timestampStrategy E.cfg.challenges.z hz
        E.cfg.challenges.α E.cfg.challenges.lam).familyData.base) := by
  have hexec :
      ((D.executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α
        E.cfg.challenges.lam) = E.exec :=
    D.honest_exec
  have hc :
      ((zeroAlphaM D.timestampStrategy E.cfg.challenges.z hz
        E.cfg.challenges.α E.cfg.challenges.lam).familyData.base).exec.ComputeRowsAccepted := by
    show ((D.executionTemplate E.cfg.challenges.z).specialize
      E.cfg.challenges.α E.cfg.challenges.lam).ComputeRowsAccepted
    rw [hexec]
    exact BuildablePackage.computeRowsAccepted E
  have hm :
      ((zeroAlphaM D.timestampStrategy E.cfg.challenges.z hz
        E.cfg.challenges.α E.cfg.challenges.lam).familyData.base).exec.MemoryRowsAccepted := by
    show ((D.executionTemplate E.cfg.challenges.z).specialize
      E.cfg.challenges.α E.cfg.challenges.lam).MemoryRowsAccepted
    rw [hexec]
    exact BuildablePackage.memoryRowsAccepted E
  refine (exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted _ hc hm).1 ?_
  constructor
  · show ComputeExactTopology
      ((D.executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam)
    rw [hexec]
    exact E.traversal.1
  · show MemoryExactTopology
      ((D.executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam)
    rw [hexec]
    exact E.traversal.2

variable {hOrb : ℕ}

theorem honestTuple_not_mem_failureUnion_zero
    (D : Data E) (I : Inputs E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hgood : E.cfg.challenges.z ∉ D.census.census.badSeeds (K := K))
    (hwin : E.cfg.challenges.z ∉ sizeWindowFailureSeeds (K := K) D.skeleton) :
    (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).honestTuple.1 ∉
      ProductionP8Containment.FailureUnion
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).strategy
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).optimized.census
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).objects.cfg.challenges.lam := by
  refine not_mem_failureUnion_of_seed _ _ D.honestSeed_ne (z := E.cfg.challenges.z) rfl
    hgood hwin ?_ ?_
  · intro hmem
    rw [mem_specializedTopologyFailureEvent_iff] at hmem
    obtain ⟨hz, hbad⟩ := hmem
    have hbad' : _ ∈ topologyBadGammas
        ((zeroAlphaM D.timestampStrategy E.cfg.challenges.z hz
          E.cfg.challenges.α E.cfg.challenges.lam).familyData.base) := hbad
    rw [MultiRootHonestArrays.topologyBadGammas_empty_of_binding _
      (zeroBase_topologyBinding D hz)] at hbad'
    exact absurd hbad' (Finset.notMem_empty _)
  · intro hmem
    rw [mem_guardedAxisFailureEvent_iff] at hmem
    obtain ⟨hz, hmem⟩ := hmem
    have hmem' : E.cfg.challenges.α ∈
        verifierGuardedRootUnion (D.executionTemplate E.cfg.challenges.z)
          E.cfg.challenges.lam := hmem
    exact honestAlpha_not_mem_verifierGuardedRootUnion D hmem'

/-! ## At the generated carrier (`genBuildableOfProgram` / `genDataOfProgram`) -/

section Generated

variable {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}

/-- **The two seed conditions at the generated `Data`, from the generator's choice**
(`hbad` at the p8 census, `hout`; the bridge is `combined_good_of_p8_good_bfsAssign`, as in
`GenGenuineTarget.nockCompiles_of_accepted_genuine`). -/
theorem genData_seed_good :
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.challenges.z ∉
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst).census.census.badSeeds (K := K) ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.challenges.z ∉
        sizeWindowFailureSeeds (K := K)
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
            hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).skeleton := by
  have hzeq : chal.z = z := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.z) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  have hskel : (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).skeleton =
      genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t) :=
    genSkeletonOfNodes_eq z α a b c (memInputs z) t
  refine ⟨?_, ?_⟩
  · show chal.z ∉ _
    rw [hzeq]
    exact not_mem_combinedCensus_badSeeds_congr (Λ := Λ) hskel _
      (genComputeSkeleton_census_gen hΛ h hconf (genMemoryForest z α chal.lam (memInputs z) t))
      (combined_good_of_p8_good_bfsAssign hΛ h hconf
        (genMemoryForest z α chal.lam (memInputs z) t) z hbad)
  · show chal.z ∉ _
    rw [hzeq, hskel]
    exact hout

end Generated

end

end Nock.RedTeam.Batch956

#print axioms Nock.RedTeam.Batch956.zeroBase_topologyBinding
#print axioms Nock.RedTeam.Batch956.honestTuple_not_mem_failureUnion_zero
#print axioms Nock.RedTeam.Batch956.genData_seed_good
