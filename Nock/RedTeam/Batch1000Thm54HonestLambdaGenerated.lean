/-
  Nock/RedTeam/Batch1000Thm54HonestLambdaGenerated.lean

  No `hgood`, no event premise.

  Here:

  * `hsvc` (every service axis of the served trace is below `ringChar K`) is a THEOREM at the
    generated carrier `genBuildableOfProgram …`: its served roots are `genRoots`, whose services
    match the requests of a generated compute node (`genRoots_spec`, `ServiceMatches`:
    `s.axis = r.axis`), and the compiler's `hfirst` bounds every such request axis
    (`genBuildableOfProgram_serviceAxes_lt`);
  * `hC` (`CprimeCoherent`) is the carrier's `genExactExecution_cprimeCoherent`
    (`genBuildableOfProgram_cprimeCoherent`);
  * `hax : FormRAxisBound` and `hwidth : FormRWidth F` stay the two premises they are everywhere
    else (`HonestFill`'s `hax` / `hwidth`; at `nockCompiles` they are
    `genComputeRows_rowsFormRAxisBound` and `FormRWidth_of_hp64`).

  `honest_lam_generated` is component 11 at the generated package.  `honest_lam_of_fill` is the
  `HonestFill` form, and `hgood_zero_built_lam` is `Batch963.hgood_zero_built` with its `hlam`
  premise DISCHARGED (replaced by `hsvc`): component 11 leaves the open list.
-/
import Nock.RedTeam.Batch999Thm54HonestPathValidity
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1000

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## A. The two carrier obligations at the generated carrier -/

section Generated

variable {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)

/-- The generated carrier. -/
abbrev Egen : BuildableNockExecution F K :=
  genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
    Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
    haxis hbad hout hKszChar hprogCap hmemCap hfirst

/-- **Every service axis of the generated served trace is below `ringChar K`.** -/
theorem genBuildableOfProgram_serviceAxes_lt :
    ∀ i, ∀ s ∈ ((Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).memoryTrace.roots i).services, s.axis < ringChar K := by
  intro i s hs
  obtain ⟨n, hn, hshape⟩ := genRoots_spec (F := F) z α a b c chal
    (congrArg ComputeTable.Inputs.z hinp) (congrArg ComputeTable.Inputs.α hinp)
    Ksz orbit horb (memInputs z) h (horb_of_window hB hwin) hmempos hcomp hmem i
  have key : ∀ x ∈ (genRoots (F := F) z α a b c chal (congrArg ComputeTable.Inputs.z hinp)
      (congrArg ComputeTable.Inputs.α hinp) Ksz orbit horb (memInputs z) h
      (horb_of_window hB hwin) hmempos hcomp hmem i).services, x.axis < ringChar K := by
    rcases hshape with ⟨r, hr, -, s0, hm, hsv⟩ | ⟨r1, hr1, r2, hr2, -, -, -, s1, s2, hm1, hm2, hsv⟩
    · rw [hsv]
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      rw [hm.2.2.1]; exact hfirst n hn r hr
    · rw [hsv]
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [hm1.2.2.1]; exact hfirst n hn r1 hr1
      · rw [hm2.2.2.1]; exact hfirst n hn r2 hr2
  exact key s hs

/-- **The generated executed rows are `C'`-coherent** (`genExactExecution_cprimeCoherent`). -/
theorem genBuildableOfProgram_cprimeCoherent :
    (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
      hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
      hfirst).exec.CprimeCoherent :=
  genExactExecution_cprimeCoherent (F := F) z α chal (congrArg ComputeTable.Inputs.z hinp)
    Ksz orbit horb a b c h hmempos hcomp hmem (horb_of_window hB hwin)

/-- **Component 11 at the generated package.**  Premises beyond the package's own arguments:
`hax` and `hwidth` only. -/
theorem honest_lam_generated
    (I : BuildableChips.Inputs (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins
      hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
      hmemCap hfirst))
    (R : CommitmentResidual (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins
      hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
      hmemCap hfirst))
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h
      hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
      hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (Egen z α hz htwo a b c chal hinp hmi Ksz orbit
      horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
      hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
      hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
      hfirst).cfg.compRows → (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins
      hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
      hmemCap hfirst).cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
      hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
      hfirst).cfg.memRows → (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins
      hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
      hmemCap hfirst).cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
      hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
      hfirst).cfg.compRows < ringChar K ∧ (Egen z α hz htwo a b c chal hinp hmi Ksz orbit horb h
      hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
      hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackage _ I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (buildFullPackage _ I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : FormRWidth F) :
    (buildFullPackage _ I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple ∉
      (buildFullPackage _ I R hzero hprl hmore hord hordM hrows hgenF hF).decodedLambdaEventOf
        (MultiRootOptimizedAcceptance.canonicalComputeTrace
          (buildFullPackage _ I R hzero hprl hmore hord hordM hrows hgenF hF))
        (MultiRootOptimizedAcceptance.canonicalMemoryTrace
          (buildFullPackage _ I R hzero hprl hmore hord hordM hrows hgenF hF)) :=
  Batch999.honest_lam _ I R hzero hprl hmore hord hordM hrows hgenF hF hax hwidth
    (genBuildableOfProgram_cprimeCoherent z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed
      hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar
      hprogCap hmemCap hfirst)
    (genBuildableOfProgram_serviceAxes_lt z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed
      hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar
      hprogCap hmemCap hfirst)

end Generated

/-! ## B. The `HonestFill` form and the open list without component 11 -/

/-- **Component 11 from `HonestFill`** at every built package (`hax`, `hwidth`, `hC` are its
fields) and the service-axis bound. -/
theorem honest_lam_of_fill (E : BuildableNockExecution F K) (I : BuildableChips.Inputs E)
    (R : CommitmentResidual E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (H : HonestFill (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF))
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K) :
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple ∉
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).decodedLambdaEventOf
        (MultiRootOptimizedAcceptance.canonicalComputeTrace
          (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF))
        (MultiRootOptimizedAcceptance.canonicalMemoryTrace
          (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF)) :=
  Batch999.honest_lam E I R hzero hprl hmore hord hordM hrows hgenF hF H.hax H.hwidth H.hC hsvc

/-- **T1 against the honest template.** -/
theorem decoded_eq_honestTemplateAxisTree (E : BuildableNockExecution F K) (D : Data E)
    (I : BuildableChips.Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hC : E.exec.CprimeCoherent) (i : Fin E.cfg.kMem) :
    DecodedLambdaEvent.decodedMTreeOfEnvs (Batch999.envsK E I R hzero hprl hmore hord hordM hrows hgenF hF)
        (Batch999.envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) E.cfg.kMem ((i : ℕ) + 1) =
      Batch995.rn (Batch998.gExp E)
        (exactAxisTree E.cfg
          ((D.executionTemplate E.cfg.challenges.z).specializeA E.cfg.challenges.α
            E.cfg.challenges.lam) i) := by
  rw [D.honest_execA]
  exact Batch999.decoded_eq_axisTree E I R hzero hprl hmore hord hordM hrows hgenF hF hC i

/-- **`Batch963.hgood_zero_built` with component 11 discharged**: the premise `hlam` is gone,
replaced by the generator obligation `hsvc` (a theorem at the generated carrier,
`genBuildableOfProgram_serviceAxes_lt`).  The open list is components 4 and 12, `hzc` and
`HonestFill`. -/
theorem hgood_zero_built_lam (E : BuildableNockExecution F K) (D : Data E) (I : Inputs E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (H : HonestFill (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord
      hordM hrows))
    (hgoodSeed : E.cfg.challenges.z ∉ D.census.census.badSeeds (K := K))
    (hwin : E.cfg.challenges.z ∉ sizeWindowFailureSeeds (K := K) D.skeleton)
    (hα0 : E.cfg.challenges.α ≠ 0)
    (hαord : E.exec.derivedRequestIO.length ≤ orderOf E.cfg.challenges.α)
    (hγ8 : (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.sampled.interPole +
      (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.sampled.sampled.coins.gamma ^ 8 ≠ 0)
    (h0 : (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.sampled.interPole ≠ 0)
    (hzc : ∀ i : Fin (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord
        hordM hrows).optimized.family.problem.cfg.memRows,
      ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.family.problem.exec.memoryPubAt i).cprime = 1)
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (hpair : (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM hrows hgenF hF).q
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).optimized.family.problem.cfg.kMem
        ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).optimized.family.problem.cfg.memRows ⊔
          (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
            hrows).optimized.Λ)
        ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).memoryBaseEnv
          (canonicalMemoryTrace (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl
            hmore hord hordM hrows hgenF hF)))
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).optimized.family.problem.cfg.memRows_pos
        (PreSeedCensus.requestTargets (buildFullPackage E I (commitmentResidualOfZero D) hzero
          hprl hmore hord hordM hrows hgenF hF).strategy.skeleton)) :
    (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).honestTuple ∉
      (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimizedFailureEvent
        (honestQc _ (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord
          hordM hrows).honestTuple (QcH _))
        (honestQm _ (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord
          hordM hrows).honestTuple (QmH _)) :=
  Batch963.hgood_zero_built E D I hzero hprl hmore hord hordM hrows hgenF hF H hgoodSeed hwin hα0 hαord
    hγ8 h0 hzc
    (honest_lam_of_fill E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM hrows hgenF hF H hsvc)
    hpair

end

end Nock.RedTeam.Batch1000

#print axioms Nock.RedTeam.Batch1000.genBuildableOfProgram_serviceAxes_lt
#print axioms Nock.RedTeam.Batch1000.genBuildableOfProgram_cprimeCoherent
#print axioms Nock.RedTeam.Batch1000.honest_lam_generated
#print axioms Nock.RedTeam.Batch1000.honest_lam_of_fill
#print axioms Nock.RedTeam.Batch1000.decoded_eq_honestTemplateAxisTree
#print axioms Nock.RedTeam.Batch1000.hgood_zero_built_lam
