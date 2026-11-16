/-
  Nock/RedTeam/Batch1250Thm54HonestGoodGenerated.lean

  `genPkg` is `Batch1061.genPkg` (the package the `nockCompiles` chain builds after repair (ii):
  `mwa := α`, `msc := 0`); the honest traces are `QcH` / `QmH`.

  * `rootResultEv_eq_empty_of_diag`: diagonal root pair, empty event.
  * Component 4 is closed (`Batch991.component4_generated` inside
    `Batch993.hgood_generated'`), as is `hzc`.  `alphaNe_genPkg` -- `α ≠ 0` (from `hB`, `hwin`).
  * §C (non-vacuity, conditional): `nonvacuous_generated_of_open` -- `bindsAtCoin_C2_combined`,
    `census_window_combined`, `not_mem_FailureUnion_combined` at `genPkg`, its honest tuple and
    `QcH`/`QmH`; `hacc` from `Batch1061.gen_honest_accepted`, `hgood` from §B, `hgoodEv` from §A,
    `hax`/`hwidth` from `Batch993.hgoodFill_generated`, `hbasis` `compilerBasis_formR`, `h` from
    `Batch489.tracesWalkHyps_of_deployed`, `hgen` from the generator's `h` and
    `genDataOfProgram_publicClaim`, `hG`/`bs`/`bf` from the chain's binders, `hΛG` from `hconf`.
-/
import Nock.RedTeam.Batch1061Thm54RepairIIHonestAcceptance
import Nock.RedTeam.Batch1000Thm54HonestLambdaGenerated
import Nock.RedTeam.Batch1173Thm54C2CombinedServedRecords
import Nock.RedTeam.Batch489Thm54FoOfEqFoW
import Nock.RedTeam.Batch940Thm54LiftStrategyReceipts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Nock.RedTeam.Batch1250

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Framework
open Nock.Framework.Thm54
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.RedTeam.Batch1061 (genPkg gen_honest_accepted)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## §A  At any package -/

section AnyPackage

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])

theorem hgoodEv_of_pinned (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hp8 : c.1 ∉ evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ c.2.2.2.lambda)
    (hpairEv : c.1 ∉ reqPairEv P Qc Qm)
    (hroot : c.1 ∉ rootResultEv P Qc Qm)
    (hα : alphaM c.1 ≠ 0) :
    c ∉ optimizedFailureEventEv P Qc Qm := by
  obtain ⟨-, hio, hts, hinter, hwalk, htileC, htileM, hγC, hγM, hαM, hlam, -⟩ :=
    P.optimizedFailureEvent_good_components Qc Qm c hgood
  simp only [optimizedFailureEventEv, Finset.mem_union, not_or]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hio⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hlam⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; exact hp8 ((mem_p8SlotEv_iff P Qc Qm c).1 h)
  · intro h; exact hts ((mem_liftTimestampFailure_iff _ _).1 h)
  · intro h; exact hinter ((mem_liftInterPoleFailure_iff _ _).1 h)
  · intro h; exact hwalk (Finset.mem_product.1 h).1
  · intro h; exact htileC (Finset.mem_product.1 h).1
  · intro h; exact htileM (Finset.mem_product.1 h).1
  · intro h; exact hγC (Finset.mem_product.1 h).1
  · intro h; exact hγM (Finset.mem_product.1 h).1
  · intro h; exact hαM (Finset.mem_product.1 h).1
  · intro h; exact hpairEv (Finset.mem_product.1 h).1
  · intro h; exact hroot (Finset.mem_product.1 h).1
  · intro h; exact hα ((mem_alphaZeroEvent_iff _).1 (Finset.mem_product.1 h).1)

theorem reqPairEv_eq_pinned_of_targets
    (ht : builtRequestTargets P Qc Qm = PreSeedCensus.requestTargets P.strategy.skeleton) :
    reqPairEv P Qc Qm =
      PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
        (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
        P.optimized.family.problem.cfg.memRows_pos
        (PreSeedCensus.requestTargets P.strategy.skeleton) := by
  unfold reqPairEv
  rw [ht]

/-- A diagonal root-result pair makes `rootResultEv` empty. -/
theorem rootResultEv_eq_empty_of_diag
    (hd : (builtSkeletonEv P Qc Qm).publicClaim.result = P.optimized.verifier.raw.claim.result) :
    rootResultEv P Qc Qm = ∅ := by
  unfold rootResultEv
  rw [PreSeedCensus.pairBadSeeds_eq_empty_of_diag]
  · ext ω; simp [liftSeed]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact hd


/-- `evFailureUnion` membership, summand by summand. -/
theorem not_mem_evFailureUnion_of_parts (T : ProductionP8Containment.ProductionStrategy F K)
    (Λ : ℕ) (lmb : K) (ω : JointCoins K) (hz : nprSeed ω ≠ 0)
    (hcen : ω ∉ collisionFailureEvent (guardedCensusEv K T.skeleton Λ))
    (htopo : ω ∉ TemplateRawJointSoundness.specializedTopologyFailureEvent T.verifier.raw lmb)
    (hax : ω ∉ envelopeAxisFailureEvent T lmb)
    (hsw : ω ∉ guardedSizeWindowFailure (K := K) T.skeleton Λ) :
    ω ∉ evFailureUnion T Λ lmb := by
  simp only [evFailureUnion, Finset.mem_union, not_or]
  refine ⟨⟨⟨⟨?_, hcen⟩, htopo⟩, hax⟩, hsw⟩
  intro h
  exact hz ((mem_zeroSeedFailureEvent_iff _).1 h)

theorem hp8Ev_of_skeleton_eq (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hS : builtSkeletonEv P Qc Qm = P.strategy.skeleton)
    (htopo : c.1 ∉ TemplateRawJointSoundness.specializedTopologyFailureEvent
      (builtStrategyEv P Qc Qm).verifier.raw c.2.2.2.lambda)
    (hax : c.1 ∉ envelopeAxisFailureEvent (builtStrategyEv P Qc Qm) c.2.2.2.lambda) :
    c.1 ∉ evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ c.2.2.2.lambda := by
  have h1 := (P.optimizedFailureEvent_good_components Qc Qm c hgood).1
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union, not_or] at h1
  obtain ⟨⟨⟨⟨hz0, hcol⟩, -⟩, -⟩, hsw⟩ := h1
  have hS' : (builtStrategyEv P Qc Qm).skeleton = P.strategy.skeleton := hS
  refine not_mem_evFailureUnion_of_parts _ _ _ _ ?_ ?_ htopo hax ?_
  · intro h; exact hz0 ((mem_zeroSeedFailureEvent_iff _).2 h)
  · rw [hS']
    intro h
    apply hcol
    unfold collisionFailureEvent at h ⊢
    rw [mem_liftSeed_iff] at h ⊢
    have heq : (guardedCensusEv K P.strategy.skeleton P.optimized.Λ).badSeeds (K := K) =
        P.optimized.census.census.badSeeds (K := K) :=
      guardedCensusEv_badSeeds_eq P.optimized.census
    rwa [heq] at h
  · rw [hS']
    intro h
    exact hsw (guardedSizeWindowFailure_subset _ _ h)

theorem hpairEv_of_skeleton_eq (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hS : builtSkeletonEv P Qc Qm = P.strategy.skeleton) :
    c.1 ∉ reqPairEv P Qc Qm := by
  have h12 := (P.optimizedFailureEvent_good_components Qc Qm c hgood).2.2.2.2.2.2.2.2.2.2.2
  rw [reqPairEv_eq_pinned_of_targets P Qc Qm (by unfold builtRequestTargets; rw [hS])]
  exact h12

/-- **`rootResultEv` is empty once the built skeleton is the compiler's** (`publicClaim_eq`). -/
theorem hrootEv_of_skeleton_eq (c : OptimizedProductionChallengeTuple K F)
    (hS : builtSkeletonEv P Qc Qm = P.strategy.skeleton)
    (hcl : P.strategy.verifier.raw.claim = P.optimized.verifier.raw.claim) :
    c.1 ∉ rootResultEv P Qc Qm := by
  rw [rootResultEv_eq_empty_of_diag P Qc Qm (by rw [hS, P.strategy.publicClaim_eq, hcl])]
  simp

end AnyPackage

/-! ## §B  At the generated package -/

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





set_option quotPrecheck false in
set_option hygiene false in
local notation "GP" => genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
  hinterCard hhon hprl hmore hord hordM hrows

set_option quotPrecheck false in
set_option hygiene false in
local notation "EG" => genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
  hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
  haxis hbad hout hKszChar hprogCap hmemCap hfirst

set_option quotPrecheck false in
set_option hygiene false in
local notation "IG" => inputsOfCarrier (EG) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n
  hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon

/-- **`hgood` at the generated package with ONLY component 12 (`hpair`) open.**  Components 1-10
from `Batch993.hgood_generated'` (4 and `hzc` by `Batch991.component4_generated` /
`Batch990.gen_inactiveCprime` inside it), 11 from `Batch1000.honest_lam_generated` (its `hax` /
`hwidth` from `Batch993.hgoodFill_generated`). -/
theorem hgood_genPkg_of_pair
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hpair : (GP).honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K (GP).q
      (GP).optimized.family.problem.cfg.kMem
      ((GP).optimized.family.problem.cfg.memRows ⊔ (GP).optimized.Λ)
      ((GP).memoryBaseEnv (canonicalMemoryTrace (GP))) (GP).optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets (GP).strategy.skeleton)) :
    (GP).honestTuple ∉ (GP).optimizedFailureEvent
      (honestQc (GP) (GP).honestTuple (QcH (GP))) (honestQm (GP) (GP).honestTuple (QmH (GP))) := by
  have G := Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq
    hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hlam := Nock.RedTeam.Batch1000.honest_lam_generated (F := F) (K := K) (q := q) (Λ := Λ) z α hz htwo a b c
    chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
    hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst (IG)
    (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
      hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
      hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (inputsOfCarrier_challenges (EG) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq
      hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF G.hax
    G.hwidth
  exact Nock.RedTeam.Batch993.hgood_generated' (F := F) (K := K) stc hK pOrbit hcap n hreq hresp
    hcard cwa α wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
    hlam hpair

/-- **Ev component 14 at the generated package**: `α ≠ 0` (`hB`, `hwin`). -/
theorem alphaNe_genPkg
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    alphaM (GP).honestTuple.1 ≠ 0 := by
  have hαeq : chal.α = α := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.α) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  show chal.α ≠ 0
  rw [hαeq]
  intro h0
  have hord0 : orderOf α = 0 := by rw [h0]; exact orderOf_eq_zero_iff'.2 (fun n hn => by simp [hn.ne'])
  omega

/-- `hF` at `F = ZMod p`. -/
theorem hF_zmod (p : ℕ) [Fact p.Prime] :
    ∀ x : ZMod p, ∃ n : ℕ, n < ringChar (ZMod p) ∧ (n : ZMod p) = x := by
  intro x
  refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
  rw [ZMod.ringChar_zmod_n]
  exact ZMod.val_lt x

/-- Every other premise of `Batch1173` is discharged here. -/
theorem nonvacuous_generated_of_open
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hpair : (GP).honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K (GP).q
      (GP).optimized.family.problem.cfg.kMem
      ((GP).optimized.family.problem.cfg.memRows ⊔ (GP).optimized.Λ)
      ((GP).memoryBaseEnv (canonicalMemoryTrace (GP))) (GP).optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets (GP).strategy.skeleton))
    (hp8Ev : (GP).honestTuple.1 ∉ evFailureUnion
      (builtStrategyEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
        (honestQm (GP) (GP).honestTuple (QmH (GP)))) (GP).optimized.Λ
      (GP).honestTuple.2.2.2.lambda)
    (hpairEv : (GP).honestTuple.1 ∉ reqPairEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
      (honestQm (GP) (GP).honestTuple (QmH (GP))))
    (hrootEv : (GP).honestTuple.1 ∉ rootResultEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
      (honestQm (GP) (GP).honestTuple (QmH (GP))))
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    ∃ hW : StrategyOfTracesLift.TracesWalkHyps (GP).optimized
        (honestQc (GP) (GP).honestTuple (QcH (GP))) (honestQm (GP) (GP).honestTuple (QmH (GP)))
        (GP).honestTuple,
      (Nock.RedTeam.Batch1024.TC (GP) (GP).honestTuple (QcH (GP)) (QmH (GP)) hW).BindsAtCoin
          (GP).honestTuple.1 (GP).honestTuple.2.2.2.lambda ∧
        (EdgeComparisonCensus.CombinedSkeletonCensus K
            (StrategyOfTracesEv.skeletonEv (GP).optimized (honestQc (GP) (GP).honestTuple (QcH (GP)))
              (honestQm (GP) (GP).honestTuple (QmH (GP)))) (GP).optimized.Λ ∧
          SizeWindowCounting.SizeWindowNounsBoundedBy
            (StrategyOfTracesEv.skeletonEv (GP).optimized (honestQc (GP) (GP).honestTuple (QcH (GP)))
              (honestQm (GP) (GP).honestTuple (QmH (GP)))) (GP).optimized.Λ) ∧
        ∃ C : EdgeComparisonCensus.CombinedSkeletonCensus K
            (Nock.RedTeam.Batch1024.TC (GP) (GP).honestTuple (QcH (GP)) (QmH (GP)) hW).skeleton
            (GP).optimized.Λ,
          (GP).honestTuple.1 ∉ ProductionP8Containment.FailureUnion
          (Nock.RedTeam.Batch1024.TC (GP) (GP).honestTuple (QcH (GP)) (QmH (GP)) hW) C
          (GP).honestTuple.2.2.2.lambda := by
  have G := Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq
    hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hacc := gen_honest_accepted (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
    hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hgood := hgood_genPkg_of_pair (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg
    mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hpair
  have hα := alphaNe_genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
    hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hgoodEv := hgoodEv_of_pinned (GP) _ _ (GP).honestTuple hgood hp8Ev hpairEv hrootEv hα
  have hbasis : FormRBasis (GP).optimized.basis := compilerBasis_formR (F := F) (K := K) hK
  -- the walk hypotheses, from acceptance and the tiling components of `hgood`
  have hgood' : (GP).honestTuple ∉ (GP).optimizedFailureEvent (canonicalComputeTrace (GP))
      (canonicalMemoryTrace (GP)) := by
    rw [← honestQc_QcH (GP), ← honestQm_QmH (GP)]; exact hgood
  have hW0 := Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed (GP) (GP).honestTuple
    (canonicalComputeTrace (GP)) (canonicalMemoryTrace (GP)) hacc.compute_satisfies
    hacc.memory_satisfies
    (Nock.RedTeam.Batch824.memStateTagChar_of_package (GP)) G.hax hbasis
    G.hwidth hacc hgood'
  have hW : StrategyOfTracesLift.TracesWalkHyps (GP).optimized
      (honestQc (GP) (GP).honestTuple (QcH (GP))) (honestQm (GP) (GP).honestTuple (QmH (GP)))
      (GP).honestTuple := by
    rw [honestQc_QcH (GP), honestQm_QmH (GP)]
    exact (Nock.RedTeam.Batch940.tracesWalkHyps_iff (GP) (GP).honestTuple _ _).2 hW0
  -- the §1 runs at the package claim
  have hclaim : (GP).optimized.verifier.raw.claim = ⟨subject, formula, result⟩ :=
    genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
      orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
      hbad hout hKszChar hprogCap hmemCap hfirst
  have hgen : genComputeSkeleton (K := K) fuel (GP).optimized.verifier.raw.claim.subject
      (GP).optimized.verifier.raw.claim.formula = .ok (t, result) := by
    rw [hclaim]; exact h
  have hG' : FieldEmbedding.evalGBy (ringChar K) fuel (GP).optimized.verifier.raw.claim.subject
      (GP).optimized.verifier.raw.claim.formula = some result := by
    rw [hclaim, ← hchar]; exact hG
  have bs : FieldEmbedding.BoundedBy (ringChar K) (GP).optimized.verifier.raw.claim.subject := by
    rw [hclaim, ← hchar]; exact hsB
  have bf : FieldEmbedding.BoundedBy (ringChar K) (GP).optimized.verifier.raw.claim.formula := by
    rw [hclaim, ← hchar]; exact hfB
  have hΛG : programLeafBound (airReorder t) ≤ (GP).optimized.Λ :=
    leafBound_of_traceConfined hconf
  refine ⟨hW, ?_, ?_, ?_⟩
  · exact Nock.RedTeam.Batch1173.bindsAtCoin_C2_combined (GP) (GP).honestTuple (QcH (GP))
      (QmH (GP)) hacc hgood hgoodEv G.hax hbasis G.hwidth hW hgen hG' bs bf hΛG hF
  · exact Nock.RedTeam.Batch1173.census_window_combined (GP) (GP).honestTuple (QcH (GP))
      (QmH (GP)) hacc hgood hgoodEv G.hax hbasis G.hwidth hW hgen hG' bs bf hΛG hF
  · exact ⟨_, Nock.RedTeam.Batch1173.not_mem_FailureUnion_combined (GP) (GP).honestTuple (QcH (GP))
      (QmH (GP)) hacc hgood hgoodEv G.hax hbasis G.hwidth hW hgen hG' bs bf hΛG hF⟩

/-- `P.strategy`'s claim is the package claim. -/
theorem strategy_claim_eq {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.strategy.verifier.raw.claim = P.optimized.verifier.raw.claim := rfl

theorem nonvacuous_generated_of_reconstruction
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hpair : (GP).honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K (GP).q
      (GP).optimized.family.problem.cfg.kMem
      ((GP).optimized.family.problem.cfg.memRows ⊔ (GP).optimized.Λ)
      ((GP).memoryBaseEnv (canonicalMemoryTrace (GP))) (GP).optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets (GP).strategy.skeleton))
    (hS : builtSkeletonEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
      (honestQm (GP) (GP).honestTuple (QmH (GP))) = (GP).strategy.skeleton)
    (htopo : (GP).honestTuple.1 ∉ TemplateRawJointSoundness.specializedTopologyFailureEvent
      (builtStrategyEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
        (honestQm (GP) (GP).honestTuple (QmH (GP)))).verifier.raw (GP).honestTuple.2.2.2.lambda)
    (haxisEv : (GP).honestTuple.1 ∉ envelopeAxisFailureEvent
      (builtStrategyEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
        (honestQm (GP) (GP).honestTuple (QmH (GP)))) (GP).honestTuple.2.2.2.lambda)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    ∃ hW : StrategyOfTracesLift.TracesWalkHyps (GP).optimized
        (honestQc (GP) (GP).honestTuple (QcH (GP))) (honestQm (GP) (GP).honestTuple (QmH (GP)))
        (GP).honestTuple,
      (Nock.RedTeam.Batch1024.TC (GP) (GP).honestTuple (QcH (GP)) (QmH (GP)) hW).BindsAtCoin
          (GP).honestTuple.1 (GP).honestTuple.2.2.2.lambda ∧
        (EdgeComparisonCensus.CombinedSkeletonCensus K
            (StrategyOfTracesEv.skeletonEv (GP).optimized (honestQc (GP) (GP).honestTuple (QcH (GP)))
              (honestQm (GP) (GP).honestTuple (QmH (GP)))) (GP).optimized.Λ ∧
          SizeWindowCounting.SizeWindowNounsBoundedBy
            (StrategyOfTracesEv.skeletonEv (GP).optimized (honestQc (GP) (GP).honestTuple (QcH (GP)))
              (honestQm (GP) (GP).honestTuple (QmH (GP)))) (GP).optimized.Λ) ∧
        ∃ C : EdgeComparisonCensus.CombinedSkeletonCensus K
            (Nock.RedTeam.Batch1024.TC (GP) (GP).honestTuple (QcH (GP)) (QmH (GP)) hW).skeleton
            (GP).optimized.Λ,
          (GP).honestTuple.1 ∉ ProductionP8Containment.FailureUnion
          (Nock.RedTeam.Batch1024.TC (GP) (GP).honestTuple (QcH (GP)) (QmH (GP)) hW) C
          (GP).honestTuple.2.2.2.lambda := by
  have hgood := hgood_genPkg_of_pair (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg
    mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hpair
  exact nonvacuous_generated_of_open (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg
    mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hpair
    (hp8Ev_of_skeleton_eq (GP) _ _ (GP).honestTuple hgood hS htopo haxisEv)
    (hpairEv_of_skeleton_eq (GP) _ _ (GP).honestTuple hgood hS)
    (hrootEv_of_skeleton_eq (GP) _ _ (GP).honestTuple hS (strategy_claim_eq (GP))) hF

end Generated

end

end Nock.RedTeam.Batch1250

#print axioms Nock.RedTeam.Batch1250.hgoodEv_of_pinned
#print axioms Nock.RedTeam.Batch1250.not_mem_evFailureUnion_of_parts
#print axioms Nock.RedTeam.Batch1250.hp8Ev_of_skeleton_eq
#print axioms Nock.RedTeam.Batch1250.hpairEv_of_skeleton_eq
#print axioms Nock.RedTeam.Batch1250.hrootEv_of_skeleton_eq
#print axioms Nock.RedTeam.Batch1250.strategy_claim_eq
#print axioms Nock.RedTeam.Batch1250.nonvacuous_generated_of_reconstruction
#print axioms Nock.RedTeam.Batch1250.reqPairEv_eq_pinned_of_targets
#print axioms Nock.RedTeam.Batch1250.rootResultEv_eq_empty_of_diag
#print axioms Nock.RedTeam.Batch1250.hgood_genPkg_of_pair
#print axioms Nock.RedTeam.Batch1250.alphaNe_genPkg
#print axioms Nock.RedTeam.Batch1250.hF_zmod
#print axioms Nock.RedTeam.Batch1250.nonvacuous_generated_of_open
