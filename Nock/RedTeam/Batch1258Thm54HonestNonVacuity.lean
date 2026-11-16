import Nock.RedTeam.Batch1250Thm54HonestGoodGenerated
import Nock.RedTeam.Batch1253Thm54HonestPairSeedIrrelevance
import Nock.RedTeam.Batch1254Thm54HonestTopologyAxis
import Nock.RedTeam.Batch1255Thm54HonestComputeReconstruction
import Nock.RedTeam.Batch1257Thm54HonestSeedWidenedChain
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1258Thm54HonestNonVacuity.lean

  * `NV P`: `Batch1173`'s three conclusions at `P`'s honest tuple and honest traces.
  * `nonvacuous_generated` (general `F`, any generated program, `genPkg`'s binders): every premise of
    `Batch1250.nonvacuous_generated_of_reconstruction` is discharged —
    `hpair` by `Batch1253.AtGen.hpair_of_seed` from the z-free seed condition `hzp`,
    `hS` replaced by its compute half `Batch1255.Gen.builtComputeTree_genPkg` (the consumers read only
    the compute tree; the memory half is not claimed, `Batch1256`),
    `htopo` / `haxisEv` by `Batch1254.T5.htopo_genPkg` / `haxisEv_genPkg`;
    remaining binders: the generator's, the seed condition `hzp`, and `hF` (open at general `F`).
  * The package is the chain's `genPkg` at
    the widened seed (`Batch1257.nvX_zmod`) avoiding `Batch1253.Seed.pairBad`; `hF` by
    `Batch1250.hF_zmod`.  No open premise.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Nock.RedTeam.Batch1258

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

/-- **The non-vacuity predicate** at any package `P`: `Batch1173`'s three conclusions at `P`'s honest
tuple and honest traces `QcH P` / `QmH P` (`BindsAtCoin` of the built strategy, the combined census
and size window of the built skeleton, and the honest tuple outside the built `FailureUnion`). -/
def NV {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop :=
    ∃ hW : StrategyOfTracesLift.TracesWalkHyps P.optimized
        (honestQc P P.honestTuple (QcH P)) (honestQm P P.honestTuple (QmH P))
        P.honestTuple,
      (Nock.RedTeam.Batch1024.TC P P.honestTuple (QcH P) (QmH P) hW).BindsAtCoin
          P.honestTuple.1 P.honestTuple.2.2.2.lambda ∧
        (EdgeComparisonCensus.CombinedSkeletonCensus K
            (StrategyOfTracesEv.skeletonEv P.optimized (honestQc P P.honestTuple (QcH P))
              (honestQm P P.honestTuple (QmH P))) P.optimized.Λ ∧
          SizeWindowCounting.SizeWindowNounsBoundedBy
            (StrategyOfTracesEv.skeletonEv P.optimized (honestQc P P.honestTuple (QcH P))
              (honestQm P P.honestTuple (QmH P))) P.optimized.Λ) ∧
        ∃ C : EdgeComparisonCensus.CombinedSkeletonCensus K
            (Nock.RedTeam.Batch1024.TC P P.honestTuple (QcH P) (QmH P) hW).skeleton
            P.optimized.Λ,
          P.honestTuple.1 ∉ ProductionP8Containment.FailureUnion
          (Nock.RedTeam.Batch1024.TC P P.honestTuple (QcH P) (QmH P) hW) C
          P.honestTuple.2.2.2.lambda

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

/-- **Non-vacuity at the generated package, honest tuple, honest traces, with no open premise beyond the
z-free seed condition `hzp` and `hF`** (`F` its own prime field). -/
theorem nonvacuous_generated
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
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hzp : z ∉ PreSeedCensus.pairBadSeeds (K := K)
      ((Nock.RedTeam.Batch1253.AtGen.rows0 t).length ⊔ Λ) (Nock.RedTeam.Batch1253.AtGen.honestPairs0 F K q t))
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
  have hpair := Nock.RedTeam.Batch1253.AtGen.hpair_of_seed (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hG hF hzp
  have hgood := Nock.RedTeam.Batch1250.hgood_genPkg_of_pair (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hpair
  have htopo := Nock.RedTeam.Batch1254.T5.htopo_genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hgood
  have haxisEv := Nock.RedTeam.Batch1254.T5.haxisEv_genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hgood
  have hSc := Nock.RedTeam.Batch1255.Gen.builtComputeTree_genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  exact Nock.RedTeam.Batch1250.nonvacuous_generated_of_open (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hpair
    (Nock.RedTeam.Batch1255.Consumers.hp8Ev_of_computeTree_eq (GP) _ _ (GP).honestTuple hgood hSc htopo haxisEv)
    (Nock.RedTeam.Batch1255.Consumers.hpairEv_of_computeTree_eq (GP) _ _ (GP).honestTuple hgood hSc)
    (Nock.RedTeam.Batch1255.Consumers.hrootEv_of_computeTree_eq (GP) _ _ (GP).honestTuple hSc) hF

end Generated

section Zmod

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional (ZMod p) K]

open Nock.NockVMROM.Thm54.TraceGen.GoodSeed in
/-- The package is the chain's `genPkg` at the widened seed (`Batch1257.nvX_zmod`)
whose `z` also avoids the z-free pair bad set `Batch1253.Seed.pairBad` of the program; at it the
three `Batch1173` theorems hold at the honest tuple and honest traces (`NV`). -/
theorem nonvacuous_zmod
    (α lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula)
    (hΛp : (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))) < p)
    (hp : 25 ≤ p)
    (hp64 : p < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ∣ p - 1)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3 < orderOf α ∧ programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf α)
    (hKszChar : compilerKszOf (0 : K) α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < p) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ NV package := by
  have hrom := evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)
  have hlen : (Nock.RedTeam.Batch1253.AtGen.rows0 (romTree (K := K) hrom)).length =
      programMemShape α (romTree (K := K) hrom) := by
    have e := congrArg List.length
      (Nock.RedTeam.Batch1253.genMemoryForest_bfs_sig (K := K) 0 α 0 (memInputs 0) (romTree (K := K) hrom))
    simp only [List.length_map] at e
    simpa [Nock.RedTeam.Batch1253.AtGen.rows0, Nock.RedTeam.Batch1253.AtGen.refForest,
      programMemShape, programMemRows, programMemRowsL] using e.symm
  have hX := Nock.RedTeam.Batch1253.Seed.pairBad_card_le (K := K) (ZMod p) p
    (programLeafBound (airReorder (romTree (K := K) hrom))) (romTree (K := K) hrom)
  rw [hlen] at hX
  obtain ⟨P, h1, h2, h3, h4, -⟩ := Nock.RedTeam.Batch1257.nvX_zmod α lmb hrun hbound hs hf hΛp hp hp64 hK hF
    hwin hKszChar
    (Nock.RedTeam.Batch1253.Seed.pairBad (K := K) (ZMod p) p
      (programLeafBound (airReorder (romTree (K := K) hrom))) (romTree (K := K) hrom)) hX NV
    (by
      intro hq hchar htwo z hz a b c chal hinp hmi Ksz orbit horb t h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb haxis hbad hout hKszChar hprogCap hmemCap hfirst
        stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows
        _hFp hsB hfB hG hp64 hzX
      have ht : t = romTree (K := K) hrom := by
        have e := h.symm.trans (romTree_spec (K := K) hrom)
        injection e with e'
        exact (Prod.mk.inj e').1
      subst ht
      exact nonvacuous_generated (F := ZMod p) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
        hinterCard hhon hprl hmore hord hordM hrows hsB hfB hG hp64 hzX
        (Nock.RedTeam.Batch1250.hF_zmod p))
  exact ⟨P, h1, h2, h3, h4⟩

end Zmod

end

end Nock.RedTeam.Batch1258

#print axioms Nock.RedTeam.Batch1258.nonvacuous_generated
#print axioms Nock.RedTeam.Batch1258.nonvacuous_zmod
