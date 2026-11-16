/-
  Nock/RedTeam/Batch991Thm54HonestPoleAssembly.lean

  The generated package is `buildFullPackage E I (commitmentResidualOfZero D)..` with
  `E = genBuildableOfProgram..`, `D = genDataOfProgram..` and `I = inputsOfCarrier E..` (the
  shape the `nockCompiles` chain builds; `Batch956` header).  Discharged here, with no new
  hypothesis:

  * component 4 (internal-pole pairs), WITHOUT `HonestFill`: `h0` / `hγ8` from the new chooser
    (`Batch990.inter_sides_inputsOfCarrier`), `inactiveMem` (`Batch957.inactiveMem_buildable`),
    `hzc` (`Batch990.gen_inactiveCprime`), and `CprimeCoherent` from the generator
    (`genExactExecution_cprimeCoherent`, its window from `hwin`): `component4_generated`;
  * component 1's seed conditions (`Batch956.genData_seed_good`), component 3's premises
    (`Batch957.gen_timestamp_premises`).

  `hgood_generated` is `hgood` at the generated package from `H : HonestFill`, `hlam`
  (component 11) and `hpair` (component 12) only.
-/
import Nock.RedTeam.Batch990Thm54HonestPoleChooser
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch991

open Nock Nock.Walk
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
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


/-- The generated execution is `C'`-coherent (`genExactExecution_cprimeCoherent`; its window
`programAcc < orderOf α` is `hwin`). -/
theorem gen_cprimeCoherent : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
    chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
    hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.CprimeCoherent := by
  have hzeq : chal.z = z := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.z) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  exact genExactExecution_cprimeCoherent (F := F) z α chal hzeq Ksz orbit horb a b c h
    hmempos hcomp hmem (by omega)

/-- **Component 4 closed at the generated package** (no `HonestFill`, no new hypothesis). -/
theorem component4_generated
    (stc : NodeEncoding.StateTagChar K) (bas : Module.Basis (Fin 3) F K) {hOrb : ℕ}
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
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
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
        hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F) :
    ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ)
        z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B
        hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
        b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n
        hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows (by claim_generated) hF).optimized.sampled.sampled.coins.gamma, (buildFullPackage (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
        hprl hmore hord hordM hrows).optimized.sampled.interPole) ∉
      interFailurePairs ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
          htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
          hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq
          hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
          horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
          hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows).hostileInterRecords
          (canonicalMemoryTrace (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq
          hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
          horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
          hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows)))
        ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
            hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
            orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
            cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
            (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
            hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
            := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
            hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
            hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl
            hmore hord hordM hrows).memorySourceEnv (canonicalMemoryTrace (buildFullPackage
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
            orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
            orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
            cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
            (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
            hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
            := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
            hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
            hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl
            hmore hord hordM hrows)))
        ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
            hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
            orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
            cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
            (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
            hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
            := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
            hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
            hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl
            hmore hord hordM hrows).memoryBaseEnv (canonicalMemoryTrace (buildFullPackage
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
            orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
            orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
            cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
            (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
            hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
            := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
            hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
            hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl
            hmore hord hordM hrows))) := by
  have hs := Batch990.inter_sides_inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
      z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
      hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit
      hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon
    (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) hprl hmore hord hordM
    hrows
  replace hs := hs (by claim_generated) hF
  exact OptimizedCanonicalHostileLists.canonical_inter_not_hostile_failure (buildFullPackage
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
      horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
      hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
      q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
      hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
      stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
      (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
      hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
      hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
      horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
      hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
      mef hinterCard hhon) hprl hmore hord hordM hrows) hs.1 hs.2
    (Batch957.inactiveMem_buildable (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
        b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) _ _ hprl hmore hord hordM hrows (by claim_generated) hF)
    (Batch990.gen_inactiveCprime (F := F) (q := q) (Λ := Λ) (z := z) (α := α) (hz := hz) (htwo :=
        htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp) (hmi := hmi) (Ksz := Ksz)
        (orbit := orbit) (horb := horb) (h := h) (hseed := hseed) (hcoins := hcoins) (hΛ := hΛ)
        (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := B) (hB := hB)
        (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq := hq) (hchar := hchar) (haxis
        := haxis) (hbad := hbad) (hout := hout) (hKszChar := hKszChar) (hprogCap := hprogCap)
        (hmemCap := hmemCap) (hfirst := hfirst)) (gen_cprimeCoherent (F := F) (q := q) (Λ := Λ) (z
        := z) (α := α) (hz := hz) (htwo := htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp :=
        hinp) (hmi := hmi) (Ksz := Ksz) (orbit := orbit) (horb := horb) (h := h) (hseed := hseed)
        (hcoins := hcoins) (hΛ := hΛ) (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem
        := hmem) (B := B) (hB := hB) (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq
        := hq) (hchar := hchar) (haxis := haxis) (hbad := hbad) (hout := hout) (hKszChar :=
        hKszChar) (hprogCap := hprogCap) (hmemCap := hmemCap) (hfirst := hfirst))

/-- **`hgood` at the generated package** from `HonestFill`, component 11 (`hlam`) and
component 12 (`hpair`) only. -/
theorem hgood_generated
    (stc : NodeEncoding.StateTagChar K) (bas : Module.Basis (Fin 3) F K) {hOrb : ℕ}
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
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
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
        hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (H : HonestFill (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
        a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ)
        z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B
        hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
        b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n
        hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows))
    (hlam : (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ)
        z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B
        hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
        b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n
        hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows).honestTuple ∉ (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α
        hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp
        hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ :=
        Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem
        B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas
        pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows).decodedLambdaEventOf (canonicalComputeTrace (buildFullPackage (genBuildableOfProgram
        (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
        hprl hmore hord hordM hrows))
      (canonicalMemoryTrace (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α
          hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
          hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq
          hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
          horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
          hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows)))
    (hpair : (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ)
        z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B
        hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
        b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n
        hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows).honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
        (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) hprl hmore hord hordM hrows).q
      (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
          (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
          hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
          := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
          hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord
          hordM hrows).optimized.family.problem.cfg.kMem
      ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
          (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
          hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
          := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
          hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord
          hordM hrows).optimized.family.problem.cfg.memRows ⊔ (buildFullPackage
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram
          (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins
          hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar
          hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z
          α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B
          hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit
          hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
          hrows).optimized.Λ)
      ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
          (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
          hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
          := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
          hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord
          hordM hrows).memoryBaseEnv (canonicalMemoryTrace (buildFullPackage (genBuildableOfProgram
          (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins
          hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar
          hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ :=
          Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
          hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit
          hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows)))
      (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
          (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
          hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
          := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
          hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord
          hordM hrows).optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ :=
          Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
          hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq
          hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
          horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
          hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows).strategy.skeleton)) :
    (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ)
        z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B
        hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
        b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n
        hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows).honestTuple ∉ (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α
        hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp
        hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ :=
        Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem
        B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas
        pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows).optimizedFailureEvent (honestQc _ (buildFullPackage (genBuildableOfProgram (F := F)
        (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
        hprl hmore hord hordM hrows).honestTuple (QcH _))
      (honestQm _ (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
          b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard
          cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F)
          (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
          hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ
          := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
          hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord
          hordM hrows).honestTuple (QmH _)) := by
  have hsg := Batch956.genData_seed_good (F := F) (q := q) (Λ := Λ) (z := z) (α := α) (hz := hz)
    (htwo := htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp) (hmi := hmi)
    (Ksz := Ksz) (orbit := orbit) (horb := horb) (h := h) (hseed := hseed) (hcoins := hcoins)
    (hΛ := hΛ) (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := B)
    (hB := hB) (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq := hq)
    (hchar := hchar) (haxis := haxis) (hbad := hbad) (hout := hout) (hKszChar := hKszChar)
    (hprogCap := hprogCap) (hmemCap := hmemCap) (hfirst := hfirst)
  have htp := Batch957.gen_timestamp_premises (F := F) (q := q) (Λ := Λ) (z := z) (α := α)
    (hz := hz) (htwo := htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp)
    (hmi := hmi) (Ksz := Ksz) (orbit := orbit) (horb := horb) (h := h) (hseed := hseed)
    (hcoins := hcoins) (hΛ := hΛ) (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp)
    (hmem := hmem) (B := B) (hB := hB) (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb)
    (hq := hq) (hchar := hchar) (haxis := haxis) (hbad := hbad) (hout := hout)
    (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap := hmemCap) (hfirst := hfirst)
  have hs := Batch990.inter_sides_inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
      z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
      hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit
      hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon
    (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) hprl hmore hord hordM
    hrows
  replace hs := hs (by claim_generated) hF
  exact Batch963.hgood_zero_built (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b
      c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
      hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (genDataOfProgram (F := F) (q :=
      q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
      hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
      (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
      hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa
      mwa wg msc mef hinterCard hhon) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q
      := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
      hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
      stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore
    hord hordM hrows (by claim_generated) hF H hsg.1 hsg.2 htp.1 htp.2 hs.2 hs.1 (Batch990.gen_inactiveCprime (F := F) (q :=
        q) (Λ := Λ) (z := z) (α := α) (hz := hz) (htwo := htwo) (a := a) (b := b) (c := c) (chal :=
        chal) (hinp := hinp) (hmi := hmi) (Ksz := Ksz) (orbit := orbit) (horb := horb) (h := h)
        (hseed := hseed) (hcoins := hcoins) (hΛ := hΛ) (hconf := hconf) (hmempos := hmempos) (hcomp
        := hcomp) (hmem := hmem) (B := B) (hB := hB) (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2)
        (hb := hb) (hq := hq) (hchar := hchar) (haxis := haxis) (hbad := hbad) (hout := hout)
        (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap := hmemCap) (hfirst := hfirst)) hlam
        hpair

theorem honestFill_generated_forces_gamma_zero
    (stc : NodeEncoding.StateTagChar K) (bas : Module.Basis (Fin 3) F K) {hOrb : ℕ}
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
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
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
        hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (H : HonestFill (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
        a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ)
        z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B
        hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
        b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n
        hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows)) :
    (ioCoinsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) n hreq hresp hcard).gamma = 0 := by
  have h1 := Batch990.honestFill_forces_gamma H
  have h2 := Batch990.gen_table_gamma_zero (F := F) (q := q) (Λ := Λ) (z := z) (α := α)
    (hz := hz) (htwo := htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp)
    (hmi := hmi) (Ksz := Ksz) (orbit := orbit) (horb := horb) (h := h) (hseed := hseed)
    (hcoins := hcoins) (hΛ := hΛ) (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp)
    (hmem := hmem) (B := B) (hB := hB) (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb)
    (hq := hq) (hchar := hchar) (haxis := haxis) (hbad := hbad) (hout := hout)
    (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap := hmemCap) (hfirst := hfirst)
  exact h1.trans h2

end

end Nock.RedTeam.Batch991

#print axioms Nock.RedTeam.Batch991.gen_cprimeCoherent
#print axioms Nock.RedTeam.Batch991.component4_generated
#print axioms Nock.RedTeam.Batch991.hgood_generated
#print axioms Nock.RedTeam.Batch991.honestFill_generated_forces_gamma_zero
