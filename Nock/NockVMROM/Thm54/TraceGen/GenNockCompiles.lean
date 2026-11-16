/-
  Nock/NockVMROM/Thm54/TraceGen/GenNockCompiles.lean

  `GY`'s own "Not claimed" line records what was
  missing: "§1's shape quantifies over the program with `Λ`, row-count and orbit side conditions
  and produces `∃ package` … the generic assembly of those into one existential statement is not
  written."  This module writes it.

  Two theorems, and the split is deliberate:

  * `exists_package_of_carrier` — at an arbitrary carrier `E` with an arbitrary `Data E`, plus the
    backend field data and the three arithmetic side conditions `inputsOfCarrier`
    (`GenCarrierInputs.lean`) spends.  Its claim conjunct is a **hypothesis**
    `hclaim : D.skeleton.publicClaim = ⟨subject, formula, result⟩`, because at an arbitrary `Data`
    nothing forces the committed claim to be about any particular program.
  * `nockCompiles_of_accepted` — the §1 shape, `∀ program the generator accepts`.  Here the claim
    conjunct is **discharged**, by `GenClaimedResult.publicClaim_genComputeNodes`, so it is not a
    premise: the emitted package's verifier claim is literally `⟨subject, formula, result⟩` with
    `result` the noun the generator returned, which `genComputeSkeleton_evalN`
    (`GenMatmulBounded.lean:334`) identifies with `Nock.evalN fuel subject formula`.

  **Every premise is stated, none is existentially quantified away.**  The hypothesis list of
  `nockCompiles_of_accepted` is exactly `genBuildableOfProgram`'s (`GenBuildableAssembly.lean:117`)
  — which is `genSemanticData`'s plus `hKsz2` plus the three capacity conditions — together with
  `inputsOfCarrier`'s backend data and its three arithmetic conditions.

  **The `evalN`-hypothesised shape is NOT this theorem.**  §1's literal antecedent is
  `hrun : evalN fuel subject formula = some result`; the antecedent here is generator acceptance.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenBuildableAssembly
import Nock.NockVMROM.Thm54.TraceGen.GenCarrierInputs
import Nock.NockVMROM.Thm54.TraceGen.GenClaimedResult
import Nock.NockVMROM.Thm54.TraceGen.GenHonestData
import Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLayout
import Nock.NockVMROM.Thm54.TraceGen.GenRomComplete
import Nock.NockVMROM.Thm54.TraceGen.GenStatement
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework.Thm54

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

variable {lmb : K}
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-! ## 1. The existential, at an arbitrary carrier

`statement_of_generated_residual` (`GenStatement.lean:111`) is applied, never re-proved; the
package is `buildFullPackage` at `inputsOfCarrier`, and the claim conjunct is read off the
residual's own `claim_eq` (`BuildablePackage.lean:70`). -/

/-- **`∃ package, Statement package ∧ the package's committed claim is this triple`,
at an arbitrary buildable carrier and an arbitrary committed `Data` over it.** -/
theorem exists_package_of_carrier
    (E : BuildableNockExecution F K) (D : Data E) {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (orbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hmemn : E.cfg.memRows ≤ n)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    {subject formula result : Noun}
    (hclaim : (Data.skeleton D).publicClaim = ⟨subject, formula, result⟩)
    (hax : FormRAxisBound
      (buildFullPackage E
        (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        (commitmentResidualOfZero D)
        (inputsOfCarrier_challenges E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        hprl hmore (by
          change 2 ≤ E.cfg.compRows →
            E.cfg.compRows ≤
              orderOf (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
                computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
                memoryExtensionFold (interCard_of_unionBound E hmemn hcard) hhon).computeWalkAlpha
          simpa [inputsOfCarrier] using hord)
        (by
          change 2 ≤ E.cfg.memRows →
            E.cfg.memRows ≤
              orderOf (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
                computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
                memoryExtensionFold (interCard_of_unionBound E hmemn hcard) hhon).memoryWalkAlpha
          simpa [inputsOfCarrier] using hordM) hrows).optimized.sampled
      (buildFullPackage E
        (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        (commitmentResidualOfZero D)
        (inputsOfCarrier_challenges E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        hprl hmore (by
          change 2 ≤ E.cfg.compRows →
            E.cfg.compRows ≤
              orderOf (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
                computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
                memoryExtensionFold (interCard_of_unionBound E hmemn hcard) hhon).computeWalkAlpha
          simpa [inputsOfCarrier] using hord)
        (by
          change 2 ≤ E.cfg.memRows →
            E.cfg.memRows ≤
              orderOf (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
                computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
                memoryExtensionFold (interCard_of_unionBound E hmemn hcard) hhon).memoryWalkAlpha
          simpa [inputsOfCarrier] using hordM) hrows).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = E.cfg.challenges.lam
        ∧ package.optimized.family.memoryWalkAlpha = memoryWalkAlpha := by
  refine ⟨buildFullPackage E
      (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
        computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
        (interCard_of_unionBound E hmemn hcard) hhon)
      (commitmentResidualOfZero D)
      (inputsOfCarrier_challenges E stc bas orbit hcap n hreq hresp hcard
        computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
        (interCard_of_unionBound E hmemn hcard) hhon)
      hprl hmore
      (by
        change 2 ≤ E.cfg.compRows →
          E.cfg.compRows ≤
            orderOf (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
              computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
              memoryExtensionFold (interCard_of_unionBound E hmemn hcard) hhon).computeWalkAlpha
        simpa [inputsOfCarrier] using hord)
      (by
        change 2 ≤ E.cfg.memRows →
          E.cfg.memRows ≤
            orderOf (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
              computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
              memoryExtensionFold (interCard_of_unionBound E hmemn hcard) hhon).memoryWalkAlpha
        simpa [inputsOfCarrier] using hordM) hrows,
    statement_of_generated_residual D _ _ hprl hmore (by
        change 2 ≤ E.cfg.compRows →
          E.cfg.compRows ≤
            orderOf (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
              computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
              memoryExtensionFold (interCard_of_unionBound E hmemn hcard) hhon).computeWalkAlpha
        simpa [inputsOfCarrier] using hord)
      (by
        change 2 ≤ E.cfg.memRows →
          E.cfg.memRows ≤
            orderOf (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
              computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
              memoryExtensionFold (interCard_of_unionBound E hmemn hcard) hhon).memoryWalkAlpha
        simpa [inputsOfCarrier] using hordM) hrows hgenF hF hax hbasis hwidth, ?_, rfl, rfl⟩
  exact (commitmentResidualOfZero D).claim_eq.symm.trans hclaim

/-! ## 2. The two IO conditions in program-measurable form

`inputsOfCarrier`'s two length bounds are stated at the carrier's derived record columns; the
generator computes both from the accepted tree, so a caller states numbers rather than measuring
lists. -/

/-- The request column of a generated execution has exactly `accAt …` entries. -/
theorem genExactExecution_requestIO_le (z α : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (n : ℕ)
    (hreqn : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ n) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).derivedRequestIO.length ≤ n := by
  rw [genExactExecution_derivedRequestIO_length (F := F) z α chal Ksz orbit horb a b c t mf
    hmempos hcomp hmem]
  exact hreqn

theorem genExactExecution_responseIO_le
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (n : ℕ)
    (hrespn : (bfsForest mf).length ≤ n) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
        hmempos hcomp hmem).derivedResponseIO.length ≤ n := by
  have hle := ExactExecution.derivedResponseIO_length_le
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem)
  have hrows : (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
      hmempos hcomp hmem).memoryRows.length = (bfsForest mf).length := by
    rw [ExactExecution.memoryRows_length]
    simp [genExactConfig]
  calc
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
        hmempos hcomp hmem).derivedResponseIO.length
        ≤ (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
            hmempos hcomp hmem).memoryRows.length := hle
    _ = (bfsForest mf).length := hrows
    _ ≤ n := hrespn


/-! ## 3. `Data` at `genBuildableOfProgram`, and the §1 existential

`genData` (`GenHonestData.lean:345`) is stated over `genBuildable … sd mt hnodup hbal …`, i.e. at
whatever `sd`/`mt` a caller supplies.  `genBuildableOfProgram` is `genBuildable` at
`genSemanticData`/`genServedMemoryTrace`, so feeding `genData` exactly those arguments produces a
`Data` over exactly that carrier.  Every fixture so far wrote this application out by
hand; it is written once here. -/

/-- **`HonestCommitment.Data` at the carrier `genBuildableOfProgram` builds**, for any program the
generator accepts.  The hypothesis list is `genBuildableOfProgram`'s, unchanged. -/
noncomputable def genDataOfProgram {q Λ : ℕ}
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
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    Data (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst) :=
  genData (F := F) z α a b c chal hinp Ksz orbit horb h hmempos hcomp hmem q (by omega) Λ hΛ hconf
    hb hq hchar haxis
    (genSemanticData (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hb hq hchar
      haxis hbad hout hfirst)
    (genServedMemoryTrace (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hfirst)
    (genExactExecution_requestNodup (F := F) z α chal Ksz orbit horb a b c t
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem (horb_of_window hB hwin))
    (genBuildable_hbal (F := F) chal Ksz orbit horb z α a b c (memInputs z)
      (genComputeRows z α t) t hmempos hcomp hmem)
    (le_of_eq hchar) htwo hKszChar
    (genBuildable_hprog (F := F) z α chal Ksz orbit horb a b c t
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem hprogCap)
    (genBuildable_hresp (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem hmemCap)

/-- **The committed public claim of `genDataOfProgram` is the program's own triple.**
`Data.skeleton` is `skeletonOfNodes` of the two committed node families, which `genData` sets to
`genComputeNodes`/`genMemoryNodes`, so this is `publicClaim_genComputeNodes` at that memory
forest. -/
theorem genDataOfProgram_publicClaim {q Λ : ℕ}
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
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    (Data.skeleton (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)).publicClaim
      = ⟨subject, formula, result⟩ :=
  publicClaim_genComputeNodes (K := K) z α a b c (genMemoryNodes z α chal.lam (memInputs z) t) h


/-- `R`/`r` are the generator's / evaluator's own
results; nothing ties them to the claim here.  Every argument of the carrier is implicit, so the
lemma is used against the expected type (the `claim_generated` default of `buildFullPackage`). -/
theorem genDataOfProgram_claimGenerated {q Λ : ℕ}
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
    {fuel' : ℕ} {r : Noun}
    (hG : FieldEmbedding.evalGBy q fuel' subject formula = some r) :
    GeneratedField.ClaimGenerated K
      (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)).verifier.raw.claim
      (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)).Λ := by
  show GeneratedField.ClaimGenerated K (Data.skeleton (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)).publicClaim Λ
  rw [genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst]
  subst hchar
  exact ⟨fuel, t, result, fuel', r, h, hG, leafBound_of_traceConfined hconf⟩

/-- `genDataOfProgram_claimGenerated` at the `Data` (the form `exists_package_of_carrier` reads). -/
theorem genDataOfProgram_claimGeneratedD {q Λ : ℕ}
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
    {fuel' : ℕ} {r : Noun}
    (hG : FieldEmbedding.evalGBy q fuel' subject formula = some r) :
    GeneratedField.ClaimGenerated K
      (Data.skeleton (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)).publicClaim
      (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).Λ := by
  show GeneratedField.ClaimGenerated K (Data.skeleton (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)).publicClaim Λ
  rw [genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst]
  subst hchar
  exact ⟨fuel, t, result, fuel', r, h, hG, leafBound_of_traceConfined hconf⟩

/-! ## 4.

Everything else is §1's shape: the program is quantified over, the
side conditions are stated, the conclusion is one existential, and the second conjunct pins the
emitted package to *this* program's committed triple. -/

/-- **`∃ package, OptimizedFullStrictThm54Statement package ∧ the package's committed claim is
`⟨subject, formula, result⟩`**, for every Nock program the ROM generator accepts.

The premises, grouped:

* **the program** — `h : genComputeSkeleton fuel subject formula =.ok (t, result)`;
* **the counted events** — `hseed`, `hcoins`, `hbad`, `hout`, plus the IO coin
  event, discharged inside `inputsOfCarrier` from the stated counting bound `hcard`;
* **the `Λ` leaf window** — `hΛ` and `hconf`;
* Both now have `∀ program` suppliers from
  *program-level* premises: `genComputeSkeleton_skeletonBounded`
  (`GenGenericBounded.lean::genComputeSkeleton_skeletonBounded`) and
  `genComputeSkeleton_axisRange` (`GenGenericAxisRange.lean::genComputeSkeleton_axisRange`), whose
  inputs are `1 < q`, atom bounds on subject and formula, and
  `FieldEmbedding.evalGBy q fuel subject formula = some result`.
  `nockCompiles_of_accepted_bounded` is
  this theorem with both supplied from those three program measurements; `nockCompiles_of_grom` and
  `GoodSeed.nockCompiles_of_grom_atRomSeed` fold the guarded run into the ROM antecedent through
  `evalGRom` (`GenGuardedRom.lean::evalGRom`), so there the binder count does not move at all.

Nothing is existentially quantified away. -/
theorem nockCompiles_of_accepted {q Λ : ℕ}
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
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
            hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
              hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
                  haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
            hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
              hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
                  haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
            hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
              hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
                  haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
            hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
              hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
                  haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = chal.lam
        ∧ package.optimized.family.memoryWalkAlpha = memoryWalkAlpha :=
  exists_package_of_carrier
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst)
    (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst)
    stc bas packageOrbit hcap n
    (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
    (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
    hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
    (by
      change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
      exact hrespn)
    (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst)
    (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
      hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
      hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
    hmore
    hord hordM hrows (genDataOfProgram_claimGeneratedD hG) hF
    (genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst)
    hax hbasis hwidth


/-! ## 5.

`GenRomComplete.lean` supplies generator **completeness**: a program that terminates inside
`NockVMROM^Λ` is accepted, and the accepted tree carries the ROM result.  So the
acceptance hypothesis of §4 need not be assumed — it is produced.  `romTree` names the tree
completeness produces, which is what lets the trace-level side conditions (`hseed`, `hcoins`,
`hconf`, `hb`, `haxis`, `hbad`, `hout` and the four capacity bounds) be *stated*: they are
properties of the emitted trace, not of the source text, so some name for that trace is
unavoidable.

`evalRom_evalN` means the antecedent below **implies** §1's `hrun : evalN fuel subject formula =
some result` rather than sitting beside it; and `gen_ok_iff_evalRom` means the restriction is not a
convenience — acceptance and ROM termination are the same condition, so no weaker hypothesis on the
program is available. -/

/-- **`∃ package, OptimizedFullStrictThm54Statement package ∧ the package's committed claim is
`⟨subject, formula, result⟩`**, for every Nock program that terminates inside the paper's
`NockVMROM`.

This is `nockCompiles_of_accepted` with its acceptance hypothesis discharged by completeness.  The
antecedent `hrom` is a condition on the *execution*, not on the source formula: `OP_2` runs a
computed formula and `OP_9` fetches its formula out of the subject, so no syntactic no-`OP_10`
condition would do (`GenRomComplete.lean`'s module docstring).  By `evalRom_evalN` it implies
`Nock.evalN fuel subject formula = some result`, i.e. §1's `hrun`. -/
theorem nockCompiles_of_rom {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrom : evalRom fuel subject formula = some result)
    (hseed : SeedGood z (romTree (K := K) hrom))
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder (romTree (K := K) hrom)))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))).length)
    (hcomp : (bfsForest [genComputeRows z α (romTree (K := K) hrom)]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder (romTree (K := K) hrom)) (bfsRows (airReorder (romTree (K := K) hrom))).length + 3 < B)
    (hKsz : accAt (airReorder (romTree (K := K) hrom)) (bfsRows (airReorder (romTree (K := K) hrom))).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α (romTree (K := K) hrom))
      (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom)) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
      (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
      (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
      (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder (romTree (K := K) hrom)) (bfsRows (airReorder (romTree (K := K) hrom))).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder (romTree (K := K) hrom))) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
        B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder (romTree (K := K) hrom)) (bfsRows (airReorder (romTree (K := K) hrom))).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c
            (romTree (K := K) hrom) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α (romTree (K := K) hrom))
            (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
                B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard) (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c
            (romTree (K := K) hrom) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α (romTree (K := K) hrom))
            (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
                B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard) (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c
            (romTree (K := K) hrom) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α (romTree (K := K) hrom))
            (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
                B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard) (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c
            (romTree (K := K) hrom) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α (romTree (K := K) hrom))
            (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) hrom))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
                B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard) (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
            B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem
          B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = chal.lam :=
  -- S2 (W-gen): `nockCompiles_of_accepted` also ties the walk coin; this off-path form keeps its three conjuncts.
  (nockCompiles_of_accepted z α hz htwo a b c chal hinp hmi Ksz orbit horb
    (romTree_spec (K := K) hrom) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
    hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst hmore stc bas packageOrbit hcap n hreqn hrespn
    hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
    hord hordM hrows hG hF hax hbasis hwidth).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

end

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_package_of_carrier
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_requestIO_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_responseIO_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.genDataOfProgram
#print axioms Nock.NockVMROM.Thm54.TraceGen.genDataOfProgram_publicClaim
#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_accepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_rom
