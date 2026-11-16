/-
  Nock/NockVMROM/Thm54/TraceGen/GenAcceptingCoin.lean

  **The generated package with a NON-EMPTY acceptance set.**

  Zero multiplicities violate the raw
  verifier's mandatory nonzero-multiplicity gate (`RawVerifier.lean:402`), so nothing accepts and
  the capstone's six acceptance/security conjuncts hold over an empty acceptance set.

  The repair needs no new mathematics.  The honest later-round message already exists, generically
  in `E` and `D`:

  * `GenericHonestArrays.alphaMCommitmentOf` / `walkArraysOf` are `commitmentResidualOf`'s two
    open arguments `A` / `W`, built from `Data E` plus `NodeEncoding.StateTagChar K`;
  * `GenericHonestArrays.honestVerifierGates_at` compiles all SEVENTEEN `VerifierGates` conjuncts
    and `honestSixRAPSatisfy_at` the twenty-four RAP evaluations, at the fibre coin
    `honestCoin E a g`;
  * `GenericHonestPackage.packageOf` / `statementOf` build the released package and its unchanged
    fourteen-field statement over that residual;
  * `ForestExponentOrderClosure.normalised_package_fibre_accepts` closes the last named window
    premise `ForestExponentOrder` unconditionally at the canonically stamped commitment.

  This module
  writes exactly that, and adds nothing else.

  Two disclosures, both load-bearing.

  1. **This is a DIFFERENT package from `b246Package` / `bpPackage`**, not a strengthening of them.
     Those are `buildFullPackage … (commitmentResidualOfZero D)`; this is
     `buildFullPackageWith … (commitmentResidualOfArrays_of_char (normData D) …)`.  Nothing here
     says the zero-residual packages accept anything, and `HN` §3's verdict about them stands.

  2. **The committed object is `normData D`, not `D`.**  Whether it is the identity at a generated `Data`, whose
     committed exponents are line numbers bounded by `hwin`/`hB`, is NOT established here.

  And a non-empty acceptance
  set is not yet an informative `containment` conclusion — that additionally needs
  `honestCoin E a g ∉ ProductionP8Containment.FailureUnion`, which is not supplied here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompiles
import Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

variable {lmb : K}
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-! ## 1. At an arbitrary carrier

`exists_package_of_carrier` (`GenNockCompiles.lean`) is the zero-residual analogue of this
theorem.  The only differences are the residual and the third conjunct. -/

/-- **`∃ package, Statement package ∧ the claim is this triple ∧ the package accepts the whole
honest fibre`**, at an arbitrary buildable carrier and an arbitrary committed `Data` over it.

The premise list is `exists_package_of_carrier`'s plus `hgt : 11 < ringChar K`. -/
theorem exists_accepting_package_of_carrier
    (E : BuildableNockExecution F K) (D : Data E) {hOrb : ℕ}
    (hgt : 11 < ringChar K)
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
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    {subject formula result : Noun}
    (hclaim : (Data.skeleton D).publicClaim = ⟨subject, formula, result⟩)
    (hax : FormRAxisBound
      (packageOf (normData D) hgt
        (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).optimized.sampled
      (packageOf (normData D) hgt
        (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).optimized.basis)
    (hbasis : FormRBasis
      (packageOf (normData D) hgt
        (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).optimized.basis)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ (∀ a g : K, package.strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam) := by
  set I : Inputs E :=
    inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
      computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
      (interCard_of_unionBound E hmemn hcard) hhon
  refine ⟨packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF,
    statementOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF hax hbasis hwidth, ?_, ?_⟩
  · have h2 : (Data.skeleton (normData D)).publicClaim = ⟨subject, formula, result⟩ := by
      rw [normData_skeleton D]; exact hclaim
    exact (commitmentResidualOfArrays_of_char (normData D) hgt).claim_eq.symm.trans h2
  · exact normalised_package_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF

/-! ## 2. Over the program

`nockCompiles_of_accepted`'s premise list, unchanged and with nothing added: `hgt` is derived from
the `hq`/`hchar` pair the theorem already carries, and `stc` is already one of its arguments. -/

/-- **`nockCompiles_of_accepted` with a non-empty acceptance set.**  For every Nock program the
ROM generator accepts, there is a package satisfying the released Theorem-5.4 statement, whose
committed claim is that program's `⟨subject, formula, result⟩`, and which **accepts every coin of
the honest later-round fibre** over the carrier's own committed `(alphaM, z)`.

Premises are exactly `nockCompiles_of_accepted`'s (`GenNockCompiles.lean`); `11 < ringChar K` comes
free from `hq : 11 < q` and `hchar : q = ringChar K`.  Not `∀ ω` — see the module header. -/
theorem nockCompiles_of_accepted_accepting {q Λ : ℕ}
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
          hchar           haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
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
      (packageOf (normData
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
            hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (hchar ▸ hq)
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
          (interCard_of_unionBound _
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
                  hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (packageOf (normData
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
            hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (hchar ▸ hq)
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
          (interCard_of_unionBound _
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
                  hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis
      (packageOf (normData
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
            hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (hchar ▸ hq)
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
          (interCard_of_unionBound _
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
                  hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ (∀ a' g' : K, package.strategy.Accepts
            (honestCoin (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
              hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
              hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) a' g') chal.lam) := by
  have hgt : 11 < ringChar K := hchar ▸ hq
  exact exists_accepting_package_of_carrier
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst)
    (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst)
    hgt stc bas packageOrbit hcap n
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

end

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_accepting_package_of_carrier
#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_accepted_accepting
