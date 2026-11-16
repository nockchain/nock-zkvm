import Nock.RedTeam.Batch1430Thm54PartAH21
import Nock.NockVMROM.Thm54.P8Core.PartAStaged12
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1431Thm54PartAStaged.lean

  * §2 **honest acceptance at the parallel package** (`Batch1061`-style): at any package with the
    honest-fill hypotheses, the honest 309 trace (`correctedCanonicalFinalTrace309`, L2) is accepted
    by the un-hosted 309 compute chip at `forget12 honestTuple12` (`compute309_accepted_of`); at the
    generated package with the memory walk coin `mwa` FREE (L3's `genPkgW`) the honest pair is
    accepted by BOTH parallel chips at `honestTuple12` (`gen_honest_accepted309`): `αW ≠ α` is
    exercised, no identity `mwa = α` is assumed.  The inverted repair-(ii) receipt (an honest walk
    built at `α` is rejected wherever `αW ≠ α`) is L3's `walk_at_alpha_rejected12`.

  Scope: the repartitioned schedule and the parallel package only; nothing here is about
  `deployedChronology`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1431

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
open Nock.RedTeam.Batch1061
open Nock.RedTeam.Batch1420
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.PartA12
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## §1 The H2.2 theorems (receipts) -/

section Staged
variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

open Classical in
/-- The fifteen-summand bound). -/
theorem h22_card (Qc : OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
    (Qm : OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X])
    (hst : PartAStaged.StagedTraces12 P Qc Qm) :
    (Finset.univ.filter fun c => c ∈ PartAStaged.consumedFailureEvent309 P (Qc c) (Qm c)).card ≤
      PartAStaged.bound15 P :=
  PartAStaged.staged_consumed_card_le P Qc Qm hst

theorem h22_same_bound :
    ((PartAStaged.bound12 P : ℕ) : ℚ) / (Fintype.card K ^ 12) =
      optimizedHostileProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ) P.hostileIOWork
        (OptimizedFailureEventEv.N P) (OptimizedFailureEventEv.M P) :=
  cardBound12_normalised _ _ _ _ _ _ Fintype.card_pos

theorem h22_bound15 :
    ((PartAStaged.bound15 P : ℕ) : ℚ) / (Fintype.card K ^ 12) =
      optimizedHostileProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ) P.hostileIOWork
          (OptimizedFailureEventEv.N P) (OptimizedFailureEventEv.M P) +
        ((1 + OptimizedFailureEventEv.M P * (OptimizedFailureEventEv.M P - 1) / 2 : ℕ) : ℚ) /
          Fintype.card K :=
  cardBound15_normalised _ _ _ _ _ _ Fintype.card_pos

end Staged

/-! ## §2 Honest acceptance at the parallel package -/

section AnyPackage
variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The honest 309 compute trace of a package (L2's `correctedCanonicalFinalTrace309`). -/
abbrev canonical309 : Fin 309 → F[X] :=
  Unhosted309.correctedCanonicalFinalTrace309 P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit

/-- The un-hosted chip at the honest tuple is the package's 309 chip. -/
theorem pkgComputeChipAt309_honest (G : Nock.RedTeam.Batch992.HgoodFill P) :
    Unhosted309.pkgComputeChipAt309 P (forget12 (Pkg12.honestTuple12 P)) =
      Unhosted309.ProductionNamedComputeRAP309 P.optimized.family.problem.cfg.compRows_pos
        P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
        P.optimized.computePublic P.optimized.orbit := by
  show Unhosted309.ProductionNamedComputeRAP309 P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis
      (DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple)
      (P.familyComputePublic P.honestTuple) P.optimized.orbit = _
  rw [G.hchalC, Nock.RedTeam.Batch992.familyComputePublic_honest G]

/-- **The honest 309 trace is accepted by the un-hosted compute chip at the honest tuple.** -/
theorem compute309_accepted_of (G : Nock.RedTeam.Batch992.HgoodFill P)
    (hbasis : FormRBasis P.optimized.basis) :
    RAP.SatisfiesWithPreprocessing (Unhosted309.pkgComputeChipAt309 P (forget12 (Pkg12.honestTuple12 P)))
      (canonical309 P) := by
  have h := Unhosted309.canonical_satisfies309 P.optimized.sampled P.optimized.computeObligations
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit P.optimized.computeAdjacentOrbit
    P.optimized.computeChallengePins P.optimized.computePublicPins P.optimized.computeRequestsPins
    P.optimized.computeLineOrigin P.optimized.computeWalkOrder G.hax hbasis G.hwidth
  show RAP.SatisfiesWithPreprocessing (Unhosted309.ProductionNamedComputeRAP309
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
      (DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple)
      (P.familyComputePublic P.honestTuple) P.optimized.orbit) (canonical309 P)
  rw [G.hchalC, Nock.RedTeam.Batch992.familyComputePublic_honest G]
  exact h

end AnyPackage

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




/-- No identity `mwa = α` is assumed or used. -/
theorem gen_honest_accepted309
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
    (cwa mwa wg : K) (mef : K)
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
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
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
    PartAStaged.AcceptanceAt309 (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows) (canonical309 (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows))
      (canonicalMemoryTrace (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows)) (Pkg12.honestTuple12 (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows)) := by
  have G : Nock.RedTeam.Batch992.HgoodFill (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows) :=
    Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq hresp
      hcard cwa mwa wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  exact ⟨compute309_accepted_of _ G (compilerBasis_formR (F := F) (K := K) hK),
    (gen_honest_accepted12 stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl
      hmore hord hordM hrows hF hsB hfB hG hp64).2⟩

end Generated

end

end Nock.RedTeam.Batch1431

#print axioms Nock.NockVMROM.Thm54.PartAStaged.staged_false_acceptance_bound12
#print axioms Nock.NockVMROM.Thm54.PartAStaged.staged_consumed_card_le
#print axioms Nock.NockVMROM.Thm54.PartAStaged.staged_consumed_probability_le
#print axioms Nock.NockVMROM.Thm54.PartAStaged.complete_false_acceptance_bound_of_staged12
#print axioms Nock.NockVMROM.Thm54.PartAStaged.strategy_staged
#print axioms Nock.NockVMROM.Thm54.PartAStaged.consumedFailureEvent12_roundLocal
#print axioms Nock.RedTeam.Batch1431.h22_card
#print axioms Nock.RedTeam.Batch1431.h22_same_bound
#print axioms Nock.RedTeam.Batch1431.compute309_accepted_of
#print axioms Nock.RedTeam.Batch1431.gen_honest_accepted309
