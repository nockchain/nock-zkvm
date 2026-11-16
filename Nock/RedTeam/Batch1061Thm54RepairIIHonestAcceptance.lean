/-
  Nock/RedTeam/Batch1061Thm54RepairIIHonestAcceptance.lean

  Section A, at ANY package: the honest-tuple memory chalVal agrees with the package's off the
  slot-2 block (`memoryChalVal_agree_off_slot2`) from `hα : alphaM honestTuple = memoryWalkAlpha`
  (the (ii) identity) plus the three table-challenge identities (slots `0`, `1`, `8`) and the raw
  slot zeros; slots `4..7` come from the honest tuple's own definition and the coordinate pins.
  With `Batch1060.namedFinalMemoryRAP_congr` that is `memoryChipAt honestTuple = memoryChip`
  WITHOUT `hchalM` (`memoryChipAt_honest_of_readSet`), so the canonical memory trace is accepted
  (`memory_accepted_of`).

  Section B, at the generated package: `genPkg` is `Batch993.hgoodFill_generated`'s package at
  `mwa := α`, `memoryScalarChallenge := 0` (what the chain passes).  `gen_honest_accepted` is
  `DeployedAcceptanceAt genPkg genPkg.honestTuple (QcH genPkg) (QmH genPkg)` -- the carried
  honest non-vacuity receipt the adjudication said must wait on (ii).  Its binders are
  `hgoodFill_generated`'s (the chain's own), with `hordM` now stated at `α`; the chain discharges
  it from the second conjunct of the signed §1 `hwin` (`Batch1063.hordM_of_window`; in production,
  `TraceGen.memRowsL_le_orderOf_of_shape` at the 18 chain discharges).  Negative control: `Batch1211`.
-/
import Nock.RedTeam.Batch993Thm54HgoodGenerated
import Nock.RedTeam.Batch1060Thm54RepairIIMemoryReadSet
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1061

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
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## A. At any package -/

section AnyPackage

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Coordinate form of a coordinate pin. -/
theorem chal_coord_of_pin (b : Basis (Fin 3) F K) (cv : ℕ → F) (q : ℕ) (X : K)
    (h : (∑ k : Fin 3, cv (6 + 3 * q + (k : ℕ)) • b k) = X) (k : Fin 3) :
    cv (6 + 3 * q + (k : ℕ)) = coord b X k := by
  rw [← h]
  exact (coord_sum_smul b (fun i : Fin 3 => cv (6 + 3 * q + (i : ℕ))) k).symm

theorem familyMemoryPublic_honest_of_alpha
    (hα : alphaM P.honestTuple.1 = P.optimized.family.memoryWalkAlpha) :
    P.familyMemoryPublic P.honestTuple = P.optimized.memoryPublic :=
  DeployedChipFamily.memoryPublicOfTuple_eq_pkg_of_alpha P.optimized.basis
    P.optimized.verifier.raw.claim P.optimized.family P.optimized.sampled
    P.optimized.memoryChallenge P.optimized.memoryPublic P.honestTuple
    P.optimized.memoryCoordinatePins hα

/-- Slot-wise agreement of the honest-tuple chalVal with the package's, every `𝕂` slot but `2`. -/
theorem slot_agree (q k : ℕ) (hq9 : q < 9) (hk3 : k < 3) (hq2 : q ≠ 2)
    (hα : alphaM P.honestTuple.1 = P.optimized.family.memoryWalkAlpha)
    (h0 : nprSeed P.honestTuple.1 =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 0)
    (h1 : (0 : K) =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 1)
    (h8 : P.objects.cfg.challenges.lam =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 8) :
    coord P.optimized.basis (DeployedChipFamily.memoryKOfTuple P.honestTuple q) ⟨k, hk3⟩ =
      P.optimized.memoryChallenge (6 + 3 * q + k) := by
  have pins := P.optimized.memoryCoordinatePins
  interval_cases q
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 0 _
      (pins.memoryChallenge ⟨0, by decide⟩) ⟨k, hk3⟩]
    simp only [DeployedChipFamily.memoryKOfTuple]
    rw [h0]
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 1 _
      (pins.memoryChallenge ⟨1, by decide⟩) ⟨k, hk3⟩]
    simp only [DeployedChipFamily.memoryKOfTuple]
    rw [h1]
  · exact absurd rfl hq2
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 3 _
      pins.walkChallenge ⟨k, hk3⟩]
    simp only [DeployedChipFamily.memoryKOfTuple]
    rw [hα]
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 4 _
      pins.sampledGamma ⟨k, hk3⟩]
    rfl
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 5 _
      pins.sampledPole ⟨k, hk3⟩]
    rfl
  · exact coord_sum_smul P.optimized.basis
      (fun i : Fin 3 => P.optimized.memoryChallenge (6 + 3 * 6 + (i : ℕ))) ⟨k, hk3⟩
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 7 _
      pins.walkGamma ⟨k, hk3⟩, P.memoryKOfTuple_honest_walkGamma]
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 8 _
      pins.sampledLambda ⟨k, hk3⟩]
    simp only [DeployedChipFamily.memoryKOfTuple]
    rw [← h8]
    rfl

/-- **The honest-tuple memory chalVal agrees with the package's off the slot-2 block.** -/
theorem memoryChalVal_agree_off_slot2
    (hα : alphaM P.honestTuple.1 = P.optimized.family.memoryWalkAlpha)
    (h0 : nprSeed P.honestTuple.1 =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 0)
    (h1 : (0 : K) =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 1)
    (h8 : P.objects.cfg.challenges.lam =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 8)
    (hlow : ∀ j, j < 6 → P.optimized.memoryChallenge j = 0)
    (hhigh : ∀ j, 33 ≤ j → P.optimized.memoryChallenge j = 0) :
    ∀ j, ¬ Nock.RedTeam.Batch1060.slot2 j →
      DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple j =
        P.optimized.memoryChallenge j := by
  intro j hj
  by_cases hin : 6 ≤ j ∧ j < 33
  · obtain ⟨hlo, hhi⟩ := hin
    have hq9 : (j - 6) / 3 < 9 := by omega
    have hk3 : (j - 6) % 3 < 3 := Nat.mod_lt _ (by omega)
    have hjeq : 6 + 3 * ((j - 6) / 3) + (j - 6) % 3 = j := by omega
    have hq2 : (j - 6) / 3 ≠ 2 := by
      intro h2
      apply hj
      constructor <;> omega
    have hslot := DeployedChipFamily.memoryChalValOfTuple_slot P.optimized.basis P.honestTuple
      ⟨(j - 6) / 3, hq9⟩ ⟨(j - 6) % 3, hk3⟩
    simp only [Fin.val_mk] at hslot
    rw [hjeq] at hslot
    rw [hslot]
    have := slot_agree P ((j - 6) / 3) ((j - 6) % 3) hq9 hk3 hq2 hα h0 h1 h8
    rw [hjeq] at this
    exact this
  · have hz : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple j = 0 := by
      unfold DeployedChipFamily.memoryChalValOfTuple
      rw [dif_neg hin]
    rw [hz]
    rcases Nat.lt_or_ge j 6 with h6 | h6
    · exact (hlow j h6).symm
    · exact (hhigh j (by omega)).symm

/-- **The deployed memory chip at the honest tuple IS the package's memory chip** once the
publics agree and the chalVals agree off the unread slot-2 block (no `hchalM`). -/
theorem memoryChipAt_honest_of_readSet
    (hpub : P.familyMemoryPublic P.honestTuple = P.optimized.memoryPublic)
    (hagree : ∀ j, ¬ Nock.RedTeam.Batch1060.slot2 j →
      DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple j =
        P.optimized.memoryChallenge j) :
    P.memoryChipAt P.honestTuple = P.memoryChip := by
  simp only [OptimizedFullStrictNockVMROMPackage.memoryChipAt,
    OptimizedFullStrictNockVMROMPackage.memoryChip, DeployedChipFamily.memoryChipAt, hpub]
  exact Nock.RedTeam.Batch1060.namedFinalMemoryRAP_congr _ _ _ _ _ _ _ _ hagree

theorem memory_accepted_of
    (hα : alphaM P.honestTuple.1 = P.optimized.family.memoryWalkAlpha)
    (h0 : nprSeed P.honestTuple.1 =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 0)
    (h1 : (0 : K) =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 1)
    (h8 : P.objects.cfg.challenges.lam =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 8)
    (hlow : ∀ j, j < 6 → P.optimized.memoryChallenge j = 0)
    (hhigh : ∀ j, 33 ≤ j → P.optimized.memoryChallenge j = 0)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt P.honestTuple) (QmH P) := by
  have hM := memoryChipAt_honest_of_readSet P (familyMemoryPublic_honest_of_alpha P hα)
    (memoryChalVal_agree_off_slot2 P hα h0 h1 h8 hlow hhigh)
  have hQM := canonicalMemoryTrace_satisfies P hmore hC
  exact sat_cast hM (memoryChipAt_width P P.honestTuple) (canonicalMemoryTrace P) hQM

theorem compute_accepted_of (G : Nock.RedTeam.Batch992.HgoodFill P)
    (hbasis : FormRBasis P.optimized.basis) :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt P.honestTuple) (QcH P) := by
  have hC := P.computeChipAt_honest_of_chalVal G.hchalC G.hst G.hs G.hf G.he
  have hQC := canonicalComputeTrace_satisfies P G.hax hbasis G.hwidth
  exact sat_cast hC (computeChipAt_width P P.honestTuple) (canonicalComputeTrace P) hQC

end AnyPackage

/-! ## B. At the generated package, after repair (ii) -/

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




/-- The package the `nockCompiles` chain builds after repair (ii): `mwa := α`,
`memoryScalarChallenge := 0` (`Batch993.hgoodFill_generated`'s package at those values). -/
noncomputable def genPkg
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
    (hgenF : GeneratedField.ClaimGenerated K
      (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)).verifier.raw.claim
      (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)).Λ := by claim_generated)
    (hF : GeneratedField.PrimeFieldElems F := by prime_field_elems) :
    OptimizedFullStrictNockVMROMPackage F K hOrb :=
  buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon) hprl hmore hord hordM hrows hgenF hF

/-- **THE PAYOFF.**  At the generated package with the memory walk at `α`, the honest trace pair
is accepted by BOTH family chips at the package's honest tuple. -/
theorem gen_honest_accepted
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
    DeployedAcceptanceAt (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows) (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).honestTuple (QcH (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows)) (QmH (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows)) := by
  have G : Nock.RedTeam.Batch992.HgoodFill (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows) :=
    Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq hresp
      hcard cwa α wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hαeq : chal.α = α := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.α) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  have hβ : chal.β = 0 := by
    have hproj := congrArg (fun inp : MemoryTable.Inputs K => inp.β) hmi
    simpa [ChallengeVector.memoryInputs, memInputs] using hproj
  have hα : alphaM (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).honestTuple.1 = (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.memoryWalkAlpha := by
    show chal.α = α
    exact hαeq
  have h0 : nprSeed (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).honestTuple.1 =
      (exactMemoryRowEnv (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.sampled
        ⟨0, (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.memRows_pos⟩).chal 0 := rfl
  have h1 : (0 : K) =
      (exactMemoryRowEnv (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.sampled
        ⟨0, (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.memRows_pos⟩).chal 1 := by
    show (0 : K) = chal.β
    exact hβ.symm
  have h8 : (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).objects.cfg.challenges.lam =
      (exactMemoryRowEnv (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.sampled
        ⟨0, (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.memRows_pos⟩).chal 8 := by
    have hrow := genExactExecution_memoryRows_lambda (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem _
      (ExactExecution.memoryRowAt_mem (genExactExecution (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
        ⟨0, hmempos⟩)
    exact hrow.symm
  have hlow : ∀ j, j < 6 → (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.memoryChallenge j = 0 := by
    intro j hj
    show BuildableChips.memoryChallenge _ _ j = 0
    unfold BuildableChips.memoryChallenge
    split_ifs <;> first | rfl | omega
  have hhigh : ∀ j, 33 ≤ j → (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.memoryChallenge j = 0 := by
    intro j hj
    show BuildableChips.memoryChallenge _ _ j = 0
    unfold BuildableChips.memoryChallenge
    rw [dif_neg (by omega), if_pos (by omega)]
    unfold BuildableChips.coordinateBlock
    rw [dif_neg (by omega)]
  have hmore' : ∀ i : Fin (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.kMem →
        ((genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          ((genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0 :=
    fun i hi1 hi2 => hmore i hi1 hi2
  exact ⟨compute_accepted_of (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows) G (compilerBasis_formR (F := F) (K := K) hK),
    memory_accepted_of (genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows) hα h0 h1 h8 hlow hhigh hmore' G.hC⟩

end Generated

end

end Nock.RedTeam.Batch1061

#print axioms Nock.RedTeam.Batch1061.memoryChipAt_honest_of_readSet
#print axioms Nock.RedTeam.Batch1061.memory_accepted_of
#print axioms Nock.RedTeam.Batch1061.compute_accepted_of
#print axioms Nock.RedTeam.Batch1061.gen_honest_accepted
