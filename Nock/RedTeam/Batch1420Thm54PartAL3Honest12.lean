/-
  Nock/RedTeam/Batch1420Thm54PartAL3Honest12.lean

  * §A, at ANY package: the memory view of the honest twelve-coin tuple agrees with the package's
    memory chalVal off the unread slot-2 block WITHOUT the repair-(ii) identity `hα` (slot 3 of the
    view IS the family walk coin, by definition), so the canonical memory trace is accepted by the
    twelve-coin chip at `honestTuple12` (`memory_accepted12_of`).
  * §B, at the generated package with the memory walk coin `mwa` FREE (`genPkgW`, i.e. the
    generator walks at `mwa := αW` and stamps at `α`): BOTH chips accept the honest pair at the
    honest twelve-coin tuple (`gen_honest_accepted12`), for every `mwa` satisfying the walk
    conjunct `hordM` (stated at `mwa`).  `Batch1061.gen_honest_accepted` needed `mwa := α`.
  * §C, the negative control at EVERY built package: acceptance of the canonical memory trace by
    the twelve-coin chip at ANY tuple `c` forces `walkAlphaOf c = I.memoryWalkAlpha`
    (`accepted12_forces_walk_coin`); so an honest walk built at `α` (repair (ii)) is REJECTED at
    every tuple with `αW ≠ α` (`walk_at_alpha_rejected12`).  A concrete gate-level instance over
    `ZMod 5` (`concrete_ln1_*`): the slot-9 line gate is nonzero where the slot-3 one vanishes.
-/
import Nock.RedTeam.Batch1061Thm54RepairIIHonestAcceptance
import Nock.RedTeam.Batch994Thm54HonestMemoryAcceptance
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1420

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

/-! ## A. At any package: no `hα` -/

section AnyPackage

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Slot-wise agreement of the memory view of the honest twelve-coin tuple with the package's
memory chalVal, every `𝕂` slot but `2`.  Unlike `Batch1061.slot_agree` there is NO `hα`: slot `3`
of the view is the family walk coin by definition. -/
theorem slot_agree12 (q k : ℕ) (hq9 : q < 9) (hk3 : k < 3) (hq2 : q ≠ 2)
    (h0 : nprSeed P.honestTuple.1 =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 0)
    (h1 : (0 : K) =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 1)
    (h8 : P.objects.cfg.challenges.lam =
      (exactMemoryRowEnv P.optimized.sampled
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).chal 8) :
    coord P.optimized.basis
        (DeployedChipFamily.memoryKOfTuple (walkView11 (Pkg12.honestTuple12 P)) q) ⟨k, hk3⟩ =
      P.optimized.memoryChallenge (6 + 3 * q + k) := by
  have pins := P.optimized.memoryCoordinatePins
  interval_cases q
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 0 _
      (pins.memoryChallenge ⟨0, by decide⟩) ⟨k, hk3⟩]
    exact congrArg (fun x => coord P.optimized.basis x ⟨k, hk3⟩) h0
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 1 _
      (pins.memoryChallenge ⟨1, by decide⟩) ⟨k, hk3⟩]
    exact congrArg (fun x => coord P.optimized.basis x ⟨k, hk3⟩) h1
  · exact absurd rfl hq2
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 3 _
      pins.walkChallenge ⟨k, hk3⟩]
    rfl
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 4 _
      pins.sampledGamma ⟨k, hk3⟩]
    rfl
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 5 _
      pins.sampledPole ⟨k, hk3⟩]
    rfl
  · exact coord_sum_smul P.optimized.basis
      (fun i : Fin 3 => P.optimized.memoryChallenge (6 + 3 * 6 + (i : ℕ))) ⟨k, hk3⟩
  · have hg : DeployedChipFamily.memoryKOfTuple (walkView11 (Pkg12.honestTuple12 P)) 7 =
        P.optimized.family.walkGamma := P.memoryKOfTuple_honest_walkGamma
    rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 7 _
      pins.walkGamma ⟨k, hk3⟩, hg]
  · rw [chal_coord_of_pin P.optimized.basis P.optimized.memoryChallenge 8 _
      pins.sampledLambda ⟨k, hk3⟩]
    exact congrArg (fun x => coord P.optimized.basis x ⟨k, hk3⟩) h8

theorem memoryChalVal_view_agree_off_slot2
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
      DeployedChipFamily.memoryChalValOfTuple P.optimized.basis (walkView11 (Pkg12.honestTuple12 P)) j =
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
    have hslot := DeployedChipFamily.memoryChalValOfTuple_slot P.optimized.basis
      (walkView11 (Pkg12.honestTuple12 P)) ⟨(j - 6) / 3, hq9⟩ ⟨(j - 6) % 3, hk3⟩
    simp only [Fin.val_mk] at hslot
    rw [hjeq] at hslot
    rw [hslot]
    have := slot_agree12 P ((j - 6) / 3) ((j - 6) % 3) hq9 hk3 hq2 h0 h1 h8
    rw [hjeq] at this
    exact this
  · have hz : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis
        (walkView11 (Pkg12.honestTuple12 P)) j = 0 := by
      unfold DeployedChipFamily.memoryChalValOfTuple
      rw [dif_neg hin]
    rw [hz]
    rcases Nat.lt_or_ge j 6 with h6 | h6
    · exact (hlow j h6).symm
    · exact (hhigh j (by omega)).symm

/-- The landed memory chip at the memory view of the honest twelve-coin tuple IS the package's
memory chip (read-set congruence, `Batch1060.namedFinalMemoryRAP_congr`). -/
theorem memoryChipAt_view_honest_of_readSet
    (hagree : ∀ j, ¬ Nock.RedTeam.Batch1060.slot2 j →
      DeployedChipFamily.memoryChalValOfTuple P.optimized.basis (walkView11 (Pkg12.honestTuple12 P)) j =
        P.optimized.memoryChallenge j) :
    P.memoryChipAt (walkView11 (Pkg12.honestTuple12 P)) = P.memoryChip := by
  have hpub : P.familyMemoryPublic (walkView11 (Pkg12.honestTuple12 P)) = P.optimized.memoryPublic :=
    Pkg12.familyMemoryPublic12_honest P
  simp only [OptimizedFullStrictNockVMROMPackage.memoryChipAt,
    OptimizedFullStrictNockVMROMPackage.memoryChip, DeployedChipFamily.memoryChipAt, hpub]
  exact Nock.RedTeam.Batch1060.namedFinalMemoryRAP_congr _ _ _ _ _ _ _ _ hagree

/-- **At any package, the canonical memory trace is accepted by the twelve-coin memory chip at the
honest twelve-coin tuple** — with no relation between the walk coin and the timestamp `α`. -/
theorem memory_accepted12_of
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
    RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 P (Pkg12.honestTuple12 P))
      (Pkg12.familyQm12 P (Pkg12.honestTuple12 P) (canonicalMemoryTrace P)) := by
  have hM := memoryChipAt_view_honest_of_readSet P
    (memoryChalVal_view_agree_off_slot2 P h0 h1 h8 hlow hhigh)
  have hQM := canonicalMemoryTrace_satisfies P hmore hC
  have h' : RAP.SatisfiesWithPreprocessing (P.memoryChipAt (walkView11 (Pkg12.honestTuple12 P)))
      (P.familyQm (walkView11 (Pkg12.honestTuple12 P)) (canonicalMemoryTrace P)) :=
    sat_cast hM (FamilyEnvCore.memoryChipAt_width P.optimized (walkView11 (Pkg12.honestTuple12 P)))
      (canonicalMemoryTrace P) hQM
  exact (Pkg12.memoryChipAt12_satisfies_iff P _ _).2 h'

end AnyPackage

/-! ## B. At the generated package with the memory walk coin FREE -/

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




/-- `Batch1061.genPkg` with the memory walk coin `mwa` FREE (the generator walks at `mwa := αW`,
stamps at `α`; zero `Gen.lean` edits: `mwa` is `inputsOfCarrier`'s own parameter). -/
noncomputable def genPkgW
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
    (hgenF : GeneratedField.ClaimGenerated K
      (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)).verifier.raw.claim
      (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)).Λ := by claim_generated)
    (hF : GeneratedField.PrimeFieldElems F := by prime_field_elems) :
    OptimizedFullStrictNockVMROMPackage F K hOrb :=
  buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg (fun _ => 0) mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg (fun _ => 0) mef hinterCard hhon) hprl hmore hord hordM hrows hgenF hF

/-- **Honest acceptance with `αW ≠ α` exercised.**  At the generated package with the memory walk
built at a FREE coin `mwa` (any `αW` satisfying the walk conjunct `hordM`, stated at `mwa`), the
honest trace pair is accepted at the honest twelve-coin tuple: the compute chip at
`forget12 honestTuple12 = honestTuple` (timestamp `α`), the twelve-coin memory chip at
`honestTuple12` (walk coin `mwa` at slot `9`).  No identity `mwa = α` is assumed or used. -/
theorem gen_honest_accepted12
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
    RAP.SatisfiesWithPreprocessing ((genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).computeChipAt (forget12 (Pkg12.honestTuple12 (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows)))) (QcH (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows)) ∧
      RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows) (Pkg12.honestTuple12 (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows)))
        (Pkg12.familyQm12 (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows) (Pkg12.honestTuple12 (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows)) (canonicalMemoryTrace (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows))) := by
  have G : Nock.RedTeam.Batch992.HgoodFill (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows) :=
    Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq hresp
      hcard cwa mwa wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hαeq : chal.α = α := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.α) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  have hβ : chal.β = 0 := by
    have hproj := congrArg (fun inp : MemoryTable.Inputs K => inp.β) hmi
    simpa [ChallengeVector.memoryInputs, memInputs] using hproj
  have h0 : nprSeed (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).honestTuple.1 =
      (exactMemoryRowEnv (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.sampled
        ⟨0, (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.memRows_pos⟩).chal 0 := rfl
  have h1 : (0 : K) =
      (exactMemoryRowEnv (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.sampled
        ⟨0, (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.memRows_pos⟩).chal 1 := by
    show (0 : K) = chal.β
    exact hβ.symm
  have h8 : (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).objects.cfg.challenges.lam =
      (exactMemoryRowEnv (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.sampled
        ⟨0, (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.memRows_pos⟩).chal 8 := by
    have hrow := genExactExecution_memoryRows_lambda (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem _
      (ExactExecution.memoryRowAt_mem (genExactExecution (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
        ⟨0, hmempos⟩)
    exact hrow.symm
  have hlow : ∀ j, j < 6 → (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.memoryChallenge j = 0 := by
    intro j hj
    show BuildableChips.memoryChallenge _ _ j = 0
    unfold BuildableChips.memoryChallenge
    split_ifs <;> first | rfl | omega
  have hhigh : ∀ j, 33 ≤ j → (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.memoryChallenge j = 0 := by
    intro j hj
    show BuildableChips.memoryChallenge _ _ j = 0
    unfold BuildableChips.memoryChallenge
    rw [dif_neg (by omega), if_pos (by omega)]
    unfold BuildableChips.coordinateBlock
    rw [dif_neg (by omega)]
  have hmore' : ∀ i : Fin (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.cfg.kMem →
        ((genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          ((genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows).optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0 :=
    fun i hi1 hi2 => hmore i hi1 hi2
  exact ⟨compute_accepted_of (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows) G (compilerBasis_formR (F := F) (K := K) hK),
    memory_accepted12_of (genPkgW (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg mef hinterCard hhon hprl hmore hord hordM hrows) h0 h1 h8 hlow hhigh hmore' G.hC⟩

end Generated
/-! ## C. The negative control: a walk built at `α` is rejected wherever `αW ≠ α` -/

section NegativeControl

variable (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
  (hzero : I.computeChallenges =
    (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
  (hprl : RowLayout.PairedRecordLayout E.exec) (hmore : BuildableAxisWitness.LaterSeedZeros E)
  (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
  (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
  (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
  (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
  (hF : GeneratedField.PrimeFieldElems F)

local notation "PB" => buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF

set_option maxRecDepth 20000 in
/-- **At every built package: acceptance of the canonical memory trace by the twelve-coin memory
chip at ANY twelve-coin tuple `c` forces `c`'s walk coin to be the coin the honest walk was built
at.**  (Mechanism: the slot-9 line gate `first · (ln − chal 9)` against the canonical
`ln(row 0) = I.memoryWalkAlpha`, `Batch994.canonical_ln_row0`, through the transport.) -/
theorem accepted12_forces_walk_coin (c : OptimizedProductionChallengeTuple12 K F)
    (hsat : RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 PB c)
      (Pkg12.familyQm12 PB c (canonicalMemoryTrace PB))) :
    walkAlphaOf c = I.memoryWalkAlpha := by
  have h2 := (Pkg12.memoryChipAt12_satisfies_iff PB c _).1 hsat
  have h := MemoryWalkDeployed.walkLn_row0 PB (walkView11 c) _ h2
  have hq : MemoryWalkDeployed.Qmh PB (walkView11 c)
      ((PB).familyQm (walkView11 c) (canonicalMemoryTrace PB)) = canonicalMemoryTrace PB := by
    funext j
    exact congrArg (canonicalMemoryTrace PB) (Fin.ext (by
      simp [MemoryWalkDeployed.Qmh, FamilyMemoryRows.honestQm, FamilyEnvCore.familyQm]))
  simp only [MemoryWalkDeployed.envK, hq] at h
  have hc := Batch994.canonical_ln_row0 E I R hzero hprl hmore hord hordM hrows hgenF hF
  have heq : (FamilyComputeRows.memorySourceEnvAt PB (walkView11 c) (canonicalMemoryTrace PB)
        (MemoryWalkDeployed.firstMem PB)).trace MemoryWalkLabel.lnRole =
      ((PB).memorySourceEnv (canonicalMemoryTrace PB)
        ⟨0, (PB).optimized.family.problem.cfg.memRows_pos⟩).trace MemoryWalkLabel.lnRole := rfl
  rw [heq, hc] at h
  exact h.symm

/-- **The repair-(ii) regression check.**  If the honest walk is built at the timestamp coin
(`I.memoryWalkAlpha = α`, what repair (ii) does), the twelve-coin memory chip REJECTS the
canonical memory trace at every tuple whose walk coin `αW ≠ α`. -/
theorem walk_at_alpha_rejected12 (hwalk : I.memoryWalkAlpha = E.cfg.challenges.α)
    (c : OptimizedProductionChallengeTuple12 K F) (hne : walkAlphaOf c ≠ E.cfg.challenges.α) :
    ¬ RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 PB c)
      (Pkg12.familyQm12 PB c (canonicalMemoryTrace PB)) := fun hs =>
  hne ((accepted12_forces_walk_coin E I R hzero hprl hmore hord hordM hrows hgenF hF c hs).trans
    hwalk)

/-- The instance at the honest landed tuple extended by any `αW ≠ α`. -/
theorem walk_at_alpha_rejected12_honest (hwalk : I.memoryWalkAlpha = E.cfg.challenges.α)
    (αW : K) (hne : αW ≠ E.cfg.challenges.α) :
    ¬ RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 PB (extend12 (PB).honestTuple αW))
      (Pkg12.familyQm12 PB (extend12 (PB).honestTuple αW) (canonicalMemoryTrace PB)) :=
  walk_at_alpha_rejected12 E I R hzero hprl hmore hord hordM hrows hgenF hF hwalk _ hne

end NegativeControl

/-! ### The concrete gate-level instance (`ZMod 5`) -/

section Concrete

open MixedCoordinateCompiler OptimizedMemoryGateBasis CoordinateCompiler Nock.Reified

/-- The slot-9 line gate, evaluated. -/
theorem ln1Gate12_eval {F K : Type} [Field F] [Field K] [Algebra F K] (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (bcur 4)
        (MixedExpr.ofExpr (Nock.Reified.Trans.walkLn1.subst walkBoundarySubst12)) : MixedExpr F).eval
        eK eF =
      algebraMap F K (eF.trace 4) * (eK.trace 31 - eK.chal 9) := by
  rw [MixedExpr.eval, MixedExpr.ofExpr_eval]
  simp [Nock.Reified.Trans.walkLn1, Nock.Reified.tc, Nock.Reified.chl, Nock.Reified.Expr.subst,
    Nock.Reified.Expr.eval, walkBoundarySubst12, extVar, CoeffExpr.eval, bcur]

/-- The landed (slot-3) line gate, evaluated. -/
theorem ln1Gate_eval {F K : Type} [Field F] [Field K] [Algebra F K] (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (bcur 4)
        (MixedExpr.ofExpr (Nock.Reified.Trans.walkLn1.subst walkBoundarySubst)) : MixedExpr F).eval
        eK eF =
      algebraMap F K (eF.trace 4) * (eK.trace 31 - eK.chal 3) := by
  rw [MixedExpr.eval, MixedExpr.ofExpr_eval]
  simp [Nock.Reified.Trans.walkLn1, Nock.Reified.tc, Nock.Reified.chl, Nock.Reified.Expr.subst,
    Nock.Reified.Expr.eval, walkBoundarySubst, extVar, CoeffExpr.eval, bcur]

/-- A first memory row whose walk line is `α = 2`, with the timestamp-slot coin `chal 3 = 2 = α`
and the walk-slot coin `chal 9 = 3 = αW ≠ α`. -/
def concreteEnvK : Env (ZMod 5) :=
  ⟨fun i => if i = 31 then 2 else 0, fun _ => 0, fun i => if i = 9 then 3 else if i = 3 then 2 else 0,
    fun _ => 0⟩

def concreteEnvF : Env (ZMod 5) := ⟨fun i => if i = 4 then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- **Concrete control, twelve-coin chip**: the honest line built at `α = 2` violates the slot-9
line gate when `αW = 3`. -/
theorem concrete_ln1_rejected12 :
    (MixedExpr.Scale (bcur 4)
        (MixedExpr.ofExpr (Nock.Reified.Trans.walkLn1.subst walkBoundarySubst12)) :
          MixedExpr (ZMod 5)).eval concreteEnvK concreteEnvF ≠ 0 := by
  rw [ln1Gate12_eval]
  simp only [concreteEnvK, concreteEnvF]
  decide

/-- **Concrete control, landed chip**: the same row satisfies the landed slot-3 line gate (it reads
`chal 3 = α`), which is why repair (ii)'s honest walk passed there. -/
theorem concrete_ln1_accepted_landed :
    (MixedExpr.Scale (bcur 4)
        (MixedExpr.ofExpr (Nock.Reified.Trans.walkLn1.subst walkBoundarySubst)) :
          MixedExpr (ZMod 5)).eval concreteEnvK concreteEnvF = 0 := by
  rw [ln1Gate_eval]
  simp only [concreteEnvK, concreteEnvF]
  decide

end Concrete

end

end Nock.RedTeam.Batch1420

#print axioms Nock.RedTeam.Batch1420.memory_accepted12_of
#print axioms Nock.RedTeam.Batch1420.gen_honest_accepted12
#print axioms Nock.RedTeam.Batch1420.accepted12_forces_walk_coin
#print axioms Nock.RedTeam.Batch1420.walk_at_alpha_rejected12
#print axioms Nock.RedTeam.Batch1420.walk_at_alpha_rejected12_honest
#print axioms Nock.RedTeam.Batch1420.concrete_ln1_rejected12
#print axioms Nock.RedTeam.Batch1420.concrete_ln1_accepted_landed
