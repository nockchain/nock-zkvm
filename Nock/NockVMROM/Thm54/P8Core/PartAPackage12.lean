/-
  Nock/NockVMROM/Thm54/P8Core/PartAPackage12.lean

  Below the statement
  (imports the Defs half only).

  * `familyMemoryPublic12 P`, `memoryChipAt12 P`, `familyQm12 P`, `computeChipAt12 P`
    (`= computeChipAt ∘ forget12`: the compute chip reads the timestamp `alphaM`, untouched under
    W-a), `OptimizedProductionAcceptanceAt12 P`.
  * `honestTuple12 P := extend12 P.honestTuple memoryWalkAlpha`: the binder `αW` placed at the
    walk coordinate, the timestamp `α` at `alphaM` — two independent coordinates.
  * `memoryChipAt12_honest_of_chalVal` (Defs `memoryChipAt_honest_of_chalVal`, re-proved at slot
    `9`): no identity `alphaM honestTuple = memoryWalkAlpha` is needed any more.
  * **C2.**  `αW` is threaded as its OWN argument, only to `memoryWalkAlpha`:
    `atJointCoinsW C ω αW`, `atCoinsW D αC γ αW`.  The P8 event union is untouched by
    definition (`p8SlotEv12_iff`, `p8SlotEv12_walk_free`): the P8 slot reads `c.1` and `λ` only.

  -- the paper
-/
import Nock.NockVMROM.Thm54.P8Core.OptimizedFailureEventEv
import Nock.NockVMROM.Thm54.P8Core.PartAMemoryChip12

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.PartA12

open Nock Nock.Framework Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. C2: `αW` as its own argument, only to `memoryWalkAlpha` -/

section C2

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

/-- **The P8 seed commitment at the joint coins and a SEPARATE walk coin `αW`.**  Identical to
`RawP8SeedCommitment.atJointCoins C ω` except `memoryWalkAlpha := αW`; in particular the problem
(and so the timestamp `alphaM ω`, `specializedProblem`'s slot) is copied unchanged. -/
def atJointCoinsW {claim : P8PublicClaim} {z : K}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p)
    (ω : JointCoins K) (αW : K) : RawPlusIOSegmentedFamily F K :=
  { C.atJointCoins ω with memoryWalkAlpha := αW }

@[simp] theorem atJointCoinsW_problem {claim : P8PublicClaim} {z : K}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) (αW : K) :
    (atJointCoinsW C ω αW).problem = (C.atJointCoins ω).problem := rfl

@[simp] theorem atJointCoinsW_memoryWalkAlpha {claim : P8PublicClaim} {z : K}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) (αW : K) :
    (atJointCoinsW C ω αW).memoryWalkAlpha = αW := rfl

theorem atJointCoinsW_computeWalkAlpha {claim : P8PublicClaim} {z : K}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) (αW : K) :
    (atJointCoinsW C ω αW).computeWalkAlpha = alphaC ω := rfl

theorem atJointCoinsW_walkGamma {claim : P8PublicClaim} {z : K}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) (αW : K) :
    (atJointCoinsW C ω αW).walkGamma = gamma ω := rfl

/-- At `αW := alphaM ω` it IS the landed `atJointCoins` (the repair-(ii) identification). -/
theorem atJointCoinsW_alphaM {claim : P8PublicClaim} {z : K}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) :
    atJointCoinsW C ω (alphaM ω) = C.atJointCoins ω := rfl

open TemplateRawJointSoundness in
/-- **The `(z, alphaM)` family at the walk coins with a SEPARATE walk coin `αW`.**  The problem is
`specializedProblem T z hz alphaM lmb` — the timestamp `alphaM`, unchanged; `αW` reaches
`memoryWalkAlpha` only. -/
def atCoinsW {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma αW : K) :
    RawPlusIOSegmentedFamily F K :=
  { D.atCoins alphaC gamma with memoryWalkAlpha := αW }

open TemplateRawJointSoundness in
/-- The timestamp coin of `atCoinsW` is `alphaM`, not `αW` (C2: no second view feeds `αW` into
`specializedProblem`'s timestamp slot). -/
@[simp] theorem atCoinsW_tableAlpha
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma αW : K) :
    (atCoinsW D alphaC gamma αW).cfg.challenges.α = alphaM := rfl

open TemplateRawJointSoundness in
@[simp] theorem atCoinsW_problem
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma αW : K) :
    (atCoinsW D alphaC gamma αW).problem = specializedProblem T z hz alphaM lmb := rfl

open TemplateRawJointSoundness in
@[simp] theorem atCoinsW_memoryWalkAlpha
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma αW : K) :
    (atCoinsW D alphaC gamma αW).memoryWalkAlpha = αW := rfl

open TemplateRawJointSoundness in
theorem atCoinsW_alphaM
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma : K) :
    atCoinsW D alphaC gamma alphaM = D.atCoins alphaC gamma := rfl

end C2

/-! ## 2. The twelve-coin objects at a package -/

namespace Pkg12

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Twelve-coin family memory publics: slots `6..8` are `αW ^ kMem`. -/
abbrev familyMemoryPublic12 (c : OptimizedProductionChallengeTuple12 K F) : ℕ → F :=
  memoryPublicOfTuple12 P.optimized.basis P.optimized.verifier.raw.claim
    P.optimized.family.problem.cfg.kMem P.optimized.memoryPublic c

/-- **The twelve-coin deployed memory chip at a tuple** (walk coin at memory slot `9`). -/
abbrev memoryChipAt12 (c : OptimizedProductionChallengeTuple12 K F) : FixedPreprocessingRAP F :=
  DeployedChipFamily12.memoryChipAt12 P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis (familyMemoryPublic12 P c)
    P.optimized.orbit c P.optimized.family.problem.cfg.kMem

/-- The compute chip at a twelve-coin tuple: the landed compute chip at `forget12 c` (it reads
the timestamp `alphaM c.1` at compute slot `0`; W-a leaves it untouched). -/
abbrev computeChipAt12 (c : OptimizedProductionChallengeTuple12 K F) : FixedPreprocessingRAP F :=
  P.computeChipAt (forget12 c)

theorem familyMemoryPublic12_eq_view (c : OptimizedProductionChallengeTuple12 K F) :
    familyMemoryPublic12 P c = P.familyMemoryPublic (walkView11 c) := rfl

theorem memoryChipAt12_width (c : OptimizedProductionChallengeTuple12 K F) :
    (memoryChipAt12 P c).rap.w = P.memoryChip.rap.w := by
  have hc : (memoryChipAt12 P c).rap.w = 205 := namedFinalMemoryRAP12_w _ _ _ _ _ _ _
  have h0 : P.memoryChip.rap.w = 205 :=
    (finalMemoryRAP_fingerprint P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
      P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).1
  exact hc.trans h0.symm

/-- Reindex a package-width memory trace at the twelve-coin chip's width. -/
def familyQm12 (c : OptimizedProductionChallengeTuple12 K F)
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Fin (memoryChipAt12 P c).rap.w → F[X] :=
  fun j => Qm (Fin.cast (memoryChipAt12_width P c) j)

/-- **Package transport.**  The twelve-coin memory chip at `c` accepts the package trace `Qm` iff
the landed memory chip at the memory view `walkView11 c` does. -/
theorem memoryChipAt12_satisfies_iff (c : OptimizedProductionChallengeTuple12 K F)
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (memoryChipAt12 P c) (familyQm12 P c Qm) ↔
      RAP.SatisfiesWithPreprocessing (P.memoryChipAt (walkView11 c))
        (P.familyQm (walkView11 c) Qm) :=
  DeployedChipFamily12.memoryChipAt12_satisfies_iff P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis (familyMemoryPublic12 P c) P.optimized.orbit c
    P.optimized.family.problem.cfg.kMem (familyQm12 P c Qm) (P.familyQm (walkView11 c) Qm)
    (fun _ _ _ => congrArg Qm (Fin.ext (by simp only [Fin.val_cast]; rfl)))

/-- **Acceptance at the twelve-coin family chips.** -/
structure OptimizedProductionAcceptanceAt12
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F) : Prop where
  compute_satisfies :
    RAP.SatisfiesWithPreprocessing (computeChipAt12 P c) (P.familyQc (forget12 c) Qc)
  memory_satisfies :
    RAP.SatisfiesWithPreprocessing (memoryChipAt12 P c) (familyQm12 P c Qm)

/-- Twelve-coin acceptance is landed compute acceptance at `forget12 c` and landed memory
acceptance at `walkView11 c`. -/
theorem acceptanceAt12_iff (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) (c : OptimizedProductionChallengeTuple12 K F) :
    OptimizedProductionAcceptanceAt12 P Qc Qm c ↔
      RAP.SatisfiesWithPreprocessing (P.computeChipAt (forget12 c)) (P.familyQc (forget12 c) Qc) ∧
        RAP.SatisfiesWithPreprocessing (P.memoryChipAt (walkView11 c))
          (P.familyQm (walkView11 c) Qm) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (memoryChipAt12_satisfies_iff P c Qm).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (memoryChipAt12_satisfies_iff P c Qm).2 h2⟩

/-! ## 3. The honest twelve-coin tuple -/

/-- **The honest twelve-coin tuple**: the landed honest tuple (timestamp `α` at `alphaM`) with the
walk binder `αW := memoryWalkAlpha` placed at the walk coordinate. -/
def honestTuple12 : OptimizedProductionChallengeTuple12 K F :=
  extend12 P.honestTuple P.optimized.family.memoryWalkAlpha

@[simp] theorem forget12_honestTuple12 : forget12 (honestTuple12 P) = P.honestTuple := rfl

/-- The timestamp coordinate of the honest twelve-coin tuple is the objects' `α`. -/
theorem honestTuple12_timestamp : alphaM (honestTuple12 P).1 = P.objects.cfg.challenges.α := rfl

/-- The walk coordinate of the honest twelve-coin tuple is the family's walk coin. -/
theorem honestTuple12_walk :
    walkAlphaOf (honestTuple12 P) = P.optimized.family.memoryWalkAlpha := rfl

/-- At the memory view of the honest twelve-coin tuple, the walk slot carries the family's walk
coin BY DEFINITION — the identity repair (ii) had to force by `mwa := α`. -/
theorem honestTuple12_view_alphaM :
    alphaM (walkView11 (honestTuple12 P)).1 = P.optimized.family.memoryWalkAlpha := rfl

/-- `memoryKOfTuple12` at the honest twelve-coin tuple: slot `9` is the family's walk coin. -/
theorem memoryKOfTuple12_honest_walkAlpha :
    memoryKOfTuple12 (honestTuple12 P) 9 = P.optimized.family.memoryWalkAlpha := rfl

theorem memoryKOfTuple12_honest_walkGamma :
    memoryKOfTuple12 (honestTuple12 P) 7 = P.optimized.family.walkGamma := by
  simp [memoryKOfTuple12, honestTuple12, extend12,
    OptimizedFullStrictNockVMROMPackage.honestTuple,
    OptimizedFullStrictNockVMROMPackage.honestProductionTuple,
    OptimizedFullStrictNockVMROMPackage.honestJointCoins, gamma]

/-- The twelve-coin memory publics at the honest twelve-coin tuple ARE the package map, with no
hypothesis at all (the walk pin `walkInitialCount` and `hα := rfl`). -/
theorem familyMemoryPublic12_honest :
    familyMemoryPublic12 P (honestTuple12 P) = P.optimized.memoryPublic :=
  DeployedChipFamily.memoryPublicOfTuple_eq_pkg_of_alpha P.optimized.basis
    P.optimized.verifier.raw.claim P.optimized.family P.optimized.sampled
    P.optimized.memoryChallenge P.optimized.memoryPublic (walkView11 (honestTuple12 P))
    P.optimized.memoryCoordinatePins rfl

/-- The landed memory chip at the honest memory view is the package's memory chip once the
chalVal agrees. -/
theorem memoryChipAt_view_honest_of_chalVal
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis (walkView11 (honestTuple12 P)) =
      P.optimized.memoryChallenge) :
    P.memoryChipAt (walkView11 (honestTuple12 P)) = P.memoryChip := by
  have hpub : P.familyMemoryPublic (walkView11 (honestTuple12 P)) = P.optimized.memoryPublic :=
    familyMemoryPublic12_honest P
  simp only [OptimizedFullStrictNockVMROMPackage.memoryChipAt,
    OptimizedFullStrictNockVMROMPackage.memoryChip, DeployedChipFamily.memoryChipAt, h, hpub]

theorem sat_cast_iff {C₁ C₂ : FixedPreprocessingRAP F} (h : C₁ = C₂)
    (hw : C₁.rap.w = C₂.rap.w) (Q : Fin C₂.rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing C₁ (fun j => Q (Fin.cast hw j)) ↔
      RAP.SatisfiesWithPreprocessing C₂ Q := by
  subst h
  rfl

/-- **`memoryChipAt_honest_of_chalVal`, re-proved at slot `9`.**  At the honest twelve-coin tuple,
once the twelve-coin memory chalVal (read through the slot swap) agrees with the package's, the
twelve-coin chip accepts exactly what the package memory chip accepts.  No identity between the
walk coin and the timestamp `α` is assumed. -/
theorem memoryChipAt12_honest_of_chalVal
    (h12 : memoryChalValOfTuple12 P.optimized.basis (honestTuple12 P) ∘ walkRawSwap =
      P.optimized.memoryChallenge)
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (memoryChipAt12 P (honestTuple12 P)) (familyQm12 P (honestTuple12 P) Qm) ↔
      RAP.SatisfiesWithPreprocessing P.memoryChip Qm := by
  rw [memoryChipAt12_satisfies_iff P]
  have h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis (walkView11 (honestTuple12 P)) =
      P.optimized.memoryChallenge := by
    rw [← memoryChalValOfTuple12_swap]; exact h12
  exact sat_cast_iff (memoryChipAt_view_honest_of_chalVal P h)
    (FamilyEnvCore.memoryChipAt_width P.optimized (walkView11 (honestTuple12 P))) Qm

/-! ## 4. The P8 slot at the twelve-coin tuple: untouched by `αW` (C2) -/

open Classical in
/-- The P8 slot lifted to the twelve-coin tuple as a cylinder. -/
def p8SlotEv12 (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple12 K F) :=
  Finset.univ.filter fun c => forget12 c ∈ OptimizedFailureEventEv.p8SlotEv P Qc Qm

/-- **The P8 event union is untouched by definition**: membership reads the JointCoins block `c.1`
(timestamp `alphaM`, verbatim) and `λ`, at the BUILT strategy, by `Iff.rfl`-level unfolding. -/
theorem p8SlotEv12_iff (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F) :
    c ∈ p8SlotEv12 P Qc Qm ↔
      c.1 ∈ P8EventEv.evFailureUnion (OptimizedFailureEventEv.builtStrategyEv P Qc Qm)
        P.optimized.Λ c.2.2.2.lambda := by
  simp only [p8SlotEv12, Finset.mem_filter, Finset.mem_univ, true_and,
    OptimizedFailureEventEv.mem_p8SlotEv_iff]
  rfl

/-- `αW` does not enter the P8 slot: changing the walk coin preserves membership. -/
theorem p8SlotEv12_walk_free (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) (c : OptimizedProductionChallengeTuple K F) (αW αW' : K) :
    extend12 c αW ∈ p8SlotEv12 P Qc Qm ↔ extend12 c αW' ∈ p8SlotEv12 P Qc Qm := by
  simp only [p8SlotEv12, Finset.mem_filter, Finset.mem_univ, true_and, forget12_extend12]

end Pkg12

end

end Nock.NockVMROM.Thm54.PartA12
