/-
  Nock/RedTeam/Batch407Thm54SeedBoundaryGenericAttack.lean

  **Generic perturbation receipt** (replaces the fixture
  `package73` RAP attack, which does not elaborate: `fullRapAttackCompiled = false`).

  Shape: `Batch443.accAttack` / `Batch271.perturb` over ANY accepted `Qm` at
  `P.memoryChipAt c`.  No package elaboration.

  A counts-only shift of
  the first row is therefore visible to `walkAccInitInGate`
  (`Batch407Leaves.walkInit_committed_not_shift_blind`).  The attack shifts the
  prover-committed memory walk SEED (`publicVal 1`, slots `9..11`) by
  `ln(1) · ΔRLC` so the first-row identity
  `ln·RLC^γ(x^mem) + acc = initial_count·cc + seed` (`:810`, `:1006`) is
  preserved.
-/
import Nock.NockVMROM.Thm54.MemoryWalkLabel
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.MemoryWalkRoots
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
import Nock.RedTeam.Batch271Thm54AnchoringReview
import Nock.RedTeam.Batch407Thm54SeedBoundaryLeaves
import Nock.RedTeam.Batch407Thm54SeedBoundaryCompileStop
import Nock.RedTeam.Batch443Thm54MemoryWalkReceipts
import Nock.RedTeam.Batch475Thm54MemoryWalkAlphaInitialCount
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch407Generic

open scoped Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.RedTeam.Batch271 (perturb colShift)
open Nock.RedTeam.Batch407Stop
open Nock.RedTeam.Batch475

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## A. -/

theorem fixture_attack_is_engineering_stop : fullRapAttackCompiled = false :=
  fullRapAttackCompiled_is_false

/-- Committed in-gate walk (OD) reads the parent counts / indicator roles.
    Restated at the Leaves fibre `ZMod 73` (the `decide` cone); not generic in `F`. -/
theorem committed_walk_not_shift_blind :
    (walkInitGates (F := Batch407Leaves.F)).all
      (fun g => Batch407Leaves.leavesM_avoid_shift g &&
        Batch407Leaves.leavesMC_base_only g) = false :=
  Batch407Leaves.walkInit_committed_not_shift_blind

theorem walkAccInit_mem_mixed (b : Module.Basis (Fin 3) F K) :
    walkAccInitInGate (F := F) ∈ mixedTransitionGates (F := F) (K := K) b := by
  refine List.mem_append_left _ ?_
  change walkAccInitInGate (F := F) ∈ paperKGates (F := F)
  simp [paperKGates, paperKGatesCore, walkGates, walkInitGates]

/-- Seed public is `publicVal 1` (`MemoryWalkLabel.seedPub`); walk-γ is memory slot `7`
(untouched). -/
theorem seedPub_is_publicVal_1 : seedPub (F := F) = .Var .publicVal 1 := rfl

theorem walkGamma_is_slot_7 : walkGammaChallengeIndex = 7 := rfl

/-! ## B. Counts shift at the first row (roles `3` = indicator, `4` = counts) -/

/-- `𝕂`-level first-row shift of the parent axis accumulators. -/
def countsShift {n : ℕ} [NeZero n] (δInd δCnt : K) : ℕ → Fin n → K :=
  fun r i =>
    if i = 0 then
      if r = 3 then δInd else if r = 4 then δCnt else 0
    else 0

theorem countsShift_off_row {n : ℕ} [NeZero n] (δInd δCnt : K)
    (r : ℕ) {i : Fin n} (hi : i ≠ 0) :
    countsShift δInd δCnt r i = 0 := by
  simp [countsShift, hi]

theorem countsShift_off_role {n : ℕ} [NeZero n] (δInd δCnt : K)
    {r : ℕ} (hr : r ≠ 3 ∧ r ≠ 4) (i : Fin n) :
    countsShift δInd δCnt r i = 0 := by
  simp [countsShift, hr.1, hr.2]

theorem countsShift_indicator {n : ℕ} [NeZero n] (δInd δCnt : K) :
    countsShift (n := n) δInd δCnt 3 0 = δInd := by
  simp [countsShift]

theorem countsShift_counts {n : ℕ} [NeZero n] (δInd δCnt : K) :
    countsShift (n := n) δInd δCnt 4 0 = δCnt := by
  simp [countsShift]

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (δInd δCnt : K)

/-- **The attack trace**: `Qm` with first-row parent `axis_indicator` / `axis_counts`
(roles `3` / `4`) shifted by `δInd` / `δCnt`. -/
noncomputable def countsAttack : Fin (P.memoryChipAt c).rap.w → F[X] :=
  let n := P.optimized.family.problem.cfg.memRows
  have : NeZero n := ⟨Nat.ne_zero_of_lt P.optimized.family.problem.cfg.memRows_pos⟩
  perturb P.optimized.memoryNodes
    (colShift P.optimized.basis (countsShift (n := n) δInd δCnt)) Qm

/-- RLC increment of the first-row label when those two coordinates move
(`labelCoordAt`: coord `4` = counts role `4`, coord `5` = indicator role `3`;
`rlcExpr` is `Σ_k γ^k · coord k`). -/
def labelDelta (γ : K) : K :=
  γ ^ 4 * δCnt + γ ^ 5 * δInd

/-- Seed increment that restores `walkAccInitInGate` at a first row with
`ln(1) = α` (`:810`): `Δseed = ln · ΔRLC`. -/
def seedDelta (α γ : K) : K :=
  α * labelDelta δInd δCnt γ

/-- Family memory publics with the prover-committed seed (slots `9..11`, `𝕂` public
role `1`) shifted by `Δ`.  Slots `6..8` stay the coin (`alphaM ^ kMem`); walk-γ
(slot `7` of the *challenge* vector) is not a public and is not touched. -/
noncomputable def seedShiftedPublic (Δ : K) : ℕ → F :=
  fun j =>
    if h : 9 ≤ j ∧ j < 12 then
      P.familyMemoryPublic c j +
        coord P.optimized.basis Δ ⟨j - 9, by omega⟩
    else
      P.familyMemoryPublic c j

theorem seedShiftedPublic_off_seed (Δ : K) (j : ℕ) (hj : ¬ (9 ≤ j ∧ j < 12)) :
    seedShiftedPublic P c Δ j = P.familyMemoryPublic c j := by
  simp [seedShiftedPublic, hj]

/-- The family chip at `c` but with a shifted seed public. -/
noncomputable def memoryChipAtSeedShift (Δ : K) : FixedPreprocessingRAP F :=
  DeployedChipFamily.memoryChipAt P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis (seedShiftedPublic P c Δ)
    P.optimized.orbit c P.optimized.family.problem.cfg.kMem

theorem memoryChipAtSeedShift_width (Δ : K) :
    (memoryChipAtSeedShift P c Δ).rap.w = (P.memoryChipAt c).rap.w := by
  have h0 : (P.memoryChipAt c).rap.w = 205 := by
    simp only [OptimizedFullStrictNockVMROMPackage.memoryChipAt,
      DeployedChipFamily.memoryChipAt]
    exact (finalMemoryRAP_fingerprint
      P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
      P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).1
  have h1 : (memoryChipAtSeedShift P c Δ).rap.w = 205 := by
    simp only [memoryChipAtSeedShift, DeployedChipFamily.memoryChipAt]
    exact (finalMemoryRAP_fingerprint
      P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
      P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (seedShiftedPublic P c Δ) P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).1
  exact h1.trans h0.symm

/-! ## C. -/

/-- The seed-consistent attack is **defined** (trace + seed public).  Full
`SatisfiesWithPreprocessing` of `memoryChipAtSeedShift` at `countsAttack` is the
remaining stitch (every gate class from `Batch407Leaves` plus the compensated
`walkAccInitInGate`).  That stitch is not in this file. -/
def seedConsistentAttackSatCompiled : Bool := false

theorem seedConsistentAttackSatCompiled_is_false :
    seedConsistentAttackSatCompiled = false := rfl

/-- Residual of the *generic attack*: the seed *can* be shifted (it is a public,
not slot `7`); the walk binds counts to the seed, not to zero.  That is **not**
a licence to deploy `readRootSel · counts = 0`.  is
`P = L − ts` at `read_root`; halt-zero is `:2061-2063`.  Honest F97
`aReadInnerPub` has `st =.read_root` and `pt.counts = 12 ≠ 0`. -/
def residualReason : String :=
  "countsAttack + seedShiftedPublic defined; SatisfiesWithPreprocessing of the seed-shifted chip not stitched; walk binds counts to the seed, not to zero; paper :2065-2070 is P = L - ts, not P = 0 — user-decision STOP, Batch408"

theorem residual_is_engineering : seedConsistentAttackSatCompiled = false :=
  seedConsistentAttackSatCompiled_is_false

/-- LIO binds the `ver`-selected roots, not the axis accumulators. -/
def lio_does_not_bind_counts : String :=
  "MemoryWalkRoots.memory_roots_bound_by_LIO binds (root, child, axis, ts); axis_counts_P / axis_indicator_P are in x^mem (:2028) and stay prover-chosen given the seed"

end Nock.RedTeam.Batch407Generic

#print axioms Nock.RedTeam.Batch407Generic.fixture_attack_is_engineering_stop
#print axioms Nock.RedTeam.Batch407Generic.committed_walk_not_shift_blind
#print axioms Nock.RedTeam.Batch407Generic.walkAccInit_mem_mixed
#print axioms Nock.RedTeam.Batch407Generic.seedPub_is_publicVal_1
#print axioms Nock.RedTeam.Batch407Generic.countsShift_counts
#print axioms Nock.RedTeam.Batch407Generic.seedShiftedPublic_off_seed
#print axioms Nock.RedTeam.Batch407Generic.memoryChipAtSeedShift_width
#print axioms Nock.RedTeam.Batch407Generic.residual_is_engineering
