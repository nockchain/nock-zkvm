import Nock.Framework.FixedPreprocessingRAP
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.JointCoins
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.NockVMROM.Thm54.ComputeWalkSeed

/-!
The deployed compute and memory chips are `FixedPreprocessingRAP F`s built from
`chalVal : ℕ → F`.

Unpinning is: build `chalVal` from `c`.  Gate bodies do not change — they
already read `env.chal j`.  Slot maps :

* compute cubic `3·q+k` = coord `k` of `computeKOfTuple c q`
  (`ExactFinalChallengeCoordinates`); carried `q ∈ {0,1,2,3,4,5,6,7,8}`
* memory cubic `6+3·q+k` = coord `k` of `memoryKOfTuple c q`
  (`ExactMemoryCoordinatePins` / `memoryCol0`); live `q ∈ {0,3,4,5,6}`
  (and `2` if a table-γ gate remains, identified with IO `γ`)

`computeChipAt` / `memoryChipAt` are
the same constructors at `chalValOfTuple`.

Family-public scaffold
`computePublicOfTuple` / `memoryPublicOfTuple`.
-/

namespace Nock.NockVMROM.Thm54
namespace DeployedChipFamily

open Module CoordinateBasis
open Nock
open Nock.Framework
open OptimizedStrictPackage
open OptimizedComputeCollisionBound
open OptimizedComputeCorrectedFinal
open OptimizedComputeCanonicalSatisfaction
open OptimizedMemoryRAP
open OptimizedMemoryCollisionAccounting

set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]

/-- Compute `𝕂` coin at index `q` read off the sampled tuple.
Retired folds `9..` are `0`. -/
def computeKOfTuple (c : OptimizedProductionChallengeTuple K F) : ℕ → K
  | 0 => alphaM c.1
  | 1 => nprSeed c.1
  | 2 => c.2.2.1.eqA
  | 3 => c.2.2.1.eqB
  | 4 => c.2.2.1.eqC
  | 5 => (nprSeed c.1)⁻¹
  | 6 => alphaC c.1
  | 7 => c.2.1.1
  | 8 => c.2.1.2
  | 9 => c.2.2.2.lambda
  | 10 => gamma c.1
  | _ => 0

/-- The walk-node RLC coin `γ` is read
by the in-gate label RLCs at compute `𝕂` slot `10`. -/
theorem computeKOfTuple_walkGamma (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 10 = gamma c.1 := rfl

/-- Memory `𝕂` coin at index `q` read off the sampled tuple.
Index map is `memoryChallengeTargets` (`BuildableChips`):
`0` table `z` = `nprSeed`, `2` record-RLC = IO `γ`, `3` memory-walk `αm`,
`4`/`5` sampled IO, `6` `interPole`, `7` the walk-node RLC coin `γ`. -/
def memoryKOfTuple (c : OptimizedProductionChallengeTuple K F) : ℕ → K
  | 0 => nprSeed c.1
  | 2 => c.2.1.1
  | 3 => alphaM c.1
  | 4 => c.2.1.1
  | 5 => c.2.1.2
  | 6 => c.2.2.2.interPole
  | 7 => gamma c.1
  | 8 => c.2.2.2.lambda
  | _ => 0

/-- The walk-node RLC coin `γ` (JointCoins `gamma`) is read by the in-gate memory
label RLCs at memory `𝕂` slot `7` (`MemoryWalkLabel.walkGammaChallengeIndex`). -/
theorem memoryKOfTuple_walkGamma (c : OptimizedProductionChallengeTuple K F) :
    memoryKOfTuple c 7 = gamma c.1 := rfl

/-- Raw `𝔽` challenge vector of the compute chip at tuple `c`.
Slots `3·q+k` carry `coord b (computeKOfTuple c q) k` for `q < 12`;
everything at or above `finalScalarChallengeBase = 36` is `0`. -/
def computeChalValOfTuple (b : Basis (Fin 3) F K)
    (c : OptimizedProductionChallengeTuple K F) : ℕ → F :=
  fun j =>
    if j < 36 then
      coord b (computeKOfTuple c (j / 3)) ⟨j % 3, Nat.mod_lt j (by decide)⟩
    else 0

/-- Raw `𝔽` challenge vector of the memory chip at tuple `c`. -/
def memoryChalValOfTuple (b : Basis (Fin 3) F K)
    (c : OptimizedProductionChallengeTuple K F) : ℕ → F :=
  fun j =>
    if h : 6 ≤ j ∧ j < 33 then
      coord b (memoryKOfTuple c ((j - 6) / 3))
        ⟨(j - 6) % 3, Nat.mod_lt _ (by decide)⟩
    else 0

theorem computeKOfTuple_alphaM (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 0 = alphaM c.1 := rfl

theorem computeKOfTuple_seed (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 1 = nprSeed c.1 := rfl

theorem computeKOfTuple_eqA (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 2 = c.2.2.1.eqA := rfl

theorem computeKOfTuple_eqB (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 3 = c.2.2.1.eqB := rfl

theorem computeKOfTuple_eqC (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 4 = c.2.2.1.eqC := rfl

theorem computeKOfTuple_alphaC (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 6 = alphaC c.1 := rfl

theorem computeKOfTuple_ioGamma (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 7 = c.2.1.1 := rfl

theorem computeKOfTuple_ioPole (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 8 = c.2.1.2 := rfl

theorem computeKOfTuple_lambda (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 9 = c.2.2.2.lambda := rfl

theorem memoryKOfTuple_ioGamma (c : OptimizedProductionChallengeTuple K F) :
    memoryKOfTuple c 4 = c.2.1.1 := rfl

theorem memoryKOfTuple_ioPole (c : OptimizedProductionChallengeTuple K F) :
    memoryKOfTuple c 5 = c.2.1.2 := rfl

theorem memoryKOfTuple_interPole (c : OptimizedProductionChallengeTuple K F) :
    memoryKOfTuple c 6 = c.2.2.2.interPole := rfl

/-- Family fill writes `c.lambda`, not the `Pub.lambda` default `1`. -/
theorem memoryKOfTuple_lambda (c : OptimizedProductionChallengeTuple K F) :
    memoryKOfTuple c 8 = c.2.2.2.lambda := rfl

theorem computeChalValOfTuple_slot
    (b : Basis (Fin 3) F K) (c : OptimizedProductionChallengeTuple K F)
    (q : Fin 12) (k : Fin 3) :
    computeChalValOfTuple b c (3 * (q : ℕ) + (k : ℕ)) =
      coord b (computeKOfTuple c q) k := by
  have hlt : 3 * (q : ℕ) + (k : ℕ) < 36 := by
    have := q.isLt; have := k.isLt; omega
  have hdiv : (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by omega
  have hmod : (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by omega
  unfold computeChalValOfTuple
  rw [if_pos hlt, hdiv]
  apply congrArg
  exact Fin.ext hmod

theorem memoryChalValOfTuple_slot
    (b : Basis (Fin 3) F K) (c : OptimizedProductionChallengeTuple K F)
    (q : Fin 9) (k : Fin 3) :
    memoryChalValOfTuple b c (6 + 3 * (q : ℕ) + (k : ℕ)) =
      coord b (memoryKOfTuple c q) k := by
  have hlo : 6 ≤ 6 + 3 * (q : ℕ) + (k : ℕ) := by omega
  have hhi : 6 + 3 * (q : ℕ) + (k : ℕ) < 33 := by
    have := q.isLt; have := k.isLt; omega
  have h : 6 ≤ 6 + 3 * (q : ℕ) + (k : ℕ) ∧
      6 + 3 * (q : ℕ) + (k : ℕ) < 33 := ⟨hlo, hhi⟩
  have hdiv : (6 + 3 * (q : ℕ) + (k : ℕ) - 6) / 3 = (q : ℕ) := by omega
  have hmod : (6 + 3 * (q : ℕ) + (k : ℕ) - 6) % 3 = (k : ℕ) := by omega
  unfold memoryChalValOfTuple
  rw [dif_pos h, hdiv]
  apply congrArg
  exact Fin.ext hmod


/-- Gate-read public slots of the deployed compute chip (`ExactFinalPublicCoordinates`
plus the A-comp `requests` block): walk `initial_count` (`0..2`) and seed (`3..5`), IO
terminal, first/last state one-hots.  None of these is `enc(z, claim.*)`. -/
def computePublicReadSet : List ℕ :=
  (List.range 9) ++ (List.range 22).map (· + 20)

theorem computePublicReadSet_length : computePublicReadSet.length = 31 := by
  simp [computePublicReadSet]

def claimPublicBase : ℕ := 42

/-- Family compute publics at tuple `c`.
Slots `3..5` are the verifier's walk seed `seedOfClaim`:
`αc · RLC^γ(LT_comp of the public claim)`.  Every other slot, including the
rest of the gate-read set (`6..8`, `20..41`), stays the package
prover-committed map.  Claim-fingerprint slots `42..68` stay deleted
(`Batch397` / `Batch401`) -/
def computePublicOfTuple (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F) : ℕ → F :=
  fun j =>
    if h0 : j < 3 then
      coord b (alphaC c.1) ⟨j, h0⟩
    else if h : 3 ≤ j ∧ j < 6 then
      coord b (ComputeWalkSeed.seedOfClaim claim c) ⟨j - 3, by omega⟩
    else
      pkgPub j

/-- Off the walk block `0..5` (`initial_count` at `0..2`, seed at `3..5`),
`computePublicOfTuple` is the package public map. -/
theorem computePublicOfTuple_eq_pkg_off_seed
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hj : ¬ j < 6) :
    computePublicOfTuple b claim pkgPub c j = pkgPub j := by
  have h0 : ¬ j < 3 := by omega
  have h1 : ¬ (3 ≤ j ∧ j < 6) := by omega
  simp [computePublicOfTuple, h0, h1]

/-- `initial_count` slots `0..2` are the `𝔽`-coordinates of the tuple's compute-walk coin
`alphaC c.1`. -/
theorem computePublicOfTuple_alpha_coord
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (k : Fin 3) :
    computePublicOfTuple b claim pkgPub c (k : ℕ) = coord b (alphaC c.1) k := by
  have h0 : (k : ℕ) < 3 := k.isLt
  simp [computePublicOfTuple, h0]

/-- Seed slots `3..5` are the `𝔽`-coordinates of `seedOfClaim`. -/
theorem computePublicOfTuple_seed_coord
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (k : Fin 3) :
    computePublicOfTuple b claim pkgPub c (3 + (k : ℕ)) =
      coord b (ComputeWalkSeed.seedOfClaim claim c) k := by
  have h : 3 ≤ 3 + (k : ℕ) ∧ 3 + (k : ℕ) < 6 := by
    have : (k : ℕ) < 3 := k.isLt
    omega
  have h0 : ¬ 3 + (k : ℕ) < 3 := by omega
  simp [computePublicOfTuple, h, h0]

/-- On the gate-read set *except* the walk block `0..5`, the family map is the
    package map.  Slots `0..2` / `3..5` are verifier-computed
    (`computePublicOfTuple_alpha_coord`, `computePublicOfTuple_seed_coord`). -/
theorem computePublicOfTuple_eq_pkg_on_readSet
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (_hj : j ∈ computePublicReadSet) (hseed : ¬ j < 6) :
    computePublicOfTuple b claim pkgPub c j = pkgPub j :=
  computePublicOfTuple_eq_pkg_off_seed b claim pkgPub c j hseed

/-- When the tuple's walk coin is the family's committed `computeWalkAlpha` and the
    verifier seed equals the family's committed seed, the family public map is the
    package map (`ExactFinalPublicCoordinates` pins `0..2` to that coin and `3..5` to
    that seed).  `hα` is `rfl` at the package's honest tuple. -/
theorem computePublicOfTuple_eq_pkg_of_seed
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (R : PlusIOSegmentedFamily F K) (hn : 0 < R.problem.cfg.compRows)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (hpub : ExactFinalPublicCoordinates b R hn pkgPub)
    (hα : alphaC c.1 = R.computeWalkAlpha)
    (hseed : ComputeWalkSeed.seedOfClaim claim c = R.computeWalkSeed) :
    computePublicOfTuple b claim pkgPub c = pkgPub := by
  funext j
  by_cases h0 : j < 3
  · have hcoord := hpub.1 ⟨0, by decide⟩ ⟨j, h0⟩
    simp [computePublicOfTuple, h0, hα]
    simpa using hcoord.symm
  by_cases hj : 3 ≤ j ∧ j < 6
  · have hk : j - 3 < 3 := by omega
    have hcoord := hpub.1 ⟨1, by decide⟩ ⟨j - 3, hk⟩
    have hj3 : 3 * (1 : ℕ) + (j - 3) = j := by omega
    simp [computePublicOfTuple, h0, hj, hseed]
    simpa [hj3] using hcoord.symm
  · exact computePublicOfTuple_eq_pkg_off_seed b claim pkgPub c j (by omega)

/-- The memory walk is the paper's FOREST recognizer: over `k` roots the recognizer inputs are
`(seed, initial_count) = (Σ_{i=1}^k RLC^γ(slt_i) · α^i, α^k)` (`:1006`) — the count starts
at `α^k` because the `k` roots occupy the line indices `α^1..α^k` and the first discovered
child is indexed `α^{k+1}`.  So the coin's value of `initial_count` is `alphaM c.1 ^ kMem`,
with `kMem = cfg.kMem` the memory root count (`:1002`, verifier-known config) — memory
publics `6..8` (`ExactMemoryCoordinatePins.walkInitialCount`). -/
def memoryPublicOfTuple (b : Basis (Fin 3) F K) (_claim : P8PublicClaim) (kMem : ℕ)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F) : ℕ → F :=
  fun j =>
    if h : 6 ≤ j ∧ j < 9 then
      coord b (alphaM c.1 ^ kMem) ⟨j - 6, by omega⟩
    else
      pkgPub j

/-- Off the memory `initial_count` block `6..8`, the family memory map is the package map. -/
theorem memoryPublicOfTuple_eq_pkg
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim) (kMem : ℕ)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hj : ¬ (6 ≤ j ∧ j < 9)) :
    memoryPublicOfTuple b claim kMem pkgPub c j = pkgPub j := by
  simp [memoryPublicOfTuple, hj]

/-- Memory `initial_count` slots `6..8` are the `𝔽`-coordinates of `alphaM c.1 ^ kMem`. -/
theorem memoryPublicOfTuple_alpha_coord
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim) (kMem : ℕ)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F) (k : Fin 3) :
    memoryPublicOfTuple b claim kMem pkgPub c (6 + (k : ℕ)) =
      coord b (alphaM c.1 ^ kMem) k := by
  have h : 6 ≤ 6 + (k : ℕ) ∧ 6 + (k : ℕ) < 9 := by
    have : (k : ℕ) < 3 := k.isLt
    omega
  simp [memoryPublicOfTuple, h]

/-- The memory map ignores the claim (the memory seed is prover-committed). -/
theorem memoryPublicOfTuple_ignores_claim
    (b : Basis (Fin 3) F K) (claim claim' : P8PublicClaim) (kMem : ℕ)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F) :
    memoryPublicOfTuple b claim kMem pkgPub c = memoryPublicOfTuple b claim' kMem pkgPub c :=
  rfl

/-- **The honest identity for the generic package's memory map**: when the tuple's memory
walk coin is the family's `memoryWalkAlpha`, the family memory map is the package map
(`ExactMemoryCoordinatePins.walkInitialCount` pins `6..8` to `memoryWalkAlpha ^ kMem`).
`hα` is `rfl` at the package's honest tuple (`honestJointCoins`).  Memory twin of
`computePublicOfTuple_eq_pkg_of_seed`. -/
theorem memoryPublicOfTuple_eq_pkg_of_alpha
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (R : PlusIOSegmentedFamily F K) {p : ℕ} [CharP K p]
    (A : SampledIOSameExecutionAssignment R p)
    (chalVal pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (hpins : OptimizedMemoryCanonicalSatisfaction.ExactMemoryCoordinatePins A b chalVal pkgPub)
    (hα : alphaM c.1 = R.memoryWalkAlpha) :
    memoryPublicOfTuple b claim R.problem.cfg.kMem pkgPub c = pkgPub := by
  funext j
  by_cases hj : 6 ≤ j ∧ j < 9
  · have hk : j - 6 < 3 := by omega
    have hsum := hpins.walkInitialCount
    have hcoord : ∀ k : Fin 3, pkgPub (6 + 3 * 0 + (k : ℕ)) =
        coord b (R.memoryWalkAlpha ^ R.problem.cfg.kMem) k := by
      intro k
      rw [← hsum]
      exact (MonolithicRAP.coord_sum_smul b (fun k' => pkgPub (6 + 3 * 0 + (k' : ℕ))) k).symm
    have hj6 : 6 + 3 * 0 + (j - 6) = j := by omega
    simp only [memoryPublicOfTuple, hj, ↓reduceDIte, hα]
    have := hcoord ⟨j - 6, hk⟩
    simp only [hj6] at this
    exact this.symm
  · exact memoryPublicOfTuple_eq_pkg b claim _ pkgPub c j hj

/-- Deployed compute chip at tuple `c`.  Gate bodies as `computeChip`;
`chalVal` reads off `c`; publics are the caller-supplied map (package). -/
def computeChipAt {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h)
    (c : OptimizedProductionChallengeTuple K F) : FixedPreprocessingRAP F :=
  ProductionNamedComputeRAP hn nodes b (computeChalValOfTuple b c) pubVal orbit

/-- Deployed memory chip at tuple `c`.  Gate bodies as `memoryChip`;
`chalVal` reads off `c`; publics are the (claim-independent) package map. -/
def memoryChipAt {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h)
    (c : OptimizedProductionChallengeTuple K F) (kMem : ℕ) : FixedPreprocessingRAP F :=
  namedFinalMemoryRAP hn nodes b (memoryChalValOfTuple b c) pubVal orbit kMem

end

end DeployedChipFamily
end Nock.NockVMROM.Thm54
