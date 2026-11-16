/-
  Nock/NockVMROM/Thm54/P8Core/SVIOAssembly.lean

  **The IO assembly twin at a common
  `requests` value, package-free.**

  The deployed assembly (`FamilyIOChainMemory.hostile_io_identity_core_at`) closes the LogUp
  identity through `compute_requests_eq_memory_requests P`: both chips read the *package's*
  `requests` public.  The identity then closes through the
  common value `ρ = m.requests c` alone:

      Σ_{r ∈ requests} compress(r)⁻¹ = ρ = Σ_{r ∈ responses} compress(r)⁻¹.

  ρ cancels; no lemma needs it constant in `c`.

  * `MemIOFacts` — the only thing the assembly reads from the memory side (a response list, its
    LogUp identity at `ρ`, nonvanishing denominators).
  * `lio_of_common_requests` — `IO.LIO` from an accepted compute row family (`IORows`), any
    `MemIOFacts` at the same coins and terminal value, and the three IO events plus the timestamp
    collision event at the committed records (chip-parametric in the memory side).
  * `lio_at_chips` — the instance at `computeChipAt309` (any public map) and `memoryChipAt12`
    (any public map), under the two read-off hypotheses `pubC (6+k) = coord b ρ k`,
    `pubM (12+k) = coord b ρ k` — exactly what `chipsOf V m c` gives with `ρ = m.requests c`.

  Paper: the paper (`:597-599` "as-is"), `:603-609`.
-/
import Nock.NockVMROM.Thm54.P8Core.SVIOCompute
import Nock.NockVMROM.Thm54.P8Core.SVIOMemory

namespace Nock.NockVMROM.Thm54.SVIO

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open OptimizedStrictPackage
open OptimizedComputeCorrectedFinal
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open DeployedChipFamily
open Unhosted309
open StrictExtension
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartA12.DeployedChipFamily12
open Module
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## 1. The memory-side interface the assembly reads -/

/-- **What the IO assembly needs from the memory side**, at IO coins `coins` and terminal value
`ρ`: a committed response list whose LogUp sum is `ρ`, with nonzero compressed denominators.
Chip-parametric: any memory chip whose accepted traces supply this plugs into
`lio_of_common_requests`. -/
structure MemIOFacts (coins : FiniteIO.IOCoins K) (ρ : K) where
  responses : List (Fin 10 → K)
  sum_eq : (responses.map fun r => (FiniteIO.compress coins r)⁻¹).sum = ρ
  ne_zero : ∀ r ∈ responses, FiniteIO.compress coins r ≠ 0

/-- An accepted memory row family supplies the facts at its own terminal public. -/
def MemIORows.facts [DecidableEq K] {b : Basis (Fin 3) F K} (R : MemIORows F K b) :
    MemIOFacts R.coins ((R.envK R.lastRow).pub 2) where
  responses := R.responses
  sum_eq := R.requests_eq_sum_compress.symm
  ne_zero := fun _ hr => R.compress_response_ne_zero hr

/-- Transport of the facts along an equality of terminal values. -/
def MemIOFacts.cast {coins : FiniteIO.IOCoins K} {ρ ρ' : K} (M : MemIOFacts coins ρ)
    (h : ρ = ρ') : MemIOFacts coins ρ' where
  responses := M.responses
  sum_eq := M.sum_eq.trans h
  ne_zero := M.ne_zero

@[simp] theorem MemIOFacts.cast_responses {coins : FiniteIO.IOCoins K} {ρ ρ' : K}
    (M : MemIOFacts coins ρ) (h : ρ = ρ') : (M.cast h).responses = M.responses := rfl

/-! ## 2. The abstract assembly: `IO.LIO` from a common terminal value -/

section Abstract

variable [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

/-- The committed records of an accepted compute family and a memory-side response list. -/
def recordsOf (R : IORows F K) (resp : List (Fin 10 → K)) : FiniteIO.PreChallengeRecords K 10 :=
  ⟨R.requests, resp⟩

/-- **The LogUp identity at a common terminal value.**  The compute terminal and the memory
terminal are the same field element `ρ`; nothing else about `ρ` is used. -/
theorem identity_of_common_requests (R : IORows F K) {ρ : K} (M : MemIOFacts R.coins ρ)
    (hρ : (R.env R.lastRow).extensionPublic 2 = ρ)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hhit : R.coins.pole ∉ FiniteIO.IOPoleHitEvent (recordsOf R M.responses) R.coins.gamma) :
    (R.requests.map fun r => (FiniteIO.compress R.coins r)⁻¹).sum =
      (M.responses.map fun r => (FiniteIO.compress R.coins r)⁻¹).sum := by
  have hpole : ∀ (i : Fin R.n) (j : Fin 3),
      activeMask (R.env i) j = 1 → slotDenominator (R.env i) j ≠ 0 := by
    intro i j hact h0
    apply hhit
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨rowRecord (R.env i) j,
      List.mem_append_left _ (R.rowRecord_mem_requests i j hact), ?_⟩
    rw [slotDenominator_eq_compress, R.rowCoins_eq] at h0
    exact h0
  rw [← R.requests_eq_sum_compress (fun i j => R.activeMask_bool hchar i j) hpole, hρ, M.sum_eq]

theorem compress_request_ne_zero (R : IORows F K) (resp : List (Fin 10 → K))
    (hhit : R.coins.pole ∉ FiniteIO.IOPoleHitEvent (recordsOf R resp) R.coins.gamma)
    {r : Fin 10 → K} (hr : r ∈ R.requests) : FiniteIO.compress R.coins r ≠ 0 := by
  intro h0
  apply hhit
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨r, List.mem_append_left _ hr, h0⟩

/-- **`IO.LIO` at a common `requests` value, chip-parametric in the memory side.**  An accepted
compute row family, any memory-side facts at the same coins and the same terminal value `ρ`,
outside the timestamp collision event at `κ 0` and the IO failure event at the committed
records: the request and response lists are `IO.LIO`. -/
theorem lio_of_common_requests {Ksz : ℕ} (R : IORows F K) {ρ : K} (M : MemIOFacts R.coins ρ)
    (hρ : (R.env R.lastRow).extensionPublic 2 = ρ)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz : R.κ 1 ≠ 0) (h5 : R.κ 5 = (R.κ 1)⁻¹)
    (hα : R.κ 0 ∉ TimestampCollisionEvent R.requests.length)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz R.requests.length)
    (hKresp : M.responses.length ≤ Ksz)
    (hio : (R.coins.gamma, R.coins.pole) ∉ FiniteIO.IOFailureEvent (recordsOf R M.responses)) :
    IO.LIO Ksz R.requests M.responses := by
  have hnot : ¬ (R.coins.gamma ∈ FiniteIO.IORLCCollisionEvent (recordsOf R M.responses) ∨
      R.coins.pole ∈ FiniteIO.IOPoleHitEvent (recordsOf R M.responses) R.coins.gamma ∨
      R.coins.pole ∈ FiniteIO.IOLogDerivEvent (recordsOf R M.responses) R.coins.gamma) := by
    intro h
    apply hio
    simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hhit := fun h => hnot (Or.inr (Or.inl h))
  have hγ := fun h => hnot (Or.inl h)
  have hlog := fun h => hnot (Or.inr (Or.inr h))
  have hreqnd := R.requests_nodup hchar hz h5 hα
  have hend := identity_of_common_requests R M hρ hchar hhit
  have hdA : ∀ i, R.coins.pole + FiniteIO.reqVals (recordsOf R M.responses) R.coins.gamma i ≠ 0 :=
    fun i => compress_request_ne_zero R M.responses hhit (List.get_mem R.requests i)
  have hdB : ∀ j, R.coins.pole + FiniteIO.respVals (recordsOf R M.responses) R.coins.gamma j ≠ 0 :=
    fun j => M.ne_zero _ (List.get_mem M.responses j)
  have hend' : (∑ i, (R.coins.pole +
        FiniteIO.reqVals (recordsOf R M.responses) R.coins.gamma i)⁻¹) =
      ∑ j, (R.coins.pole + FiniteIO.respVals (recordsOf R M.responses) R.coins.gamma j)⁻¹ := by
    have h := hend
    rw [show R.requests = (recordsOf R M.responses).requests from rfl,
      show M.responses = (recordsOf R M.responses).responses from rfl,
      OptimizedHostileIOAssembly.sum_requests_eq_sum_fin,
      OptimizedHostileIOAssembly.sum_responses_eq_sum_fin] at h
    exact h
  exact FiniteIO.finiteIO_sound_of_identity (recordsOf R M.responses) R.coins hdA hdB hend' hKp
    hKreq hKresp hreqnd
    (FiniteIO.responses_nodup_of_identity (recordsOf R M.responses) R.coins hdA hdB hend' hKp
      hKreq hKresp hreqnd hγ hlog) hγ hlog

end Abstract

/-! ## 3. The instance at the standalone chips -/

section AtChips

variable [Fintype K] [Fintype F] [DecidableEq K]
  {h nC nM : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → F) (hinjC : Function.Injective nodesC)
  (hnM : 0 < nM) (nodesM : Fin nM → F) (hinjM : Function.Injective nodesM)
  (b : Basis (Fin 3) F K) (pubC pubM : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodesC i)
  (hadjM : ∀ (i : Fin nM) (hi : (i : ℕ) + 1 < nM), nodesM ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodesM i)
  (c : OptimizedProductionChallengeTuple12 K F) (kMem : ℕ)

/-- A public map that reads `ρ` at slots `base.. base+2` gathers to `ρ`. -/
theorem gathered_eq_of_coord (pub : ℕ → F) (base : ℕ) (ρ : K)
    (hpub : ∀ k : Fin 3, pub (base + (k : ℕ)) = coord b ρ k) :
    (∑ k : Fin 3, pub (base + (k : ℕ)) • b k) = ρ := by
  simp_rw [hpub]
  exact reconstruct_coord b ρ

/-- The compute coins of the 309 family at `forget12 c` are the tuple's IO coins `c.2.1`. -/
theorem rows309_coins
    (Qc : Fin (computeChipAt309 hnC nodesC b pubC orbit (forget12 c)).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipAt309 hnC nodesC b pubC orbit (forget12 c)) Qc) :
    (rows309 hnC nodesC hinjC b pubC orbit hadjC (forget12 c) Qc hsat).coins = ⟨c.2.1.1, c.2.1.2⟩ :=
  rfl

/-- **The memory facts at `memoryChipAt12`, at the common value `ρ`.** -/
def memIOFacts12 (ρ : K)
    (hreqM : ∀ k : Fin 3, pubM (12 + (k : ℕ)) = coord b ρ k)
    (Qm : Fin (memoryChipAt12 hnM nodesM b pubM orbit c kMem).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (memoryChipAt12 hnM nodesM b pubM orbit c kMem) Qm) :
    MemIOFacts (⟨c.2.1.1, c.2.1.2⟩ : FiniteIO.IOCoins K) ρ :=
  (memRows12 hnM nodesM hinjM b pubM orbit hadjM c kMem Qm hsat).facts.cast
    ((envK12_pub2 hnM nodesM b pubM orbit c kMem Qm _).trans
      (gathered_eq_of_coord b pubM 12 ρ hreqM))

@[simp] theorem memIOFacts12_responses (ρ : K)
    (hreqM : ∀ k : Fin 3, pubM (12 + (k : ℕ)) = coord b ρ k)
    (Qm : Fin (memoryChipAt12 hnM nodesM b pubM orbit c kMem).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (memoryChipAt12 hnM nodesM b pubM orbit c kMem) Qm) :
    (memIOFacts12 hnM nodesM hinjM b pubM orbit hadjM c kMem ρ hreqM Qm hsat).responses =
      (memRows12 hnM nodesM hinjM b pubM orbit hadjM c kMem Qm hsat).responses := rfl

/-- **The IO twin at the standalone chips.**  Fix any nodes, basis, orbit and public maps, and a
common value `ρ` that the compute chip reads at publics `6..8` and the memory chip at `12..14`
(in the standalone verifier, `ρ = m.requests c`, a B2 message).  Every pair of traces the two
chips accept at the twelve-coin tuple `c`, outside the timestamp collision event at `alphaM`
and the IO failure event at the committed records, has `IO.LIO` request and response lists.
No package; `ρ` is never required to be constant in `c`. -/
theorem lio_at_chips {p : ℕ} [CharP K p] {Ksz : ℕ} (ρ : K)
    (hreqC : ∀ k : Fin 3, pubC (6 + (k : ℕ)) = coord b ρ k)
    (hreqM : ∀ k : Fin 3, pubM (12 + (k : ℕ)) = coord b ρ k)
    (Qc : Fin (computeChipAt309 hnC nodesC b pubC orbit (forget12 c)).rap.w → F[X])
    (hsatC : RAP.SatisfiesWithPreprocessing (computeChipAt309 hnC nodesC b pubC orbit (forget12 c)) Qc)
    (Qm : Fin (memoryChipAt12 hnM nodesM b pubM orbit c kMem).rap.w → F[X])
    (hsatM : RAP.SatisfiesWithPreprocessing (memoryChipAt12 hnM nodesM b pubM orbit c kMem) Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0)
    (hα : alphaM c.1 ∉ TimestampCollisionEvent
      (rows309 hnC nodesC hinjC b pubC orbit hadjC (forget12 c) Qc hsatC).requests.length)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz
      (rows309 hnC nodesC hinjC b pubC orbit hadjC (forget12 c) Qc hsatC).requests.length)
    (hKresp : (memRows12 hnM nodesM hinjM b pubM orbit hadjM c kMem Qm hsatM).responses.length ≤ Ksz)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent
      ⟨(rows309 hnC nodesC hinjC b pubC orbit hadjC (forget12 c) Qc hsatC).requests,
        (memRows12 hnM nodesM hinjM b pubM orbit hadjM c kMem Qm hsatM).responses⟩) :
    IO.LIO Ksz (rows309 hnC nodesC hinjC b pubC orbit hadjC (forget12 c) Qc hsatC).requests
      (memRows12 hnM nodesM hinjM b pubM orbit hadjM c kMem Qm hsatM).responses := by
  set R := rows309 hnC nodesC hinjC b pubC orbit hadjC (forget12 c) Qc hsatC
  have hρ : (R.env R.lastRow).extensionPublic 2 = ρ :=
    (env309_requests hnC nodesC b pubC orbit (forget12 c) Qc _).trans
      (gathered_eq_of_coord b pubC 6 ρ hreqC)
  have := lio_of_common_requests (p := p) R
    (memIOFacts12 hnM nodesM hinjM b pubM orbit hadjM c kMem ρ hreqM Qm hsatM)
    hρ hchar hz0 rfl hα hKp hKreq hKresp hio
  exact this

end AtChips

end

end Nock.NockVMROM.Thm54.SVIO
