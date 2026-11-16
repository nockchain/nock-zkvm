/-
  Nock/NockVMROM/Thm54/TraceGen/GenCarrierInputs.lean

  **`BuildableChips.Inputs` for an arbitrary buildable carrier, from that carrier's own
  row-count and IO-capacity fields.**

  `Inputs E` (`BuildableChips.lean:45`) is the pre-compilation backend record: state-tag
  characteristic, three walk challenges, a strict package orbit with its two active-domain
  capacity certificates, IO coins outside the three counted IO failure events, and the verifier's
  compiler folds.  Every existing inhabitant of it (`ServedForestModule.inputsMG`,
  `DistinctCensusCommitment`, `DotConfig769.inputs`) rebuilds the capacity and coin arguments by
  hand at its own fixture.

  Three pieces, none of them new mathematics:

  * `monolithicActiveDomains_of_carrier` — the two capacity certificates from `ExactConfig`'s own
    `compRows_le` / `memRows_le` plus `memoryRows_eq_M_add_two_mul_L`.
    The strict package orbit's height `hOrb` need not be the table orbit's height, so the
    hypothesis is `2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb`.
  * `exists_ioCoins_of_length_bound` — good IO coins from the counted union bound at any **upper bound** on the two record-column
    lengths, rather than at their exact values.  `ioFailureUnionBound_mono` is the missing
    monotonicity step; the carrier's own `programIOCapacity` / `memoryIOCapacity` then supply the
    bound with no measurement of the program at all.

  **`computeChallenges = default` is the verifier's compiler FOLDS, not the RLC coins.**
  `FinalComputeChallengeTuple K` has fields `challenge9`, `challenge11` (extension folds) and
  `challenge36` (the raw scalar selector fold) — `OptimizedComputeCollisionBound.lean:515`.  The
  compute RLC coins are `ComputeTable.Inputs.a/b/c` (`ComputeTable.lean:158`), which live on the
  carrier's `ChallengeVector` and are untouched here.
-/
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.TraceGen.GenWF
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound

noncomputable section


variable {F K : Type} [Field F]
  [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## The two active-domain capacity certificates -/

/-- **`MonolithicActiveDomains` off the carrier's own row bounds.**

`ExactConfig` already carries `compRows ≤ 2 ^ orbit.h` and `memRows ≤ 2 ^ orbit.h`, and
`memoryRows_eq_M_add_two_mul_L` turns the second into the paper's `M + 2L` budget with no extra hypothesis — it is a consequence of `recordCountBalance`, a field
of every `BuildableNockExecution`.  So the only thing a caller supplies is the comparison between
the table orbit `E.cfg.orbit` and the strict *package* orbit, whose heights are independent
objects. -/
theorem monolithicActiveDomains_of_carrier {hOrb : ℕ}
    (E : BuildableNockExecution F K) (orbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb) :
    MonolithicActiveDomains orbit E.cfg.compRows
      (RowLayout.memoryM E.exec) (RowLayout.memoryL E.exec) where
  computeCapacity := le_trans E.cfg.compRows_le hcap
  memoryCapacity := by
    rw [← E.memoryRows_eq_M_add_two_mul_L]
    exact le_trans E.cfg.memRows_le hcap

/-! ## Good IO coins from an upper bound on the two record columns -/

/-- The counted IO failure mass is monotone in the two record-column lengths.  Immediate from the
shape of `ioFailureUnionBound` (`FiniteFieldIOSoundness.lean:278`), and it is what lets a caller
spend a *capacity* bound instead of measuring its program's record columns. -/
theorem ioFailureUnionBound_mono {m k₁ k₂ k₁' k₂' cardK : ℕ}
    (h₁ : k₁ ≤ k₁') (h₂ : k₂ ≤ k₂') :
    ioFailureUnionBound m k₁ k₂ cardK ≤ ioFailureUnionBound m k₁' k₂' cardK := by
  have hs : k₁ + k₂ ≤ k₁' + k₂' := Nat.add_le_add h₁ h₂
  have hsq : (k₁ + k₂) * (k₁ + k₂) ≤ (k₁' + k₂') * (k₁' + k₂') := Nat.mul_le_mul hs hs
  unfold ioFailureUnionBound
  exact Nat.add_le_add
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsq))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs))

variable [Fintype K] [DecidableEq K]

/-- **Good IO coins for any carrier whose record columns are bounded by `n`.**

`exists_io_coins` (`GenWF.lean:472`) needs the failure event to miss at least one `(γ, pole)` pair;
`IOFailureEvent_card_le` bounds its cardinality at the *actual* column lengths, and
`ioFailureUnionBound_mono` relaxes that to any upper bound.  No property of the program enters. -/
theorem exists_ioCoins_of_length_bound
    (E : BuildableNockExecution F K) (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K)) :
    ∃ coins : IOCoins K,
      (coins.gamma, coins.pole) ∉ IOFailureEvent (executionRecords E) ∧
      (coins.gamma, coins.pole) ∉ IOFailureEvent (executionRecords10 E) :=
  exists_ioCoins10_of_length_bound E n hreq hresp hcard

/-- **The same, spending the carrier's own two capacity fields.**  `programIOCapacity` and
`memoryIOCapacity` are `BuildableNockExecution` fields, so the request/response columns are below
`2 ^ E.cfg.orbit.h`; nothing about the program is measured. -/
theorem exists_ioCoins_of_capacity
    (E : BuildableNockExecution F K)
    (hcard : RecordCarrier.honestIOBound (2 ^ E.cfg.orbit.h) (2 ^ E.cfg.orbit.h)
      (Fintype.card K) < Fintype.card (K × K)) :
    ∃ coins : IOCoins K,
      (coins.gamma, coins.pole) ∉ IOFailureEvent (executionRecords E) ∧
      (coins.gamma, coins.pole) ∉ IOFailureEvent (executionRecords10 E) :=
  exists_ioCoins_of_length_bound E (2 ^ E.cfg.orbit.h)
    (le_of_lt (Nat.lt_of_succ_le E.programIOCapacity))
    (le_of_lt (Nat.lt_of_succ_le E.memoryIOCapacity)) hcard

/-- The chosen coins. -/
def ioCoinsOfCarrier
    (E : BuildableNockExecution F K) (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K)) :
    IOCoins K :=
  Classical.choose (exists_ioCoins_of_length_bound E n hreq hresp hcard)

theorem ioCoinsOfCarrier_good
    (E : BuildableNockExecution F K) (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K)) :
    ((ioCoinsOfCarrier E n hreq hresp hcard).gamma,
        (ioCoinsOfCarrier E n hreq hresp hcard).pole) ∉
      IOFailureEvent (executionRecords E) :=
  (Classical.choose_spec (exists_ioCoins_of_length_bound E n hreq hresp hcard)).1

theorem ioCoinsOfCarrier_good10
    (E : BuildableNockExecution F K) (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K)) :
    ((ioCoinsOfCarrier E n hreq hresp hcard).gamma,
        (ioCoinsOfCarrier E n hreq hresp hcard).pole) ∉
      IOFailureEvent (executionRecords10 E) :=
  (Classical.choose_spec (exists_ioCoins_of_length_bound E n hreq hresp hcard)).2

/-- **`4 · memRows + 1 < |K|` from the honest IO union-bound hypothesis**, once `memRows ≤ n`.

`honestIOBound n n |K| = |K| · (68 n² + 8 n)`, so `hcard` is `68 n² + 8 n < |K|`.
That majorizes `4 n + 1` (and `1 < |K|` when `n = 0`). -/
theorem interCard_of_unionBound
    (E : BuildableNockExecution F K) {n : ℕ}
    (hmem : E.cfg.memRows ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K)) :
    4 * E.cfg.memRows + 1 < Fintype.card K := by
  have hprod : Fintype.card (K × K) = Fintype.card K * Fintype.card K :=
    Fintype.card_prod K K
  have hpoly : 68 * n * n + 8 * n < Fintype.card K := by
    have hq : 0 < Fintype.card K := Fintype.card_pos
    rw [RecordCarrier.honestIOBound_eq, hprod] at hcard
    exact Nat.lt_of_mul_lt_mul_left hcard
  have hle : 4 * E.cfg.memRows + 1 ≤ 4 * n + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 4 hmem) 1
  have h4n : 4 * n + 1 < Fintype.card K := by
    cases n with
    | zero =>
      simpa using (Fintype.one_lt_card : 1 < Fintype.card K)
    | succ n =>
      have : 4 * (n + 1) + 1 ≤ 68 * (n + 1) * (n + 1) + 8 * (n + 1) := by
        have h2 : 68 * (n + 1) * (n + 1) + 8 * (n + 1) =
            68 * n * n + 144 * n + 76 := by ring
        omega
      exact lt_of_le_of_lt this hpoly
  exact lt_of_le_of_lt hle h4n

/-! ## The assembly -/

/-- **`Inputs E` for an arbitrary buildable carrier.**

The three IO conditions are the three components of one counted event, split by
`not_mem_ioFailure_components`; the two active-domain certificates come from the carrier's own row
bounds. -/
def inputsOfCarrier
    (E : BuildableNockExecution F K) {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (b : Module.Basis (Fin 3) F K)
    (orbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (_memoryExtensionFold : K)
    (hinterCard : 4 * E.cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    Inputs E where
  stateTagChar := stc
  computeWalkAlpha := computeWalkAlpha
  memoryWalkAlpha := memoryWalkAlpha
  walkGamma := walkGamma
  hOrb := hOrb
  basis := b
  orbit := orbit
  activeDomains := monolithicActiveDomains_of_carrier E orbit hcap
  ioCoins := ioCoinsOfCarrier E n hreq hresp hcard
  ioPoleHitGood := (not_mem_ioFailure_components (ioCoinsOfCarrier_good E n hreq hresp hcard)).1
  ioGammaGood := (not_mem_ioFailure_components (ioCoinsOfCarrier_good E n hreq hresp hcard)).2.1
  ioLogDerivGood := (not_mem_ioFailure_components (ioCoinsOfCarrier_good E n hreq hresp hcard)).2.2
  computeChallenges := default
  memoryScalarChallenge := memoryScalarChallenge
  memoryExtensionFold :=
    interPoleOfE' E (ioCoinsOfCarrier E n hreq hresp hcard).gamma
      (interCard'_of_basis E b hinterCard)
  interPoleHitGood :=
    interPoleOfE'_good E (ioCoinsOfCarrier E n hreq hresp hcard).gamma
      (interCard'_of_basis E b hinterCard)
  honestVer := hhon
  ioGood10 := ioCoinsOfCarrier_good10 E n hreq hresp hcard
  interPoleHitGood10 :=
    interPoleOfE'_good10 E (ioCoinsOfCarrier E n hreq hresp hcard).gamma
      (interCard'_of_basis E b hinterCard)

/-- The fold tuple `buildFullPackage`'s `hzero` wants, by `rfl`. -/
theorem inputsOfCarrier_challenges
    (E : BuildableNockExecution F K) {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (b : Module.Basis (Fin 3) F K)
    (orbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
    (hinterCard : 4 * E.cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon).computeChallenges
      = default :=
  rfl

/-- **The generated internal pole misses `0` and `-γ^8`**: the
pole of `inputsOfCarrier` is `interPoleOfE'` at the chosen IO `γ`, so both closed-form side
conditions of the internal-pole component (`interNe`, `interGamma8`) hold. -/
theorem inputsOfCarrier_interPole_sides
    (E : BuildableNockExecution F K) {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (b : Module.Basis (Fin 3) F K)
    (orbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
    (hinterCard : 4 * E.cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).memoryExtensionFold ≠ 0 ∧
      (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
          hhon).memoryExtensionFold +
        (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
          hhon).ioCoins.gamma ^ 8 ≠ 0 :=
  ⟨interPoleOfE'_ne_zero E _ (interCard'_of_basis E b hinterCard),
    interPoleOfE'_add_gamma8_ne_zero E _ (interCard'_of_basis E b hinterCard)⟩

/-- And its orbit height, by `rfl` — the package type is indexed by it. -/
theorem inputsOfCarrier_hOrb
    (E : BuildableNockExecution F K) {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (b : Module.Basis (Fin 3) F K)
    (orbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
    (hinterCard : 4 * E.cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon).hOrb = hOrb :=
  rfl

end

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.monolithicActiveDomains_of_carrier
#print axioms Nock.NockVMROM.Thm54.TraceGen.ioFailureUnionBound_mono
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_ioCoins_of_length_bound
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_ioCoins_of_capacity
#print axioms Nock.NockVMROM.Thm54.TraceGen.inputsOfCarrier
#print axioms Nock.NockVMROM.Thm54.TraceGen.inputsOfCarrier_challenges
#print axioms Nock.NockVMROM.Thm54.TraceGen.inputsOfCarrier_interPole_sides
