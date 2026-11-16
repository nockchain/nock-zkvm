/-
  Nock/NockVMROM/Thm54/TraceGen/GenInputs.lean

  Generator-side `BuildableChips.Inputs` over `K3`, binding IO through the
  existing `programIOCapacity` / `memoryIOCapacity` fields of
  `BuildableNockExecution`.

  Identification, not new mathematics:

  * table-level compute Inputs is `challengeInputs` (item 2 / GenWF);
  * table-level memory Inputs is the `(z, β, γ)` triple;
  * good IO coins exist by `exists_io_coins` once the union bound is
    strictly below `|K|²` — for orbit `h = 3` the two capacity fields
    give request/response lengths `≤ 7`, which is far below `|K3| = 97³`;
  * `inputsOfK3` fills `basis` with `CubicField97.K3.basis` (the degree-1
    wall) and consumes those coins.  Strict orbit / active-domain
    witnesses remain carried, the same species as item-4 size windows.

  `zeroEndpointFamily` already threads `E.programIOCapacity` and
  `E.memoryIOCapacity`; this module names that consumption.
  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenWF
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.ForestExponentWindow

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen.CubicField97

variable {K : Type} [Field K]

/-! ## Table-level Inputs -/

/-- Verifier-sampled compute coins; item 2 already named this. -/
abbrev computeInputsOf (z α a b c : K) : ComputeTable.Inputs K :=
  challengeInputs z α a b c

/-- Verifier-sampled memory LogUp coins `(z, β, γ)`. -/
def memoryInputsOf (z β γ : K) : MemoryTable.Inputs K := ⟨z, β, γ⟩

/-! ## Capacity fields bound the committed IO prefixes -/

variable {F : Type} [Field F] [Algebra F K]

theorem programIOCapacity_binds (E : BuildableNockExecution F K) :
    E.exec.derivedRequestIO.length + 1 ≤ 2 ^ E.cfg.orbit.h :=
  E.programIOCapacity

theorem memoryIOCapacity_binds (E : BuildableNockExecution F K) :
    E.exec.derivedResponseIO.length + 1 ≤ 2 ^ E.cfg.orbit.h :=
  E.memoryIOCapacity

theorem executionRecords_lengths (E : BuildableNockExecution F K) :
    (executionRecords E).requests.length = E.exec.derivedRequestIO.length ∧
      (executionRecords E).responses.length = E.exec.derivedResponseIO.length :=
  ⟨rfl, rfl⟩

theorem length_le_seven_of_h3 {k : ℕ} (h : k + 1 ≤ 2 ^ 3) : k ≤ 7 := by
  have : k + 1 ≤ 8 := by simpa using h
  omega

theorem derivedRequestIO_length_le_seven_of_h3
    (E : BuildableNockExecution F K) (hh : E.cfg.orbit.h = 3) :
    E.exec.derivedRequestIO.length ≤ 7 :=
  length_le_seven_of_h3 (by simpa [hh] using E.programIOCapacity)

theorem derivedResponseIO_length_le_seven_of_h3
    (E : BuildableNockExecution F K) (hh : E.cfg.orbit.h = 3) :
    E.exec.derivedResponseIO.length ≤ 7 :=
  length_le_seven_of_h3 (by simpa [hh] using E.memoryIOCapacity)

/-! ## Good IO coins from the union bound -/

theorem exists_ioCoins_of_E [Fintype K] [DecidableEq K]
    (E : BuildableNockExecution F K)
    (hcard :
      RecordCarrier.honestIOBound
          E.exec.derivedRequestIO.length
          E.exec.derivedResponseIO.length
          (Fintype.card K) <
        Fintype.card (K × K)) :
    ∃ coins : IOCoins K,
      (coins.gamma, coins.pole) ∉ IOFailureEvent (executionRecords E) ∧
      (coins.gamma, coins.pole) ∉ IOFailureEvent (executionRecords10 E) :=
  RecordCarrier.exists_io_coins_two_of_bounds _ _ (by
    simpa [RecordCarrier.honestIOBound, executionRecords10, executionRecords] using hcard)

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.CubicField97
namespace K3

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Classical

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-- `ringChar K3 = 97` from `CharP K3 97`.  Named before the `ringChar K` local
    instance so that instance still synthesizes. -/
theorem ringChar_eq : ringChar K3 = 97 :=
  CharP.eq K3 (ringChar.charP K3) (inferInstanceAs (CharP K3 97))

local instance finiteDimK3 : FiniteDimensional (ZMod 97) K3 :=
  basis.finiteDimensional_of_finite

local instance charRingK3 : CharP K3 (ringChar K3) := ringChar.charP K3

noncomputable section

/-- Paper state-tag characteristic: `ringChar K3 = 97 > 11`. -/
theorem stateTagChar : NodeEncoding.StateTagChar K3 :=
  NodeEncoding.stateTagChar_of_charP (K := K3) (ringChar K3)
    (by rw [ringChar_eq]; norm_num)

/-- For orbit `h = 3` the capacity fields give `kᵢ ≤ 7`.  The union bound at
    those lengths is `1400 · 97³`, strictly below `|K3|² = 97⁶`. -/
theorem ioFailureUnionBound_le_seven :
    ∀ {k₁ k₂ : ℕ}, k₁ ≤ 7 → k₂ ≤ 7 →
      RecordCarrier.honestIOBound k₁ k₂ (Fintype.card K3) < Fintype.card (K3 × K3) := by
  intro k₁ k₂ hk1 hk2
  have hmono := RecordCarrier.honestIOBound_mono (Fintype.card K3) hk1 hk2
  refine lt_of_le_of_lt hmono ?_
  rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod, card_eq]
  norm_num

/-- Good IO coins for any K3 execution whose configured orbit has `h = 3`.
    The length bounds are exactly `programIOCapacity` / `memoryIOCapacity`. -/
theorem exists_ioCoins_of_orbit3 (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3) :
    ∃ coins : IOCoins K3,
      (coins.gamma, coins.pole) ∉ IOFailureEvent (executionRecords E) ∧
      (coins.gamma, coins.pole) ∉ IOFailureEvent (executionRecords10 E) :=
  exists_ioCoins_of_E E
    (by
      simpa [card_eq] using
        ioFailureUnionBound_le_seven
          (derivedRequestIO_length_le_seven_of_h3 E hh)
          (derivedResponseIO_length_le_seven_of_h3 E hh))

/-- Concrete coins from the two capacity fields at orbit `h = 3`. -/
def ioCoinsOf (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3) : IOCoins K3 :=
  Classical.choose (exists_ioCoins_of_orbit3 E hh)

theorem ioCoinsOf_good (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3) :
    ((ioCoinsOf E hh).gamma, (ioCoinsOf E hh).pole) ∉
      IOFailureEvent (executionRecords E) :=
  (Classical.choose_spec (exists_ioCoins_of_orbit3 E hh)).1

theorem ioCoinsOf_good10 (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3) :
    ((ioCoinsOf E hh).gamma, (ioCoinsOf E hh).pole) ∉
      IOFailureEvent (executionRecords10 E) :=
  (Classical.choose_spec (exists_ioCoins_of_orbit3 E hh)).2

theorem ioCoinsOf_poleHitGood (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3) :
    (ioCoinsOf E hh).pole ∉
      IOPoleHitEvent (executionRecords E) (ioCoinsOf E hh).gamma :=
  (not_mem_ioFailure_components (ioCoinsOf_good E hh)).1

theorem ioCoinsOf_gammaGood (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3) :
    (ioCoinsOf E hh).gamma ∉ IORLCCollisionEvent (executionRecords E) :=
  (not_mem_ioFailure_components (ioCoinsOf_good E hh)).2.1

theorem ioCoinsOf_logDerivGood (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3) :
    (ioCoinsOf E hh).pole ∉
      IOLogDerivEvent (executionRecords E) (ioCoinsOf E hh).gamma :=
  (not_mem_ioFailure_components (ioCoinsOf_good E hh)).2.2

/-! ## Backend Inputs over K3 -/

/-- In-table hit-event mass (nine- and ten-slot) at orbit `h = 3`: `memRows ≤ 8`,
`|K3| = 97³`. -/
theorem interCard_of_orbit3 (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3) :
    2 * ((executionInterRecords E).requests.length +
      (executionInterRecords E).responses.length) + 1 < Fintype.card K3 :=
  executionInterRecords_card_lt_of_memRows E (by
    have hle : E.cfg.memRows ≤ 8 := by
      simpa [hh] using E.cfg.memRows_le
    have hq : Fintype.card K3 = 97 ^ 3 := card_eq
    omega)

/-- Generic `BuildableChips.Inputs` over `K3`.  The Fin-3 basis is the power
    basis (degree-1 executions cannot inhabit this).  IO coins are those of
    `ioCoinsOf`, i.e. the capacity-bound counting argument.  Strict orbit and
    active-domain witnesses stay carried.  The internal pole is `interPoleOfE`, so `interPoleHitGood` is a theorem, not a field of `E`. -/
def inputsOf (E : BuildableNockExecution (ZMod 97) K3)
    (hh : E.cfg.orbit.h = 3)
    (computeWalkAlpha memoryWalkAlpha walkGamma : K3)
    (orbit : StrictOrbitDomain (ZMod 97) 3 3)
    (activeDomains :
      MonolithicActiveDomains orbit E.cfg.compRows
        (RowLayout.memoryM E.exec) (RowLayout.memoryL E.exec))
    (computeChallenges : FinalComputeChallengeTuple K3)
    (memoryScalarChallenge : Fin 4 → ZMod 97)
    (_memoryExtensionFold : K3)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    Inputs E where
  stateTagChar := stateTagChar
  computeWalkAlpha := computeWalkAlpha
  memoryWalkAlpha := memoryWalkAlpha
  walkGamma := walkGamma
  hOrb := 3
  basis := basis
  orbit := orbit
  activeDomains := activeDomains
  ioCoins := ioCoinsOf E hh
  ioPoleHitGood := ioCoinsOf_poleHitGood E hh
  ioGammaGood := ioCoinsOf_gammaGood E hh
  ioLogDerivGood := ioCoinsOf_logDerivGood E hh
  computeChallenges := computeChallenges
  memoryScalarChallenge := memoryScalarChallenge
  memoryExtensionFold :=
    interPoleOfE E (ioCoinsOf E hh).gamma (interCard_of_orbit3 E hh)
  interPoleHitGood :=
    interPoleOfE_good E (ioCoinsOf E hh).gamma (interCard_of_orbit3 E hh)
  honestVer := hhon
  ioGood10 := ioCoinsOf_good10 E hh
  interPoleHitGood10 :=
    interPoleOfE_good10 E (ioCoinsOf E hh).gamma (interCard_of_orbit3 E hh)

/-- `zeroEndpointFamily` consumes the two capacity fields of `E` by construction. -/
theorem zeroEndpointFamily_uses_capacity
    (E : BuildableNockExecution (ZMod 97) K3) (I : Inputs E) :
    PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
        (ExactCanonicalRAPProblem.ofChained E.chained)
        I.stateTagChar I.computeWalkAlpha I.walkGamma I.memoryWalkAlpha
        0 0 0 E.programIOCapacity E.memoryIOCapacity =
      zeroEndpointFamily E I :=
  rfl

/-! ## Non-vacuity -- union bound at the capacity ceiling, empty-record coins -/

theorem ioFailureUnionBound_seven_nonvacuous :
    RecordCarrier.honestIOBound 7 7 (Fintype.card K3) < Fintype.card (K3 × K3) :=
  ioFailureUnionBound_le_seven (Nat.le_refl 7) (Nat.le_refl 7)

theorem exists_ioCoins_empty_nonvacuous :
    ∃ coins : IOCoins K3,
      (coins.gamma, coins.pole) ∉ IOFailureEvent emptyRecords8 :=
  goodIOCoinsK3_exists

end

end K3
end Nock.NockVMROM.Thm54.TraceGen.CubicField97

#print axioms Nock.NockVMROM.Thm54.TraceGen.programIOCapacity_binds
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_ioCoins_of_E
#print axioms Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.exists_ioCoins_of_orbit3
#print axioms Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.inputsOf
#print axioms Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.zeroEndpointFamily_uses_capacity
#print axioms Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.ioFailureUnionBound_seven_nonvacuous
