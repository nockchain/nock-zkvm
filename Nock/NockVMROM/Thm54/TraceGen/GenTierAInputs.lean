/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAInputs.lean

  Backend `Inputs (dotBuildable hfirst)` over `K = GaloisField 769 3`.  Thirteen
  requests and thirteen responses; `hOrb = 8` so capacity `2^8 = 256`
  covers the 8 compute rows and 184 memory rows.  Failure mass uses
  `ioFailureBound_generic` with lengths 13/13 against `|K|² = 769⁶`.

  Does not claim `statement_of_generated_residual`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAHonestData
import Nock.NockVMROM.Thm54.TraceGen.GenTierABinds
import Nock.NockVMROM.Thm54.TraceGen.GenTierAInputsPrep
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.ForestExponentWindow

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.BuildableChips

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

local instance charRingK : CharP K (ringChar K) := ringChar.charP K

noncomputable section

variable (hfirst :
  ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
    ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0)


def sampledRecords : FiniteIO.PreChallengeRecords K 9 :=
  executionRecords (dotBuildable hfirst)

theorem sampledRecords_lengths :
    (sampledRecords hfirst).requests.length = 13 ∧ (sampledRecords hfirst).responses.length = 13 := by
  constructor
  · change (execThreaded seedZ alphaA).derivedRequestIO.length = 13
    exact derivedRequestIO_length
  · change (execThreaded seedZ alphaA).derivedResponseIO.length = 13
    exact derivedResponseIO_length

theorem ioFailureBound_generic {L : Type*} [Field L] [Fintype L] [DecidableEq L] {n : ℕ}
    (records : FiniteIO.PreChallengeRecords L n)
    (hr : records.requests.length = 13) (hs : records.responses.length = 13)
    (hcard : FiniteIO.ioFailureUnionBound n 13 13 (Fintype.card L) < Fintype.card (L × L)) :
    (FiniteIO.IOFailureEvent records).card < Fintype.card (L × L) := by
  refine lt_of_le_of_lt (FiniteIO.IOFailureEvent_card_le records) ?_
  rw [hr, hs]
  exact hcard

theorem ioFailureBound :
    (FiniteIO.IOFailureEvent (sampledRecords hfirst)).card < Fintype.card (K × K) :=
  ioFailureBound_generic (sampledRecords hfirst) (sampledRecords_lengths hfirst).1
    (sampledRecords_lengths hfirst).2
    (by
      rw [FiniteIO.ioFailureUnionBound, Fintype.card_prod, card_K]
      norm_num)

theorem goodIOCoins_exists :
    ∃ coins : FiniteIO.IOCoins K,
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (sampledRecords hfirst) ∧
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (executionRecords10 (dotBuildable hfirst)) :=
  RecordCarrier.exists_io_coins_ext _ (sampledRecords hfirst)
    (sampledRecords_lengths hfirst).1.le (sampledRecords_lengths hfirst).2.le
    (by
      rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod, card_K]
      norm_num)

def ioCoins : FiniteIO.IOCoins K := Classical.choose (goodIOCoins_exists hfirst)

theorem ioCoins_good :
    ((ioCoins hfirst).gamma, (ioCoins hfirst).pole) ∉ FiniteIO.IOFailureEvent (sampledRecords hfirst) :=
  (Classical.choose_spec (goodIOCoins_exists hfirst)).1

theorem ioCoins_good10 :
    ((ioCoins hfirst).gamma, (ioCoins hfirst).pole) ∉
      FiniteIO.IOFailureEvent (executionRecords10 (dotBuildable hfirst)) :=
  (Classical.choose_spec (goodIOCoins_exists hfirst)).2

theorem not_mem_ioFailure_components {L : Type*} [Field L] [Fintype L] [DecidableEq L] {n : ℕ}
    {records : FiniteIO.PreChallengeRecords L n} {γ p : L}
    (h : (γ, p) ∉ FiniteIO.IOFailureEvent records) :
    p ∉ FiniteIO.IOPoleHitEvent records γ
      ∧ γ ∉ FiniteIO.IORLCCollisionEvent records
      ∧ p ∉ FiniteIO.IOLogDerivEvent records γ := by
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at h
  exact ⟨h.2.1, h.1, h.2.2⟩

theorem ioCoins_poleHitGood :
    (ioCoins hfirst).pole ∉ FiniteIO.IOPoleHitEvent (sampledRecords hfirst) (ioCoins hfirst).gamma :=
  (not_mem_ioFailure_components (ioCoins_good hfirst)).1

theorem ioCoins_gammaGood :
    (ioCoins hfirst).gamma ∉ FiniteIO.IORLCCollisionEvent (sampledRecords hfirst) :=
  (not_mem_ioFailure_components (ioCoins_good hfirst)).2.1

theorem ioCoins_logDerivGood :
    (ioCoins hfirst).pole ∉ FiniteIO.IOLogDerivEvent (sampledRecords hfirst) (ioCoins hfirst).gamma :=
  (not_mem_ioFailure_components (ioCoins_good hfirst)).2.2

theorem inputs_interCard :
    2 * ((executionInterRecords (dotBuildable hfirst)).requests.length +
      (executionInterRecords (dotBuildable hfirst)).responses.length) + 1 < Fintype.card K :=
  executionInterRecords_card_lt_of_memRows_eq (dotBuildable hfirst)
    (show (dotBuildable hfirst).cfg.memRows = 184 from rfl) card_K (by norm_num)

def inputs : Inputs (dotBuildable hfirst) where
  stateTagChar := stateTagChar
  computeWalkAlpha := 2
  memoryWalkAlpha := 2
  walkGamma := 5
  hOrb := 8
  basis := basis
  orbit := strictOrbit
  activeDomains :=
    { computeCapacity := by
        rw [show (dotBuildable hfirst).cfg.compRows = 8 from rfl]; norm_num
      memoryCapacity := by
        rw [← (dotBuildable hfirst).memoryRows_eq_M_add_two_mul_L,
          show (dotBuildable hfirst).cfg.memRows = 184 from rfl]; norm_num }
  ioCoins := ioCoins hfirst
  ioPoleHitGood := ioCoins_poleHitGood hfirst
  ioGammaGood := ioCoins_gammaGood hfirst
  ioLogDerivGood := ioCoins_logDerivGood hfirst
  computeChallenges := default
  memoryScalarChallenge := fun j => (j : F) + 1
  memoryExtensionFold := interPoleOfE (dotBuildable hfirst) (ioCoins hfirst).gamma (inputs_interCard hfirst)
  interPoleHitGood := interPoleOfE_good (dotBuildable hfirst) (ioCoins hfirst).gamma (inputs_interCard hfirst)
  honestVer := execThreaded_honestVer seedZ alphaA
  ioGood10 := ioCoins_good10 hfirst
  interPoleHitGood10 :=
    interPoleOfE_good10 (dotBuildable hfirst) (ioCoins hfirst).gamma (inputs_interCard hfirst)

theorem inputs_challenges : (inputs hfirst).computeChallenges = default := rfl

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.ioFailureBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.inputs
