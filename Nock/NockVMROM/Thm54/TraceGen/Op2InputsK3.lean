/-
  Nock/NockVMROM/Thm54/TraceGen/Op2InputsK3.lean

  Stage 3 of the OP2 Layer-2 CORE: the backend `Inputs Op2Execution` record over
  the computable cubic table field `K3`.  Five requests and five responses
  (`F,T,B,C,S`); `hOrb = 5` so capacity `2⁵ = 32` covers the 23 memory rows.
  Failure mass uses `ioFailureBound_generic` with lengths 5/5 against `|K3|² = 97⁶`
  — never enumerating `Finset.univ (K3 × K3)`
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2DataK3
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.ExtensionField

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.TraceGen.CubicField97

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-- The consumed-`q` char instance for the table field. -/
local instance charRingK3 : CharP K (ringChar K) := ringChar.charP K

noncomputable section

variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)

/-! ## Backend field data over `K3` -/

/-- Paper state-tag characteristic: `ringChar K3 = 97 > 11`. -/
theorem stateTagCharK3 : NodeEncoding.StateTagChar K :=
  NodeEncoding.stateTagChar_of_charP (K := K) (ringChar K) (by rw [ringChar_K3]; norm_num)

/-- Strict RAP orbit of exact order `3 · 2⁵ = 96`.  `96 ∣ 96`. -/
def strictOrbitK3 : StrictOrbitDomain F 3 5 where
  ω := Classical.choose (exists_zmod_generator_of_dvd_sub_one 97 96 (by norm_num))
  βcoset := 1
  e_pos := by norm_num
  h_pos := by norm_num
  order_ω := by
    simpa using Classical.choose_spec
      (exists_zmod_generator_of_dvd_sub_one 97 96 (by norm_num))
  βcoset_ne_zero := one_ne_zero

/-! ## The sampled finite IO of the OP2/K3 slice and its failure bound -/

/-- The committed IO record pair of the slice: five requests, five responses. -/
def sampledRecordsK3 : FiniteIO.PreChallengeRecords K 9 :=
  executionRecords (Op2Execution hfirst)

/-- The OP2 slice samples exactly five requests and five responses. -/
theorem sampledRecordsK3_lengths :
    (sampledRecordsK3 hfirst).requests.length = 5 ∧
      (sampledRecordsK3 hfirst).responses.length = 5 := by
  constructor
  · change (exec seedZ alphaA).derivedRequestIO.length = 5
    simp [ExactExecution.derivedRequestIO, rawRequests_eq]
  · change (exec seedZ alphaA).derivedResponseIO.length = 5
    simp [derived_responses]

/-- The failure bound, proved for an *abstract* field `L` with the record lengths passed as
hypotheses.  Instantiating at `records = sampledRecordsK3` is a plain application, so the kernel
never evaluates the whole K3 execution to prove a defeq length. -/
theorem ioFailureBound_generic {L : Type*} [Field L] [Fintype L] [DecidableEq L] {n : ℕ}
    (records : FiniteIO.PreChallengeRecords L n)
    (hr : records.requests.length = 5) (hs : records.responses.length = 5)
    (hcard : FiniteIO.ioFailureUnionBound n 5 5 (Fintype.card L) < Fintype.card (L × L)) :
    (FiniteIO.IOFailureEvent records).card < Fintype.card (L × L) := by
  refine lt_of_le_of_lt (FiniteIO.IOFailureEvent_card_le records) ?_
  rw [hr, hs]
  exact hcard

/-- The joint IO failure mass is far below `|K3|² = 97⁶`: with five requests and five
responses the union bound is `720 · 97³`. -/
theorem ioFailureBoundK3 :
    (FiniteIO.IOFailureEvent (sampledRecordsK3 hfirst)).card <
      Fintype.card (K × K) :=
  ioFailureBound_generic (sampledRecordsK3 hfirst)
    (sampledRecordsK3_lengths hfirst).1 (sampledRecordsK3_lengths hfirst).2
    (by
      rw [FiniteIO.ioFailureUnionBound, Fintype.card_prod,
        show Fintype.card K = 97 ^ 3 from Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.card_eq]
      norm_num)

theorem goodIOCoinsK3_exists :
    ∃ coins : FiniteIO.IOCoins K,
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (sampledRecordsK3 hfirst) ∧
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (executionRecords10 (Op2Execution hfirst)) :=
  RecordCarrier.exists_io_coins_ext _ (sampledRecordsK3 hfirst)
    (sampledRecordsK3_lengths hfirst).1.le (sampledRecordsK3_lengths hfirst).2.le
    (by
      rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod,
        show Fintype.card K = 97 ^ 3 from Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.card_eq]
      norm_num)

def ioCoinsK3 : FiniteIO.IOCoins K := Classical.choose (goodIOCoinsK3_exists hfirst)

theorem ioCoinsK3_good :
    ((ioCoinsK3 hfirst).gamma, (ioCoinsK3 hfirst).pole) ∉
      FiniteIO.IOFailureEvent (sampledRecordsK3 hfirst) :=
  (Classical.choose_spec (goodIOCoinsK3_exists hfirst)).1

theorem ioCoinsK3_good10 :
    ((ioCoinsK3 hfirst).gamma, (ioCoinsK3 hfirst).pole) ∉
      FiniteIO.IOFailureEvent (executionRecords10 (Op2Execution hfirst)) :=
  (Classical.choose_spec (goodIOCoinsK3_exists hfirst)).2

theorem not_mem_ioFailure_components {L : Type*} [Field L] [Fintype L] [DecidableEq L] {n : ℕ}
    {records : FiniteIO.PreChallengeRecords L n} {γ p : L}
    (h : (γ, p) ∉ FiniteIO.IOFailureEvent records) :
    p ∉ FiniteIO.IOPoleHitEvent records γ
      ∧ γ ∉ FiniteIO.IORLCCollisionEvent records
      ∧ p ∉ FiniteIO.IOLogDerivEvent records γ := by
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at h
  exact ⟨h.2.1, h.1, h.2.2⟩

theorem ioCoinsK3_poleHitGood :
    (ioCoinsK3 hfirst).pole ∉
      FiniteIO.IOPoleHitEvent (sampledRecordsK3 hfirst) (ioCoinsK3 hfirst).gamma :=
  (not_mem_ioFailure_components (ioCoinsK3_good hfirst)).1

theorem ioCoinsK3_gammaGood :
    (ioCoinsK3 hfirst).gamma ∉ FiniteIO.IORLCCollisionEvent (sampledRecordsK3 hfirst) :=
  (not_mem_ioFailure_components (ioCoinsK3_good hfirst)).2.1

theorem ioCoinsK3_logDerivGood :
    (ioCoinsK3 hfirst).pole ∉
      FiniteIO.IOLogDerivEvent (sampledRecordsK3 hfirst) (ioCoinsK3 hfirst).gamma :=
  (not_mem_ioFailure_components (ioCoinsK3_good hfirst)).2.2

/-! ## The backend inputs record -/

theorem inputsK3_interCard :
    2 * ((executionInterRecords (Op2Execution hfirst)).requests.length +
      (executionInterRecords (Op2Execution hfirst)).responses.length) + 1 < Fintype.card K :=
  executionInterRecords_card_lt_of_memRows_eq (Op2Execution hfirst)
    (show (Op2Execution hfirst).cfg.memRows = 23 from rfl) K3.card_eq (by norm_num)

/-- **The OP2/K3 backend inputs.**  Inhabited because `K3` has `finrank (ZMod 97) K3 = 3`. -/
def inputsK3 : Inputs (Op2Execution hfirst) where
  stateTagChar := stateTagCharK3
  computeWalkAlpha := 2
  memoryWalkAlpha := 3
  walkGamma := 5
  hOrb := 5
  basis := (Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.basis : Module.Basis (Fin 3) F K)
  orbit := strictOrbitK3
  activeDomains :=
    { computeCapacity := by
        rw [show (Op2Execution hfirst).cfg.compRows = 4 from rfl]; norm_num
      memoryCapacity := by
        rw [← (Op2Execution hfirst).memoryRows_eq_M_add_two_mul_L,
          show (Op2Execution hfirst).cfg.memRows = 23 from rfl]; norm_num }
  ioCoins := ioCoinsK3 hfirst
  ioPoleHitGood := ioCoinsK3_poleHitGood hfirst
  ioGammaGood := ioCoinsK3_gammaGood hfirst
  ioLogDerivGood := ioCoinsK3_logDerivGood hfirst
  computeChallenges := default
  memoryScalarChallenge := fun j => (j : F) + 1
  memoryExtensionFold := interPoleOfE (Op2Execution hfirst) (ioCoinsK3 hfirst).gamma
    (inputsK3_interCard hfirst)
  interPoleHitGood := interPoleOfE_good (Op2Execution hfirst) (ioCoinsK3 hfirst).gamma
    (inputsK3_interCard hfirst)
  honestVer := honestVer
  ioGood10 := ioCoinsK3_good10 hfirst
  interPoleHitGood10 := interPoleOfE_good10 (Op2Execution hfirst) (ioCoinsK3 hfirst).gamma
    (inputsK3_interCard hfirst)


theorem inputsK3_challenges : (inputsK3 hfirst).computeChallenges = default := rfl

end

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.strictOrbitK3
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.ioFailureBoundK3
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.inputsK3
