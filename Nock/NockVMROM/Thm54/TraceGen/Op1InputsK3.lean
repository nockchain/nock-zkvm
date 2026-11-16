/-
  Nock/NockVMROM/Thm54/TraceGen/Op1InputsK3.lean

  The backend `Inputs Op1Execution_K3` record.

  This is the input that the degree-1 OP1 slice provably cannot have
  (`GenStatement.inputs_op1Execution_isEmpty`, from `no_basis_fin3_field_self`), because `Inputs E`
  carries `basis : Basis (Fin 3) F K` and forces `finrank F K = 3`.  Over the cubic table field
  `K = K3` (`finrank (ZMod 97) K3 = 3`) that obstruction is gone, and the record is inhabited by
  `K3`'s power basis.  The record follows `DistinctCensusCommitment.inputsD` field-for-field:

  * `basis` is `CubicField97.basis` (the `1, X, X²` power basis) — the only field that was the wall.
  * `stateTagChar` comes from `CharP K3 97` and `11 < 97`.
  * `orbit` is a strict RAP orbit of exact order `3 · 2³ = 24` over `ZMod 97` (`24 ∣ 96`).
  * `activeDomains` bounds the `1` compute row and the `5` memory rows by `2³ = 8`.
  * `ioCoins` is a good coin pair, existing by the finite-field cardinality argument
    (`IOFailureEvent_card_le`): the OP1 slice samples one request and one response, so its failure
    mass `32·97³` is far below `|K3|² = 97⁶`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1DataK3
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.ExtensionField

namespace Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

open Nock Nock.Framework Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.TraceGen.CubicField97

-- `K3`'s `Fintype`/`DecidableEq` instances (via `ZMod 97 ×³` and a polynomial quotient) are
-- structurally deeper than `GaloisField 97 3`, so the anonymous-constructor elaboration of
-- `inputsK3` and its instance search exceed the default recursion budget.
set_option maxRecDepth 10000
-- The `inputsK3` term is large; skip the term-traversing constructor-name linter (it otherwise
-- recurses on the whole `Inputs` structure and inflates memory) — hygiene is unaffected.
set_option linter.constructorNameAsVariable false

/-- The consumed-`q` char instance for the table field, mirroring the F73/F97 fixtures
(`ConcreteStrictPackage.lean:533`). -/
local instance charRingK3 : CharP K (ringChar K) := ringChar.charP K

noncomputable section

variable
  (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
  (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
  (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA))

/-! ## Backend field data over `K3` -/

/-- Paper state-tag characteristic: `ringChar K3 = 97 > 11`. -/
theorem stateTagCharK3 : NodeEncoding.StateTagChar K :=
  NodeEncoding.stateTagChar_of_charP (K := K) (ringChar K) (by rw [ringChar_K3]; norm_num)

/-- Strict RAP orbit of exact order `3 · 2³ = 24`. -/
def strictOrbitK3 : StrictOrbitDomain F 3 3 where
  ω := Classical.choose (exists_zmod_generator_of_dvd_sub_one 97 24 (by norm_num))
  βcoset := 1
  e_pos := by norm_num
  h_pos := by norm_num
  order_ω := by
    simpa using Classical.choose_spec
      (exists_zmod_generator_of_dvd_sub_one 97 24 (by norm_num))
  βcoset_ne_zero := one_ne_zero

/-! ## The sampled finite IO of the OP1/K3 slice and its failure bound -/

/-- The committed IO record pair of the slice: one request, one response. -/
def sampledRecordsK3 : FiniteIO.PreChallengeRecords K 9 :=
  executionRecords (Op1Execution_K3 hread hdec hver)

/-- The OP1 slice samples exactly one request and one response. -/
theorem sampledRecordsK3_lengths :
    (sampledRecordsK3 hread hdec hver).requests.length = 1 ∧
      (sampledRecordsK3 hread hdec hver).responses.length = 1 := by
  constructor
  · change (exec seedZ alphaA).derivedRequestIO.length = 1
    simp [ExactExecution.derivedRequestIO, rawRequests_eq]
  · change (exec seedZ alphaA).derivedResponseIO.length = 1
    rw [ExactExecution.derivedResponseIO_eq_map_encRecC (exec seedZ alphaA)
      (memory_cprimeCoherent seedZ alphaA)]
    simp [rawResponses_eq]

/-- The failure bound, proved for an *abstract* field `L` with the record lengths passed as
hypotheses.  This keeps `records` opaque: instantiating at `records = sampledRecordsK3` is a plain
application, so the kernel never has to prove `sampledRecordsK3.requests.length =def= 1` by
evaluating the whole K3 execution (that defeq check costs ~120s of kernel time). -/
theorem ioFailureBound_generic {L : Type*} [Field L] [Fintype L] [DecidableEq L] {n : ℕ}
    (records : FiniteIO.PreChallengeRecords L n)
    (hr : records.requests.length = 1) (hs : records.responses.length = 1)
    (hcard : FiniteIO.ioFailureUnionBound n 1 1 (Fintype.card L) < Fintype.card (L × L)) :
    (FiniteIO.IOFailureEvent records).card < Fintype.card (L × L) := by
  refine lt_of_le_of_lt (FiniteIO.IOFailureEvent_card_le records) ?_
  rw [hr, hs]
  exact hcard

/-- The joint IO failure mass is far below the `|K3|² = 97⁶` coin pairs: with one request and one
response the union bound is `32·97³`. -/
theorem ioFailureBoundK3 :
    (FiniteIO.IOFailureEvent (sampledRecordsK3 hread hdec hver)).card <
      Fintype.card (K × K) :=
  ioFailureBound_generic (sampledRecordsK3 hread hdec hver)
    (sampledRecordsK3_lengths hread hdec hver).1
    (sampledRecordsK3_lengths hread hdec hver).2
    (by
      rw [FiniteIO.ioFailureUnionBound, Fintype.card_prod,
        show Fintype.card K = 97 ^ 3 from Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.card_eq]
      norm_num)

/-- A good coin pair exists by the cardinality argument.

The `⊆`-then-`card_le_card` contradiction reduces the folded `K3 × K3` membership through a
structural defeq check that exceeds the file-default recursion budget, so this one declaration
raises it locally (the surrounding `simp`-based fields conversely need the *lower* default, since a
higher budget lets `simp` over-unfold `K3`'s decidability). -/
theorem goodIOCoinsK3_exists :
    ∃ coins : FiniteIO.IOCoins K,
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (sampledRecordsK3 hread hdec hver) ∧
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (executionRecords10 (Op1Execution_K3 hread hdec hver)) :=
  RecordCarrier.exists_io_coins_ext _ (sampledRecordsK3 hread hdec hver)
    (sampledRecordsK3_lengths hread hdec hver).1.le (sampledRecordsK3_lengths hread hdec hver).2.le
    (by
      rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod,
        show Fintype.card K = 97 ^ 3 from Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.card_eq]
      norm_num)

def ioCoinsK3 : FiniteIO.IOCoins K :=
  Classical.choose (goodIOCoinsK3_exists hread hdec hver)

theorem ioCoinsK3_good :
    ((ioCoinsK3 hread hdec hver).gamma, (ioCoinsK3 hread hdec hver).pole) ∉
      FiniteIO.IOFailureEvent (sampledRecordsK3 hread hdec hver) :=
  (Classical.choose_spec (goodIOCoinsK3_exists hread hdec hver)).1

theorem ioCoinsK3_good10 :
    ((ioCoinsK3 hread hdec hver).gamma, (ioCoinsK3 hread hdec hver).pole) ∉
      FiniteIO.IOFailureEvent (executionRecords10 (Op1Execution_K3 hread hdec hver)) :=
  (Classical.choose_spec (goodIOCoinsK3_exists hread hdec hver)).2

/-- Split a `∉ IOFailureEvent` fact into its three event components.  Proved for an *abstract* field
`L` so instantiating at `K = K3` is a plain application — the concrete `K3` decidability never
unfolds (a direct `simp` over `K3` exhausts the recursion/memory budget). -/
theorem not_mem_ioFailure_components {L : Type*} [Field L] [Fintype L] [DecidableEq L] {n : ℕ}
    {records : FiniteIO.PreChallengeRecords L n} {γ p : L}
    (h : (γ, p) ∉ FiniteIO.IOFailureEvent records) :
    p ∉ FiniteIO.IOPoleHitEvent records γ
      ∧ γ ∉ FiniteIO.IORLCCollisionEvent records
      ∧ p ∉ FiniteIO.IOLogDerivEvent records γ := by
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at h
  exact ⟨h.2.1, h.1, h.2.2⟩

theorem ioCoinsK3_poleHitGood :
    (ioCoinsK3 hread hdec hver).pole ∉
      FiniteIO.IOPoleHitEvent (sampledRecordsK3 hread hdec hver)
        (ioCoinsK3 hread hdec hver).gamma :=
  (not_mem_ioFailure_components (ioCoinsK3_good hread hdec hver)).1

theorem ioCoinsK3_gammaGood :
    (ioCoinsK3 hread hdec hver).gamma ∉
      FiniteIO.IORLCCollisionEvent (sampledRecordsK3 hread hdec hver) :=
  (not_mem_ioFailure_components (ioCoinsK3_good hread hdec hver)).2.1

theorem ioCoinsK3_logDerivGood :
    (ioCoinsK3 hread hdec hver).pole ∉
      FiniteIO.IOLogDerivEvent (sampledRecordsK3 hread hdec hver)
        (ioCoinsK3 hread hdec hver).gamma :=
  (not_mem_ioFailure_components (ioCoinsK3_good hread hdec hver)).2.2

/-! ## The backend inputs record -/

theorem inputsK3_interCard :
    2 * ((executionInterRecords (Op1Execution_K3 hread hdec hver)).requests.length +
      (executionInterRecords (Op1Execution_K3 hread hdec hver)).responses.length) + 1 <
        Fintype.card K :=
  executionInterRecords_card_lt_of_memRows_eq (Op1Execution_K3 hread hdec hver)
    (show (Op1Execution_K3 hread hdec hver).cfg.memRows = 6 from rfl) K3.card_eq (by norm_num)

/-- **The OP1/K3 backend inputs.**  Inhabited (unlike `Inputs Op1Execution` over degree-1
`ZMod 97`) because the table field `K3` has `finrank (ZMod 97) K3 = 3`, so the power basis fills the
`basis : Basis (Fin 3) F K` field that was the wall. -/
def inputsK3 : Inputs (Op1Execution_K3 hread hdec hver) where
  stateTagChar := stateTagCharK3
  computeWalkAlpha := 2
  memoryWalkAlpha := 3
  walkGamma := 5
  hOrb := 3
  basis := (Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.basis : Module.Basis (Fin 3) F K)
  orbit := strictOrbitK3
  activeDomains :=
    -- Project the two row counts by `rfl` (`compRows = 1`, `memRows = 5`) instead of
    -- `norm_num [Op1Execution_K3, cfg]`, which simp-normalizes all 14 fields of the K3 execution
    -- (including the heavy semantic proofs) and blows the memory budget under a parallel build.
    { computeCapacity := by
        rw [show (Op1Execution_K3 hread hdec hver).cfg.compRows = 1 from rfl]; norm_num
      memoryCapacity := by
        rw [← (Op1Execution_K3 hread hdec hver).memoryRows_eq_M_add_two_mul_L,
          show (Op1Execution_K3 hread hdec hver).cfg.memRows = 6 from rfl]; norm_num }
  ioCoins := ioCoinsK3 hread hdec hver
  ioPoleHitGood := ioCoinsK3_poleHitGood hread hdec hver
  ioGammaGood := ioCoinsK3_gammaGood hread hdec hver
  ioLogDerivGood := ioCoinsK3_logDerivGood hread hdec hver
  computeChallenges := default
  memoryScalarChallenge := fun j => (j : F) + 1
  memoryExtensionFold :=
    interPoleOfE (Op1Execution_K3 hread hdec hver) (ioCoinsK3 hread hdec hver).gamma
      (inputsK3_interCard hread hdec hver)
  interPoleHitGood :=
    interPoleOfE_good (Op1Execution_K3 hread hdec hver) (ioCoinsK3 hread hdec hver).gamma
      (inputsK3_interCard hread hdec hver)
  honestVer := honestVer seedZ alphaA
  ioGood10 := ioCoinsK3_good10 hread hdec hver
  interPoleHitGood10 := interPoleOfE_good10 (Op1Execution_K3 hread hdec hver) (ioCoinsK3 hread hdec hver).gamma
    (inputsK3_interCard hread hdec hver)


theorem inputsK3_challenges : (inputsK3 hread hdec hver).computeChallenges = default := rfl

end

end Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.strictOrbitK3
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.ioFailureBoundK3
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.inputsK3
