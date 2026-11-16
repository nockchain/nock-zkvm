/-
  Nock/RedTeam/Batch646Thm54LambdaEventHostileForm.lean

  The hostile form reads the event's three inputs from `(Qc, Qm)`.  Measured against the B1 round
  map (`DeployedStaging.computeColRound` / `memoryColRound`):

  * **Certificate bits — round 0, PASS.**  `c_j` at compute columns `202 + j` (`j < 63`), the shift
    `m_k` at `265 + k` (`k < 6`): `cert_block_round0`.
  * **Forest shape — round 0, PASS.**  `typedMemoryForest` is the BFS inversion (`rebuildForest`)
    of the committed rows under `memoryFanout`, which reads ONLY the state (`fanout_reads_state`);
    the state is the selector block, columns `0..3` (`selectors_round0`).  Nothing of round ≥ 1.
  * **Record exponent — FINDING (blocking for B as proposed).**  The memory chip has NO round-0
    carrier of a record's exponent.  The only exponent-bearing datum of a memory record row is its
    timestamp `ts`, record slot `7` of `OptimizedMemoryHostileAccumulator.rowRecord` = `𝕂` role `26` = physical
    columns `84..86`, which are **round 2** (`ts_round2`).  The compute side's exponents ARE
    structural (`OptimizedHostileTimestamps.hostile_timestamp_eq`: `ts(i, j) = α^{S(i) + j + 1}`,
    from the `ln` chain gates and `ln₀ = 1`), but a memory row acquires its exponent only through
    the record it answers — the `IO.LIO` pairing of `hostile_LIO'`, whose records contain `ts`.
    So the per-tree Form R polynomial of the decoded hostile forest cannot be written from
    round-0 data alone: its `X^e` exponents are post-`α` on the memory chip.
  * Consequence: option B does not reduce R4 to a round-0 event.
-/
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch646

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.StrategyOfTraces

/-! ## Rounds of the three inputs -/

/-- Certificate bits `c_j` (`202 + j`, `j < 63`) and shift bits `m_k` (`265 + k`, `k < 6`): round 0. -/
theorem cert_block_round0 :
    (∀ j, j < 63 → computeColRound (202 + j) = 0) ∧
      (∀ k, k < 6 → computeColRound (265 + k) = 0) := by
  refine ⟨fun j hj => ?_, fun k hk => ?_⟩ <;>
  · simp only [computeColRound]
    split_ifs <;> omega

/-- The memory selector block `0..3` (the state): round 0. -/
theorem selectors_round0 : ∀ c, c < 4 → memoryColRound c = 0 := by
  intro c hc; simp [memoryColRound]; omega

/-- The timestamp of a memory record, record slot `7` = `𝕂` role `26` = columns `84..86`: round 2. -/
theorem ts_round2 : memoryColRound 84 = 2 ∧ memoryColRound 85 = 2 ∧ memoryColRound 86 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [memoryColRound, memoryRoleRound]

theorem rowRecord_ts_is_role26 {F K : Type} [Field F] [Field K] [Algebra F K]
    (envK : Reified.Env K) (envF : Reified.Env F) :
    OptimizedMemoryHostileAccumulator.rowRecord envK envF 7 = envK.trace 26 := by
  simp [OptimizedMemoryHostileAccumulator.rowRecord]

/-- `𝕂` role `26` occupies physical columns `6 + 3·26 + k = 84 + k`. -/
theorem role26_cols (k : ℕ) (_hk : k < 3) : 6 + 3 * 26 + k = 84 + k := by omega

/-- The forest shape reads only the state: `memoryFanout` ignores the data component. -/
theorem fanout_reads_state {K : Type} [Field K] (st : MState) (d d' : DTmem K) :
    memoryFanout (st, d) = memoryFanout (st, d') := rfl

/-- And the fanouts of the four states (`decompose 2`, `halt 0`, `read_root 1`, `verify_child 1`). -/
theorem fanouts :
    fanoutMem .decompose = 2 ∧ fanoutMem .halt = 0 ∧ fanoutMem .read_root = 1 ∧
      fanoutMem .verify_child = 1 := ⟨rfl, rfl, rfl, rfl⟩

/-! ## The compute exponent is structural; the memory one is not carried pre-`α` -/

/-- Restating the deployed fact used by the proposal (name check only): compute request `(i, j)`'s
timestamp is `ln₀ · α^{S(i) + j + 1}`.  This is a type-level citation of
`OptimizedHostileTimestamps.hostile_timestamp_eq`, whose statement reads the structural exponent
`prefixExp P Qc i + j + 1`. -/
example := @OptimizedHostileTimestamps.hostile_timestamp_eq

/-- The memory record of a row had nine `𝕂` slots: `19..26` and `C'` (`57`), none an exponent
(slot `7` is the timestamp value).  **Since the thirty-first move it has ten**: the tenth is the
round-0 base column `reqIdx` (`181`), lifted — the pre-`α` exponent carrier this batch found
missing.  (By the definition, read.) -/
theorem rowRecord_slots {F K : Type} [Field F] [Field K] [Algebra F K]
    (envK : Reified.Env K) (envF : Reified.Env F) :
    (∀ c : Fin 10, (c : ℕ) < 8 →
        OptimizedMemoryHostileAccumulator.rowRecord envK envF c = envK.trace (19 + (c : ℕ))) ∧
      OptimizedMemoryHostileAccumulator.rowRecord envK envF 8 = envK.trace 57 ∧
      OptimizedMemoryHostileAccumulator.rowRecord envK envF 9 =
        algebraMap F K (envF.trace 181) := by
  refine ⟨fun c hc => ?_, ?_, ?_⟩
  · simp [OptimizedMemoryHostileAccumulator.rowRecord, hc]
  · simp [OptimizedMemoryHostileAccumulator.rowRecord]
  · simp [OptimizedMemoryHostileAccumulator.rowRecord]

end Nock.RedTeam.Batch646
