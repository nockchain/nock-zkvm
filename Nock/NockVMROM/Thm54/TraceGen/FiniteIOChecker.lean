/-
  Nock/NockVMROM/Thm54/TraceGen/FiniteIOChecker.lean

  Phase 4b of the trace-generator track: the finite-field IO checker.

  The compute/memory chips of `TraceGen/Checker.lean` verify each row against its per-row AIR.  The
  IO chip is the third chip: it certifies that the value-keyed memory *requests* issued by the
  compute rows and the *responses* served by the memory rows match as multisets, via the finite-`K`
  prover-committed LogUp of `FiniteFieldIO` — the two accumulators `Σ 1/(pole + RLC^γ(req))` and
  `Σ mult/(pole + RLC^γ(resp))` reaching the same public terminal.

  This module ships:

  * `recordsOfReqs` — the generator's `ServiceReq` request/response lists, encoded to width-`m`
    record vectors, packaged as the `PreChallengeRecords` the finite-IO argument consumes.
  * `ioRowSeq` — the *computable* row-environment sequence builder over the committed columns.  The
    reference `progEnvAt`/`memEnvAt` (`FiniteFieldIOAIR.lean:250,258`) are `noncomputable` (they
    `dif`-split on the record length); the underlying `ioRowEnv` (`:58`) is computable, so a checker
    that actually evaluates the gates builds its rows through `ioRowSeq` and reads them back with
    `ioRowSeq_get`.
  * `finiteIO_gates_zero_of_LIO` — **the checker theorem**: for any record set in `IO.LIO` (distinct
    responses that the requests permute) whose sampled pole does not hit a compressed record, there
    is a committed witness under which every gate of the finite-field IO AIRs `finiteIOProgAIR` /
    `finiteIOMemAIR` (`:153,163`) evaluates to zero at every committed row.

  The `pole`-avoidance hypothesis is the unavoidable completeness side-condition; it is precisely
  counted event (1) of the soundness analysis, whose finite failure mass over the `|K|²` coin pairs
  is bounded by `IOFailureEvent_card_le` (`FiniteFieldIOSoundness.lean:283`) — the negligibility
  assertion, not a computational membership test (that event is `noncomputable`).

  Wiring the concrete OP1/cons generated `ServiceReq`s through `recordsOfReqs` and discharging their
  `IO.LIO` / pole-avoidance obligations over `ZMod 97` is done in `FiniteIOInstance.lean`: the record
  set is built from the generator's OWN emitted requests (`Gen.genServiceReqs G.computeNodes`, tied
  to `genTrace` via `gen_op1ServiceReqs_eq` / `gen_consServiceReqs_eq`), so the IO chip is stated
  over `genTrace` output at parity with the compute/memory chips.
-/
import Nock.NockVMROM.Thm54.FiniteFieldIOAIR
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Nock.NockVMROM.Thm54.TraceGen.Row

namespace Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker

open Nock Nock.Reified
open Nock.NockVMROM.Thm54.FiniteIO
open scoped BigOperators

variable {K : Type} [Field K] {m : ℕ}

/-! ## `recordsOfReqs` — the generator's requests/responses as a `PreChallengeRecords` -/

/-- **`recordsOfReqs`.**  Encode the generator's request/response `ServiceReq` lists to width-`m`
    record vectors through a chosen record encoder `e` (the honest encoder fingerprints
    `(root, child, axis, ts)` at the seed `z`), and package them as the `PreChallengeRecords` the
    finite-field IO argument consumes.  Memoryless/positionless: the records are value-keyed, no
    committed-line pointer enters. -/
def recordsOfReqs (e : ServiceReq K → (Fin m → K))
    (reqs resps : List (ServiceReq K)) : PreChallengeRecords K m where
  requests := reqs.map e
  responses := resps.map e

@[simp] theorem recordsOfReqs_requests (e : ServiceReq K → (Fin m → K))
    (reqs resps : List (ServiceReq K)) :
    (recordsOfReqs e reqs resps).requests = reqs.map e := rfl

@[simp] theorem recordsOfReqs_responses (e : ServiceReq K → (Fin m → K))
    (reqs resps : List (ServiceReq K)) :
    (recordsOfReqs e reqs resps).responses = resps.map e := rfl

/-! `progEnvAt`/`memEnvAt` are `noncomputable`; `ioRowEnv` is computable.  A checker that evaluates
    the finite-IO gates builds its rows here and indexes them with `ioRowSeq_get`. -/

/-- One committed IO row: `(acc, inv, mult, multInv, record)`. -/
abbrev IORow (K : Type*) (m : ℕ) := K × K × K × K × (Fin m → K)

/-- **The computable IO row-environment sequence.**  Maps the committed rows to their
    `ioRowEnv`s at the fixed record base `4` and shared `terminal` (`FiniteFieldIOAIR.lean:58`). -/
def ioRowSeq (coins : IOCoins K) (terminal : K) (rows : List (IORow K m)) : List (Env K) :=
  rows.map (fun r => ioRowEnv coins 4 r.1 r.2.1 r.2.2.1 r.2.2.2.1 terminal r.2.2.2.2)

@[simp] theorem ioRowSeq_length (coins : IOCoins K) (terminal : K) (rows : List (IORow K m)) :
    (ioRowSeq coins terminal rows).length = rows.length := by
  simp [ioRowSeq]

/-- The `i`-th environment of the computable sequence is the `ioRowEnv` of the `i`-th committed
    row — so a checker reads back exactly the honest row environment at each index. -/
theorem ioRowSeq_getElem (coins : IOCoins K) (terminal : K) (rows : List (IORow K m))
    (i : ℕ) (h : i < rows.length) :
    (ioRowSeq coins terminal rows)[i]'(by simpa [ioRowSeq] using h)
      = ioRowEnv coins 4 rows[i].1 rows[i].2.1 rows[i].2.2.1
          rows[i].2.2.2.1 terminal rows[i].2.2.2.2 := by
  simp only [ioRowSeq, List.getElem_map]

/-! ## The finite-IO checker theorem -/

/-- The request-side gate-satisfaction predicate: every gate of `finiteIOProgAIR` evaluates to zero
    at every committed request row (the LHS of `reified_finiteIOProg_sound`). -/
def ProgGatesZero (records : PreChallengeRecords K m) (coins : IOCoins K)
    (w : PostChallengeIOWitness records coins) : Prop :=
  ioAccInit.eval (progEnvAt records coins w 0) = 0
    ∧ (∀ i, i < records.requests.length →
        (ioInvPin m 4).eval (progEnvAt records coins w i) = 0)
    ∧ (∀ i, i < records.requests.length →
        ioProgAccStep.eval (Trans.twoRow (progEnvAt records coins w i)
          (progEnvAt records coins w (i + 1))) = 0)
    ∧ ioTerm.eval (progEnvAt records coins w records.requests.length) = 0

/-- The response-side gate-satisfaction predicate: every gate of `finiteIOMemAIR` evaluates to zero
    at every committed response row (the LHS of `reified_finiteIOMem_sound`). -/
def MemGatesZero (records : PreChallengeRecords K m) (coins : IOCoins K)
    (w : PostChallengeIOWitness records coins) : Prop :=
  ioAccInit.eval (memEnvAt records coins w 0) = 0
    ∧ (∀ j, j < records.responses.length →
        (ioInvPin m 4).eval (memEnvAt records coins w j) = 0)
    ∧ (∀ j, j < records.responses.length →
        ioMultBool.eval (memEnvAt records coins w j) = 0)
    ∧ (∀ j, j < records.responses.length →
        ioMultInvPin.eval (memEnvAt records coins w j) = 0)
    ∧ (∀ j, j < records.responses.length →
        ioMemAccStep.eval (Trans.twoRow (memEnvAt records coins w j)
          (memEnvAt records coins w (j + 1))) = 0)
    ∧ ioTerm.eval (memEnvAt records coins w records.responses.length) = 0

/-- **`finiteIO_gates_zero_of_LIO` — the Phase-4b finite-IO checker.**  For a record set in
    `IO.LIO` (distinct responses which the requests permute) whose sampled `pole` does not hit any
    compressed record, there is a committed post-challenge witness under which every gate of both
    finite-field IO AIRs `finiteIOProgAIR m` / `finiteIOMemAIR m` (`FiniteFieldIOAIR.lean:153,163`)
    evaluates to zero at every committed row.  Composes completeness `finiteIO_complete_of_LIO`
    (`FiniteFieldIO.lean:246`) with the tight biconditional `reified_finiteIO_sound` (`:406`).

    The `hpole` denominator hypothesis is the unavoidable completeness side-condition (counted
    event (1) of the soundness analysis, bounded by `IOFailureEvent_card_le`,
    `FiniteFieldIOSoundness.lean:283`). -/
theorem finiteIO_gates_zero_of_LIO {Ksz : ℕ} (records : PreChallengeRecords K m)
    (coins : IOCoins K)
    (hlio : IO.LIO Ksz records.requests records.responses)
    (hpole : ∀ v ∈ records.requests ++ records.responses, compress coins v ≠ 0) :
    ∃ w : PostChallengeIOWitness records coins,
      ProgGatesZero records coins w ∧ MemGatesZero records coins w := by
  obtain ⟨w, hw⟩ := finiteIO_complete_of_LIO records coins hlio hpole
  refine ⟨w, ?_, ?_⟩
  · exact (reified_finiteIO_sound records coins w).mpr hw |>.1
  · exact (reified_finiteIO_sound records coins w).mpr hw |>.2

end Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker

#print axioms Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker.finiteIO_gates_zero_of_LIO
#print axioms Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker.ioRowSeq_getElem
