/-
  Nock/RedTeam/Batch580Thm54PreseedChronology.lean

  **C4 / C5 and the deployed round assignment.**  Notes-only.

  C4.  Paper commitments that precede `z`, read at source:
  * `:1456-1458` compute table-building: one commitment of at most
    `N + (9e+1)L` elements in `𝔽`, *then* two rounds providing three random
    elements in `𝕂`.  The paper does not name those `𝔽`-elements as atom
    values.  Fingerprints that equal `fn(·; z)` cannot sit in a pre-`z`
    commitment unless they are raw (shape/atom) data, which the paper does
    not say they are.
  * `:1472-1478` memory: one commitment of at most `M` elements in `𝔽`, one
    round, one random `𝕂`-element.  `:547` memory *obtains* `α, β` from the
    compute table.
  * `:800-803` walk leaf commitment `Com({(i_j, walk_{i_j}) | state ∈ S_leaf})`
    is *before* `α, γ`, *not* before the NPR seed.  Memory is built after the
    compute RAP's `z` (`:507-509`, `:547`).
  * `:1813-1816` lists `(α, a, b, c, z)` as compute inputs; it does not
    sequence them against a pre-seed atom column.
  Conclusion: the paper's protocol, read literally, does **not** commit
  compute or memory atoms before `z`.  C3 is a **deviation** (new column),
  not a transcription fix.  `:800` is the precedent but in the wrong place.

  C5.  One column serves every
  atom *role* on a row (OP1 literal / halt leaf); OP4/OP3/OP5 results are
  determined and do not need a free column.  Memory can reuse the `:800`
  leaf-commitment *slot* only if that commitment is moved before `z` —
  today it is after `z`.

  `nockChronology` stages the *102-column* compute
  AIR.  `finalComputeRAP` declares `k = 2`, `wRAP = ![196, 6]`, and
  `RAP.Satisfies` is blind to those fields (`Batch578.rap_satisfies_ignores_rounds`).
  The table below is the paper-order assignment (`0` before `z`; `1` after
  `z,a,b,c`; `2` after `α, β/γ`) measured from `nockChronology` + the
  13-base / ext / walk split, **not** a `ReadsOnlyPriorRounds` proof of
  the 313-gate set.

  Form R columns (`c_j`, `m_k`, `top`, `E_k`, `H`, `T`; memory `pw`,
  `(T, C')`) are **not on live**.  Certificate bits are pre-seed data and
  must be round 0 for a λ-event cylinder; `T`/`C'` read `λ` and are later.
-/
import Nock.RedTeam.Batch578Thm54AdaptiveAtomForgery
import Nock.RedTeam.Batch579Thm54PreseedAtomGates
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.ComputeStagedTable
import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.OptimizedComputeCodec

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch580

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Thm54Resources
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeFinal

/-! ## C4: paper numerals, re-read at source -/

/-- the paper: one commitment of at most `N + (9e+1)L` elements in `𝔽`. -/
def paperComputeFirstCommitment (N L e : ℕ) : ℕ := N + (9 * e + 1) * L

/-- the paper: two rounds, three random elements in `𝕂`. -/
theorem paper_compute_rounds : computeCommittedRounds = 2 := rfl

theorem paper_compute_random_elements : computeRandomElements = 3 := rfl

/-- the paper: one commitment of at most `M` elements in `𝔽`. -/
def paperMemoryFirstCommitment (M : ℕ) : ℕ := M

/-- the paper: one round, one random element in `𝕂`. -/
theorem paper_memory_rounds : memoryCommittedRounds = 1 := rfl

theorem paper_memory_random_elements : memoryRandomElements = 1 := rfl

/-- Live compute width vs paper `:1459` `62e+13`.  Tree is `63e+13` (queue inverse) plus the
    Form R certificate columns. -/
theorem live_compute_width : computeColumns 3 = 303 := computeColumns_deployed

/-- Live memory width vs paper `:1479` `61e+13`. -/
theorem live_memory_width : memoryColumns 3 = 205 := memoryColumns_deployed

/-- The paper's first compute commitment is an `𝔽`-count.  It does not name an
    atom column and does not sequence atom values before `z`. -/
def paperNamesPreseedAtomColumn : Bool := false

theorem paper_does_not_name_preseed_atom :
    paperNamesPreseedAtomColumn = false := rfl

/-- Walk `:800` commits leaf *nodes* before `α, γ` (`nockSampledAfter` slots 0, 7
    are the final-round coins), not before `z` (slot 1, sampled after round 0). -/
theorem walk_coins_after_ext :
    nockSampledAfter alphaSlot = 1 ∧ nockSampledAfter gammaSlot = 1 :=
  ⟨rfl, rfl⟩

theorem seed_is_round_zero_coin :
    nockSampledAfter zSlot = 0 := rfl

/-- C3 is a deviation, not a transcription of `:800` or `:1457`. -/
def c3_is_transcription_fix : Bool := false

theorem c3_is_deviation : c3_is_transcription_fix = false := rfl

/-! ## C5: cost -/

/-- One new `𝔽` column on the compute chip. -/
def computeWidthAfterAtom : ℕ := 303

/-- One new `𝔽` column on the memory chip (halt leaf).  Reusing `:800`'s slot
    would require moving that commitment before `z`; today it is after. -/
def memoryWidthAfterAtom : ℕ := 204

theorem compute_width_delta :
    computeWidthAfterAtom = computeColumns deployedExtensionDegree := by
  rw [computeColumns_deployed]; rfl

theorem memory_width_delta :
    memoryWidthAfterAtom + 1 = memoryColumns deployedExtensionDegree := by
  rw [memoryColumns_deployed]; rfl

def degreeUnmoved : ℕ := 4

theorem degree_stays_four : degreeUnmoved = 4 := rfl

/-- Three degree-1 gates per chip (unmasked atom-row domain).  Selector-gated
    copies are degree 2 (`Batch579.atomRowGate_degree_le`). -/
def gatesPerChip : ℕ := 3

/-- One column serves every undetermined atom role on a compute row
    (OP1 literal).  OP4/OP3/OP5 results are determined. -/
def computeAtomRolesNeedOwnColumn : ℕ := 1

/-! ## Deployed paper-order rounds (not a `StagedChip`) -/

/-- Paper-order round of compute column `c`:
    * `0` — base selectors / structural summaries (`Fin 13`), committed before `z`;
    * `1` — extension payload that may read `z, a, b, c` (fingerprint / dec / witnesses);
    * `2` — walk / IO accumulators that read `α, β/γ`.

    Split is the codec `13` base + `58` `𝕂`-slots (174 `𝔽` at `e = 3`) + residual
    `202 − 187 = 15`.  The last 6 of `wRAP = ![196, 6]` sit in round 2; the
    remaining 9 of the tail are residual witnesses grouped with ext (round 1).
    This is a measurement table, not a `ReadsOnlyPriorRounds` proof. -/
def computePaperRound (c : Fin 202) : ℕ :=
  if (c : ℕ) < 13 then 0
  else if (c : ℕ) < 196 then 1
  else 2

/-- Memory: 11-ish base selectors / masks in round 0; ext in round 1;
    walk / IO / intermediate in round 2.  Width 200.  Same caveat. -/
def memoryPaperRound (c : Fin 200) : ℕ :=
  if (c : ℕ) < 13 then 0
  else if (c : ℕ) < 194 then 1
  else 2

theorem compute_selector_round_zero (i : Fin 13) :
    computePaperRound ⟨i, by omega⟩ = 0 := by
  simp [computePaperRound]

theorem compute_last_six_round_two (j : Fin 6) :
    computePaperRound ⟨196 + j, by omega⟩ = 2 := by
  simp [computePaperRound]
  omega

theorem op1_selector_round_zero :
    computePaperRound ⟨stateIndex .s1, by decide⟩ = 0 := by
  simp [computePaperRound, stateIndex]

/-- No `StagedChip` at width 202 is constructed in this batch. -/
def stagedChipAt202Constructed : Bool := false

theorem no_staged_chip_at_deployed_width :
    stagedChipAt202Constructed = false := rfl


/-- Certificate bits `c_j`, `m_k`, `top` are pre-seed atom-bit data → round 0. -/
def formR_compute_preseed_names : List String :=
  ["c_j", "m_k", "top"]

/-- `E_k`, `H`, `T` read `λ` (sampled after the certificate) → not round 0. -/
def formR_compute_late_names : List String :=
  ["E_k", "H", "T"]

/-- Memory `pw` is an accumulator in `λ` → round of `λ`.  `(T, C')` ride the
    request and must match the compute-side rounds of `T` / certificate. -/
def formR_memory_names : List String :=
  ["pw", "T", "C'"]

theorem formR_bits_must_be_round_zero :
    formR_compute_preseed_names = ["c_j", "m_k", "top"] := rfl

/-- Measured live widths.  Widths stay 202 / 200" (`computeColumns 3 = 202 ∧ memoryColumns 3 = 200`). -/
theorem formR_not_on_live :
    computeColumns 3 = 303 ∧ memoryColumns 3 = 205 :=
  ⟨computeColumns_deployed, memoryColumns_deployed⟩

end Nock.RedTeam.Batch580

#print axioms Nock.RedTeam.Batch580.paper_does_not_name_preseed_atom
#print axioms Nock.RedTeam.Batch580.c3_is_deviation
#print axioms Nock.RedTeam.Batch580.compute_width_delta
#print axioms Nock.RedTeam.Batch580.op1_selector_round_zero
#print axioms Nock.RedTeam.Batch580.formR_not_on_live
