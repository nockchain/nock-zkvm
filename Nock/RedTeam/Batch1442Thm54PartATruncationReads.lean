import Nock.NockVMROM.Thm54.P8Core.PartAOpenItems

/-
  Nock/RedTeam/Batch1442Thm54PartATruncationReads.lean

  **L4's open item (b) — the truncation hides no
  read.**

  The parallel package's consumed event is L3's twelve-coin event at the 303-column truncation of
  the 309 trace (`PartAStaged.consumedFailureEvent309`).  The truncation drops exactly the six walk
  limbs `303..308` (`PartAOpenItems.dropped_eq_walkLimbs`) and the event reads the 309 trace only
  through columns `< 303` (`PartAOpenItems.consumedFailureEvent309_congr_lt303`).  A read would be
  HIDDEN if a landed summand read the walk `count`/`acc` — which the landed layout hosts in the two
  host roles of each row's own state (`Unhosted309.hostRolesOf`) and the 309 layout moves to
  `303..308` — since the truncation keeps the host cells (fingerprints at 309) and drops the walk.

  Every consumed summand reads the compute trace through four families of row readers:
  (i) the decoded table `Env.ofSubst computeSubst` (`decodeSource`: `inpOf`, `pubOfState`,
  `decOf`, `exOf` read decoded indices `0..92` and challenges only — `decoders_read_lt94`), used by
  the built strategy (summands 1, 12, 13) and the label decoders (5, 6, 8);
  (ii) the hosted child tags `childTagHost curReader (rowStateOf E)` (summands 5, 8);
  (iii) the request records and activity masks `rowRecord` / `activeMask` (summands 2, 3);
  (iv) selectors and round-0 base / certificate columns (summands 1-M1, 3, 6, 11).

  * `decoded_insensitive`, `tags_insensitive`, `records_insensitive` (decided over all 11 states):
    on a row whose selectors are one-hot at state `s`, none of (i)–(iii) reads the host roles of
    `s`, the residual roles `58/59`, or any source index `≥ 303` (`Unhosted309.diffAt s`); (iv)
    reads no `𝕂`-role at all.
  * `decoded_eq_off_hosts`: the soundness form — two row environments that match the selectors
    and agree off `diffAt s` decode the same table at every index `< 94`.
  * Positive controls: the retargeted walk source `coreSrc 74` IS host-sensitive at every state
    (`control_walk_sensitive`), and the instrument sees the four cross-state tag reads that do touch
    a host (`control_cross_state_tags`: a tag decoder of state `t ≠ s` at a row of state `s`).

  So no consumed summand reads the walk values in either layout: the truncation hides no read.
  Scope: rows with one-hot selectors (acceptance forces them; the event matters only on accepted
  traces)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1442

open Nock Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

/-! ## (i) The decoded table -/

/-- **(i)** Every decoded index `< 94` is host-insensitive at every state. -/
theorem decoded_insensitive :
    ∀ s : Fin 11, ∀ k : Fin 94,
      Insensitive (curSel s) (diffAt s) (computeTraceSubst .traceCur k) = true := by
  decide +kernel

section Readers
variable {K : Type*} [Field K]

/-- The strategy's decoders read decoded indices `0..92` (and challenges) only. -/
theorem decoders_read_lt94 {E E' : Env K} (h : ∀ k, k < 94 → E.trace k = E'.trace k)
    (hc : E.chal = E'.chal) (st : ComputeTable.State) :
    inpOf E = inpOf E' ∧ pubOfState E st = pubOfState E' st ∧ decOf E = decOf E' ∧
      exOf E = exOf E' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [inpOf, hc]
  · simp (disch := omega) only [pubOfState, fpOf, mrOf, h]
  · simp (disch := omega) only [decOf, fpOf, h]
  · simp (disch := omega) only [exOf, h]

/-- **Soundness form of (i)**: on a row matching the one-hot selectors at `s`, two source envs that
agree off `diffAt s` decode the same table at every index `< 94`. -/
theorem decoded_eq_off_hosts (s : Fin 11) {E₁ E₂ : Env K}
    (h₁ : Matches (curSel s) E₁) (h₂ : Matches (curSel s) E₂)
    (hagree : ∀ k i, diffAt s k i = false → varVal E₁ k i = varVal E₂ k i)
    (k : ℕ) (hk : k < 94) :
    (computeTraceSubst .traceCur k).eval E₁ = (computeTraceSubst .traceCur k).eval E₂ :=
  eval_eq_of_insensitive (curSel s) (diffAt s) _ (decoded_insensitive s ⟨k, hk⟩) h₁ h₂ hagree

end Readers

/-! ## (ii) The hosted child tags, at the row's own state -/

theorem tags_insensitive :
    ∀ s : Fin 11, ∀ j : Fin 3,
      Insensitive (curSel s) (diffAt s)
        (ComputeWalkLabel.childTagHost ComputeWalkLabel.curReader (stOfIdx s) j) = true := by
  decide +kernel

/-! ## (iii) The request records and activity masks -/

/-- The source of record slot `c` of request slot `j` (`HostileRecordLists.rowRecord`). -/
def recordSrc (j : Fin 3) (c : Fin 10) : Expr :=
  if (c : ℕ) = 9 then (sampledSlotE .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else if (c : ℕ) = 6 then (sampledSlotT .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else if (c : ℕ) = 8 then (sampledSlotC .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).subst finalSampledNamespace

theorem recordSrc_eval {F K : Type} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (j : Fin 3) (c : Fin 10) :
    OptimizedComputeHostileAccumulator.rowRecord env j c = (recordSrc j c).eval env.toSourceEnv := by
  unfold OptimizedComputeHostileAccumulator.rowRecord recordSrc
  split_ifs <;> rfl

theorem records_insensitive :
    ∀ s : Fin 11, ∀ j : Fin 3,
      (∀ c : Fin 10, Insensitive (curSel s) (diffAt s) (recordSrc j c) = true) ∧
        Insensitive (curSel s) (diffAt s) (sampledActive .traceCur (j : ℕ)) = true := by
  decide +kernel

/-! ## Positive controls -/

/-- The retargeted walk-count step reads the host cells at every state (L2's
`retargeted_core_sensitive`, restated at one position). -/
theorem control_walk_sensitive :
    ∀ s : Fin 11, Insensitive (curSel s) (diffAt s) (coreSrc ⟨74, by omega⟩) = false := by
  decide +kernel

/-- The instrument sees host reads in the tag decoders when the decoder's state is NOT the row's:
exactly four `(row state, decoder state, slot)` triples. -/
theorem control_cross_state_tags :
    ((List.finRange 11).flatMap fun s => (List.finRange 11).flatMap fun t =>
      (List.finRange 3).filterMap fun j =>
        if Insensitive (curSel s) (diffAt s)
            (ComputeWalkLabel.childTagHost ComputeWalkLabel.curReader (stOfIdx t) j) then none
        else some ((s : ℕ), (t : ℕ), (j : ℕ))).length = 4 := by
  decide +kernel

end Nock.RedTeam.Batch1442

#print axioms Nock.RedTeam.Batch1442.decoded_insensitive
#print axioms Nock.RedTeam.Batch1442.decoded_eq_off_hosts
#print axioms Nock.RedTeam.Batch1442.decoders_read_lt94
#print axioms Nock.RedTeam.Batch1442.tags_insensitive
#print axioms Nock.RedTeam.Batch1442.records_insensitive
#print axioms Nock.RedTeam.Batch1442.control_walk_sensitive
#print axioms Nock.RedTeam.Batch1442.control_cross_state_tags
