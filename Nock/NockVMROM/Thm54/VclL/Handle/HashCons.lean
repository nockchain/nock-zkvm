/-
  Nock/NockVMROM/Thm54/VclL/Handle/HashCons.lean

  Additive; no generator edit, `Gen.lean` untouched.

  The honest cell rows (`honestVCLJ_of_run` → `HonestMemHonest` / `HonestVCLW` → `cellRows0 … H.d.cells`;
  B0 form `GenMemTable.tableB0`) are indexed by `Demand.cells d = closureOf d.roots`, a `List.dedup`.
  * `honest_one_row_per_noun` — every noun of the closure has exactly one row;
  * `honest_handle_eq_iff` — two closure nouns have equal honest serials iff they are equal;
  * `honest_den_injective` — on the honest B0 table, two serials with equal `denH` are equal:
    OP5 "=" decided by handle equality is COMPLETE on honest traces (equal nouns get equal handles).
  Verdict: PROVED (hash-consing is by construction, `closureOf_nodup`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.Serial
import Nock.NockVMROM.Thm54.TraceGen.GenPathRows

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock
open Nock.NockVMROM.Thm54.VclL

section HashCons
variable {q : ℕ}

/-- **One row per distinct noun**: the honest table's index list is `closureOf d.roots`, a dedup. -/
theorem honest_one_row_per_noun (d : Demand) : ∀ n ∈ d.cells, d.cells.count n = 1 :=
  fun _ hn => List.count_eq_one_of_mem (closureOf_nodup _) hn

/-- **Honest serials name nouns injectively**: two closure nouns have equal serials iff equal. -/
theorem honest_handle_eq_iff (d : Demand) {n m : Noun} (hn : n ∈ d.cells) (hm : m ∈ d.cells) :
    d.cells.idxOf n = d.cells.idxOf m ↔ n = m := by
  constructor
  · intro h
    have hn' := List.idxOf_lt_length_iff.mpr hn
    have hm' := List.idxOf_lt_length_iff.mpr hm
    have e1 := List.getElem_idxOf hn'
    have e2 := List.getElem_idxOf hm'
    simp only [h] at e1
    exact e1.symm.trans e2
  · rintro rfl; rfl

/-- The honest serial `i` of the closure denotes the closure's `i`-th noun. -/
theorem honest_den_getElem (d : Demand) (vcs xcs : List Noun)
    (hatoms : ∀ n ∈ d.cells, AtomsLt q n) (hrank : ∀ n ∈ d.cells, rankOf n < 2 ^ 110)
    {i : ℕ} (hi : i < d.cells.length) :
    denH (tableB0 q d.cells vcs xcs) (true, i) = some d.cells[i] := by
  have hmem : d.cells[i] ∈ d.cells := List.getElem_mem hi
  have hidx : d.cells.idxOf d.cells[i] = i := (closureOf_nodup _).idxOf_getElem i hi
  rw [denH_cell]
  have := genMemTable_preZNounOfTable d.cells vcs xcs (fun n hn => closureOf_isCell hn)
    (fun n hn c hc => closureOf_closed hn hc) hatoms _ hmem (hrank _ hmem)
  rwa [hidx] at this

/-- **Hash-consing, denotation form**: on the honest B0 table, serials with equal `denH` are
equal, so OP5 "=" by handle equality is complete on honest traces. -/
theorem honest_den_injective (d : Demand) (vcs xcs : List Noun)
    (hatoms : ∀ n ∈ d.cells, AtomsLt q n) (hrank : ∀ n ∈ d.cells, rankOf n < 2 ^ 110)
    {i j : ℕ} (hi : i < d.cells.length) (hj : j < d.cells.length)
    (h : denH (tableB0 q d.cells vcs xcs) (true, i) = denH (tableB0 q d.cells vcs xcs) (true, j)) :
    i = j := by
  rw [honest_den_getElem d vcs xcs hatoms hrank hi, honest_den_getElem d vcs xcs hatoms hrank hj,
    Option.some.injEq] at h
  exact (List.Nodup.getElem_inj_iff (closureOf_nodup _)).mp h

end HashCons

end Nock.NockVMROM.Thm54.VclL.Handle
