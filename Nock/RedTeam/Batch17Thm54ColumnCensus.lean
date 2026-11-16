import Nock.NockVMROM.Cost

/-!
# Column census: relabelling is impossible, expansion is the mechanism (Track A)

The plan's Track A asked whether the paper's per-chip column widths (`62e + 13` compute,
`61e + 13` memory; `199`/`196` at `e = 3`) could be reconciled with our abstract AIR widths
(`94` compute, `35` memory) by *classifying* existing columns as base-field or extension-valued.
They cannot: no integer split works, and our own classified split over-counts. The honest mechanism
is **coordinate expansion** — each extension-valued column expands into `e` base-field columns — and
the paper's widths are already in that expanded form, over a genuinely different (smaller) abstract
column set than ours.

All facts are compiled over the concrete paper defs (`Nock.NockVM.comp_io_columns`), the reified
parametric split (`reifiedNockParamCost`), and the reified AIR width (`computeAIR.numTraceCols`).
-/

namespace Nock.RedTeam.Batch17

open Nock Nock.Reified Nock.NockVMROM

/-- **Compute relabelling is impossible.** No base/extension classification `(b, k)` of the `94`
abstract compute columns reproduces the paper's `199` at `e = 3` while matching `94` at `e = 1`:
`b + k = 94` and `b + 3k = 199` force `2k = 105`, which has no natural solution. -/
theorem b17_compute_no_column_classification :
    ¬ ∃ b k : ℕ, b + k = 94 ∧ b + 3 * k = 199 := by
  rintro ⟨b, k, h1, h2⟩; omega

/-- **Memory relabelling is impossible** and even out of range: `b + k = 35`, `b + 3k = 196` force
`2k = 161` (so `k = 80.5 > 35`), impossible over `ℕ`. -/
theorem b17_memory_no_column_classification :
    ¬ ∃ b k : ℕ, b + k = 35 ∧ b + 3 * k = 196 := by
  rintro ⟨b, k, h1, h2⟩; omega

/-- **Our classified split over-counts.** The reified `(80 extension, 14 base)` compute split
evaluates at `e = 3` to `254`, not the paper's `199`: the abstract column model treats more columns
as extension-valued and is a different, larger object. -/
theorem b17_our_split_overcounts :
    reifiedNockParamCost.compCols.eval 3 = 254 ∧
      paperParamCost.compIOCols.eval 3 = 199 ∧
      reifiedNockParamCost.compCols.eval 3 ≠ paperParamCost.compIOCols.eval 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The paper's `e = 1` width already differs from our abstract width.** `comp_io_columns 1 = 75`
whereas `computeAIR.numTraceCols = 94`, so the two are not the same object even at `e = 1`. -/
theorem b17_paper_e1_ne_abstract :
    Nock.NockVM.comp_io_columns 1 = 75 ∧
      computeAIR.numTraceCols = 94 ∧
      Nock.NockVM.comp_io_columns 1 ≠ computeAIR.numTraceCols := by
  refine ⟨by decide, computeAIR_numTraceCols, ?_⟩
  rw [computeAIR_numTraceCols]; decide

/-- The coordinate-expansion translator: a column split `(base, ext)` — `base` base-field columns and
`ext` extension-valued columns — has base-field width `base + ext · e`. -/
def expandedWidth (base ext e : ℕ) : ℕ := base + ext * e

/-- **The paper's widths are exactly coordinate expansions.** The compute chip is the `(13, 62)`
split and the memory chip is the `(13, 61)` split; both reproduce the paper at `e = 1` and `e = 3`.
Matching them requires re-deriving the base/extension split by coordinate expansion, not relabelling
our `94`/`35` abstract columns. -/
theorem b17_paper_is_coordinate_expansion :
    expandedWidth 13 62 1 = 75 ∧ expandedWidth 13 62 3 = 199 ∧
      expandedWidth 13 61 1 = 74 ∧ expandedWidth 13 61 3 = 196 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Gate and degree measurement (Track C measure) -/

/-- **Degree agrees; gate-count bases differ and are recorded, not forced equal.** Both the paper
and the reified AIR have maximum constraint degree `4`. But the paper counts *transition gates*
(`87` compute, `88` memory at `e = 3`) while the reified AIR counts *degree-4 constraints* at the
abstract row granularity (`13` compute, `1` memory). These are different counting bases; the census
records the mismatch rather than asserting a false equality. -/
theorem b17_degree_agrees_gate_basis_differs {K : Type*} [Field K] :
    reifiedNockParamCost.compMaxDeg = 4 ∧
      paperParamCost.compMaxDeg = 4 ∧
      paperParamCost.compIODeg4.eval 3 = 87 ∧
      paperParamCost.memIODeg4.eval 3 = 88 ∧
      computeAIR.constraints.countP (fun c => c.degree == 4) = 13 ∧
      (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4) = 2 := by
  refine ⟨rfl, rfl, ?_, ?_, computeAIR_deg4, memoryAIR_deg4⟩
  · exact paperParamCost_IO_thm54.2.2.1
  · exact paperParamCost_IO_thm54.2.2.2

/-- **The abstract degree-4 count is not the paper's transition-gate count.** `13 ≠ 87` compute and
`2 ≠ 88` memory: the bases are genuinely different, which is why no equality is asserted. -/
theorem b17_gate_counts_differ {K : Type*} [Field K] :
    computeAIR.constraints.countP (fun c => c.degree == 4) ≠
        paperParamCost.compIODeg4.eval 3 ∧
      (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4) ≠
        paperParamCost.memIODeg4.eval 3 := by
  rw [computeAIR_deg4, memoryAIR_deg4, paperParamCost_IO_thm54.2.2.1,
    paperParamCost_IO_thm54.2.2.2]
  exact ⟨by decide, by decide⟩

end Nock.RedTeam.Batch17

#print axioms Nock.RedTeam.Batch17.b17_degree_agrees_gate_basis_differs
#print axioms Nock.RedTeam.Batch17.b17_gate_counts_differ
#print axioms Nock.RedTeam.Batch17.b17_compute_no_column_classification
#print axioms Nock.RedTeam.Batch17.b17_memory_no_column_classification
#print axioms Nock.RedTeam.Batch17.b17_our_split_overcounts
#print axioms Nock.RedTeam.Batch17.b17_paper_e1_ne_abstract
#print axioms Nock.RedTeam.Batch17.b17_paper_is_coordinate_expansion
