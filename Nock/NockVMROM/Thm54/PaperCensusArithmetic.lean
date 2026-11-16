import Nock.NockVMROM.Thm54.MonolithicMemRAP

/-!
# Theorem 5.4 paper-census arithmetic

This module isolates the first R6 question: whether the two generic compilation results cited in
the body numerically account for the final monolithic fingerprints.

The source RAP counts are already the results of applying the walk construction:

* `Thm:comp_38` states `57e + 13` columns and `20e + 13` transition gates, and its proof obtains them by applying `Thm:Walk_IOP`;
* `Thm:mem_38` states `54e + 5` columns and `20e + 13` transition gates, and its proof applies `Corr:forest`.

`Thm:IO_result` then lists the *additional* generic IO costs:

* compute: `e` columns and `e` transition gates;
* memory: `e + 1` columns and one degree-one plus `e` degree-three transition gates.

The identities below compare exactly those stated increments with the final fingerprints at
the paper.  They do not infer a semantic defect: the body also says the final
construction is formed "along with the IO columns", so the residual summands are
the precisely located connective/census data that a semantic chip template must account for.
-/

namespace Nock.NockVMROM.Thm54
namespace PaperCensusArithmetic

/-- `Thm:comp_38` after adding only `Thm:IO_result`'s stated compute-column increment. -/
def compAfterGenericIOColumns (e : ℕ) : ℕ :=
  Nock.ComputeTable.comp_columns e + e

/-- `Thm:comp_38` after adding only `Thm:IO_result`'s stated compute-transition increment. -/
def compAfterGenericIOTransitions (e : ℕ) : ℕ :=
  Nock.ComputeTable.comp_deg4_gates e + e

/-- `Thm:mem_38` after adding only `Thm:IO_result`'s stated memory-column increment. -/
def memAfterGenericIOColumns (e : ℕ) : ℕ :=
  Nock.MemoryTable.mem_columns e + (e + 1)

/-- `Thm:mem_38` after adding only `Thm:IO_result`'s stated memory-transition increments. -/
def memAfterGenericIOTransitions (e : ℕ) : ℕ :=
  Nock.MemoryTable.mem_deg4_gates e + (1 + e)

/-- The stated compute source-plus-generic-IO column arithmetic normalizes to `58e + 13`. -/
theorem compAfterGenericIOColumns_eq (e : ℕ) :
    compAfterGenericIOColumns e = 58 * e + 13 := by
  simp [compAfterGenericIOColumns, Nock.ComputeTable.comp_columns]
  omega

/-- The stated compute source-plus-generic-IO transition arithmetic normalizes to `21e + 13`. -/
theorem compAfterGenericIOTransitions_eq (e : ℕ) :
    compAfterGenericIOTransitions e = 21 * e + 13 := by
  simp [compAfterGenericIOTransitions, Nock.ComputeTable.comp_deg4_gates]
  omega

/-- The stated memory source-plus-generic-IO column arithmetic normalizes to `55e + 6`. -/
theorem memAfterGenericIOColumns_eq (e : ℕ) :
    memAfterGenericIOColumns e = 55 * e + 6 := by
  simp [memAfterGenericIOColumns, Nock.MemoryTable.mem_columns]
  omega

/-- The stated memory source-plus-generic-IO transition arithmetic normalizes to `21e + 14`. -/
theorem memAfterGenericIOTransitions_eq (e : ℕ) :
    memAfterGenericIOTransitions e = 21 * e + 14 := by
  simp [memAfterGenericIOTransitions, Nock.MemoryTable.mem_deg4_gates]
  omega

/-- Direct subtraction from `Thm:comp_38` to the capstone leaves `5e` columns.  This is an
observed identity between the two paper statements, not a derivation of the summand. -/
theorem comp_capstone_from_walk_columns (e : ℕ) :
    Nock.ComputeTable.comp_columns e + 5 * e = Nock.NockVM.comp_io_columns e := by
  simp [Nock.ComputeTable.comp_columns, Nock.NockVM.comp_io_columns]
  omega

/-- Direct subtraction from `Thm:comp_38` to the capstone leaves `4e + 2` transition gates. -/
theorem comp_capstone_from_walk_transitions (e : ℕ) :
    Nock.ComputeTable.comp_deg4_gates e + (4 * e + 2)
      = Nock.NockVM.comp_io_deg4_gates e := by
  simp [Nock.ComputeTable.comp_deg4_gates, Nock.NockVM.comp_io_deg4_gates]
  omega

/-- Direct subtraction from `Thm:mem_38` to the capstone leaves `7e + 8` columns. -/
theorem mem_capstone_from_walk_columns (e : ℕ) :
    Nock.MemoryTable.mem_columns e + (7 * e + 8) = Nock.NockVM.mem_io_columns e := by
  simp [Nock.MemoryTable.mem_columns, Nock.NockVM.mem_io_columns]
  omega

/-- Direct subtraction from `Thm:mem_38` to the capstone leaves `4e + 3` transition gates. -/
theorem mem_capstone_from_walk_transitions (e : ℕ) :
    Nock.MemoryTable.mem_deg4_gates e + (4 * e + 3)
      = Nock.NockVM.mem_io_deg4_gates e := by
  simp [Nock.MemoryTable.mem_deg4_gates, Nock.NockVM.mem_io_deg4_gates]
  omega

/-- The final compute width needs a further `4e` beyond the explicitly listed generic increment. -/
theorem comp_columns_residual (e : ℕ) :
    compAfterGenericIOColumns e + 4 * e = Nock.NockVM.comp_io_columns e := by
  simp [compAfterGenericIOColumns, Nock.ComputeTable.comp_columns, Nock.NockVM.comp_io_columns]
  omega

/-- The final compute transition count needs a further `3e + 2`. -/
theorem comp_transitions_residual (e : ℕ) :
    compAfterGenericIOTransitions e + (3 * e + 2) = Nock.NockVM.comp_io_deg4_gates e := by
  simp [compAfterGenericIOTransitions, Nock.ComputeTable.comp_deg4_gates,
    Nock.NockVM.comp_io_deg4_gates]
  omega

/-- The final memory width needs a further `6e + 7`. -/
theorem mem_columns_residual (e : ℕ) :
    memAfterGenericIOColumns e + (6 * e + 7) = Nock.NockVM.mem_io_columns e := by
  simp [memAfterGenericIOColumns, Nock.MemoryTable.mem_columns, Nock.NockVM.mem_io_columns]
  omega

/-- The final memory transition count needs the same further `3e + 2` as the compute side. -/
theorem mem_transitions_residual (e : ℕ) :
    memAfterGenericIOTransitions e + (3 * e + 2) = Nock.NockVM.mem_io_deg4_gates e := by
  simp [memAfterGenericIOTransitions, Nock.MemoryTable.mem_deg4_gates,
    Nock.NockVM.mem_io_deg4_gates]
  omega

/-- At every genuine extension degree, the explicitly enumerated compute-column increment alone
does not reach the capstone width. -/
theorem comp_stated_increment_ne_capstone {e : ℕ} (he : 0 < e) :
    compAfterGenericIOColumns e ≠ Nock.NockVM.comp_io_columns e := by
  rw [compAfterGenericIOColumns_eq]
  simp [Nock.NockVM.comp_io_columns]
  omega

/-- The corresponding memory-column comparison also remains strict at every positive degree. -/
theorem mem_stated_increment_ne_capstone {e : ℕ} (he : 0 < e) :
    memAfterGenericIOColumns e ≠ Nock.NockVM.mem_io_columns e := by
  rw [memAfterGenericIOColumns_eq]
  simp [Nock.NockVM.mem_io_columns]
  omega

/-- Concrete cubic snapshot: the stated generic increments reach `187/76` on compute and `171/77`
on memory, while the capstone fingerprints are `199/87` and `196/88`. -/
theorem cubic_snapshot :
    compAfterGenericIOColumns 3 = 187 ∧
      compAfterGenericIOTransitions 3 = 76 ∧
      memAfterGenericIOColumns 3 = 171 ∧
      memAfterGenericIOTransitions 3 = 77 ∧
      Nock.NockVM.comp_io_columns 3 = 199 ∧
      Nock.NockVM.comp_io_deg4_gates 3 = 87 ∧
      Nock.NockVM.mem_io_columns 3 = 196 ∧
      Nock.NockVM.mem_io_deg4_gates 3 = 88 := by
  norm_num [compAfterGenericIOColumns, compAfterGenericIOTransitions,
    memAfterGenericIOColumns, memAfterGenericIOTransitions,
    Nock.ComputeTable.comp_columns, Nock.ComputeTable.comp_deg4_gates,
    Nock.MemoryTable.mem_columns, Nock.MemoryTable.mem_deg4_gates,
    Nock.NockVM.comp_io_columns, Nock.NockVM.comp_io_deg4_gates,
    Nock.NockVM.mem_io_columns, Nock.NockVM.mem_io_deg4_gates]

end PaperCensusArithmetic
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.comp_columns_residual
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.comp_transitions_residual
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.mem_columns_residual
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.mem_transitions_residual
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.comp_capstone_from_walk_columns
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.comp_capstone_from_walk_transitions
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.mem_capstone_from_walk_columns
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.mem_capstone_from_walk_transitions
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.comp_stated_increment_ne_capstone
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.mem_stated_increment_ne_capstone
#print axioms Nock.NockVMROM.Thm54.PaperCensusArithmetic.cubic_snapshot
