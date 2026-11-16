/-
  Nock/RedTeam/Batch1690Thm54VclLGenerator.lean

  **The VCL-L generator (cell table, path rows, lookup columns),
  its theorems' axioms, fixtures and the measured `D` / `P` receipts.**

  Production: `TraceGen/GenMemTable.lean` (hash-consed closure, B0/B1 rows, row gates, validity and
  export balances, decode) and `TraceGen/GenPathRows.lean` (axis bits, edge chains, certificate bits,
  path rows, `Demand` from `genComputeSkeleton`'s rows, glue `genVclL_accepts`).

  **Measured** (`scratchpad/vcl-l-v1/ProbeV1.lean`, run against the live `genComputeSkeleton` at
  `K := ℚ`, `lean --run`; the hash-consed closure by interning, cross-checked against the SPEC
  `closureOf` / `exportConsumers` / `vcsOf` list lengths on small instances: `D`, `mx`, `mv`, distinct
  deep reads and `P` agree exactly on dec 12, add 6, ack 12, mul 3).
  `N` = compute rows, `D` = cell-table rows (distinct cells of every subject, formula and read root),
  `Dd` = distinct deep `(root, axis)` reads (path rows), `P` = Σ depth over them (edge rows),
  `mx` = `P` + shallow lookups, `mv` = cell references + root bindings, `bits` = bit length of the
  largest rank `μ` in the closure (`< 110` required), `maxLook` = lookups per row.

  | program      | N     | D    | D/N   | Dd   | P    | P/N   | maxDepth | mv    | mx    | rank bits | maxLook |
  |--------------|-------|------|-------|------|------|-------|----------|-------|-------|-----------|---------|
  | dec 100      | 1200  | 222  | 0.185 | 200  | 400  | 0.333 | 2        | 2622  | 1199  | 5         | 2       |
  | dec 1000     | 12000 | 2022 | 0.169 | 2000 | 4000 | 0.333 | 2        | 26022 | 11999 | 5         | 2       |
  | add 100      | 1415  | 331  | 0.234 | 303  | 808  | 0.571 | 3        | 3164  | 1719  | 6         | 2       |
  | mul 10       | 2429  | 391  | 0.161 | 553  | 2100 | 0.865 | 5        | 5371  | 3653  | 6         | 2       |
  | fib 12       | 30979 | 688  | 0.022 | 874  | 2288 | 0.074 | 3        | 62690 | 22233 | 7         | 2       |
  | ifib 12      | 5605  | 1253 | 0.224 | 1616 | 4071 | 0.726 | 4        | 12485 | 7294  | 6         | 2       |
  | ack 22       | 833   | 102  | 0.122 | 84   | 168  | 0.202 | 2        | 1791  | 704   | 7         | 2       |
-/
import Nock.NockVMROM.Thm54.TraceGen.GenPathRows
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1690

open Nock Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.TraceGen

/-! ## Fixtures (decided) -/

abbrev a1 : Noun := .atom 1
abbrev a2 : Noun := .atom 2
abbrev a3 : Noun := .atom 3
/-- `[[1 2] [[1 2] 3]]`: a shared subterm `[1 2]`. -/
abbrev nShared : Noun := .cell (.cell a1 a2) (.cell (.cell a1 a2) a3)

/-- The closure is hash-consed: three distinct cells (the shared `[1 2]` once). -/
theorem closure_shared : (closureOf [nShared]).length = 3 := by decide

/-- The unfolded tree has four cells; the rank is the unshared count. -/
theorem rank_shared : rankOf nShared = 4 := by decide

/-- The root has in-degree 0, the shared cell 2 (two references), `[[1 2] 3]` 1. -/
theorem vcs_shared : (vcsOf (closureOf [nShared]) []).length = 3 := by decide

/-- Axis bits: `6 = 0b110` reads right then left; `axisFold` inverts them. -/
theorem axisBits_six : axisBits 6 = [true, false] := by decide
theorem axisBits_thirteen : axisBits 13 = [true, false, true] := by decide
theorem axisFold_thirteen : axisFold (axisBits 13) = 13 := axisFold_axisBits 13 (by decide)

/-- The edge parents of the read `(nShared, 6)`: the root and its right child. -/
theorem edgeParents_example :
    (pathSteps nShared (axisBits 6)).map Prod.fst = [nShared, .cell (.cell a1 a2) a3] := by decide

/-- A depth-1 read is an export lookup, a depth-2 read is a path row. -/
theorem shallow_deep_split : isDeep 2 = false ∧ isDeep 3 = false ∧ isDeep 4 = true ∧
    isDeep 13 = true := by decide

/-- The path rows are deduplicated with multiplicity: three reads of two distinct deep keys. -/
theorem deepReads_dedup :
    (deepReads [(nShared, 6), (nShared, 6), (nShared, 4), (nShared, 2)]).length = 2 := by decide

theorem cert_three : certVal (certBits 3) = 59 := by decide

/-! ## Negative control: a root binding dropped

If the root binding is counted in `mv` (`vcsOf`) but dropped from the compute side's validity
lookups, the validity multiset no longer balances (one provide, no consume): the balance is
load-bearing for `mv`. -/

section NC
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp]

theorem nc_dropped_binding_unbalanced (z : Kfp) :
    ¬ ValidityBalanced (tableRows (q := q) z [.cell a1 a2] (vcsOf [.cell a1 a2] [.cell a1 a2]) []) [] := by
  intro h
  have := h.length_eq
  simp [vProv, vCons, tableRows, rowB0, expand, vcsOf, childCells, selfCell, a1, a2, Noun.isCell] at this

end NC

end Nock.RedTeam.Batch1690

#print axioms Nock.RedTeam.Batch1690.closure_shared
#print axioms Nock.RedTeam.Batch1690.nc_dropped_binding_unbalanced
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_serial
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_decode
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_preZNounOfTable
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_rank_limbs
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_rowOK
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_rows_ok
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_mv_eq_consumers
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_mx_eq_consumers
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_validity_balanced
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_export_balanced
#print axioms Nock.NockVMROM.Thm54.VclL.genMemTable_accepts
#print axioms Nock.NockVMROM.Thm54.VclL.closureOf_hyps
#print axioms Nock.NockVMROM.Thm54.VclL.chainAcc_edgesOf
#print axioms Nock.NockVMROM.Thm54.VclL.chainEnd_edgesOf
#print axioms Nock.NockVMROM.Thm54.VclL.cert_sound
#print axioms Nock.NockVMROM.Thm54.VclL.genPathRows_record_is_slot
#print axioms Nock.NockVMROM.Thm54.VclL.genPathRows_ok
#print axioms Nock.NockVMROM.Thm54.VclL.genPathRows_export_balanced
#print axioms Nock.NockVMROM.Thm54.VclL.genVclL_accepts
#print axioms Nock.NockVMROM.Thm54.VclL.genVclL_decode
#print axioms Nock.NockVMROM.Thm54.VclL.genComputeSkeleton_requests_length
#print axioms Nock.NockVMROM.Thm54.VclL.skelRows_requests_length
#print axioms Nock.NockVMROM.Thm54.VclL.demandOfGen_reads_le
#print axioms Nock.NockVMROM.Thm54.VclL.rowLookups_le_two
