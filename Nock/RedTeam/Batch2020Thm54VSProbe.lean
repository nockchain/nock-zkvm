import Nock.NockVMROM.Thm54.VclL.Handle.Serial
import Nock.NockVMROM.Thm54.VclL.Handle.Ground
import Nock.NockVMROM.Thm54.VclL.Handle.NC
import Nock.NockVMROM.Thm54.VclL.Handle.HashCons

/-!
Collects the serial-table lemmas of the handle development: under `SerialOK` the handle denotation `denH` is functional and grounded (`denH_serial_meaning`), the negative-control tables are rejected (`NC.dup_table_rejected`), and honest handles are one row per noun and injective. The `#print axioms` lines record the axiom dependencies.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch2020

open Nock
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle

/-- Under `SerialOK`, `denH (true, i)` is the noun of the unique row with key `i`. -/
theorem receipt_meaning {q : ℕ} {t : List (CellRowB0 q)} (hs : SerialOK t) (i : ℕ) (n : Noun) :
    denH t (true, i) = some n ↔ ∃ c ∈ t, c.idx = i ∧ rowNounKey t (fuelChip - 1) c = some n :=
  (denH_serial_meaning hs i n).1

/-- The duplicate-row table is rejected by `SerialOK`, while the twin table has equal handles for keys `0` and `1`. -/
theorem receipt_ncs :
    (¬ SerialOK (NC.tDup.map (·.b0))) ∧
      denH (NC.tTwin.map (·.b0)) (true, 0) = denH (NC.tTwin.map (·.b0)) (true, 1) :=
  ⟨NC.dup_table_rejected, NC.nc_op5_ne_by_serial_unsound.2.2.1⟩

end Nock.RedTeam.Batch2020

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.serial_functional
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.serial_functional_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.cellTable_rows_functional
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.getElem?_eq_rowByKey
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.decodeB0_eq_decodeKey
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.denH_serial_meaning
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ExportBalanced.served
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.exportRec_grounded
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.served_grounded
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.toy_grounding
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.NC.nc_dup_serial_op5_eq_accepted
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.NC.dup_table_rejected
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.NC.served_key_functional
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.NC.nc_op5_ne_by_serial_unsound
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.honest_one_row_per_noun
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.honest_handle_eq_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.honest_den_injective
#print axioms Nock.RedTeam.Batch2020.receipt_meaning
#print axioms Nock.RedTeam.Batch2020.receipt_ncs
