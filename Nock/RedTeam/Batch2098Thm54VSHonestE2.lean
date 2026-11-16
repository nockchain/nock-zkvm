/-
  Nock/RedTeam/Batch2098Thm54VSHonestE2.lean

  1. `den_cellRec`, `den_walkRec`, `recDen_entry` (DenRecH): the chip's `den` of a cell / walk record is
     the export key's `recDen` / the walk record's `recDenP` at the row's columns.
  2. `slot_terms_row`, `export_terms_row`, `path_terms_row`, `termValX_row`, `termValP_row` (RowTermH): at
     an honest row (`AtRow`, `Sem`, OP3 hosted) each slot's `act * inv` is the sum of `1/den` over its active
     records, and the export / path accumulator row terms (`termVal` of `slotsX` / `slotsP`) are
     `Sigma 1/recDen (entryRec _)` over `exportEntries` and `Sigma 1/recDenP (entRecP _)` over
     `consEntries (hn r)`.  Hypotheses: honest slot inverses, non-zero active denominators (the priced pole
     event), the limb bridge.
  NOT DONE: `walkTraceH` / `cellTraceH` chip acceptance (the converse of `expandChip_restrict`), the
  `mixedCompile` lowering.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.DenRecH
import Nock.NockVMROM.Thm54.VclL.Handle.RowTermH

set_option autoImplicit false

namespace Nock.RedTeam.Batch2098

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms den_eval
#print axioms den_cellRec
#print axioms den_walkRec
#print axioms recDen_entry
#print axioms selS_eval
#print axioms active_le_one
#print axioms extras_01
#print axioms slot_terms_row
#print axioms filter_export_eq
#print axioms filter_path_eq
#print axioms export_terms_row
#print axioms path_terms_row
#print axioms termVal_eq_slots
#print axioms termValX_row
#print axioms termValP_row

end Nock.RedTeam.Batch2098
