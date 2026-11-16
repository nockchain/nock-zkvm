/-
  Nock/RedTeam/Batch2095Thm54VSHonestE.lean

  1. `inTree_pathKeys` (PathKeyShape): every node of a generated tree has `rowPathKeys g` = the OP0 / OP9
     read `pkOf (rowOfSkel g.skel)` (generator induction mirroring `inTree_rowShape`).
  2. `demandH2` (HonestDemand2): the demand whose walk reads are `walkReadsH rows` (OP0/OP9 plus the OP5
     pair).  `demandH2_cells_mem_iff` / `demandH2_cells_perm`: the cells are unchanged as a SET (Perm); exact
     list equality is not claimed.  `demandH2_balance`: the walk balance for its reads.
     `pathKind_rowPathKeys_eq`: its OP0 / OP9 part equals `rowPathKeys` up to the `pathKind` filter (literal
     equality is false: axis-1 reads are in `rowPathKeys`, not in `walkReadsH`).
  3. `slot_term` (SlotTermH): a slot's accumulator contribution `act * inv` equals the sum of `1/den` over
     its active records (export and path), given 0/1 activity, at most one active, non-zero active
     denominators.  Pure algebra; the per-row activity casework is NOT done.
  NOT DONE: `walkTraceH` / `cellTraceH` chip acceptance (needs the converse of `expandChip_restrict`),
  per-row `termVal`, mixedCompile lowering.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.PathKeyShape
import Nock.NockVMROM.Thm54.VclL.Handle.HonestDemand2
import Nock.NockVMROM.Thm54.VclL.Handle.SlotTermH

set_option autoImplicit false

namespace Nock.RedTeam.Batch2095

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms inTree_pathKeys
#print axioms rpk_eq
#print axioms consEntries_root_mem
#print axioms walkReads_root_mem
#print axioms pathKeys_root_mem
#print axioms demandH2_cells_mem_iff
#print axioms demandH2_cells_perm
#print axioms demandH2_one_row
#print axioms handle_cells_memH2
#print axioms demandH2_balance
#print axioms isPathAx_iff
#print axioms pathKind_rowPathKeys_row
#print axioms pathKind_rowPathKeys_eq
#print axioms walkReadsH_split
#print axioms sum_filter_act
#print axioms sum_filter_act1
#print axioms slot_term

end Nock.RedTeam.Batch2095
