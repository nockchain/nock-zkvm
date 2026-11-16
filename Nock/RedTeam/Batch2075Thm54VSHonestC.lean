/-
  Nock/RedTeam/Batch2075Thm54VSHonestC.lean

  1. `rowOfSkelH` (a new builder beside `rowOfSkel`): OP3 hosts `hdN sf1 / tlN sf1` in `f_tth / f_ttt`.
     `honest_row_base_gatesH`: the base gates at it (the 101 arithmetic + equality gates); `op3_witness_hosted`:
     the hosted columns of an OP3 row read exactly `expKey sf1`; `handle_cells_memH`: the demand covers them.
  2. `slot_bad_roots` / `pole_free_but_few`: the pole-free condition `D != 0 or A = 0` is the complement of the
     named honest bad event `SlotBad`; over `N` rows at most `4N` coins `rho` are bad (1 per no-pair slot,
     2 for the pair slot), no hypothesis.  `slotGate_bad_unsat`: at a bad coin no inverse satisfies the gate.
  3. `mhH` / `export_total_link(_inv)`: the honest multiplicity of `cellChipH` column 129 and the equality of
     the compute consumed total with the cell twin's `mh`-weighted total, for every weight (`1/den`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestMh
import Nock.NockVMROM.Thm54.VclL.Handle.PoleFree

set_option autoImplicit false

namespace Nock.RedTeam.Batch2075

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms rowOfSkelH_sem
#print axioms honest_row_base_gatesH
#print axioms op3_witness_hosted
#print axioms handle_cells_memH
#print axioms slot_bad_roots
#print axioms pole_free_but_few
#print axioms slotGate_honest_of_not_bad
#print axioms slotGate_bad_unsat
#print axioms exportEntries_H
#print axioms export_total_link
#print axioms export_total_link_inv

end Nock.RedTeam.Batch2075
