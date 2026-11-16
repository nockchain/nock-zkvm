/-
  Nock/RedTeam/Batch4266Thm54J8r3bReader.lean

  `hrealA`: `holdsN_formula_cell` (an atom formula never holds, so the public check `isCellN c.formula` rejects
  no true claim) and `hrealA_of_check`.  At the canonical reader `valReader`: `hidxA_valReader` (serial gate),
  `hB_valReader` (g1).  S1: `SmallU` (the restated smallness: what the chain lemmas read), `smallU_of_small`, and
  `smallU_valReader` (from the gates, `nA ≤ 2^62`, `ValidityServed`, `ConsumeServedQ`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8

namespace Nock.RedTeam.Batch4266

open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8

#print axioms holdsN_formula_cell
#print axioms hrealA_of_check
#print axioms natOf_eq_val
#print axioms tA_idx
#print axioms hidxA_valReader
#print axioms limbs_lt_B
#print axioms hB_valReader
#print axioms smallU_of_small
#print axioms val_le_one_of_bool
#print axioms atom_bool
#print axioms idR_lt_of_served
#check @smallU_valReader
#print axioms smallU_valReader

end Nock.RedTeam.Batch4266
