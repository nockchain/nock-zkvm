/-
  Nock/RedTeam/Batch4227Thm54J8r3aReader.lean

  The atom-table reader
  `rAT` (Q2's `valReader`, coin-free, round-0 columns `< 205`), the census map `extT8 = extB p ∘ rAT` (staged);
  `linkR3_of_R3A` derives `hRA` / `hrn` / `hwRA` (Q2 lemmas) and `hprs` (census readout at the decoded cell table);
  `probJ8R3A_final` (`< 2^-155`, conditional on `LinkJ8R3A` only).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A

namespace Nock.RedTeam.Batch4227

open Nock.NockVMROM.Thm54.VclL.Handle

#check @LinkJ8R3A.probJ8R3A_final
#print axioms LinkJ8R3A.rAT_eq
#print axioms LinkJ8R3A.rAT_congr
#print axioms LinkJ8R3A.extT8_staged
#print axioms LinkJ8R3A.rowsMJ8_eq_cellT
#print axioms LinkJ8R3A.linkR3_of_R3A
#print axioms LinkJ8R3A.probJ8R3A_final

end Nock.RedTeam.Batch4227
