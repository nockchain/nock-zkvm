/-
  Nock/RedTeam/Batch4229Thm54J8r3aCensusG.lean

  `realizeG`: the census
  readout extended by `censusG Pb c` (still `≤ 2^66`); `linkR3_of_R3G` derives `hprsG` with `hprs hRA hrn hwRA`;
  `probJ8R3G_final` (`< 2^-155`, conditional on `LinkJ8R3G` only).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G

namespace Nock.RedTeam.Batch4229

open Nock.NockVMROM.Thm54.VclL.Handle

#check @LinkJ8R3G.probJ8R3G_final
#print axioms LinkJ8R3G.realizeG
#print axioms LinkJ8R3G.linkX_of_R3G
#print axioms LinkJ8R3G.linkR3_of_R3G
#print axioms LinkJ8R3G.probJ8R3G_final

end Nock.RedTeam.Batch4229
