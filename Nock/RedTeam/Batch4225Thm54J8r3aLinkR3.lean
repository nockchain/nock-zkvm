/-
  Nock/RedTeam/Batch4225Thm54J8r3aLinkR3.lean

  At the real data
  `RR = realIO (realizeJ8 R0 (layPb Pb skel hs) …) Pb`, `LL = real40 (realize40 L0 (layPb Pb skel hs) …) Pb`:
  `linkX_of_R3` (`LinkJ8R3` ⇒ `LinkJ8X'`, deriving rdX budX rdP budP rdS budS hcount rdWC rdWW hHXW hseedsV) and
  `probJ8R3_final` (`< 2^-155` at the census corner, conditional on `LinkJ8R3` only, under `BudJ8`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3

namespace Nock.RedTeam.Batch4225

open Nock.NockVMROM.Thm54.VclL.Handle

#check @LinkJ8R3.probJ8R3_final
#print axioms LinkJ8R3.linkX_of_R3
#print axioms LinkJ8R3.probJ8R3_final

end Nock.RedTeam.Batch4225
