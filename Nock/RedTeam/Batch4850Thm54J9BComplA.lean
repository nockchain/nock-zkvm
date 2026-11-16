/-
  Nock/RedTeam/Batch4850Thm54J9BComplA.lean

  **J-9 B general completeness, phase A, receipt for `Handle/ComplJ9B`.**
  `ComplJ9BObligations` (= `ComplJ8Obligations` with the compute fields at `pubVJ9`, `balV`'s first clause over
  `claimRecsJ9`, and the J-9 claim checks: `hclA` dropped, `hclI` at cell and big positions, `hcen'` over
  `censusGJ9`); `honest_accepted_J9B_of_obligations` (`Good χ → AcceptsJ9V`), `probJ9B_notGood_le`, `exists_good9`,
  `complJ9B_of_obligations`, all PROVED from the obligations.  The obligations are not discharged here.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9B

set_option autoImplicit false

namespace Nock.RedTeam.Batch4850

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9B

#print axioms honest_accepted_J9B_of_obligations
#print axioms probJ9B_notGood_le
#print axioms exists_good9
#print axioms complJ9B_of_obligations

end Nock.RedTeam.Batch4850
