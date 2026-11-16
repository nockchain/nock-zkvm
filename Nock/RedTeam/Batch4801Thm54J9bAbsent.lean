/-
  Nock/RedTeam/Batch4801Thm54J9bAbsent.lean

  **J-9 (B) step 2a: soundness of `AcceptsJ9V` at an ABSENT atom walk.**
  * `LinkJ9A.claimRecsT9_eq` (the readout's claim records, cells and big atoms, are the verifier's `claimRecsJ9`);
  * `LinkJ9A.hsoundJ9XUA` with the big case `hbig` (`claim_den` for a big claim leaf: F1 excludes a cell provider,
    an `mb` row serves the record, the census over `claimX` pins the atom);
  * **`LinkJ9A.probJ9_absent`**: `< 2^-155` at `krootsV = 0`, through `RepriceJ8.probJ8X_lt_155_census32` (no new
    summand, no new coin; `P = 2^66`; `hreg` read at `|censusG| + 6 ≤ 2^31`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9A

set_option autoImplicit false

namespace Nock.RedTeam.Batch4801

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms LinkJ9A.claimRecsT9_eq
#print axioms LinkJ9A.hinjX_of_outside
#print axioms LinkJ9A.linkXUA9_of_R5
#print axioms LinkJ9A.hsoundJ9XUA
#print axioms LinkJ9A.probJ9_absent

end Nock.RedTeam.Batch4801
