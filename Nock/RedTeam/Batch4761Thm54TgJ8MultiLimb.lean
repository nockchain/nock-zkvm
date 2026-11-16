/-
  Nock/RedTeam/Batch4761Thm54TgJ8MultiLimb.lean

  Multi-limb hardening of `genJ8A`:
  * the atom table's rows are in LINK order (`linkOrder`: a row `[0 X]` is followed by its suffix `X`, g7.3′ / g7.4);
    a link successor is the suffix of a `[0 X]` row of the list (`linkSucc_some`); with the `p` duplicate the pad row
    is still last (`acsOfD_last`);
  * the scope-waived harness verdict `checkJ8W` requires every static conjunct not flagged claim-scope
    (`checkJ8W_static`).
  Kernel, structural only.
-/
import Nock.V1J8.GenAtomBig

namespace Nock.RedTeam.Batch4761

#print axioms Nock.V1J8.Gen.acsOfD_last
#print axioms Nock.V1J8.Gen.linkSucc_some
#print axioms Nock.V1J8.Gen.checkJ8W_static

end Nock.RedTeam.Batch4761
