/-
  Nock/RedTeam/Batch4743Thm54TgJ8Pub.lean

  NOT claimed: any chip check (S3+), `checkJ8_iff`.  The native run is `docs/j8/tgj8-pub-harness.lean.txt` (#eval,
  reported, not gated).
-/
import Nock.V1J8.PubExe

namespace Nock.RedTeam.Batch4743

#check @Nock.V1J8.Exe.checkPubJ8E_iff
#check @Nock.V1J8.Exe.acceptsJ8V_iff_exe
#print axioms Nock.V1J8.Exe.chalVJ8E_spec
#print axioms Nock.V1J8.Exe.toQ_compressE
#print axioms Nock.V1J8.Exe.encE_spec
#print axioms Nock.V1J8.Exe.claimRecsJ8E_spec
#print axioms Nock.V1J8.Exe.pinRecsJ8E_spec
#print axioms Nock.V1J8.Exe.pinConsE_spec
#print axioms Nock.V1J8.Exe.checkPubJ8E_iff
#print axioms Nock.V1J8.Exe.acceptsJ8V_iff_exe

end Nock.RedTeam.Batch4743
