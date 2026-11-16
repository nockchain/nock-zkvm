/-
  Nock/RedTeam/Batch2172Thm54VSQCompleteness.lean

  New module
  `HonestEpsVSQ`; additive.  `vsqCompleteness` (`Pr[¬ HonestGoodVSQ] ≤ epsCVSQ`), `vsqCompleteness_figure`
  (`< 2^-126` at Goldilocks, rows `≤ 2^31`), `honest_accepted_VSQ_whp`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestEpsVSQ

namespace Nock.RedTeam.Batch2172

open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

#print axioms vsqCompleteness
#print axioms epsCVSQ_lt
#print axioms two_pow_189_le_cK
#print axioms vsqCompleteness_figure
#print axioms honest_accepted_VSQ_whp

end Nock.RedTeam.Batch2172
