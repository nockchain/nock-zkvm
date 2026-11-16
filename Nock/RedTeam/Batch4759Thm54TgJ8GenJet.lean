/-
  Nock/RedTeam/Batch4759Thm54TgJ8GenJet.lean

  * every output's layout is `layoutJ8 Rt regs ids` and the registry premise `RegOK` of `checkJ8_iff` holds for it
    (given `WellTyped`);
  * on the jetted matmul `n = 2` it returns an input at every coin vector, and that input's registry conjuncts of the
    static block (`hlay hsmall huniq haxT hnd`, `|regs| ≤ g`) hold, its J chip has 237 rows (kernel).
  Native verdicts (`nockvm-j8check check --prog mat [--tamper]`) are not part of this file.
-/
import Nock.V1J8.GenJetMat

namespace Nock.RedTeam.Batch4759

open Nock.V1J8.Exe Nock.V1J8.GenJ

theorem mat_generated (χ : CoinsE) :
    ∃ I, Nock.V1J8.Gen.genJ8J matRt [7] 2 Nock.Jet.Autogen.toyS Nock.Edit.GenX.Demo.matProg χ = some I :=
  mat_some χ

#print axioms Nock.V1J8.GenJ.genJ8J_spec
#print axioms Nock.V1J8.GenJ.genJ8J_regOK
#print axioms Nock.V1J8.GenJ.mat_static_cheap

end Nock.RedTeam.Batch4759
