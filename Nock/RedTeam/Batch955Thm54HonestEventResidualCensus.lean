/-
  Nock/RedTeam/Batch955Thm54HonestEventResidualCensus.lean

  Additive; nothing consumes this.

  | # | premise | component | coordinate read | `HonestEventResidual` field(s) |
  |---|---|---|---|---|
  |  1 | `hp8`     | `ProductionP8Containment.FailureUnion P.strategy census lam` | `c.1` | `failureUnion` |
  |  2 | `hio`     | `P.famIOEventOf Qc Qm` | `c` | -- (discharged: `Batch909.hioEvent_honest`) |
  |  3 | `hts`     | `TimestampCollisionEvent (hostileRequests Qc).length` | `alphaM c.1` | `alphaNe`, `alphaOrder` |
  |  4 | `hinter`  | `interFailurePairs (hostileInterRecords Qm)..` | `(c.2.1.1, c.2.2.2.interPole)` | `interNe`, `interGamma8`, `inactiveMem`, `inactiveCprime` |
  |  5 | `hwalk`   | `P.computeWalkRootEvent Qc` | `c.1` | `walk` |
  |  6 | `htileC`  | `P.computeTilingEventOf Qc` | `c.1` | `tileC` |
  |  7 | `htileM`  | `P.memoryTilingEventOf Qm` | `c.1` | `tileM` |
  |  8 | `hγC`     | `P.computePrefixGammaEventOf Qc` | `c.1` (`gamma`) | `gammaC` |
  |  9 | `hγM`     | `P.memoryPrefixGammaEventOf Qm` | `c.1` (`gamma`) | `gammaM` |
  | 10 | `hαM`     | `P.memoryForestAlphaEventOf Qm` | `c.1` | `forestAlpha` |
  | 11 | `hlamEv`  | `P.decodedLambdaEventOf Qc Qm` | `c` (`(alphaM, λ)`) | `lam` |
  | 12 | `hpair`   | `PreSeedCensus.reqPairEventOfEnvs.. (requestTargets..)` | `c.1` (`nprSeed`) | `pair` |

  Fifteen fields in all.
-/
import Nock.RedTeam.Batch909Thm54R4HonestInstance
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch955

open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

#check @OptimizedFullStrictNockVMROMPackage.notMem_optimizedFailureEvent_of_components
#check @OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent
#check @Nock.RedTeam.Batch909.HonestEventResidual
#check @Nock.RedTeam.Batch909.HonestEventResidual.mk
#check @Nock.RedTeam.Batch909.hioEvent_honest
#check @Nock.RedTeam.Batch909.hgood_honest

end Nock.RedTeam.Batch955
