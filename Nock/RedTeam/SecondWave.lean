/-
  Nothing that is only checked once is checked at
  all: they now build with the default target and are registered in
  `../../redteam-status.json`'s `checked_artifacts`, so a refactor can no longer
  silently invalidate them.

  Two classes live here, and they expire differently.

  * **Durable negatives.** Conclusions that stay true whatever the Theorem 5.4
    statement becomes: `AtkDegree` (`RAP.d` does not bound the composed univariate
    degree), `BPadding` (padding does not remove the wrap failure), `CDegree`,
    `DClock`, `ASelector`, `AtkPoint`, `AtkKindedSat`, `Rev1SegmentedRAP`,
    `Rev2`, `Rev3S2Analysis`, `Rev4`, `RtEasy`, `RtMore`, `AtkP8a`,
    `P9bPrimeExistence`.
  * **Dated vacuity witnesses.** `RtAlias` (G1) and `AtkPackage` (G1/G2/G9)
    exhibit no-Nock and empty-language inhabitants of the structural bundle.
-/
import Nock.RedTeam.SecondWave.ASelector
import Nock.RedTeam.SecondWave.AtkDegree
import Nock.RedTeam.SecondWave.AtkKindedSat
import Nock.RedTeam.SecondWave.AtkP8a
import Nock.RedTeam.SecondWave.AtkPackage
import Nock.RedTeam.SecondWave.AtkPoint
import Nock.RedTeam.SecondWave.BPadding
import Nock.RedTeam.SecondWave.CDegree
import Nock.RedTeam.SecondWave.DClock
import Nock.RedTeam.SecondWave.P9bPrimeExistence
import Nock.RedTeam.SecondWave.Rev1SegmentedRAP
import Nock.RedTeam.SecondWave.Rev2
import Nock.RedTeam.SecondWave.Rev3S2Analysis
import Nock.RedTeam.SecondWave.Rev4
import Nock.RedTeam.SecondWave.RtAlias
import Nock.RedTeam.SecondWave.RtEasy
import Nock.RedTeam.SecondWave.RtMore
