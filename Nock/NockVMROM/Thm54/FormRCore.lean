/-
  Nock/NockVMROM/Thm54/FormRCore.lean

  The namespaces stay `Nock.RedTeam.Batch5xx` so that
  every old name — and every registered receipt that uses it — elaborates to the same constant.

  * `Nock.RedTeam.Batch554` §§A–C (from `Batch554Thm54PwFunctional.lean`): the weighted tree
    and functional, the `MTree` instance, `vpaths` / `rpaths`, `addrP`, `bitsOf`, `Cpoly`,
    `bracket` and `bracket_zero_iff`.  §D (the concrete D-λ traces, which need `Batch546`) stays.
  * `Nock.RedTeam.Batch556` §§A–C (from `Batch556Thm54PwEvent.lean`): `F`, `Fα`,
    `bivariate_bad_card_le`, per-root and cylinder bounds.  §§D–F (Goldilocks figures, the
    collision event, `evalGRom`) stay.
  * `Nock.RedTeam.Batch575` (from `Batch575Thm54FormRMtree.lean`): the accumulators (`Y`,
    `scale`, `Tpoly`, `C'poly`, `formRPw`, `formRCounts`, `UniqueExponents`, `Paired`,
    `Padding`), the path and coefficient lemmas (S1), `formR_counts_zero_iff` (S2's identity),
    and S3 (`degY_le`, `formR_event_card`, `formR_work_vs_majorant`).  The S2 failure receipts
    (`s2_nested_fails`, `pw_not_load_bearing`, …) and the Bridge note stay.

  One sub-module per source file (`FormRCore/PwFunctional`, `PwEvent`, `Majorant`, `Mtree`), so
  that each moved block elaborates in the same module structure as before and its auto-generated
  auxiliaries (matchers, `eq_def`) keep their statements.  Their only outside imports are
  `Nock.AxisBatching`, `Nock.AxisBridge` and `Nock.Reference` — strictly below
  `OptimizedStrictPackage` and `ProductionP8Containment`.
-/
import Nock.NockVMROM.Thm54.FormRCore.PwFunctional
import Nock.NockVMROM.Thm54.FormRCore.PwEvent
import Nock.NockVMROM.Thm54.FormRCore.Majorant
import Nock.NockVMROM.Thm54.FormRCore.Mtree
