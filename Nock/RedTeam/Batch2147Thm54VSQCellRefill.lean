/-
  Nock/RedTeam/Batch2147Thm54VSQCellRefill.lean

  New module `RefillMQ`; additive.

  * `refillC`: columns `0..225` of the `𝕂′` cell twin trace (the original chip's columns and `mh`) as the SAME
    polynomials, the `𝕂` inverse `den⁻¹` and the inclusive prefix sum of `mh · den⁻¹` interpolated on
    `226..231`; `refillC_trace_old/new`, `refillC_next_old/new`, `fillMC_inv/acc`;
  * **`cellChipH_of_HQ`**: `cellChipHQ` acceptance (with preprocessing) at `chalsQ / pubsQ` gives `cellChipH`
    acceptance (with preprocessing) of `refillC` at `chals / pubs`, when the vectors agree on the leaves
    `< 33` / publics `< 4` (`CpCongr`), every row key has a nonzero `𝕂` denominator and `pubs 4` is the total.
  Satisfiability: relative — the hypothesis is `cellChipHQ` acceptance, satisfiable by
  `CellTraceHQ.cellChipHQ_accepts_honest`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RefillMQ

namespace Nock.RedTeam.Batch2147

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms RefillMQ.refillC_trace_old
#print axioms RefillMQ.refillC_trace_new
#print axioms RefillMQ.refillC_next_new
#print axioms RefillMQ.cellChipH_of_HQ

end Nock.RedTeam.Batch2147
