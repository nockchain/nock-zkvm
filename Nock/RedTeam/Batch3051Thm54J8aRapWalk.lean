/-
  Nock/RedTeam/Batch3051Thm54J8aRapWalk.lean

  * `computeChipVCLHX_sat_iff`, `baseX_of_sat`, `walkX_of_sat`, `masksCX`: the RAP facts of the J-8
    compute chip `computeChipVCLHX` (base gates as `BaseHoldsX`, the nine `walkGatesX` at the gathered
    `𝕂` environment, preprocessing masks `17 / 18`).
  * `walkRowsX_of_sat`: an accepted trace (`XCtx`) is a `WalkRowsX`; `cwalkX_of_sat`: `Walk.WalkSat`
    over `rowsWX`; `base_oh_of_sat`: the `base` / `oh` fields of `RowsAccX`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8

namespace Nock.RedTeam.Batch3051

open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8

#print axioms computeChipVCLHX_sat_iff
#print axioms baseX_of_sat
#print axioms walkX_of_sat
#print axioms masksCX
#print axioms oneHotX_of_base
#print axioms stX_spec
#print axioms walkRowsX_of_sat
#print axioms cwalkX_of_sat
#print axioms base_oh_of_sat

end Nock.RedTeam.Batch3051
