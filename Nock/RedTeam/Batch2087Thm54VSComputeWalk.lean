/-
  Nock/RedTeam/Batch2087Thm54VSComputeWalk.lean

  **The compute
  walk of `computeChipVCLH` at VS as `Walk.WalkSat` with the row shift.**  Additive.  New module
  `Thm54/VclL/Handle/CWalkChipVS.lean`: `rowsC` (decoded rows, 1-indexed), `selIdx_of_rowSel`,
  `rowsC_congr`, `rowsC_eq`, `rowsC_small`, **`rowsC_root`** (root row = the claim handles),
  **`cwalk_sat`** (`WalkSat` at `α = χ₁₃`, `γ = χ₁₄`, `initial_count = α`,
  `seed = RLC^γ(label 1)·α`, `out = 0`, queue witness and terminal) — the compute-walk publics
  `IC = αW`, `seed = αW·RLC(claim label)`, `out = 0` confirmed.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS

namespace Nock.RedTeam.Batch2087

open Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS

#print axioms selIdx_of_rowSel
#print axioms rowsC_congr
#print axioms rowsC_eq
#print axioms rowsC_small
#print axioms rowsC_root
#print axioms cwalk_sat

end Nock.RedTeam.Batch2087
