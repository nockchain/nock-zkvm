/-
  Nock/RedTeam/Batch4262Thm54J8r3bZAtHvp.lean

  `chalsAJ8Z` = `chalsAJ8` with leaves `37 / 38` rewired to `z = (χ₂, χ₃)`; `chalsAJ8Z_ok` / `_agree` / `_y` /
  `_01` re-proved; `chalsAJ8Z_zAt`: the g5 key's size entry reads `z`.  The `mb ≠ 0` forms `bnd_of_mb'`,
  `extB_mb'`, `atomLeaves_extB_of_mb'`; `mbVp_atomLeaves` (g4 + g5 + T1 at any vector with `zAt = z`) and
  `hvp_of_mb`: `AtomLeaves (encJ8 δ χ) (mbVp … (chalsAJ8Z δ χ) …) (extB p rA)`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesZJ8

namespace Nock.RedTeam.Batch4262

open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesZJ8

#print axioms chalsAJ8Z_of_ne
#print axioms chalsAJ8Z_agree
#print axioms chalsAJ8Z_y
#print axioms chalsAJ8Z_01
#print axioms chalsAJ8Z_ok
#print axioms chalsAJ8Z_zAt
#print axioms bnd_of_mb'
#print axioms extB_mb'
#print axioms atomLeaves_extB_of_mb'
#print axioms restr_traceK
#print axioms combL_eq
#print axioms mbVp_atomLeaves
#check @hvp_of_mb
#print axioms hvp_of_mb

end Nock.RedTeam.Batch4262
