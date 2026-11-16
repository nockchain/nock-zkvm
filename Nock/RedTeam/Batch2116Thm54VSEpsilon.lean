/-
  Nock/RedTeam/Batch2116Thm54VSEpsilon.lean

  **The instance arguments discharged and `boundVCLH''`.**
  Additive.  New module `Thm54/VclL/Handle/EpsVS.lean`:
  * `standaloneVS_sound'`: `standaloneVS_sound` with `Fact (ringChar F).Prime` (from `2^63 < ringChar F`)
    and the `ZMod` algebra (`zmodAlg`, unique up to `Subsingleton`: `zmodAlg_unique`) derived;
  * `boundVCLH'' c c' N D W Λ`: the ten summand weights over `|𝕂|^coins` as an explicit function;
    `epsilonVS_eq`: `epsilonOf (allSummandsG …) = boundVCLH'' …` (so `epsilonVS_le`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EpsVS

namespace Nock.RedTeam.Batch2116

open Nock.NockVMROM.Thm54.VclL.Handle.EpsVS

#print axioms prime_of_big
#print axioms zmodAlg_unique
#print axioms standaloneVS_sound'
#print axioms epsilonVS_eq
#print axioms epsilonVS_le

end Nock.RedTeam.Batch2116
