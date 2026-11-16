/-
  Nock/RedTeam/Batch2136Thm54VSQHandleSummands.lean

  Additive.  New module
  `Thm54/VclL/Handle/SummandsHQ.lean`: `projQ` (VSQ traces at the VS widths), `listsQ_staged` (round-0
  lists coin-independent along a VSQ-staged strategy), `ioSpecHQ` (`γH′ = χ₁₁ + χ₁₅√δ`,
  `ρH′ = χ₁₂ + χ₁₆√δ`), `evXQ / evPQ` (weighted failure events of the lifted lists), `ioSummandHXQ /
  ioSummandHPQ` (coins `{11, 15, 12, 16}`, `dep = ∅`, weights the two handle numerators of
  `boundVCLHQ''`), `mem_ioSummandHXQ / HPQ`, `ioSpecHQ_dep_card = 4`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ

namespace Nock.RedTeam.Batch2136

open Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ

#print axioms listsQ_staged
#print axioms evXQ_card
#print axioms evPQ_card
#print axioms ioSummandHXQ
#print axioms ioSummandHPQ
#print axioms mem_ioSummandHXQ
#print axioms mem_ioSummandHPQ
#print axioms ioSpecHQ_dep_card

end Nock.RedTeam.Batch2136
