/-
  Nock/RedTeam/Batch4703Thm54J8Stage.lean

  Full completeness of THE
  inhabitant (`*[[0 0] [0 1]] = [0 0]`, J chip and atom walk absent, atom table one inert pad row):
  `trJ0_staged : StJ8 (χ ↦ trJ0 χ)` (compute `stC`: columns `≥ 69` read `chalVJ8`, `χ₁₃`, `χ₁₄` and not the public
  vector, `trX_pub`; cell `stM` / walk `stW`: round-1 roles read `z′ = (χ₂, χ₃)`; atom `stA`: round-1 roles read
  `y = (χ₁₇, χ₁₈)`; J and atom walk zero; round-2 columns trivially), and `inhabitant_staged_complete`
  (`StJ8`, `|badJ0| ≤ 25 · |K|^18`, `|Coins| = |K|^19`, `AcceptsJ8V` at every coin outside `badJ0`), with its
  Goldilocks instance `inhabitant_staged_complete_goldilocks`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage

namespace Nock.RedTeam.Batch4703

open Nock.NockVMROM.Thm54.VclL.Handle

#check @InhabJ8Stage.trJ0_staged
#check @InhabJ8Stage.inhabitant_staged_complete
#check @InhabJ8Stage.inhabitant_staged_complete_goldilocks
#print axioms InhabJ8Stage.trJ0_staged
#print axioms InhabJ8Stage.stC
#print axioms InhabJ8Stage.stM
#print axioms InhabJ8Stage.stW
#print axioms InhabJ8Stage.stA
#print axioms InhabJ8Stage.inhabitant_staged_complete
#print axioms InhabJ8Stage.inhabitant_staged_complete_goldilocks

end Nock.RedTeam.Batch4703
