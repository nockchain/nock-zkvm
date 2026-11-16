/-
  Nock/RedTeam/Batch4701Thm54J8StageGood.lean

  Completeness of THE
  inhabitant (`*[[0 0] [0 1]] = [0 0]`, J chip and atom walk absent, atom table one inert pad row) at EVERY coin
  outside an explicit honest bad set: `inhabitant_of_good` (`GoodJ0 χ` → `AcceptsJ8V` at the honest message and
  traces of `χ`), `badJ0` = a union of 25 sets each pinning one coordinate (`χ₅` / `χ₁₂` against a pole-free
  part not reading it, or `χ₁₃ χ₂ χ₁₇ χ₁₂ = 0`), `card_badJ0 : |badJ0| ≤ 25 · |K|^18` (`card_coins : |Coins| =
  |K|^19`), `good_of_not_bad`, and the combination `inhabitant_outside_bad`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Good

namespace Nock.RedTeam.Batch4701

open Nock.NockVMROM.Thm54.VclL.Handle

#check @InhabJ8Good.inhabitant_of_good
#check @InhabJ8Good.card_badJ0
#check @InhabJ8Good.inhabitant_outside_bad
#print axioms InhabJ8Good.inhabitant_of_good
#print axioms InhabJ8Good.card_pin
#print axioms InhabJ8Good.card_badJ0
#print axioms InhabJ8Good.good_of_not_bad
#print axioms InhabJ8Good.inhabitant_outside_bad

end Nock.RedTeam.Batch4701
