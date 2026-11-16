/-
  Nock/RedTeam/Batch4760Thm54TgJ8GenAtom.lean

  The J-8 tracegen with big atoms,
  `genJ8A` (the atom table from the run's big atoms: comb spines, limb bits, the conversion / inc chain, `mb` / `mi`
  provides and the old-export consumes; big handles `(2, root serial)` and the cell table's `kb` columns; the atom
  walk over the OP5 big-vs-big first-difference reads):
  * off big atoms the handle map is `genJ8`'s `hdl` (`hdlB_eq_hdl`); a big atom is kind `2` at its root comb's serial
    (`hdlB_big`); the comb spine starts at the comb (`spineOf_head`); the pad row `[0 1]` is the atom table's last row
    (`acsOf_last`).  Kernel, structural only.
  Native verdicts (`nockvm-j8check check --prog cnt|ne5|eq5 [--tamper]`) are NOT
  kernel-checked here.
-/
import Nock.V1J8.GenAtom

namespace Nock.RedTeam.Batch4760

#print axioms Nock.V1J8.Gen.hdlB_eq_hdl
#print axioms Nock.V1J8.Gen.hdlB_big
#print axioms Nock.V1J8.Gen.spineOf_head
#print axioms Nock.V1J8.Gen.acsOf_last

end Nock.RedTeam.Batch4760
