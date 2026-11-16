/-
  Nock/RedTeam/Batch4750Thm54TgJ8FillX.lean

  The executable compute fill:
  **`colXE_eq : colXE H pd r fst lst = HonestCompX.colX H pd r fst lst`** (any field with `DecidableEq`; the honest
  builder decides with `Classical`, the twin with the instances).  The S6 native harness
  (`docs/j8/tgj8-check-harness.lean.txt`, #eval, reported, not gated) fills the example's compute row with `colXE` and
  runs the assembled `checkJ8` at the frame coin `χ0`: honest true, ten tampers false.  NOT claimed: equality of the
  cell / walk / atom fills of that harness to their honest builders (`HonestKW`, the walk twin, `HonestA8`); a
  tracegen over `genX` for general programs.
-/
import Nock.V1J8.FillX

namespace Nock.RedTeam.Batch4750

#check @Nock.V1J8.FillX.colXE_eq
#print axioms Nock.V1J8.FillX.colXE_eq

end Nock.RedTeam.Batch4750
