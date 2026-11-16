/-
  Kernel tie of one J-9 A literal (see `J8ChipsK.lean`, `J9AChipsGen.lean`).
-/
import NockvmE2E.Exec.J8ChipsK
import NockvmE2E.Exec.J9AChips
import NockvmE2E.Emit.ChipsJ9A
import NockvmE2E.Emit.ComputeX9

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit

theorem tie_split_2 : tieB (splitSpecAt 2) chipSplit_2 = true := by decide +kernel

end NockvmE2E.Exec.J9AChips

#print axioms NockvmE2E.Exec.J9AChips.tie_split_2
