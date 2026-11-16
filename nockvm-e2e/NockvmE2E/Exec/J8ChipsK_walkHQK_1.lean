/-
  Kernel tie of one hop-0 literal (see `J8ChipsK.lean`).
-/
import NockvmE2E.Exec.J8ChipsK

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.J8ChipsK
open NockvmE2E.Exec NockvmE2E.Exec.J8Chips NockvmE2E.Emit Nock.Emit

theorem tie_walkHQK_1 : tieB (walkAtomSpecAt 1) chipWalkHQK_1 = true := by decide +kernel

end NockvmE2E.Exec.J8ChipsK

#print axioms NockvmE2E.Exec.J8ChipsK.tie_walkHQK_1
