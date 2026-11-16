import Nock.NockVMROM.Thm54.FormRCore.PwEvent

/-! The row-count majorant `pwAccountingWork'` for the event accounting, and the proof that it bounds `deg Q + E + 1`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch557

/-- The event majorant with the scale `n − 1`: `deg Q ≤ 2(n−1) + M`, `E ≤ 3N + 3`, one spare. -/
def pwAccountingWork' (n N M : ℕ) : ℕ := M + 3 * N + 2 * (n - 1) + 4

theorem pwAccountingWork'_majorises (n N M dQ E : ℕ) (hd : dQ ≤ 2 * (n - 1) + M)
    (hE : E ≤ 3 * N + 3) : dQ + E + 1 ≤ pwAccountingWork' n N M := by
  unfold pwAccountingWork'; omega

end Nock.RedTeam.Batch557
