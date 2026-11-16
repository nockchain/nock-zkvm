/-
  Nock/RedTeam/Batch4753Thm54TgJ8FillAtom.lean

  The executable atom-table fill
  of the example (the one-row inert pad cell `[0 1]`, every multiplicity `0`; `K6`, computable):
  * **`atomColZ_eq`**: every column `c < 349` equals the honest column function `fullCol (HonestA8.colA (padC …)
    newPad)` at `KC`, `powerBasis3`, `deltaF`, given the atom chals carry `(γH′, ρH′)` at `33..36`, `zA` at `37 / 38`
    and `ChalsOK` for `(γ′, ρ′)`;
  * **`atomTrace_eq`**: the interpolants ARE `HonestA8.atomTraceHQ` (= `padTraceA`); **`atomTrace_eq_frame`** /
    **`interpOf_atom`**: at the frame coins (`coOfA χe` with seed `y = (χ₁₇, χ₁₈)`, `zA = zE χe`) they ARE
    `InhabJ8Atom.trA0 deltaF powerBasis3 … (toχ χe)` (no hypothesis: `chalsAJ8Z_ok`, `chalsAJ8Z_zAt` discharge them).
  `FillAtom` uses `y`.
-/
import Nock.V1J8.FillAtom

namespace Nock.RedTeam.Batch4753

#check @Nock.V1J8.FillMem.atomColZ_eq
#check @Nock.V1J8.FillMem.atomTrace_eq_frame
#print axioms Nock.V1J8.FillMem.atomColZ_eq
#print axioms Nock.V1J8.FillMem.atomTrace_eq_frame
#print axioms Nock.V1J8.FillMem.interpOf_atom

end Nock.RedTeam.Batch4753
