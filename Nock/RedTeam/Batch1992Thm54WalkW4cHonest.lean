/-
  Nock/RedTeam/Batch1992Thm54WalkW4cHonest.lean

  **The honest datum of the walk memory family
  (`VclL/Chips/HonestVCLW.lean`).**

  * `HonestVCLW δF hT hP hC kr`: cells = the generator's `d.cells`, walk = `GenWalk.walkRows`,
    `krW = kr`, `kr + |walk| < p` (the `hmemW` content).  The cell table's side-0 export multiplicity
    counts the walk consumers (`xs0W`: every walk row's node, plus the depth-1 side-0 lookups).
  * `trace_stagedW` (B0 coin-free, B1 seed only, B2 after every coin of `frameVCL`).
  * `bad` (zero seed + three pole summands: `3nC`, `2nC + nW`, **`2nW`** — `recL` AND `recR` of every
    walk row, the unconditional path-provide inverses) and `epsilon_badW`:
    `ε = (1 + 5·nC + 3·nW) / |𝕂|²` (COMPILED; the path family's was `(1 + 5nC + 2nP)/|𝕂|²`).
  * `acceptedW`: outside `bad` both `ok`-gated chips (`vclChipW`, `okW` from the datum) accept the
    honest traces at `req` / `msg2`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestVCLW

#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.trace_stagedW
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.bad_decodeW
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.epsilon_badW
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cell_acceptedW
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walk_acceptedW
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.acceptedW
