/-
  Nock/RedTeam/Batch1850Thm54VclLHonestMem.lean

  **The honest side of `memSoundnessVCL`.**  Production: `VclL/Chips/HonestMemAccept.lean`, `VclL/Chips/HonestMemHonest.lean`,
  `VclL/Chips/MemSoundnessVCL.lean` (`Honest := HonestVCL`, `PEmpty` retired).

  * `cellOk_sat` / `pathOk_sat` — the `ok = true` chips accept the interpolated honest trace given the row facts.
  * `HonestVCL` — the honest datum (a verifier datum whose memory tables are the generator's tables of a
    `Demand`; numeric facts `2^63 < p`, `rows + 1 < p`, prime-field elements, node adjacency/injectivity,
    rank `< 2^110`, depth `≤ 62`, row counts).  `HonestVCL.trace` (= `honestQ`), `.req` / `.msg2` (the
    accumulators' terminals), `.bad` (zero seed + three pole summands), `trace_staged` (= `honest_staged`),
    `accepted` (= `honest_accepted`), `epsilon_bad` (`ε = (1 + 5 nC + 2 nP) / |𝕂|²`).

  **Labelled.**  (a) `honestReq` is DEFINED as the accumulator terminals; its equality with the compute side's
  request sums (`Σ den⁻¹` over the honest binds / reads, via the validity / export balances of
  `GenMemTable`/`GenPathRows`) is NOT proved here.  (b) `HonestVCL` bundles the components of `GoodM`
  (adjacency, injectivity, `2^63 < p`, `rows + 1 < p`, `PrimeFieldElems`) rather than a full `V.Checks`.
  (c) The path chains need depth `≤ 62` and `memRows` equal to the generator's row counts (so ≥ 1 deep read).
  (d) The per-side export multiplicities `mx` / `mx1` are the generator's sided counts (`xs0` / `xs1`); their
  balance against the path chip's `pxKey` consumes is not needed for acceptance and not proved here.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1850

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms cellOk_sat
#print axioms pathOk_sat
#print axioms poleSummand_mem
#print axioms trace_staged
#print axioms bad_decode
#print axioms cell_accepted
#print axioms path_accepted
#print axioms accepted
#print axioms epsilon_bad
#print axioms memSoundnessVCL

end Nock.RedTeam.Batch1850
