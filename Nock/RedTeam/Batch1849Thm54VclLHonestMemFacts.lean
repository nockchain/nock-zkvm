/-
  Nock/RedTeam/Batch1849Thm54VclLHonestMemFacts.lean

  **The honest memory tables' facts from the generator.**
  Production: `VclL/Chips/HonestMemFill.lean`, `HonestMemGenCell.lean`,
  `HonestMemGenPath.lean`.

  * `cellFill` / `cellFill_facts`, `pathFill` / `pathFill_facts` — the round-2 fills (inverses, zero-weight
    consumer inverse `0`, prefix-sum accumulators) and the B2 halves of `CellMixedFacts` / `PathMixedFacts`
    given the pole conditions and the accumulator terminals.
  * `cellRows0` (generator rows: `rowB0` cast into `F`, the 110 rank bits, `enc z` fingerprints, `mx`
    SPLIT per side `xs0` / `xs1`), `cellRows0_baseFacts` (`CellBaseFacts`), `cellRows0_cons` / `_atomL` /
    `_atomR`.
  * `pathTable` (chains of the distinct deep reads), `pathTable_good`, `pathBaseFacts_of_good`
    (`PathBaseFacts`), `pathMixedRows_of_good` (root threading, `p_step = childOf`).
  * `xs_count_add`: the per-side export counts add up to the generator's single `mx`.

  **Labelled.**  Not yet derived here: the pole conditions (they become the honest bad summands), the
  `Honest` structure and `honest_accepted`.  `Honest := PEmpty` is still in place.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemGenPath
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1849

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL

#print axioms cellFill_facts
#print axioms pathFill_facts
#print axioms cellBaseFacts_fill
#print axioms pathBaseFacts_fill
#print axioms cellRows0_baseFacts
#print axioms cellRows0_cons
#print axioms cellRows0_atomL
#print axioms cellRows0_atomR
#print axioms chainRows_good
#print axioms pathTable_good
#print axioms pathBaseFacts_of_good
#print axioms pathMixedRows_of_good
#print axioms xs_count_add

end Nock.RedTeam.Batch1849
