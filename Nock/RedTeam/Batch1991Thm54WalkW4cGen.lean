/-
  Nock/RedTeam/Batch1991Thm54WalkW4cGen.lean

  **The honest walk table's values and row facts
  (`VclL/Chips/HonestWalkGen.lean`).**

  * `walkRow0` (row `j` of the read trie in BFS order, `GenWalk.walkRows`): `idx`, `axisFold` prefix,
    `rootIdx`, `len`, trie states, `e`, multiplicities, the queue counter `qH` and its inverse, the six
    bits of `61 − len` with `u = b₁b₂`, the four fingerprints at the seed, and the explicit in-gate walk
    `ln = α^{j+1}`, `count = countH`, `acc = accH` at `nodeVal = RLC^γ(enc(lblW))`.
  * `walkRow0_base`: `WalkBaseFacts` on every row from `walkRows_queue` / `walkRows_root` /
    `walkRows_len_le` and `krW + |walkRows| < p` (the `hmemW` content).
  * **`walkRow0_K`**: `WalkKFacts` on every row at EVERY coin pair `(α, γ)` — trunk
    `honest_walk_acc_zero` (terminal zero), `lblV_walkRow0` / `keyV_walkRow0` (the row's label / key
    are `lblW` / `keyW`, given `2^63 < p`, `|cells| < p`), `ccV_walkRow0` (the in-gate child sum is
    trunk's `chldCol` sum: `trie_child_get` + `dtW_child`).  No coin event on the walk.
  * `walkFill` / `walkFill_mixed`: the IO fill; `WalkMixedFacts` given non-zero denominators on every
    row for `xKey`, `recL` AND `recR` (the unconditional path-provide inverses) and the terminals.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestWalkGen

#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.trie_child_get
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkRow0_base
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.lblV_walkRow0
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.keyV_walkRow0
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.ccV_walkRow0
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkRow0_K
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkFill_mixed
