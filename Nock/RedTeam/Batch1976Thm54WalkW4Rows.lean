/-
  Nock/RedTeam/Batch1976Thm54WalkW4Rows.lean

  **The honest walk rows (`VclL/Walk/GenWalkRows.lean`).**

  * `trie` / `walkForest` / `walkRows` / `krW`: the read trie per distinct read root of the
    `Demand`'s path reads (`pathKind` = `pathReads` before its dedup, multiplicity kept), in BFS
    order (trunk `bfsForest`); a one-node dummy when there is no path read; `kr := #roots`
    (`one_le_krW`, `krW_le_rows`).
  * `trie_fanout` (fanout = cL + cR), `inTree_trie_inv` (every row is a trie node), the depth guard
    `walkRows_len_le` (`len ≤ 61` from the path chip's `depthOf ≤ 62`).
  * **`honest_walk_acc_zero`**: on any BFS forest, at any node valuation and any `α`, the explicit
    columns `α^i`, `α^kr·α^{Sf fo i}`, `accInGate` satisfy `WalkSatInGate` at `initial_count = α^kr`
    and the terminal is `0` — reused from trunk (`bfsForest_isForestFullBFT`, `forestQueueP_eval`,
    `walkSatInGate_completeness`); no coin event on the walk.
  * Toys (computed by `simp`): a two-read-site trie, the empty-read dummy, and the depth tightness
    control (a depth-3 read puts a walk row at `len = 2 = depth − 1`, so `len ≤ 61 ⇔ depth ≤ 62`).
-/
import Nock.NockVMROM.Thm54.VclL.Walk.GenWalkRows

set_option autoImplicit false

namespace Nock.RedTeam.Batch1976

open Nock Nock.Walk Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk

/-- A toy root `[[1 2] 3]`. -/
def toyRoot : Noun := .cell (.cell (.atom 1) (.atom 2)) (.atom 3)
/-- Reads: axis `4` twice, axis `3` once. -/
def toyP : List (Noun × ℕ) := [(toyRoot, 4), (toyRoot, 4), (toyRoot, 3)]

/-- Two walk rows: the root (continues left, emits the axis-3 record once) and its left child
(a leaf of the walk, emits the axis-4 record with multiplicity 2). -/
theorem toy_rows :
    (walkRows [toyRoot] toyP).map (fun t => (t.label.bits, t.label.cL, t.label.cR, t.label.mL, t.label.mR)) =
      [([], true, false, 0, 1), ([false], false, false, 2, 0)] := by
  simp [walkRows, walkForest, walkRoots, pathKind, targetsOf, toyP, toyRoot, trie, bfsForest, cont, contT,
    multT, sideTails, isPathAx, axisBits, axisBitsAux, depthOf, NTree.children]

/-- No path read: one dummy row (fanout 0, no record). -/
theorem toy_dummy :
    (walkRows [toyRoot] []).map (fun t => (t.label.bits, t.label.cL, t.label.cR, t.label.mL, t.label.mR)) =
      [([], false, false, 0, 0)] := by
  simp [walkRows, walkForest, walkRoots, pathKind, toyRoot, trie, bfsForest, cont, contT, multT,
    sideTails, NTree.children]

/-- A left spine of depth 3. -/
def deepRoot : Noun := .cell (.cell (.cell (.atom 1) (.atom 2)) (.atom 3)) (.atom 4)

/-- **Depth tightness (control for `walkRows_len_le`)**: a read at depth 3 (axis 8) puts a walk row
at `len = 2`: the guard `len ≤ 61` is exactly `depthOf ≤ 62`, the path chip's premise. -/
theorem deep_rows :
    (walkRows [deepRoot] [(deepRoot, 8)]).map (fun t => t.label.bits.length) = [0, 1, 2] := by
  simp [walkRows, walkForest, walkRoots, pathKind, targetsOf, deepRoot, trie, bfsForest, cont, contT,
    multT, sideTails, isPathAx, axisBits, axisBitsAux, depthOf, NTree.children]

end Nock.RedTeam.Batch1976

#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.trie_fanout
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.inTree_trie_inv
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.one_le_krW
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.krW_le_rows
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows_len_le
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.walkSatInGate_explicit
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.honest_walk_acc_zero
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows_acc_zero
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows_queue
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows_reach
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows_root
#print axioms Nock.RedTeam.Batch1976.toy_rows
#print axioms Nock.RedTeam.Batch1976.toy_dummy
#print axioms Nock.RedTeam.Batch1976.deep_rows
