/-
  Nock/RedTeam/Batch1978Thm54WalkW4bBound.lean

  **The `hmemP` question settled.**

  * **What the walk chip's soundness uses.**  It is re-proved
    (`RowBridgeW.walk_tiling`) from `1 ≤ kroots` and **`kroots + n < p`**: off the last row the
    integer queue length `kroots + Sf i − i` starts at `kroots ≥ 1`, drops by at most one per row
    and is never `0` (`walk_queue_ne`), so it is `≥ 0` at the last row and `≤ kroots + n`.  `GoodW`
    now carries `kr + memRows t < p` (implied by the old `3·memRows t < p` because `kr ≤ memRows t`,
    `goodW_weaker` below).
  * **Why the binder `hmemP : pathLen + 1 < p` cannot stay verbatim.**  The honest walk needs
    `krW + |walkRows| < p`.  On three roots with one axis-2 read each the path table has
    `Σ depth = 3` rows and the walk has `krW = 3`, `|walkRows| = 3`: at `p = 5`, `pathLen + 1 < p`
    holds and `krW + |walkRows| < p` fails (`hmemP_does_not_give_walk_bound`; the old
    `3·|walkRows| < p` fails too).  So the completeness twin swaps `hmemP` one-for-one for
    **`hmemW : krW + |walkRows| < p`** (`WalkBound`), which alone supplies every walk-side public
    condition of `GoodW` (`walkBound_public`).  (Whether the REST of the binder list implies the
    walk bound is UNCONFIRMED; nothing in it bounds `krW + |walkRows|` directly.)
-/
import Nock.NockVMROM.Thm54.VclL.Walk.GenWalkRows
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCLW

set_option autoImplicit false

namespace Nock.RedTeam.Batch1978

open Nock Nock.Walk Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.TraceGen

/-- **The walk-table bound** (the swap of `hmemP`): `krW + |walkRows| < p`. -/
def WalkBound (cells : List Noun) (preads : List (Noun × ℕ)) (p : ℕ) : Prop :=
  krW cells preads + (walkRows cells preads).length < p

/-- **The walk bound gives every walk-side public condition** `GoodW` reads at the honest `kr = krW`:
`1 ≤ kr`, `kr ≤ rows`, `kr + rows < p`, and `GoodM`'s `rows + 1 < p`. -/
theorem walkBound_public {cells : List Noun} {preads : List (Noun × ℕ)} {p : ℕ}
    (h : WalkBound cells preads p) :
    1 ≤ krW cells preads ∧ krW cells preads ≤ (walkRows cells preads).length ∧
      krW cells preads + (walkRows cells preads).length < p ∧ (walkRows cells preads).length + 1 < p := by
  have h1 := one_le_krW cells preads
  have h2 := krW_le_rows cells preads
  unfold WalkBound at h
  exact ⟨h1, h2, h, by omega⟩

theorem goodW_weaker {kr n p : ℕ} (hkn : kr ≤ n) (h3 : 3 * n < p) : kr + n < p := by omega

/-! ## The negative control: `hmemP`'s content does not give the walk bound -/

/-- Three distinct roots. -/
def rA : Noun := .cell (.atom 1) (.atom 2)
def rB : Noun := .cell (.atom 3) (.atom 4)
def rC : Noun := .cell (.atom 5) (.atom 6)

/-- One axis-2 read per root. -/
def reads3 : List (Noun × ℕ) := [(rA, 2), (rB, 2), (rC, 2)]

/-- The walk: three one-node tries. -/
theorem reads3_walk : krW [rA, rB, rC] reads3 = 3 ∧ (walkRows [rA, rB, rC] reads3).length = 3 := by
  constructor <;>
  simp [krW, walkRows, walkForest, walkRoots, pathKind, targetsOf, reads3, rA, rB, rC, trie, bfsForest,
    cont, contT, multT, sideTails, isPathAx, axisBits, axisBitsAux, depthOf, NTree.children]

/-- The path table's row count `Σ_{distinct deep reads} depth` (`pathTable` = one chain row per edge;
no padding since a deep read exists) is `3`. -/
theorem reads3_path : ((pathReads reads3).map fun r => depthOf r.2).sum = 3 := by
  simp [pathReads, reads3, rA, rB, rC, isPathAx, depthOf, axisBits, axisBitsAux]

theorem hmemP_does_not_give_walk_bound :
    ((pathReads reads3).map fun r => depthOf r.2).sum + 1 < 5 ∧ ¬ WalkBound [rA, rB, rC] reads3 5 ∧
      ¬ 3 * (walkRows [rA, rB, rC] reads3).length < 5 := by
  obtain ⟨hk, hw⟩ := reads3_walk
  refine ⟨by rw [reads3_path]; norm_num, ?_, ?_⟩
  · unfold WalkBound; rw [hk, hw]; norm_num
  · rw [hw]; norm_num

end Nock.RedTeam.Batch1978

#print axioms Nock.RedTeam.Batch1978.walkBound_public
#print axioms Nock.RedTeam.Batch1978.goodW_weaker
#print axioms Nock.RedTeam.Batch1978.reads3_walk
#print axioms Nock.RedTeam.Batch1978.reads3_path
#print axioms Nock.RedTeam.Batch1978.hmemP_does_not_give_walk_bound
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walk_tiling
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkHyps_of_chip
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.records_genuine_of_chip
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.memSoundnessVCLW
