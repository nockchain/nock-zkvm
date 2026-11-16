/-
  Nock/RedTeam/Batch233Thm54StateCoverageNonvacuity.lean

  **The evidence base: what the broad program exercises that Tier A cannot.**

  Three separate
  entries, one pattern: "witnessed at a live configuration" has been weaker evidence than it sounds,
  because the one live configuration takes four of the eleven `ComputeTable.State` values.

  This module is the check that pattern implies.  It shows, at the seventeen-row program of
  `GenBroadProgram`:

  1. **the coverage** — eight states here, four at Tier A, all eleven between them;
  2. **`SeedGood` excludes seeds.**  `Batch180.dot_seedGood` is `∀ z`.  Here `SeedGood` is **false**
     at `z = φ(62)`, because `62 + 62 ³ ≡ 0 (mod 769)` kills the `cons` clause at the `[4 [1 1]]`
     autocons row.  So the first counted seed event is a real event.
  3. **`ComputeCoinsGeneric` excludes coins — and excludes exactly Tier A's.**
     `Batch180.dot_computeCoins` is `∀ a b c`.  Here the condition is **false at `(0, 0, 0)`**, the
     coin vector every `φ(8)/φ(4)` configuration except the matmul one commits.  The `.s5` row's
     two operands are `1` and `2`, so `rlc5Form a b c = -c`, and `c = 0` fails it.  That is why
     `Batch231` commits `(0, 0, 1)`.
  4. **the size-window inventory contains a two-leaf noun**, so `1 < orderOf z` — which is all Tier
     A's `hout` reduces to (`Batch180.dot_condResult_leaves`) — does **not** discharge `hout` here;
  5. **the comparison census contains an off-diagonal pair**, so `hbad` is not a conjunction of
     self-pairs.

  Point 3 is the sharpest: a condition proved `∀ a b c` at one program is *refuted* at another, at
  that program's own coin vector.
-/
import Nock.RedTeam.Batch231Thm54BroadProgramSemanticData
import Nock.RedTeam.Batch216Thm54SemanticCoverageAtTierA
import Nock.NockVMROM.Thm54.TraceGen.GenWF

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Nock.RedTeam.Batch233

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable TableWFBounds

abbrev DK := Batch231.DK
abbrev DF := Batch231.DF

/-! ## 1. Coverage -/

/-- **Tier A's eight rows miss seven of the eleven states.**  Its list is
`Batch216.b216States = [s6, s2, s1, s1, s1, s9, s1, s1]`. -/
theorem tierA_misses_seven :
    ∀ st ∈ [State.s0, .s3, .s4, .s5, .s7, .s8, .cons], st ∉ Batch216.b216States := by
  decide

/-- **The broad program supplies exactly those seven, plus `s1`.** -/
theorem bp_supplies_the_seven :
    ∀ st ∈ [State.s0, .s3, .s4, .s5, .s7, .s8, .cons], st ∈ bpStates := by
  decide

/-- **Between them the two programs cover all eleven states.** -/
theorem coverage_complete :
    ∀ st : State, st ∈ bpStates ∨ st ∈ Batch216.b216States := by
  decide

/-- And the broad program's own count is eight. -/
theorem bp_eight_states : bpStates.eraseDups.length = 8 := by decide

/-! ## 2. `SeedGood` excludes seeds

`Batch180.dot_seedGood (z : DK) : SeedGood z dotTree` is universally quantified — `ES.2` verified
that its binder really is `(z : DK)` and concluded the condition "excludes no seed".  At this
program it does. -/

/-- `62 ² = -1` in `𝔽₇₆₉`, so `62 + 62 ³ = 62 · (1 + 62 ²) = 0`. -/
theorem sixtytwo_root : (62 : DF) + 62 ^ 3 = 0 := by decide

/-- The `[4 [1 1]]` autocons row is in the emitted tree. -/
theorem bp_inTree_R3 : InTree (bpTree (K := DK)) bpR3Tree := by
  refine InTree.sub (s := bpR1Tree) ?_ (InTree.sub (s := bpR2Tree) ?_
    (InTree.sub (s := bpR3Tree) ?_ (InTree.here _)))
  · simp [bpTree_children]
  · simp [bpR1Tree_children]
  · simp [bpR2Tree_children]

/-- **`SeedGood` is FALSE at `z = φ(62)`.**

The seed kills the `dyck` coordinate of the `[4 [1 1]]` autocons head, which is exactly what
`RowSeedGood`'s `cons` clause forbids.  Contrast `Batch180.dot_seedGood`, which holds at *every*
seed because Tier A has no `cons` row at all. -/
theorem bp_seedGood_false :
    ¬ SeedGood (DotConfig769.φ (62 : DF)) (bpTree (K := DK)) := by
  intro hall
  have hcons := (hall bpR3Tree bp_inTree_R3).1 rfl
  refine hcons ?_
  rw [show formulaHead (bpR3Tree (K := DK)).label.skel.formula = bp4 from rfl,
    Batch231.bp_dyck4]
  rw [← map_pow, ← map_add, sixtytwo_root, map_zero]

/-! ## 3. `ComputeCoinsGeneric` excludes coins, and excludes Tier A's

`Batch180.dot_computeCoins (z α a b c : DK) : ComputeCoinsGeneric z α a b c …` is universally
quantified in the coins.  Here the `.s5` row's operands are the atoms `1` and `2`, so
`deltaSize = deltaDyck = 0` and `deltaLeaf = 1 - 2 = -1`; `rlc5Form a b c = -c`, which vanishes
exactly at `c = 0`. -/

theorem bp_air_bfsForest_len : (bfsForest [bpTreeAir (K := DK)]).length = 17 := by
  rw [bp_air_bfsForest]; rfl

/-- The `.s5` row sits at 1-based BFS index `10` of the AIR-ordered tree. -/
theorem bp_label10 :
    (bfsLabelAt (bpTreeAir (K := DK)) 10).skel = (bp5Tree (K := DK)).label.skel := by
  have hi : 10 - 1 < (bfsRows (bpTreeAir (K := DK))).length := by
    rw [bp_air_rowsLen]; omega
  rw [bfsLabelAt_skel _ 10 hi]
  simp [bp_air_bfsRows]

/-- **`ComputeCoinsGeneric` is FALSE at coins `(0, 0, 0)`** — Tier A's coin vector, and every
`φ(8)/φ(4)` configuration's but the matmul one's.  This is why `Batch231` commits `(0, 0, 1)`. -/
theorem bp_computeCoins_false (z α : DK) :
    ¬ ComputeCoinsGeneric z α 0 0 0 (bpTreeAir (K := DK)) := by
  intro hall
  have hmem : 10 ∈ List.range' 1 (bfsForest [bpTreeAir (K := DK)]).length := by
    rw [bp_air_bfsForest_len]; decide
  have h := hall 10 hmem
  have hstate : (bfsLabelAt (bpTreeAir (K := DK)) 10).skel.state = State.s5 := by
    rw [bp_label10]; rfl
  rw [renderNode_op5_row z α _ hstate] at h
  refine h ⟨by simp [renderOp5Row], ?_⟩ ?_
  · rw [show (renderOp5Row z α (bfsLabelAt (bpTreeAir (K := DK)) 10).stamp
        (bfsLabelAt (bpTreeAir (K := DK)) 10).skel).2.2.1.sf1_e = encC z (.atom 1) from by
      rw [bp_label10]; simp [renderOp5Row, bp5Tree, skelNode, genSkelOp5,
        P8Census.skeletonSubformula, ComputeTable.fanoutComp, bp5Sf1, bp5Sf2]]
    rw [show (renderOp5Row z α (bfsLabelAt (bpTreeAir (K := DK)) 10).stamp
        (bfsLabelAt (bpTreeAir (K := DK)) 10).skel).2.2.1.sf2_e = encC z (.atom 2) from by
      rw [bp_label10]; simp [renderOp5Row, bp5Tree, skelNode, genSkelOp5,
        P8Census.skeletonSubformula, ComputeTable.fanoutComp, bp5Sf1, bp5Sf2]]
    exact Batch231.bp_op5_enc_ne z
  · simp [rlc5Form]

/-- And on the tree the generator emits, before `airReorder`. -/
theorem bp_computeCoins_false_air (z α : DK) :
    ¬ ComputeCoinsGeneric z α 0 0 0 (airReorder (bpTree (K := DK))) := by
  rw [airReorder_bpTree]
  exact bp_computeCoins_false z α

/-! ## 4–5. Skeleton-row membership, and what it exhibits -/

/-- Any BFS index's skeleton is a row of the semantic skeleton.  Generic; the specific
memberships below are instances. -/
theorem skel_mem_computeSkeletonRows (u : NTree (GenComputeRow DK))
    (mf : List (NTree (GenMemoryRow DK))) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [u]).length) :
    (bfsLabelAt u i).skel ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign u) mf) := by
  rw [computeSkeletonRows_genSemantic, computeSkeletonRows_genCompute]
  have hlab := bfsAssign_bfsForest_labels u
  have hmem : bfsLabelAt u i ∈ (bfsForest [bfsAssign u]).map NTree.label := by
    rw [hlab]; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  obtain ⟨n, hn, hne⟩ := List.mem_map.mp hmem
  exact List.mem_map.mpr ⟨n, hn, by rw [hne]⟩

/-- The `.s3` row sits at 1-based BFS index `15`. -/
theorem bp_label15 :
    (bfsLabelAt (bpTreeAir (K := DK)) 15).skel = (bp3Tree (K := DK)).label.skel := by
  have hi : 15 - 1 < (bfsRows (bpTreeAir (K := DK))).length := by
    rw [bp_air_rowsLen]; omega
  rw [bfsLabelAt_skel _ 15 hi]
  simp [bp_air_bfsRows]

open SizeWindowCounting in
/-- **The size-window inventory contains a two-leaf noun** — the `.s3` row's recursive-call
result `[1 2]`.  Tier A's whole inventory is one one-leaf noun
(`Batch180.dot_sizeWindowNouns`, `dot_condResult_leaves`), so its `hout` collapses to
`1 < orderOf z`; here `2 < orderOf z` is needed and `Batch231.seedZ_order_gt_two` supplies it. -/
theorem bp_sizeWindow_has_two_leaf (mf : List (NTree (GenMemoryRow DK))) :
    ∃ n ∈ skeletonSizeWindowNouns
        (genSemanticSkeleton (bfsAssign (bpTreeAir (K := DK))) mf),
      n.leaves = 2 := by
  refine ⟨bp3Call, ?_, rfl⟩
  rw [skeletonSizeWindowNouns, List.mem_flatMap]
  refine ⟨(bfsLabelAt (bpTreeAir (K := DK)) 15).skel,
    skel_mem_computeSkeletonRows _ mf 15 (by rw [bp_air_bfsForest_len]; decide), ?_⟩
  rw [bp_label15]
  simp [requiredSizeWindowNouns, bp3Tree, skelNode, genSkelOp3,
    P8Census.skeletonSubformula, ComputeTable.fanoutComp]

/-- **The comparison census contains an off-diagonal pair** — the `.s5` row's `equalityOperand`
occurrence, comparing the operands `1` and `2`.  So `hbad` at this program is not a conjunction of
self-pairs, and `Batch231.bp_sepSeed_one_two` is the fact that pays for it. -/
theorem bp_census_has_offdiagonal (mf : List (NTree (GenMemoryRow DK))) :
    ∃ c ∈ P8Census.skeletonComparisonCensus (K := DK)
        (genSemanticSkeleton (bfsAssign (bpTreeAir (K := DK))) mf),
      c.left ≠ c.right := by
  refine ⟨P8Census.skeletonUse .equalityOperand (.atom 1) (.atom 2), ?_, by decide⟩
  rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
  refine ⟨(bfsLabelAt (bpTreeAir (K := DK)) 10).skel,
    skel_mem_computeSkeletonRows _ mf 10 (by rw [bp_air_bfsForest_len]; decide), ?_⟩
  rw [bp_label10]
  simp [P8Census.skeletonComparisons, bp5Tree, skelNode, genSkelOp5,
    P8Census.skeletonDec, P8Census.skeletonSubformula, SemanticStrategy.decActive,
    ComputeTable.fanoutComp, bp5Sf1, bp5Sf2, P8Census.skeletonUse]

end Nock.RedTeam.Batch233

#print axioms Nock.RedTeam.Batch233.tierA_misses_seven
#print axioms Nock.RedTeam.Batch233.bp_supplies_the_seven
#print axioms Nock.RedTeam.Batch233.coverage_complete
#print axioms Nock.RedTeam.Batch233.bp_seedGood_false
#print axioms Nock.RedTeam.Batch233.bp_computeCoins_false
#print axioms Nock.RedTeam.Batch233.bp_computeCoins_false_air
#print axioms Nock.RedTeam.Batch233.bp_sizeWindow_has_two_leaf
#print axioms Nock.RedTeam.Batch233.bp_census_has_offdiagonal
