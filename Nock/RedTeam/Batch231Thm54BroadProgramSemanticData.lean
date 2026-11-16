/-
  Nock/RedTeam/Batch231Thm54BroadProgramSemanticData.lean

  **`genSemanticData` at a SECOND program — the broad one, eight of the eleven states.**

  Every generic theorem of the chain has had exactly one consumer, Tier A: eight rows, states `{s6, s2, s1, s9}`.  `ES.2` measured what that
  costs and found two of the counted seed conditions **vacuous** there — `SeedGood` proved `∀ z`
  and `ComputeCoinsGeneric` proved `∀ a b c`, because their clauses are gated on `cons`, `.s5` and
  `.s3` rows the program does not have.

  This module instantiates `genSemanticData` at `GenBroadProgram`'s program

      *[[5 7] [[7 [1 5] [0 1]] [[8 [1 3] [0 3]] [[5 [1 1] [1 2]] [[4 [1 1]] [3 [1 [1 2]]]]]]]]
        = [5 [[5 7] [1 [2 0]]]]

  — seventeen rows, states `{cons, s0, s1, s3, s4, s5, s7, s8}` — at the same field
  `GaloisField 769 3`, the same seed `φ(8)`, the same `α = φ(4)`, the same orbit and `Λ = 22`, but
  at coins `(0, 0, 1)` rather than `(0, 0, 0)`.  What changes is which hypotheses have content:

  | hypothesis | at Tier A | here |
  |---|---|---|
  | `hseed` | `∀ z`, all three clauses vacuous | six field facts, all three clauses live |
  | `hcoins` | `∀ a b c`, no `.s5` row | needs `c = 1`; `op5C1Ready` at the `.s5` row |
  | `hout` | one noun, one leaf, collapses to `1 < orderOf z` | two nouns, `2 < orderOf z` |
  | `hbad` | one off-diagonal pair (OP6 branches) | one off-diagonal pair (OP5 operands) |
  | `hb`, `haxis` | `DotConfig769`'s own bounds | the generic derivations (`GG` §3–4) |
  | `hmem` | 184 rows | 227 rows, still inside `2 ^ 8 = 256` |

  The seed conditions are therefore **exercised** rather than merely supplied.  Nothing here is a
  capstone: `Data`, `Inputs`, `buildFullPackage` and the mandatory `claimedResult = result`
  conjunct are untouched.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenBroadSeed
import Nock.NockVMROM.Thm54.TraceGen.GenBroadMem
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticData
import Nock.NockVMROM.Thm54.TraceGen.GenGenericBounded
import Nock.NockVMROM.Thm54.TraceGen.GenGenericAxisRange
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig769
import Nock.RedTeam.Batch180Thm54GenericSemanticDataAtTierA

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Nock.RedTeam.Batch231

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy

/-- The table field, `GaloisField 769 3`. -/
abbrev DK := DotConfig769.K
/-- The base field, `ZMod 769`. -/
abbrev DF := DotConfig769.F

/-! ## The two instances the counted-seed formulation forces (`ES.2`)

`badSeeds` and `sizeWindowFailureSeeds` are `Finset.univ.filter`s, so `genRows` carries
`[Fintype K] [DecidableEq K]`, and instance search finds neither at `GaloisField 769 3`.  `local`
so nothing downstream inherits them. -/

noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

/-! ## The challenge vector — coins `(0, 0, 1)`

Tier A commits `(0, 0, 0)` and can, because it has no `.s5` row.  This program's `.s5` row makes
the coin obligation live, and `c = 1` is what discharges it (`GenWF.lean:278`,
`computeCoinsGeneric_c_one`). -/

noncomputable def bpChal : ChallengeVector DK where
  a := 0
  b := 0
  c := 1
  lam := MemoryTable.formRDefault
  α := DotConfig769.alphaA
  z := DotConfig769.seedZ
  β := 0
  γ := 0

theorem bp_hinp :
    bpChal.computeInputs = ⟨DotConfig769.alphaA, DotConfig769.seedZ, 0, 0, 1⟩ := rfl

theorem bp_hmi : bpChal.memoryInputs = memInputs DotConfig769.seedZ := rfl

/-! ## `orderOf` the seed: exactly `128`

`DotConfig769.seedZ_order_gt_one` is `1 < orderOf seedZ`, which was enough at Tier A because its
whole size-window inventory was one single-leaf noun (`ES.2`).  This program's inventory has a
two-leaf noun, so `2 < orderOf seedZ` is needed and the exact order is computed. -/

theorem eight_pow_128 : (8 : DF) ^ 128 = 1 := by decide

theorem eight_pow_64_ne : (8 : DF) ^ 64 ≠ 1 := by decide

theorem seedZ_pow_128 : DotConfig769.seedZ ^ 128 = 1 := by
  rw [DotConfig769.seedZ, ← map_pow, eight_pow_128, map_one]

theorem seedZ_pow_64_ne : DotConfig769.seedZ ^ 64 ≠ 1 := by
  rw [DotConfig769.seedZ, ← map_pow]
  intro h
  exact eight_pow_64_ne (DotConfig769.φ_injective (by simpa using h))

theorem seedZ_sq_ne : DotConfig769.seedZ ^ 2 ≠ DotConfig769.seedZ := by
  rw [DotConfig769.seedZ, ← map_pow]
  intro h
  exact absurd (DotConfig769.φ_injective h) (by decide)

/-- `2 < orderOf seedZ`.  `orderOf ∣ 128` rules out `0`; `seedZ ≠ 1` rules out `1`; and
`seedZ ^ 2 ≠ 1` — which follows from `seedZ ^ 2 ≠ seedZ` together with `seedZ ≠ 1` — rules out
`2`. -/
theorem seedZ_order_gt_two : 2 < orderOf DotConfig769.seedZ := by
  have hdvd : orderOf DotConfig769.seedZ ∣ 128 :=
    orderOf_dvd_of_pow_eq_one seedZ_pow_128
  have hne0 : orderOf DotConfig769.seedZ ≠ 0 := by
    intro h
    rw [h] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by decide)
  have hne1 : orderOf DotConfig769.seedZ ≠ 1 := by
    intro h
    have : DotConfig769.seedZ = 1 := orderOf_eq_one_iff.mp h
    rw [DotConfig769.seedZ] at this
    exact absurd (DotConfig769.φ_injective (by simpa using this)) (by decide)
  have hne2 : orderOf DotConfig769.seedZ ≠ 2 := by
    intro h
    have hsq : DotConfig769.seedZ ^ 2 = 1 := by
      rw [← h]; exact pow_orderOf_eq_one _
    have h8 : (8 : DF) ^ 2 = 1 := by
      apply DotConfig769.φ_injective
      simpa [DotConfig769.seedZ, map_pow] using hsq
    exact absurd h8 (by decide)
  omega

/-! ## The six field facts `bp_seedGood` asks for

The four `cons` heads have two distinct Dyck words: `[7 …]`, `[8 …]` and `[5 …]` share the shape
`[atom [[atom atom] [atom atom]]]`, and `[4 [1 1]]` is `[atom [atom atom]]`.  Their `dyck`
coordinates are therefore `z + z⁴ + z⁵ + z⁷` and `z + z³`, and at `z = φ(8)` those are
`φ(49)` and `φ(520)` — neither zero mod `769`.  **This is the first time the `cons` clause of
`RowSeedGood` has excluded any seed at a live program.** -/

theorem bp_dyck7 (z : DK) : (encC z bp7).dyck = z + z ^ 4 + z ^ 5 + z ^ 7 := by
  simp [encC, hornerLE, NPR.dyckBits, bp7, bp7Tail, bp7B, bp7C, Noun.dyckWord,
    Noun.shape, BTree.encode]
  ring

theorem bp_dyck8 (z : DK) : (encC z bp8).dyck = z + z ^ 4 + z ^ 5 + z ^ 7 := by
  simp [encC, hornerLE, NPR.dyckBits, bp8, bp8Tail, bp8B, bp8C, Noun.dyckWord,
    Noun.shape, BTree.encode]
  ring

theorem bp_dyck5 (z : DK) : (encC z bp5).dyck = z + z ^ 4 + z ^ 5 + z ^ 7 := by
  simp [encC, hornerLE, NPR.dyckBits, bp5, bp5Tail, bp5B, bp5C, Noun.dyckWord,
    Noun.shape, BTree.encode]
  ring

theorem bp_dyck4 (z : DK) : (encC z bp4).dyck = z + z ^ 3 := by
  simp [encC, hornerLE, NPR.dyckBits, bp4, bp4Tail, Noun.dyckWord,
    Noun.shape, BTree.encode]
  ring

/-- `z + z⁴ + z⁵ + z⁷ = φ(49) ≠ 0` at `z = φ(8)`. -/
theorem bp_dyckA_ne : DotConfig769.seedZ + DotConfig769.seedZ ^ 4
    + DotConfig769.seedZ ^ 5 + DotConfig769.seedZ ^ 7 ≠ 0 := by
  rw [DotConfig769.seedZ]
  intro h
  have h8 : (8 : DF) + 8 ^ 4 + 8 ^ 5 + 8 ^ 7 = 0 := by
    apply DotConfig769.φ_injective
    simpa [map_pow] using h
  exact absurd h8 (by decide)

/-- `z + z³ = φ(520) ≠ 0` at `z = φ(8)`. -/
theorem bp_dyckB_ne : DotConfig769.seedZ + DotConfig769.seedZ ^ 3 ≠ 0 := by
  rw [DotConfig769.seedZ]
  intro h
  have h8 : (8 : DF) + 8 ^ 3 = 0 := by
    apply DotConfig769.φ_injective
    simpa [map_pow] using h
  exact absurd h8 (by decide)

theorem bp_two_ne_one : (2 : DK) ≠ 1 := by
  intro h
  have h1 : (1 : DK) = 0 := by linear_combination h
  exact one_ne_zero h1

/-- `encC z 1 ≠ encC z 2`: the `leaf` coordinates are the constants `1` and `2`.

**Read this carefully.**  The `.s5` clause is on its right disjunct here — the operands genuinely
differ — but the separation is `z`-free, because `leafF` of an atom is a one-element list and its
Horner value is that constant.  So this clause, while no longer vacuous in the sense `ES.2` flagged,
still **excludes no seed** at an `OP_5` row whose operands are atoms.  It can only exclude seeds
when the operands are cells; and exactly then `op5C1Ready` fails and `hcoins` has no discharge in
the tree.  That tension is `Batch232`'s subject. -/
theorem bp_op5_enc_ne (z : DK) : encC z (.atom 1) ≠ encC z (.atom 2) := by
  intro h
  have hleaf : (encC z (.atom 1)).leaf = (encC z (.atom 2)).leaf := by rw [h]
  simp [encC, hornerLE, NPR.leafF, Noun.leafList] at hleaf
  exact bp_two_ne_one hleaf.symm

/-- `(encC z [1 2]).size = z ^ 2 ≠ z` — the `.s3` clause on its **cell** branch. -/
theorem bp_op3_size_ne : (encC DotConfig769.seedZ bp3Call).size ≠ DotConfig769.seedZ := by
  rw [encC_size, show bp3Call.leaves = 2 from rfl]
  exact seedZ_sq_ne

theorem bp_seedGood_at769 : SeedGood DotConfig769.seedZ (bpTree (K := DK)) :=
  bp_seedGood DotConfig769.seedZ
    (by rw [bp_dyck7]; exact bp_dyckA_ne)
    (by rw [bp_dyck8]; exact bp_dyckA_ne)
    (by rw [bp_dyck5]; exact bp_dyckA_ne)
    (by rw [bp_dyck4]; exact bp_dyckB_ne)
    (bp_op5_enc_ne _)
    bp_op3_size_ne

/-! ## `hbad` — the one off-diagonal pair -/

theorem bp_ringChar_gt_two : 2 < ringChar DK := by
  have h : ringChar DK = 769 := DotConfig769.ringChar_K
  rw [h]; norm_num

/-- `SepSeed z 1 2` at every seed: the second `NPR.fn` coordinate is `1` against `2`. -/
theorem bp_sepSeed_one_two (z : DK) :
    GlobalCarryRecognizer.SepSeed z (.atom 1) (.atom 2) := by
  intro _
  intro h
  have h2 : (NPR.fn (K := DK) (.atom 1) z).2.1 = (NPR.fn (K := DK) (.atom 2) z).2.1 := by
    rw [h]
  rw [NPR.fn, NPR.fn] at h2
  simp only at h2
  rw [← hornerLE_eq_eval, ← hornerLE_eq_eval] at h2
  simp [hornerLE, NPR.leafF, Noun.leafList] at h2
  exact bp_two_ne_one h2.symm

/-! ## Row counts and capacities -/

theorem bfsAssign_size (u : NTree (GenComputeRow DK)) :
    (bfsAssign u).size = (bfsForest [u]).length := by
  have h1 : (bfsAssign u).size = (bfsForest [bfsAssign u]).length := by
    rw [bfsForest_length, totalSize]; simp
  rw [h1, bfsForest_bfsAssign, List.length_map, List.length_range']

theorem bp_genComputeRows_len (z α : DK) :
    (bfsForest [genComputeRows z α (bpTree (K := DK))]).length = 17 := by
  rw [bfsForest_length, totalSize, genComputeRows, renderRows_eq_mapNTree]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mapNTree_size,
    Nat.add_zero]
  rw [bfsAssign_size, airReorder_bpTree, bp_air_bfsForest]
  rfl

theorem bp_accAt_le :
    accAt (airReorder (bpTree (K := DK)))
      (bfsRows (airReorder (bpTree (K := DK)))).length ≤ 51 := by
  rw [airReorder_bpTree, bp_air_rowsLen]
  exact accAt_le_three_mul _ 17

theorem bp_air_traceConfined : TraceConfined 22 (airReorder (bpTree (K := DK))) := by
  rw [airReorder_bpTree]
  exact bp_traceConfined

theorem bp_hmempos :
    0 < (bfsForest (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
      (memInputs DotConfig769.seedZ) (bpTree (K := DK)))).length :=
  bp_memRows_pos _ _ _

theorem bp_hmem :
    (bfsForest (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
      (memInputs DotConfig769.seedZ) (bpTree (K := DK)))).length
      ≤ 2 ^ DotConfig769.executionOrbit.h := by
  rw [bp_memRowsLen]
  norm_num [DotConfig769.executionOrbit]

theorem bp_hcomp :
    (bfsForest [genComputeRows DotConfig769.seedZ DotConfig769.alphaA
      (bpTree (K := DK))]).length ≤ 2 ^ DotConfig769.executionOrbit.h := by
  rw [bp_genComputeRows_len]
  norm_num [DotConfig769.executionOrbit]

/-! ## `hb` and `haxis` from the generic derivations (`GG` §3–4) -/

theorem bp_hb :
    (genSemanticSkeleton (bfsAssign (airReorder (bpTree (K := DK))))
      (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (bpTree (K := DK)))).BoundedBy 769 :=
  genComputeSkeleton_skeletonBounded _ _ _ (by norm_num)
    (bp_subject_bounded (by norm_num)) (bp_formula_bounded (by norm_num))
    (bp_evalGBy (by norm_num)) (genComputeSkeleton_bp 0)

theorem bp_haxis :
    SkeletonAxisRange 769
      (genSemanticSkeleton (bfsAssign (airReorder (bpTree (K := DK))))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (bpTree (K := DK)))) :=
  genComputeSkeleton_axisRange (by norm_num)
    (bp_subject_bounded (by norm_num)) (bp_formula_bounded (by norm_num))
    (bp_evalGBy (by norm_num)) (genComputeSkeleton_bp 0) _


theorem bp_hlt :
    ∀ n, InTree (bfsAssign (airReorder (bpTree (K := DK)))) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar DK := by
  rw [DotConfig769.ringChar_K]
  exact skeleton_assigned_request_axes_lt (K := DK) (by norm_num)
    (genComputeSkeleton_bp (K := DK) 0)
    (show evalGRom 769 6 bpSubject bpFormula = some bpResult by
      have h2 : (1 : ℕ) + 1 < 769 := by norm_num
      simp [evalGRom, FieldEmbedding.lusGBy, bpFormula, bp7, bp8, bp5, bp4, bp3,
        bpR1, bpR2, bpR3, bp7Tail, bp8Tail, bp5Tail, bp4Tail, bp3Tail, bp7B, bp7C, bp8B, bp8C,
        bp5B, bp5C, bp3Call, bpSubject, bpResult, bpR1Result, bpR2Result, bpR3Result,
        Noun.slot, Noun.tis, Noun.wut, h2])
    (bp_subject_bounded (by norm_num)) (bp_formula_bounded (by norm_num))

/-! ## `hout` — two nouns now, not one -/

open SizeWindowCounting in
/-- **Every size-window noun of this program has at most two leaves**, and the two-leaf one is
real: the `.s3` row's call result is the cell `[1 2]`.  Tier A's whole inventory is one one-leaf
noun (`Batch180.dot_sizeWindowNouns`, `dot_condResult_leaves`), so `hout` collapsed there to
`1 < orderOf z`; here it needs `2 < orderOf z`. -/
theorem bp_sizeWindow_leaves_le (mf : List (NTree (GenMemoryRow DK))) :
    ∀ n ∈ skeletonSizeWindowNouns
        (genSemanticSkeleton (bfsAssign (airReorder (bpTree (K := DK)))) mf),
      n.leaves ≤ 2 := by
  intro n hn
  rw [skeletonSizeWindowNouns, List.mem_flatMap] at hn
  obtain ⟨s, hs, hns⟩ := hn
  refine bfsAssign_computeSkeletonRows_of_bfsRows
    (fun s => ∀ m ∈ requiredSizeWindowNouns s, m.leaves ≤ 2)
    (airReorder (bpTree (K := DK))) mf ?_ s hs n hns
  rw [airReorder_bpTree]
  intro g hg
  rw [bp_air_bfsRows] at hg
  fin_cases hg <;>
    simp [requiredSizeWindowNouns, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp, bp3Call, Noun.leaves,
      bpTreeAir, bp7TreeAir, bpR1TreeAir, bp8TreeAir, bpR2Tree, bpR3Tree,
      bp5Tree, bp4Tree, bp3Tree, bp7CTree, bp8CTree, bpOp1Tree, skelNode,
      genSkelCons, genSkelOp7, genSkelOp8, genSkelOp5, genSkelOp4, genSkelOp3,
      genSkelOp1, genSkelOp0]

open SizeWindowCounting in
theorem bp_hout :
    DotConfig769.seedZ ∉ sizeWindowFailureSeeds (K := DK)
      (genSemanticSkeleton (bfsAssign (airReorder (bpTree (K := DK))))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (bpTree (K := DK)))) := by
  intro hmem
  rw [mem_sizeWindowFailureSeeds_iff] at hmem
  obtain ⟨-, n, hn, hw⟩ := hmem
  have hord := seedZ_order_gt_two
  have hle := bp_sizeWindow_leaves_le _ n hn
  exact hw ⟨by omega, by omega⟩

/-! ## The instantiation -/

/-- **`sd : ExactExecutionSemanticData 769 22` at the broad program.**

Every hypothesis of `genSemanticData` supplied, at `GaloisField 769 3`, seed `φ(8)`, `α = φ(4)`,
coins `(0, 0, 1)`, `Ksz = 64`, `orbit.h = 8`, `Λ = 22`, `B = 192`.  The second program the
generic chain has ever been driven at, and the first at which `hseed`, `hcoins` and `hout` have
content. -/
noncomputable def bp_semanticData :
    SemanticTrace.ExactExecutionSemanticData 769 22
      (genExactConfig (F := DF) bpChal 64 DotConfig769.executionOrbit
        (by norm_num [DotConfig769.executionOrbit])
        (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (bpTree (K := DK)))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
        bp_hmempos bp_hcomp bp_hmem)
      (genExactExecution (F := DF) bpChal 64 DotConfig769.executionOrbit
        (by norm_num [DotConfig769.executionOrbit]) 0 0 1
        (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (bpTree (K := DK)))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
        bp_hmempos bp_hcomp bp_hmem) :=
  genSemanticData (F := DF) DotConfig769.seedZ DotConfig769.alphaA
    DotConfig769.seedZ_ne_zero DotConfig769.two_ne_zero 0 0 1
    bpChal bp_hinp bp_hmi
    64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
    (genComputeSkeleton_bp 0)
    bp_seedGood_at769
    (bp_computeCoins _ _)
    (by norm_num) bp_air_traceConfined
    bp_hmempos bp_hcomp bp_hmem
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := bp_accAt_le; omega)
    (by have := bp_accAt_le; omega)
    bp_hb (by norm_num) DotConfig769.ringChar_K.symm bp_haxis
    (not_mem_badSeeds_of_pairs _ _
      (bp_pairs_sep DotConfig769.seedZ bp_ringChar_gt_two (bp_sepSeed_one_two _) _))
    bp_hout bp_hlt

end Nock.RedTeam.Batch231

#print axioms Nock.RedTeam.Batch231.seedZ_order_gt_two
#print axioms Nock.RedTeam.Batch231.bp_seedGood_at769
#print axioms Nock.RedTeam.Batch231.bp_sepSeed_one_two
#print axioms Nock.RedTeam.Batch231.bp_genComputeRows_len
#print axioms Nock.RedTeam.Batch231.bp_hb
#print axioms Nock.RedTeam.Batch231.bp_haxis
#print axioms Nock.RedTeam.Batch231.bp_sizeWindow_leaves_le
#print axioms Nock.RedTeam.Batch231.bp_hout
#print axioms Nock.RedTeam.Batch231.bp_semanticData
