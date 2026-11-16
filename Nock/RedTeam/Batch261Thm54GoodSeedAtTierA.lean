/-
  Nock/RedTeam/Batch261Thm54GoodSeedAtTierA.lean

  **`GenGoodSeedExists` instantiated: Tier A's program has a good NPR seed, and the counted
  failure set it avoids is not empty.**

  `GoodSeed.exists_good_seed_of_accepted` is `∀ program`; a generic theorem is not finished until
  something uses it, so this batch runs it at the one program whose every measurement the tree
  already carries — Tier A's dotted pair at `p = 769`, `Λ = 22`, `|𝕂| = 769³`.

  Three things are recorded, and the third is the one that makes the first non-trivial.

  1. `b261_rows` / `b261_budget_lt` — the arithmetic side condition, at the program's own
     measurements: `seedBudget 22 8 = 1 + (3 + 10·8)·43 + ∑_{d≤22} d ≤ 4054`, against
     `Fintype.card DK = 769³ = 454756609` (`Batch241.card_DK`).  The margin is five orders of
     magnitude; this is not a `2 < 769` instantiation.
  2. `b261_exists_good_seed` — the existential itself, at Tier A's accepted tree and at the very
     memory forest the chosen seed generates.
  3. `b261_one_mem_sizeWindowFailureSeeds` — **the failure set is inhabited**: `z = 1` is in it,
     because `orderOf (1 : DK) = 1` and `SizeWindow` (`OpcodeSemantics.lean:125`) demands
     `1 < orderOf z`.  So the existential in (2) is a genuine selection and not the vacuous
     statement that every seed is good.  (The set is *small* — `Batch180` records that Tier A's
     whole size-window inventory is one noun of one leaf — but "small" is the point of the
     counting, and "empty" it is not.)

  **Not claimed.**  Nothing here is a soundness statement.  The bad seeds were already excluded and
  already priced by `complete_false_acceptance_bound`; this batch only witnesses that the excluded
  set does not exhaust the carrier, which is what `containment` needs in order not to be vacuous.
  No `§J` box moves.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.RedTeam.Batch180Thm54GenericSemanticDataAtTierA
import Nock.RedTeam.Batch241Thm54CoinCounting

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Nock.RedTeam.Batch261

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.RedTeam

abbrev DK := DotConfig769.K

/-! `badSeeds` and `sizeWindowFailureSeeds` are `Finset.univ.filter`s over `K`, so both carry
`[Fintype K] [DecidableEq K]`, and instance search finds neither at `GaloisField 769 3`.  These are
the same two `local` instances `Batch180` and `Batch241` declare, by the same definitions. -/

noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

noncomputable section

/-! ## 1. The program's two measurements -/

/-- The compute row count the budget is stated against is Tier A's eight rows.  `bfsAssign`
restamps but does not reshape (`bfsForest_bfsAssign`), so the AIR-ordered tree's BFS length carries
over unchanged. -/
theorem b261_rows :
    (bfsForest [bfsAssign (airReorder (dotTree (K := DK)))]).length = 8 := by
  rw [bfsForest_bfsAssign, List.length_map, List.length_range']
  have h := Batch180.dot_air_rowsLen
  simpa [bfsRows, List.length_map] using h

/-- The whole size-window inventory is one noun of one leaf (`Batch180.dot_sizeWindowNouns`,
`dot_condResult_leaves`), and `1 ≤ 22`. -/
theorem b261_hwinNouns :
    SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
        ([] : List (NTree (GenMemoryRow DK)))) DotConfig769.Λ := by
  have hset :
      skeletonSizeWindowNouns
          (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
            ([] : List (NTree (GenMemoryRow DK))))
        = [dotCondResult] := by
    have hirr :
        skeletonSizeWindowNouns
            (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
              ([] : List (NTree (GenMemoryRow DK))))
          = skeletonSizeWindowNouns
            (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
              (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
                (memInputs DotConfig769.seedZ) (dotTree (K := DK)))) := rfl
    rw [hirr, Batch180.dot_genSkeleton, Batch180.dot_sizeWindowNouns]
  intro n hn
  rw [hset, List.mem_singleton] at hn
  subst hn
  rw [Batch180.dot_condResult_leaves]
  norm_num [DotConfig769.Λ]

/-- The arithmetic side condition, at Tier A: `seedBudget 22 8 ≤ 4054 < 769³`. -/
theorem b261_budget_lt :
    GoodSeed.seedBudget DotConfig769.Λ 8 < Fintype.card DK := by
  have hs : sizeWindowRootBound DotConfig769.Λ ≤ 22 * 22 :=
    sizeWindowRootBound_le_square DotConfig769.Λ
  have hcard : Fintype.card DK = 769 ^ 3 := Batch241.card_DK
  rw [hcard]
  unfold GoodSeed.seedBudget
  norm_num [DotConfig769.Λ] at hs ⊢
  omega

/-! ## 2. The existential, at Tier A -/

/-- **A good NPR seed exists for Tier A's program.**  `GoodSeed.exists_good_seed_of_accepted` with
its two measurements discharged; the conclusion is stated at the memory forest the chosen seed
itself generates. -/
theorem b261_exists_good_seed (α : DK) :
    ∃ z : DK, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := DK) (Λ := DotConfig769.Λ)
              (by norm_num [DotConfig769.Λ]) (genComputeSkeleton_dot (K := DK) 0)
              Batch180.dot_air_traceConfined
              (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (dotTree (K := DK)))).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := DK)
              (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
                (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (dotTree (K := DK)))) :=
  GoodSeed.exists_good_seed_of_accepted (K := DK) (Λ := DotConfig769.Λ)
    (by norm_num [DotConfig769.Λ]) (genComputeSkeleton_dot (K := DK) 0)
    Batch180.dot_air_traceConfined α b261_hwinNouns
    (by rw [b261_rows]; exact b261_budget_lt)

/-! ## 3. The set being avoided is not empty

Without this the existential would be compatible with "no seed is ever bad", i.e. with the
counting being about nothing. -/

/-- `z = 1` fails the size window: `orderOf (1 : DK) = 1`, and `SizeWindow` asks `1 < orderOf z`
(`OpcodeSemantics.lean:125`).  So Tier A's counted size-window failure set is inhabited. -/
theorem b261_one_mem_sizeWindowFailureSeeds :
    (1 : DK) ∈ sizeWindowFailureSeeds (K := DK)
      (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (dotTree (K := DK)))) := by
  rw [Batch180.dot_genSkeleton, mem_sizeWindowFailureSeeds_iff]
  refine ⟨one_ne_zero, dotCondResult, ?_, ?_⟩
  · rw [Batch180.dot_sizeWindowNouns]; exact List.mem_singleton_self _
  · intro hw
    have h1 : (1 : ℕ) < orderOf (1 : DK) := hw.one_lt_order
    rw [orderOf_one] at h1
    exact absurd h1 (by norm_num)

/-- And therefore a good seed is a *selection*: the existential of §2 is not satisfied by every
seed of the carrier. -/
theorem b261_selection_is_real :
    ∃ z : DK, z ∈ sizeWindowFailureSeeds (K := DK)
      (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (dotTree (K := DK)))) :=
  ⟨1, b261_one_mem_sizeWindowFailureSeeds⟩

end

end Nock.RedTeam.Batch261

#print axioms Nock.RedTeam.Batch261.b261_rows
#print axioms Nock.RedTeam.Batch261.b261_hwinNouns
#print axioms Nock.RedTeam.Batch261.b261_budget_lt
#print axioms Nock.RedTeam.Batch261.b261_exists_good_seed
#print axioms Nock.RedTeam.Batch261.b261_one_mem_sizeWindowFailureSeeds
#print axioms Nock.RedTeam.Batch261.b261_selection_is_real
