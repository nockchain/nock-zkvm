/-
  Nock/RedTeam/Batch289Thm54P64SeedConcretization.lean

  `rowBad_card_le_of_generated` discharges the three `SeedGood` shapes from
  the generator + `hconf`/`hs`/`hf`/`hG`.  `exists_vcomp_seed_of_accepted`
  then avoids the `KM` union together with the Dyck-bad set.  No new
  failure event or soundness summand: `seedBudgetVcomp` is a compiler
  numeral.

  `romSeedVcomp` remains `Classical.choose`, so `GoodSeed.nockCompiles_p64`
  is not instantiated here.  The concrete-seed path is
  `nockCompiles_of_grom_atTree_p62` at `seedZ` — every live witness already
  used that literal, and it is a joint-good seed (`b289_seedZ_joint`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.RedTeam.Batch261Thm54GoodSeedAtTierA
import Nock.RedTeam.Batch288Thm54P63SeedCoins
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch289

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.Framework.Thm54
open Nock.RedTeam
open Nock.NockVMROM.Thm54.BuildableAxisWitness

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

noncomputable section





/-- The joint budget at Tier A: `seedBudget 22 8 + 3·8·43 ≤ 4054 + 1032 = 5086 < 769³`. -/
theorem b289_budget_vcomp_lt :
    seedBudgetVcomp DotConfig769.Λ 8 < Fintype.card DK := by
  have hs : sizeWindowRootBound DotConfig769.Λ ≤ 22 * 22 :=
    sizeWindowRootBound_le_square DotConfig769.Λ
  have hcard : Fintype.card DK = 769 ^ 3 := Batch241.card_DK
  rw [hcard]
  unfold seedBudgetVcomp GoodSeed.seedBudget
  norm_num [DotConfig769.Λ] at hs ⊢
  omega


/-- **`seedZ` is a literal joint-good seed.**  `KM` (`≠ 0`, outside p8 / size-window)
and `SeedGood` (vacuous at Tier A).  This is the concretization: a closed-form
value satisfies the predicate `romSeedVcomp` chooses. -/
theorem b289_seedZ_joint :
    seedZ ≠ (0 : DK) ∧ SeedGood seedZ (dotTree (K := DK)) :=
  ⟨seedZ_ne_zero, Batch180.dot_seedGood _⟩


/-- The joint existential at Tier A's accepted tree. -/
theorem b289_exists_vcomp_seed (α : DK) :
    ∃ z : DK, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := DK)
              (by norm_num [DotConfig769.Λ]) (genComputeSkeleton_dot (K := DK) 0)
              Batch180.dot_air_traceConfined
              (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (dotTree (K := DK)))).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := DK)
              (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
                (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (dotTree (K := DK))))
      ∧ SeedGood z (dotTree (K := DK)) :=
  exists_vcomp_seed_of_accepted (K := DK) (q := 769) (Λ := DotConfig769.Λ)
    (by norm_num) (by rw [DotConfig769.ringChar_K])
    Batch263.b263_subject_bounded Batch263.b263_formula_bounded Batch263.b263_evalG
    (genComputeSkeleton_dot (K := DK) 0)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined α
    Batch261.b261_hwinNouns
    (by rw [Batch261.b261_rows]; exact b289_budget_vcomp_lt)

/-- **`nockCompiles` at a concrete seed.**  Same package as `Batch288`, at
`seedZ` / `DotConfig769`.  `nockCompiles_p64` itself stays uninstantiated
(`romSeedVcomp` is `Classical.choose`). -/
noncomputable def b289_nockCompiles_literal :=
  Batch288.b288_nockCompiles_p63

end

end Nock.RedTeam.Batch289

#print axioms Nock.RedTeam.Batch289.b289_budget_vcomp_lt
#print axioms Nock.RedTeam.Batch289.b289_seedZ_joint
#print axioms Nock.RedTeam.Batch289.b289_exists_vcomp_seed
#print axioms Nock.RedTeam.Batch289.b289_nockCompiles_literal
