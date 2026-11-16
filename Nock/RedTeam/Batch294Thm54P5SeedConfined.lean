/-
  Nock/RedTeam/Batch294Thm54P5SeedConfined.lean

  Order honoured: (1) `seedZ = φ(7^(2^32−1))` of order `2^32` by two
  `ZMod p` kernels of `orderOf_eq_prime_pow`; (2) combinator
  `mm_traceConfined` at `Λ = 568` (lemma, not a binder); (3) Dyck /
  SeedGood / hout at the new seed.  `hbad` is the residual.

  Ruled out (not implemented): SubISA OP7/OP9;
  `decide` at an extension field; `hconf` as a sixth binder of
  `nockCompiles`.  No new failure-event summand.  No §1 instance.
-/
import Nock.Field
import Nock.NockVMROM.Thm54.GoldilocksOrbit
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksHbad
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksSeed
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.SizeWindowCounting

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch294

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GoldilocksOrbit
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open ComputeTable

abbrev GF := MatmulConfigGoldilocks.F
abbrev GK := MatmulConfigGoldilocks.K

/-! ## 1. Seed and the two `ZMod p` kernels. -/

theorem b294_seedZ : seedZ = φ goldilocksSeedBase := rfl

theorem b294_seed_not_eight :
    goldilocksSeedBase ≠ (8 : GF) := by
  intro h
  have hord := goldilocksSeedBase_order
  rw [h, eight_order] at hord
  exact (by decide : ¬ 64 = 2 ^ 32) hord

theorem b294_eight_order : orderOf (8 : GF) = 64 :=
  eight_order

theorem b294_seedBase_order : orderOf goldilocksSeedBase = 2 ^ 32 :=
  goldilocksSeedBase_order

theorem b294_kernel_31 : goldilocksSeedBase ^ (2 ^ 31) = (-1 : GF) :=
  goldilocksSeedBase_pow_two_pow_31

theorem b294_kernel_32 : goldilocksSeedBase ^ (2 ^ 32) = (1 : GF) :=
  goldilocksSeedBase_pow_two_pow_32

theorem b294_seedZ_order : orderOf seedZ = 2 ^ 32 :=
  seedZ_order

theorem b294_seedBase_val :
    goldilocksSeedBase = (1753635133440165772 : GF) :=
  goldilocksSeedBase_val

/-! ## 2. `mm_traceConfined` is a lemma, not a binder. -/

theorem b294_traceConfined :
    TraceConfined 568 (airReorder (mmTree (K := GK))) :=
  mm_traceConfined

theorem b294_traceConfined_2048 :
    TraceConfined 2048 (airReorder (mmTree (K := GK))) :=
  mm_traceConfined_2048

/-! ## 3. SeedGood and hout at the new seed. -/

theorem b294_seedGood : SeedGood seedZ (mmTree (K := GK)) :=
  mmTree_seedGood

variable [Fintype GK] [DecidableEq GK]

theorem b294_hout :
    seedZ ∉ sizeWindowFailureSeeds (K := GK)
      (genSemanticSkeleton (bfsAssign (airReorder (mmTree (K := GK))))
        (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (mmTree (K := GK)))) :=
  mm_hout

/-! ## 4. -/

theorem b294_hbad_residual (hΛ : 1 ≤ (568 : ℕ)) :
    seedZ ∉ (genSkeletonP8Census (K := GK) hΛ
      (mmTree_gen (K := GK)) mm_traceConfined
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
        (mmTree (K := GK)))).census.badSeeds :=
  mm_hbad hΛ

end Nock.RedTeam.Batch294

#print axioms Nock.RedTeam.Batch294.b294_seedZ_order
#print axioms Nock.RedTeam.Batch294.b294_traceConfined
#print axioms Nock.RedTeam.Batch294.b294_seedGood
#print axioms Nock.RedTeam.Batch294.b294_hout
#print axioms Nock.RedTeam.Batch294.b294_hbad_residual
#print axioms Nock.RedTeam.Batch294.b294_kernel_31
