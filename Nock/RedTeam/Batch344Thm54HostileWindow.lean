/-
  Nock/RedTeam/Batch344Thm54HostileWindow.lean

  **Hostile window / workload majorant.**  Production statements live in
  `HostileWorkloadMajorant.lean`.  This artifact instantiates the step-1 inequality at
  the matmul counts (`N = 401`, `M = 30936`) and the Peano-fib counts (`N = 33`,
  `M = 1277`), records the recomputed figures beside the old `123 / 122 / 120`, and
  runs the negative control: `p8WorkHostile` at `M := 1` is below the honest
  topology term of matmul, hence below every honest `workload` at those row counts.

  Instrument for every numeral: `norm_num` on the closed form, or the named
  `GoldilocksParameters` / `RealProgramSoundness` comparison theorems.  No
  `decide` at `GaloisField`.  No `sorry` / `admit` / `native_decide`.
-/
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch344

open Nock.NockVMROM.Thm54.HostileWorkloadMajorant
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

/-! ## A. Closed-form numerals

Instrument: `norm_num` after `p8WorkHostile_eq`. -/

theorem p8WorkHostile_matmul : p8WorkHostile 401 30936 = 1466097601 := by
  norm_num [p8WorkHostile, p8Majorant]

theorem p8WorkHostile_peano_fib : p8WorkHostile 33 1277 = 3377181 := by
  norm_num [p8WorkHostile, p8Majorant]

theorem p8WorkHostile_matmul_M1 : p8WorkHostile 401 1 = 26081 := by
  norm_num [p8WorkHostile, p8Majorant]

theorem matmul_topology : 24 * 401 + 8 * 30936 = 257112 := by norm_num

theorem peano_fib_topology : 24 * 33 + 8 * 1277 = 11008 := by norm_num

/-! ## B. Step-1 inequality at the two programs

Generic in the strategy: any `T` whose compute-row count and two workload
bounds sit under the program's `(N, M)` inhabits the majorant. -/

section Receipts

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **Matmul (`N = 401`, `M = 30936`).** -/
theorem workload_le_p8WorkHostile_matmul
    (T : ProductionStrategy F K)
    (hrows : (computeSkeletonRows T.skeleton).length ≤ 401)
    (htop : fixedTopologyWorkload T ≤ 24 * 401 + 8 * 30936)
    (hax : fixedAxisWorkload T ≤ 3 * 401 * 30936)
    (hformR : formRUniformWorkload T ≤ 30936 * (3 * 401 + 130))
    (hmrows : (memorySkeletonRows T.skeleton).length ≤ 30936) :
    workload T 30936 (fixedTopologyWorkload T) (fixedAxisWorkload T)
      ≤ p8WorkHostile 401 30936 + 30936 * (3 * 401 + 130) + 30936 * (2 * 30936 - 1) :=
  workload_le_p8WorkHostile T 401 30936 hrows htop hax hformR hmrows

/-- **Peano-fib (`N = 33`, `M = 1277`).** -/
theorem workload_le_p8WorkHostile_peano_fib
    (T : ProductionStrategy F K)
    (hrows : (computeSkeletonRows T.skeleton).length ≤ 33)
    (htop : fixedTopologyWorkload T ≤ 24 * 33 + 8 * 1277)
    (hax : fixedAxisWorkload T ≤ 3 * 33 * 1277)
    (hformR : formRUniformWorkload T ≤ 1277 * (3 * 33 + 130))
    (hmrows : (memorySkeletonRows T.skeleton).length ≤ 1277) :
    workload T 1277 (fixedTopologyWorkload T) (fixedAxisWorkload T)
      ≤ p8WorkHostile 33 1277 + 1277 * (3 * 33 + 130) + 1277 * (2 * 1277 - 1) :=
  workload_le_p8WorkHostile T 33 1277 hrows htop hax hformR hmrows

/-! ## C. Negative control

`p8WorkHostile 401 1 = 26081` is strictly below the honest matmul topology
`24·401 + 8·30936 = 257112`, hence below every `workload` whose topology
summand is that of matmul.  The majorant is not vacuously huge: at `M := 1`
it undershoots the honest cost. -/

theorem p8WorkHostile_M1_lt_matmul_topology :
    p8WorkHostile 401 1 < 24 * 401 + 8 * 30936 := by
  rw [p8WorkHostile_matmul_M1, matmul_topology]
  norm_num

/-- Any strategy whose topology equals the matmul row counts has honest
`workload` strictly above `p8WorkHostile 401 1`. -/
theorem p8WorkHostile_M1_lt_honest_matmul_workload
    (T : ProductionStrategy F K) (Λ axisWorkload : ℕ)
    (htop : fixedTopologyWorkload T = 24 * 401 + 8 * 30936) :
    p8WorkHostile 401 1
      < workload T Λ (fixedTopologyWorkload T) axisWorkload := by
  have htopo : 24 * 401 + 8 * 30936
      ≤ workload T Λ (fixedTopologyWorkload T) axisWorkload := by
    simpa [htop] using workload_ge_topology T Λ (fixedTopologyWorkload T) axisWorkload
  exact lt_of_lt_of_le p8WorkHostile_M1_lt_matmul_topology htopo

end Receipts

/-! ## D. Figures, computed, beside `123 / 122 / 120`

| | old | at `p8WorkHostile` |
|---|---|---|
| paper configuration (`ioWork ≤ 16^65`) | 123 | **122** |
| real programs `2^31` (ceiling-free) | 122 | **122** |
| real programs `2^32` (ceiling-free) | 120 | **120** |

The `16^65` ceiling still applies to the paper-configuration analogue — same
`KB`/`LG` qualification.  `123` is lost: `not_123_at_paper_configuration_majorant`. -/

theorem paper_config_is_122 (ioWork : ℕ) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound (p8WorkHostile (2 ^ 31) (2 ^ 31)) ioWork
        (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_at_paper_configuration_majorant ioWork hio

theorem paper_config_floor (ioWork : ℕ) :
    1 / (2 : ℚ) ^ 125
      < goldilocksHostileFailureBound (p8WorkHostile (2 ^ 31) (2 ^ 31)) ioWork
          (2 ^ 31) (2 ^ 31) :=
  hostile_lower_bound_at_paper_configuration_majorant ioWork

theorem paper_config_not_123 :
    ¬ goldilocksHostileFailureBound (p8WorkHostile (2 ^ 31) (2 ^ 31)) (16 ^ 65)
        (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 :=
  not_123_at_paper_configuration_majorant

theorem real_programs_two_pow_31_is_122 :
    goldilocksHostileFailureBound (p8WorkHostile (2 ^ 31) (2 ^ 31) + 2 ^ 31 * (2 * 2 ^ 31 - 1))
        (ioFailureUnionBound 10 (3 * 2 ^ 31) (2 ^ 31) (Fintype.card Nock.Field.K))
        (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_for_real_programs_at_two_pow_31_majorant
    (2 ^ 31) (2 ^ 31) (le_rfl) (le_rfl)

theorem real_programs_two_pow_32_is_120 :
    goldilocksHostileFailureBound (p8WorkHostile (2 ^ 32) (2 ^ 32) + 2 ^ 32 * (2 * 2 ^ 32 - 1))
        (ioFailureUnionBound 10 (3 * 2 ^ 32) (2 ^ 32) (Fintype.card Nock.Field.K))
        (2 ^ 32) (2 ^ 32)
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_for_real_programs_at_two_pow_32_majorant
    (2 ^ 32) (2 ^ 32) (le_rfl) (le_rfl)

theorem hostile_bound_at_majorant_rfl (N M ioWork : ℕ) :
    goldilocksHostileFailureBound (p8WorkHostile N M) ioWork N M =
      hostileBoundAtMajorant cardKGold N M ioWork :=
  hostile_bound_at_majorant N M ioWork

/-- Generic restatement of the consumed bound function at the majorant. -/
theorem hostile_bound_eq_rfl (cardK cardF N M ioWork : ℕ) :
    Nock.NockVMROM.Thm54.OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound
        cardK cardF (p8WorkHostile N M) ioWork N M =
      hostileBoundAtMajorant cardK N M ioWork :=
  hostile_bound_eq cardK cardF N M ioWork

end

end Nock.RedTeam.Batch344

#print axioms Nock.RedTeam.Batch344.p8WorkHostile_matmul
#print axioms Nock.RedTeam.Batch344.p8WorkHostile_peano_fib
#print axioms Nock.RedTeam.Batch344.workload_le_p8WorkHostile_matmul
#print axioms Nock.RedTeam.Batch344.workload_le_p8WorkHostile_peano_fib
#print axioms Nock.RedTeam.Batch344.p8WorkHostile_M1_lt_matmul_topology
#print axioms Nock.RedTeam.Batch344.p8WorkHostile_M1_lt_honest_matmul_workload
#print axioms Nock.RedTeam.Batch344.paper_config_is_122
#print axioms Nock.RedTeam.Batch344.paper_config_floor
#print axioms Nock.RedTeam.Batch344.paper_config_not_123
#print axioms Nock.RedTeam.Batch344.real_programs_two_pow_31_is_122
#print axioms Nock.RedTeam.Batch344.real_programs_two_pow_32_is_120
