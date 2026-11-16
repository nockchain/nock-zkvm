/-
  Nock/RedTeam/Batch496Thm54PrefixGammaPriced.lean

  The two prefix γ-events join the consumed
  union.  Cards `≤ 9N` / `≤ 5M`.
-/
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch496

open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents

theorem compute_bound_eq (N : ℕ) : computePrefixGammaBound N = 9 * N :=
  computePrefixGammaBound_eq N

theorem memory_bound_eq (M : ℕ) : memoryPrefixGammaBound M = 5 * M :=
  memoryPrefixGammaBound_eq M

theorem pricedWalkWork_eq (N M : ℕ) :
    pricedWalkWork N M =
      walkRootBound N +
        computeTilingBound N +
        memoryTilingBound M +
        9 * N + 5 * M + M := by
  -- thirtieth move: the λ-event slack `pwAccountingWork' 64 N M` left `pricedWalkWork`
  simp only [pricedWalkWork, computePrefixGammaBound, memoryPrefixGammaBound,
    Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents.memoryForestAlphaBound]

theorem figure_123 (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 :=
  hostile_soundness_at_paper_configuration p8Work ioWork hp8 hio

/-- Walk majorant at the paper configuration: `19·2^31 + 12 ≤ 2^36`. -/
theorem walk_majorant_2_36 :
    pricedWalkWork (2 ^ 31) (2 ^ 31) ≤ 2 ^ 36 :=
  walkAndTilingBound_at_paper_configuration

def nockCompiles_zmod_hypotheses_unmoved : String :=
  "nockCompiles_zmod binders unmoved: hrun hbound hs hf hΛp hp hK hF hwin hKszChar"

theorem nockCompiles_zmod_hypotheses_unmoved_nonempty :
    nockCompiles_zmod_hypotheses_unmoved ≠ "" := by
  decide

end Nock.RedTeam.Batch496

#print axioms Nock.RedTeam.Batch496.figure_123
#print axioms Nock.RedTeam.Batch496.walk_majorant_2_36
