import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch444

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem w_s_d_k {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.w = 205 ∧
      (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.s = 156 ∧
      (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.d = 4 ∧
      (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.k = 1 :=
  OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit 1

theorem e_three {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.e = 3 :=
  OptimizedMemoryRAP.finalMemoryRAP_e hn nodes b chalVal pubVal orbit 1

theorem all_gates_degree_le_four :
    ∀ g ∈ paperKGates (K := K) (F := F), g.degree ≤ 4 :=
  paperKGates_degree

/-- The hosted gate list has length `45`. -/
theorem hosted_length :
    (MemoryPaperFactorization.hostedPaperKGates (K := K) (F := F)).length = 45 := by
  simp [MemoryPaperFactorization.hostedPaperKGates, MemoryPaperFactorization.hostedPaperKGatesCore,
    MemoryPaperFactorization.rapMemGates, MemoryPaperFactorization.tabVMemGates,
    MemoryPaperFactorization.tabVMemClassIndices, MemoryPaperFactorization.baseTypedClassGates,
    MemoryPaperFactorization.baseTypedClassIndices, MemoryPaperFactorization.bottomPins,
    MemoryPaperFactorization.bottomPinIndices, MemoryPaperFactorization.hostedWalkGates,
    MemoryPaperFactorization.hostedWalkInitGates, MemoryPaperFactorization.hostedWalkStepGates,
    MemoryPaperFactorization.ioCoreGates, MemoryPaperFactorization.hostedNewGates]

/-- The committed gate list has length `49`. -/
theorem committed_length : (paperKGates (K := K) (F := F)).length = 49 :=
  paperKGates_length

/-- The memory walk summand of the K-side bound at the paper's width. -/
theorem memory_walk_bound_width : NodeEncoding.memoryNodeWidth - 1 = 5 := rfl

/-- The bound function's name, for the record (its body reads no encoder width). -/
def CONSUMED_BOUND : String :=
  "OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound"

/-- The cited soundness figures (name, bits). -/
def FIGURES : List (String × ℕ) :=
  [("GoldilocksParameters.hostile_soundness_at_paper_configuration", 123),
   ("RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31", 122),
   ("RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32", 120)]

theorem figures_length : FIGURES.length = 3 := by decide

end Nock.RedTeam.Batch444

#print axioms Nock.RedTeam.Batch444.w_s_d_k
#print axioms Nock.RedTeam.Batch444.all_gates_degree_le_four
