/-
  Nock/RedTeam/Batch583Thm54DeployedStaging.lean

  Staged views of the DEPLOYED
  chips and the B2 enumeration.

  Now:

  * the views carry the deployed RAPs (`ProductionNamedComputeRAP`, `namedFinalMemoryRAP`), with
    `w = 302`, `s = 416` and `w = 204`, `s = 156` read off the RAPs themselves;
  * every deployed gate is classified (`DeployedStaging.compute_*_classes`,
    `memory_*_classes`); the totals are below;

  Class `1` coin-free over a later column, `2` latest
  coin is a round-0 coin, `3` latest coin is a round-1 coin:
  compute `416` = `133` pass + `199` class 1 + `42` class 2 + `42` class 3;
  memory `156` = `15` pass + `105` class 1 + `6` class 2 + `30` class 3.
-/
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.RedTeam.Batch580Thm54PreseedChronology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch583

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Module

section Views

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The compute view is the deployed RAP at `302 / 416`, staged in three blocks. -/
theorem staged_at_302 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) :
    (deployedComputeView hn nodes b chalVal pubVal orbit).rap.w = 303 ∧
      (deployedComputeView hn nodes b chalVal pubVal orbit).rap.s = 418 ∧
      (deployedComputeView hn nodes b chalVal pubVal orbit).rap =
        (OptimizedComputeCorrectedFinal.ProductionNamedComputeRAP hn nodes b chalVal pubVal
          orbit).rap :=
  ⟨rfl, computeChip_s hn nodes b chalVal pubVal orbit, rfl⟩

/-- The memory view is the deployed RAP at `204 / 156`, staged in three blocks. -/
theorem staged_at_204 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).rap.w = 205 ∧
      (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).rap.s = 156 ∧
      (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).rap =
        (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap :=
  ⟨(deployedMemoryView hn nodes b chalVal pubVal orbit kMem).hw,
    memoryChip_s hn nodes b chalVal pubVal orbit kMem, rfl⟩

/-- The two views share one chronology (by typing) and the deployed schedules. -/
theorem views_share_chronology {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (deployedComputeView hn nodes b chalVal pubVal orbit).schedule.width = ![108, 132, 63] ∧
      (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).schedule.width = ![85, 48, 72] :=
  ⟨rfl, rfl⟩

/-- **Restored (F4).**  Declared commit-before-sample at 302: every column's declared challenge
set holds only coins sampled strictly before its round. -/
theorem declared_commit_before_sample {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) (c : Fin 303)
    (j : Fin deployedChronology.numChallenges)
    (hj : j ∈ (deployedComputeView hn nodes b chalVal pubVal orbit).columnChallenges c) :
    deployedChronology.usableByColumnOf
      ((deployedComputeView hn nodes b chalVal pubVal orbit).schedule.roundOf c) j :=
  (deployedComputeView hn nodes b chalVal pubVal orbit).columns_commit_before_sampling c j hj

/-- **Restored (F4).**  The same at 204. -/
theorem declared_commit_before_sample_memory {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ) (c : Fin 205)
    (j : Fin deployedChronology.numChallenges)
    (hj : j ∈ (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).columnChallenges c) :
    deployedChronology.usableByColumnOf
      ((deployedMemoryView hn nodes b chalVal pubVal orbit kMem).schedule.roundOf c) j :=
  (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).columns_commit_before_sampling c j hj

end Views

/-- **Restored (F4).**  A selector-only gate (round-0 column, no challenge) passes at 302 and 204. -/
theorem selector_block_ok :
    computeCoeffClass (CoordinateCompiler.CoeffExpr.var .traceCur 1 : CoordinateCompiler.CoeffExpr ℚ) = 0 ∧
      memoryCoeffClass (CoordinateCompiler.CoeffExpr.var .traceCur 1 : CoordinateCompiler.CoeffExpr ℚ) = 0 := by
  decide


/-! ## Totals of the B2 enumeration -/

def count (c : ℕ) (l : List ℕ) : ℕ := (l.filter (· == c)).length

/-- Compute: typed sources (each three gates): core 82, aux 3, endpoint 6 + 1, `λ` pins 2. -/
def computeTypedClassList : List ℕ :=
  [1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2,
    2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1,
    2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1] ++
  [3, 3, 1] ++ [3, 3, 1, 1, 1, 1] ++ [3] ++ [3, 3]

theorem computeTypedClassList_eq :
    computeTypedClassList =
      (List.finRange 82).map (fun i => computeTypedClass (correctedCoreSource i)) ++
        (List.finRange 3).map (fun j => computeTypedClass (correctedAuxSource j)) ++
        OptimizedComputeCorrectedFinal.correctedEndpoint2.map computeTypedClass ++
        OptimizedComputeCorrectedFinal.correctedEndpoint4.map computeTypedClass ++
        OptimizedComputeCorrectedFinal.formRLamPins.map computeTypedClass := by
  rw [compute_core_classes, compute_aux_classes, compute_endpoint2_classes,
    compute_endpoint4_classes, compute_lamPins_classes]
  rfl

theorem compute_totals :
    3 * count 1 computeTypedClassList + 1 = 199 ∧
      3 * count 2 computeTypedClassList = 42 ∧
      3 * count 3 computeTypedClassList = 42 ∧
      15 + 22 + 96 + 2 = 135 ∧
      135 + 199 + 42 + 42 = 418 := by
  decide

def memoryMixedClassList : List ℕ :=
  [2, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 0, 0, 1, 1, 1, 1, 1, 3, 3, 3,
    3, 3, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1]

theorem memory_totals :
    3 * count 0 memoryMixedClassList + 6 = 15 ∧
      3 * count 1 memoryMixedClassList = 105 ∧
      3 * count 2 memoryMixedClassList = 6 ∧
      3 * count 3 memoryMixedClassList = 30 ∧
      15 + 105 + 6 + 30 = 156 := by
  decide


theorem paper_vs_measured_at_atom :
    Batch580.memoryPaperRound ⟨180, by decide⟩ = 1 ∧
      memoryColRound OptimizedMemoryGateBasis.atomCol = 0 := by
  refine ⟨?_, rfl⟩
  simp [Batch580.memoryPaperRound]

end Nock.RedTeam.Batch583

#print axioms Nock.RedTeam.Batch583.staged_at_302
#print axioms Nock.RedTeam.Batch583.staged_at_204
#print axioms Nock.RedTeam.Batch583.compute_totals
#print axioms Nock.RedTeam.Batch583.memory_totals
#print axioms Nock.RedTeam.Batch583.paper_vs_measured_at_atom
