import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.MemoryHaltRowsBase

/-!
# Concrete non-vacuity of the optimized memory RAP

This module instantiates the same-object canonical memory construction over
`F73 ⊂ K73cubic` using the existing strict package
.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryCanonicalSatisfaction
namespace Concrete

open Nock
open Nock.Framework
open Module
open scoped Polynomial
open StrictExtension
open CoordinateBasis
open ConcreteStrictPackage
open OptimizedComputeSampledTrace.Concrete
open OptimizedMemorySameExecution.Concrete
open OptimizedMemorySemanticRealization
open OptimizedMemoryCanonicalTrace
open OptimizedMemoryCodec
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open CoordinateCompiler
open MonolithicRAP
open Nock.Reified

noncomputable section

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- The five canonical memory rows occupy the first five points of the strict base-field orbit. -/
def honestMemoryNodes :
    Fin honestLegacyFamily.problem.cfg.memRows → F73 :=
  fun i => strictOrbit.βcoset * strictOrbit.ω ^ (i : ℕ)

theorem honestMemoryNodes_injective : Function.Injective honestMemoryNodes := by
  decide

theorem honestMemoryNodes_aligned :
    MemoryOrbitAligned honestMemoryNodes strictOrbit := by
  intro i hi
  change strictOrbit.βcoset * strictOrbit.ω ^ ((i : ℕ) + 1) =
    strictOrbit.βcoset * strictOrbit.ω ^ (i : ℕ) * strictOrbit.ω
  rw [pow_succ]
  ring

/-- Three-coordinate serialization of a finite tuple of cubic-field values. -/
def coordinateBlock {n : ℕ} (v : Fin n → K73cubic) (j : ℕ) : F73 :=
  if h : j / 3 < n then coord basis73 (v ⟨j / 3, h⟩) ⟨j % 3, Nat.mod_lt _ (by omega)⟩
  else 0

theorem coordinateBlock_reconstruct {n : ℕ} (v : Fin n → K73cubic) (q : Fin n) :
    (∑ k : Fin 3, coordinateBlock v (3 * (q : ℕ) + (k : ℕ)) • basis73 k) = v q := by
  have hdiv : ∀ k : Fin 3, (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by
    intro k
    omega
  have hmod : ∀ k : Fin 3, (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by
    intro k
    omega
  simpa [coordinateBlock, hdiv, hmod, reconstruct] using reconstruct_coord basis73 (v q)

/-- The F73 fixture's memory `𝕂` challenge targets: the three table challenges, the walk `α`,
the sampled IO coins `γ` (slot `4`) and IO pole (slot `5`), and — W4 stage 2 — the sampled
internal `intermediate` pole at slot `6`, walk `γ` at slot `7`, and form-R `λ` at slot `8`. -/
def honestMemoryChallengeTargets : Fin 9 → K73cubic
  | 0 => (exactMemoryRowEnv honestSampled
      ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩).chal 0
  | 1 => (exactMemoryRowEnv honestSampled
      ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩).chal 1
  | 2 => (exactMemoryRowEnv honestSampled
      ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩).chal 2
  | 3 => honestLegacyFamily.memoryWalkAlpha
  | 4 => honestSampled.sampled.coins.gamma
  | 5 => honestSampled.sampled.coins.pole
  | 6 => honestSampled.interPole
  | 7 => honestLegacyFamily.walkGamma
  | 8 => (exactMemoryRowEnv honestSampled
      ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩).chal 8

def honestMemoryPublicTargets : Fin 3 → K73cubic
  | 0 => honestLegacyFamily.memoryWalkAlpha ^ honestLegacyFamily.problem.cfg.kMem
  | 1 => honestLegacyFamily.memoryWalkSeed
  | 2 => honestSampled.witness10.terminal

/-- Coordinate pins for the concrete memory challenges and aggregate forest public values. -/
def honestMemoryChalVal (j : ℕ) : F73 :=
  if j < 4 then 2
  else if 6 ≤ j then coordinateBlock honestMemoryChallengeTargets (j - 6) else 0

def honestMemoryPubVal (j : ℕ) : F73 :=
  if 6 ≤ j then coordinateBlock honestMemoryPublicTargets (j - 6) else 0

theorem honestMemoryPins :
    ExactMemoryCoordinatePins honestSampled basis73
      honestMemoryChalVal honestMemoryPubVal := by
  constructor
  · intro q
    let q4 : Fin 9 := ⟨q, by omega⟩
    have htarget : honestMemoryChallengeTargets q4 =
        (exactMemoryRowEnv honestSampled
          ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩).chal q := by
      fin_cases q <;> rfl
    rw [← htarget]
    have hcell : ∀ k : Fin 3,
        honestMemoryChalVal (6 + 3 * (q : ℕ) + (k : ℕ)) =
          coordinateBlock honestMemoryChallengeTargets (3 * (q4 : ℕ) + (k : ℕ)) := by
      intro k
      have harg : 6 + 3 * (q : ℕ) + (k : ℕ) - 6 =
          3 * (q : ℕ) + (k : ℕ) := by omega
      rw [honestMemoryChalVal, if_neg (by omega), if_pos (by omega), harg]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryChallengeTargets q4
  · have hcell : ∀ k : Fin 3,
        honestMemoryChalVal (6 + 3 * 3 + (k : ℕ)) =
          coordinateBlock honestMemoryChallengeTargets (3 * 3 + (k : ℕ)) := by
      intro k
      have harg : 6 + 3 * 3 + (k : ℕ) - 6 = 3 * 3 + (k : ℕ) := by omega
      rw [honestMemoryChalVal, if_neg (by omega), if_pos (by omega), harg]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryChallengeTargets (3 : Fin 9)
  · have hcell : ∀ k : Fin 3,
        honestMemoryPubVal (6 + 3 * 0 + (k : ℕ)) =
          coordinateBlock honestMemoryPublicTargets (3 * 0 + (k : ℕ)) := by
      intro k
      simp [honestMemoryPubVal]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryPublicTargets (0 : Fin 3)
  · have hcell : ∀ k : Fin 3,
        honestMemoryPubVal (6 + 3 * 2 + (k : ℕ)) =
          coordinateBlock honestMemoryPublicTargets (3 * 2 + (k : ℕ)) := by
      intro k
      have harg : 6 + 3 * 2 + (k : ℕ) - 6 = 3 * 2 + (k : ℕ) := by omega
      rw [honestMemoryPubVal, if_pos (by omega), harg]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryPublicTargets (2 : Fin 3)
  · have hcell : ∀ k : Fin 3,
        honestMemoryChalVal (6 + 3 * 4 + (k : ℕ)) =
          coordinateBlock honestMemoryChallengeTargets (3 * 4 + (k : ℕ)) := by
      intro k
      have harg : 6 + 3 * 4 + (k : ℕ) - 6 = 3 * 4 + (k : ℕ) := by omega
      rw [honestMemoryChalVal, if_neg (by omega), if_pos (by omega), harg]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryChallengeTargets (4 : Fin 9)
  · have hcell : ∀ k : Fin 3,
        honestMemoryChalVal (6 + 3 * 5 + (k : ℕ)) =
          coordinateBlock honestMemoryChallengeTargets (3 * 5 + (k : ℕ)) := by
      intro k
      have harg : 6 + 3 * 5 + (k : ℕ) - 6 = 3 * 5 + (k : ℕ) := by omega
      rw [honestMemoryChalVal, if_neg (by omega), if_pos (by omega), harg]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryChallengeTargets (5 : Fin 9)
  · have hcell : ∀ k : Fin 3,
        honestMemoryChalVal (6 + 3 * 6 + (k : ℕ)) =
          coordinateBlock honestMemoryChallengeTargets (3 * 6 + (k : ℕ)) := by
      intro k
      have harg : 6 + 3 * 6 + (k : ℕ) - 6 = 3 * 6 + (k : ℕ) := by omega
      rw [honestMemoryChalVal, if_neg (by omega), if_pos (by omega), harg]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryChallengeTargets (6 : Fin 9)
  · have hcell : ∀ k : Fin 3,
        honestMemoryChalVal (6 + 3 * 7 + (k : ℕ)) =
          coordinateBlock honestMemoryChallengeTargets (3 * 7 + (k : ℕ)) := by
      intro k
      have harg : 6 + 3 * 7 + (k : ℕ) - 6 = 3 * 7 + (k : ℕ) := by omega
      rw [honestMemoryChalVal, if_neg (by omega), if_pos (by omega), harg]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryChallengeTargets (7 : Fin 9)
  · have hcell : ∀ k : Fin 3,
        honestMemoryChalVal (6 + 3 * 8 + (k : ℕ)) =
          coordinateBlock honestMemoryChallengeTargets (3 * 8 + (k : ℕ)) := by
      intro k
      have harg : 6 + 3 * 8 + (k : ℕ) - 6 = 3 * 8 + (k : ℕ) := by omega
      rw [honestMemoryChalVal, if_neg (by omega), if_pos (by omega), harg]
    simp_rw [hcell]
    exact coordinateBlock_reconstruct honestMemoryChallengeTargets (8 : Fin 9)

theorem honestMemoryDenominatorsSafe :
    MemoryDenominatorsSafe honestSampled :=
  memoryDenominatorsSafe_of_sampled honestSampled

theorem honest_memoryRows :
    honestLegacyFamily.problem.exec.memoryRows =
      [ConcreteStrictPackage.dummyHaltRow ConcreteStrictPackage.honestSeed,
       ConcreteStrictPackage.readRow ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha,
       ConcreteStrictPackage.decomposeRow ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha,
       ConcreteStrictPackage.headRow ConcreteStrictPackage.honestSeed,
       ConcreteStrictPackage.verifyRow ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha,
       ConcreteStrictPackage.tailRow ConcreteStrictPackage.honestSeed] := by
  change (TemplateRawJointSoundness.specializedProblem
      ConcreteStrictPackage.timestampStrategy ConcreteStrictPackage.honestSeed
      ConcreteStrictPackage.honestSeed_ne ConcreteStrictPackage.honestAlpha MemoryTable.formRDefault).exec.memoryRows = _
  rw [ConcreteStrictPackage.specializedProblem_eq]
  exact (ConcreteStrictPackage.execution_rows _ _).2

theorem honest_pairedRecordLayout :
    RowLayout.PairedRecordLayout honestLegacyFamily.problem.exec := by
  simp [RowLayout.PairedRecordLayout, RowLayout.consumedRecordList,
    RowLayout.addedRecordList, honest_memoryRows, MemoryTable.responseRecords,
    RowLayout.consumedRecords, ConcreteStrictPackage.dummyHaltRow,
    ConcreteStrictPackage.dummyHaltPub, ConcreteStrictPackage.readRow,
    ConcreteStrictPackage.decomposeRow, ConcreteStrictPackage.headRow,
    ConcreteStrictPackage.verifyRow, ConcreteStrictPackage.tailRow,
    ConcreteStrictPackage.readPub, ConcreteStrictPackage.decomposePub,
    ConcreteStrictPackage.headPub, ConcreteStrictPackage.verifyPub,
    ConcreteStrictPackage.tailPub]

-- Provisional: `C' = 1` is gone on row-level rows; coherence instead.
theorem honest_hC : honestLegacyFamily.problem.exec.CprimeCoherent := by
  have h := execution_cprimeCoherent honestSeed honestAlpha
  unfold ExactExecution.CprimeCoherent at h ⊢
  rw [honest_memoryRows]
  rwa [(execution_rows honestSeed honestAlpha).2] at h

theorem honest_ver :
    ∀ row ∈ honestLegacyFamily.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  simp [honest_memoryRows, ConcreteStrictPackage.dummyHaltRow,
    ConcreteStrictPackage.dummyHaltPub, ConcreteStrictPackage.readRow,
    ConcreteStrictPackage.decomposeRow, ConcreteStrictPackage.headRow,
    ConcreteStrictPackage.verifyRow, ConcreteStrictPackage.tailRow,
    ConcreteStrictPackage.readPub, ConcreteStrictPackage.decomposePub,
    ConcreteStrictPackage.headPub, ConcreteStrictPackage.verifyPub,
    ConcreteStrictPackage.tailPub]

theorem honest_memRows_eq_five :
    honestLegacyFamily.problem.cfg.memRows = 6 := by
  change (ConcreteStrictPackage.cfg ConcreteStrictPackage.honestSeed
    ConcreteStrictPackage.honestAlpha).memRows = 6
  rfl

theorem honest_memory_walk_order :
    2 ≤ honestLegacyFamily.problem.cfg.memRows →
      honestLegacyFamily.problem.cfg.memRows ≤
        orderOf honestLegacyFamily.memoryWalkAlpha := by
  intro _
  have hrows : honestLegacyFamily.problem.cfg.memRows = 6 := honest_memRows_eq_five
  have hα : honestLegacyFamily.memoryWalkAlpha = honestAlpha := rfl
  have hord : orderOf honestAlpha = 9 := honestAlpha_order
  rw [hrows, hα, hord]
  omega

theorem honest_two_ne_zero : (2 : K73cubic) ≠ 0 := by
  intro h
  have : (2 : F73) ≠ 0 := by decide
  apply this
  exact (algebraMap F73 K73cubic).injective (by simpa only [map_ofNat, map_zero] using h)

theorem honest_pole9_ne_zero (i : Fin honestLegacyFamily.problem.cfg.memRows) :
    MemoryPaperFactorization.poleSource.eval
      (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i) ≠ 0 := by
  set envK := canonicalGatheredEnv honestSampled honestMemoryNodes basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit i
  have h6 : envK.chal 6 = 2 := honestMemoryPins.sampledInterPole
  have h4 : envK.chal 4 = honestSampled.sampled.coins.gamma :=
    honestMemoryPins.sampledGamma
  have hγ0 : honestSampled.sampled.coins.gamma = 0 := rfl
  have h19 : envK.trace 19 = (exactMemoryRowEnv honestSampled i).trace 23 :=
    canonical_table_role honestSampled honestMemoryNodes
      honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit honestMemoryPins i 23 (by norm_num) (by norm_num) (by decide)
  simp [MemoryPaperFactorization.poleSource, recordRLCExpr, Expr.eval, h6, h4, hγ0, h19]
  have hsz : (exactMemoryRowEnv honestSampled i).trace 23 =
      (honestLegacyFamily.problem.exec.memoryPubAt i).mem.root.size := rfl
  rw [hsz]
  have h3 : (3 : K73cubic) ≠ 0 := by
    intro h
    have : (3 : F73) ≠ 0 := by decide
    apply this
    exact (algebraMap F73 K73cubic).injective (by simpa only [map_ofNat, map_zero] using h)
  fin_cases i <;>
    (simp [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, honest_memoryRows,
        List.get_eq_getElem, ConcreteStrictPackage.dummyHaltRow,
        ConcreteStrictPackage.dummyHaltPub, ConcreteStrictPackage.readRow,
        ConcreteStrictPackage.decomposeRow, ConcreteStrictPackage.headRow,
        ConcreteStrictPackage.verifyRow, ConcreteStrictPackage.tailRow,
        ConcreteStrictPackage.readPub, ConcreteStrictPackage.decomposePub,
        ConcreteStrictPackage.headPub, ConcreteStrictPackage.verifyPub,
        ConcreteStrictPackage.tailPub, ConcreteStrictPackage.requestRecord,
        ConcreteStrictPackage.rowRecord, NockVM.formRRow,
        ConcreteStrictPackage.formula_fp, ComputeTable.MemRec.zero] <;>
      first | exact honest_two_ne_zero | (norm_num; exact h3))

/-- The 31st: at `γ = 0` the pole's `reqIdx` slot vanishes (`γ⁹ · reqIdx = 0`). -/
theorem honest_pole_ne_zero (i : Fin honestLegacyFamily.problem.cfg.memRows) :
    MemoryPaperFactorization.poleSourceMixed.eval
      (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i)
      (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i) ≠ 0 := by
  have h4 : (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
      honestMemoryChalVal honestMemoryPubVal strictOrbit i).chal 4 =
        honestSampled.sampled.coins.gamma := honestMemoryPins.sampledGamma
  have hγ0 : honestSampled.sampled.coins.gamma = 0 := rfl
  have h9 : MemoryPaperFactorization.poleSourceMixed.eval
      (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i)
      (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i) =
      MemoryPaperFactorization.poleSource.eval
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit i) := by
    simp [MemoryPaperFactorization.poleSourceMixed, reqIdxRLCTerm,
      MixedCoordinateCompiler.MixedExpr.eval, MixedCoordinateCompiler.MixedExpr.ofExpr_eval,
      h4, hγ0]
  rw [h9]
  exact honest_pole9_ne_zero i

theorem honest_hdenAll (i : Fin honestLegacyFamily.problem.cfg.memRows) :
    MemoryPaperFactorization.poleSourceMixed.eval
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit i)
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit i) ≠ 0 ∨
      MemoryPaperFactorization.aggregatorSign
        (honestLegacyFamily.problem.exec.memoryPubAt i).st = (0 : K73cubic) :=
  Or.inl (honest_pole_ne_zero i)

/-- The 29th: the F73 fixture's `halt` rows carry base-field leaves (every row is bound to its
skeleton row, `ConcreteStrictPackage.bind_*Row`; skeleton `halt` parents are atoms). -/
theorem honest_hhalt : OptimizedMemoryCanonicalSatisfaction.HaltLeavesBase honestSampled := by
  apply MemoryHaltLeavesHonest.haltLeavesBase_of_rows
  change MemoryHaltLeavesHonest.HaltRowsBase
    (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec
  rw [specializedProblem_eq]
  intro row hrow hst
  rw [(execution_rows honestSeed honestAlpha).2] at hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf (bind_dummyHaltRow _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf (bind_readRow _ _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf (bind_decomposeRow _ _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf (bind_headRow _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf (bind_verifyRow _ _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf (bind_tailRow _) hst

/-- Concrete source-RAP satisfaction, from later-seed zeros.  At form R the
    served read-root is not table-zero (`honest_served_root_not_table_zero`);
    `hmore` is the remaining Relaxis join. -/
theorem honest_source_memory_satisfies
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    RAP.SatisfiesWithPreprocessing
      (namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
        honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
      (canonicalSourceTrace honestSampled honestMemoryNodes basis73 honestLegacyFamily.problem.cfg.kMem) :=
  canonicalSourceTrace_satisfies honestSampled honestProduction
    honestMemoryNodes honestMemoryNodes_injective basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit honestMemoryPins
    honestMemoryNodes_aligned honestMemoryDenominatorsSafe
    honest_pairedRecordLayout honest_ver honest_memory_walk_order hmore
    honestLegacyFamily.problem.memory_same_lambda honest_hC honest_hdenAll honest_hhalt

/-- Concrete final-RAP satisfaction, from later-seed zeros. Remaining Relaxis join. -/
theorem honest_final_memory_satisfies
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    RAP.SatisfiesWithPreprocessing
      (namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
        honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
      (canonicalFinalMemoryTrace honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit) :=
  canonicalFinalMemoryTrace_satisfies honestSampled honestProduction
    honestMemoryNodes honestMemoryNodes_injective basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit honestMemoryPins
    honestMemoryNodes_aligned honestMemoryDenominatorsSafe
    honest_pairedRecordLayout honest_ver honest_memory_walk_order hmore
    honestLegacyFamily.problem.memory_same_lambda honest_hC honest_hdenAll honest_hhalt

/-- Concrete inhabitant of the threaded satisfaction-plus-axis realization export.
    `hmore` is the remaining Relaxis join at form R. -/
theorem honest_memory_realization
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    RAP.SatisfiesWithPreprocessing
        (namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
          honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
        (canonicalSourceTrace honestSampled honestMemoryNodes basis73 honestLegacyFamily.problem.cfg.kMem) ∧
      RAP.SatisfiesWithPreprocessing
        (namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
          honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
        (canonicalFinalMemoryTrace honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit) ∧
      -- Provisional: axis accounting on the a-bearing view `honestExecA`.
      ∀ (root : Fin honestLegacyFamily.problem.cfg.kMem) (e : ℕ),
        e ∈ AxisBridge.readExps
            (exactAxisTree honestLegacyFamily.problem.cfg honestExecA root) →
        e ∈ AxisBridge.verifyExps
            (exactAxisTree honestLegacyFamily.problem.cfg honestExecA root) →
        Nock.AxisBatching.MTree.vaxis e
            (exactAxisTree honestLegacyFamily.problem.cfg honestExecA root) =
          Nock.AxisBatching.MTree.Relaxis e
            (exactAxisTree honestLegacyFamily.problem.cfg honestExecA root) := by
  refine canonicalMemoryRealization honestSampled honestProduction honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestMemoryPins honestMemoryNodes_aligned honestMemoryDenominatorsSafe
    honest_pairedRecordLayout honest_ver honest_memory_walk_order hmore
    honestLegacyFamily.problem.memory_same_lambda honest_hC honest_hdenAll honest_hhalt ?_
  have htwoBase : (2 : F73) ≠ 0 := by decide
  intro hk
  apply htwoBase
  apply (algebraMap F73 K73cubic).injective
  simpa only [map_ofNat, map_zero] using hk

/-! ## Concrete malformed-witness controls -/

def honestReadMemoryIndex : Fin honestLegacyFamily.problem.cfg.memRows :=
  ⟨1, by
    change 1 < (ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows
    norm_num [ConcreteStrictPackage.cfg]⟩

def honestVerifyMemoryIndex : Fin honestLegacyFamily.problem.cfg.memRows :=
  ⟨4, by
    change 4 < (ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows
    norm_num [ConcreteStrictPackage.cfg]⟩

theorem honest_read_state :
    (honestLegacyFamily.problem.exec.memoryPubAt honestReadMemoryIndex).st =
      .read_root := by
  have h := ConcreteStrictPackage.honestRawLegacy_memoryPubAt_one
  change honestLegacyFamily.problem.exec.memoryPubAt _ =
    ConcreteStrictPackage.readPub honestSeed honestAlpha at h
  let j : Fin honestLegacyFamily.problem.cfg.memRows := honestReadMemoryIndex
  change honestLegacyFamily.problem.exec.memoryPubAt j =
    ConcreteStrictPackage.readPub honestSeed honestAlpha at h
  exact congrArg (fun r : MemoryTable.Pub K73cubic => r.st) h

theorem honest_verify_state :
    (honestLegacyFamily.problem.exec.memoryPubAt honestVerifyMemoryIndex).st =
      .verify_child := by
  have h := ConcreteStrictPackage.honestRawLegacy_memoryPubAt_four
  change honestLegacyFamily.problem.exec.memoryPubAt _ =
    ConcreteStrictPackage.verifyPub honestSeed honestAlpha at h
  let j : Fin honestLegacyFamily.problem.cfg.memRows := honestVerifyMemoryIndex
  change honestLegacyFamily.problem.exec.memoryPubAt j =
    ConcreteStrictPackage.verifyPub honestSeed honestAlpha at h
  exact congrArg (fun r : MemoryTable.Pub K73cubic => r.st) h

theorem honest_verify_timestamp_ne_zero :
    (honestLegacyFamily.problem.exec.memoryPubAt honestVerifyMemoryIndex).mem.ts ≠ 0 := by
  have h := ConcreteStrictPackage.honestRawLegacy_memoryPubAt_four
  change honestLegacyFamily.problem.exec.memoryPubAt _ =
    ConcreteStrictPackage.verifyPub honestSeed honestAlpha at h
  let j : Fin honestLegacyFamily.problem.cfg.memRows := honestVerifyMemoryIndex
  change honestLegacyFamily.problem.exec.memoryPubAt j =
    ConcreteStrictPackage.verifyPub honestSeed honestAlpha at h
  have hts := congrArg (fun r : MemoryTable.Pub K73cubic => r.mem.ts) h
  change (honestLegacyFamily.problem.exec.memoryPubAt j).mem.ts ≠ 0
  rw [hts]
  change (4 : K73cubic) ≠ 0
  intro hzero
  have hfour : (4 : F73) ≠ 0 := by decide
  apply hfour
  apply (algebraMap F73 K73cubic).injective
  simpa only [map_ofNat, map_zero] using hzero

theorem honest_read_axis_ne_zero :
    (honestLegacyFamily.problem.exec.memoryPubAt honestReadMemoryIndex).mem.axis ≠ 0 := by
  have h := ConcreteStrictPackage.honestRawLegacy_memoryPubAt_one
  change honestLegacyFamily.problem.exec.memoryPubAt _ =
    ConcreteStrictPackage.readPub honestSeed honestAlpha at h
  let j : Fin honestLegacyFamily.problem.cfg.memRows := honestReadMemoryIndex
  change honestLegacyFamily.problem.exec.memoryPubAt j =
    ConcreteStrictPackage.readPub honestSeed honestAlpha at h
  have hax := congrArg (fun r : MemoryTable.Pub K73cubic => r.mem.axis) h
  change (honestLegacyFamily.problem.exec.memoryPubAt j).mem.axis ≠ 0
  rw [hax]
  -- Provisional: the row-level read row carries `T = λ^m`, `λ = formRDefault = 2`.
  change ConcreteStrictPackage.rowT ≠ 0
  unfold ConcreteStrictPackage.rowT MemoryTable.formRT
  exact pow_ne_zero _ honest_two_ne_zero

theorem honest_response_active :
    responseActive (K := K73cubic)
      (honestLegacyFamily.problem.exec.memoryPubAt honestReadMemoryIndex).ver = 1 := by
  have h := honest_ver
    (honestLegacyFamily.problem.exec.memoryRowAt honestReadMemoryIndex)
    (ExactExecution.memoryRowAt_mem _ _)
  have hst := honest_read_state
  have hver :
      (honestLegacyFamily.problem.exec.memoryPubAt honestReadMemoryIndex).ver = true := by
    change (honestLegacyFamily.problem.exec.memoryRowAt honestReadMemoryIndex).2.2.ver = true
    have hsteq :
        (honestLegacyFamily.problem.exec.memoryRowAt honestReadMemoryIndex).2.2.st =
          (honestLegacyFamily.problem.exec.memoryPubAt honestReadMemoryIndex).st := by
      simp [ExactExecution.memoryPubAt]
    rw [hsteq, hst] at h
    simpa using h
  simp [responseActive, hver]

theorem honest_base_gate_zero (j : Fin 6) :
    ((baseTransitionGates basis73).get
      ⟨j, by simp [baseTransitionGates_length basis73]⟩).eval
      (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) = 0 := by
  have hvanish : ∀ g ∈ baseTransitionGates basis73,
      g.eval (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) = 0 := by
    intro g hg
    simp only [baseTransitionGates, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact (MemoryPaperFactorization.canonical_paperRowCore honestSampled honestProduction
        honestMemoryNodes honestMemoryNodes_injective basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit honestMemoryPins
        honestMemoryNodes_aligned honestMemoryDenominatorsSafe
        honest_pairedRecordLayout honest_ver
        honestLegacyFamily.problem.memory_same_lambda honest_hC
        honestReadMemoryIndex (honest_hdenAll _)).1 _ hg
    · rw [hg]
      exact canonical_readRootVerGate honestSampled honestMemoryNodes
        honestMemoryNodes_injective basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit honest_ver
        honestReadMemoryIndex
  exact hvanish _ (List.get_mem _ _)

/-! ### The four retyped gates, as mutation controls

Before stage 3b the first mask, last mask and intermediate chain were *compressed* base gates at
list positions `5`, `6` and `13`, and these controls indexed them positionally.  They are now
`𝕂`-valued mixed gates, so the control is stated against the gate the chip actually commits: the
compiled coordinate `0` of the mixed gate.  It is a strictly better control — it detects the same
mutation with **no compression coin in the statement at all**. -/

/-- The mixed first-mask gate's coordinate `0` rejects a malformed extension first mask while
fixed base preprocessing remains untouched. -/
theorem honest_wrong_first_extension_mask_mixed_gate :
    (MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
      (firstMaskMixed (F := F73)) 0).eval
      (mutateCurrentTrace
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 147 1) = 1 := by
  have hz := canonical_firstMaskBindingCoord_zero honestSampled honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestReadMemoryIndex 0
  simp [MixedCoordinateCompiler.mixedCompile, firstMaskMixed, memoryCol0, bcur,
    maskBindingCoord, extCoord, mutateCurrentTrace, CoeffExpr.eval] at hz ⊢
  linear_combination hz

/-- The mixed last-mask gate's coordinate `0` rejects a malformed extension last mask. -/
theorem honest_wrong_last_extension_mask_mixed_gate :
    (MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
      (lastMaskMixed (F := F73)) 0).eval
      (mutateCurrentTrace
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 150 1) = 1 := by
  have hz := canonical_lastMaskBindingCoord_zero honestSampled honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestReadMemoryIndex 0
  simp [MixedCoordinateCompiler.mixedCompile, lastMaskMixed, memoryCol0, bcur,
    maskBindingCoord, extCoord, mutateCurrentTrace, CoeffExpr.eval] at hz ⊢
  linear_combination hz

/-- Pre-W2 folded base gate `5` (first sampled terminal coordinate, column `126`).
Previously stated against the committed `baseTransitionGates`. -/
theorem honest_wrong_terminal_gate :
    ((foldedBaseTransitionGates basis73).get ⟨5, by simp [foldedBaseTransitionGates_length]⟩).eval
      (mutateCurrentTrace
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 126 1) = 1 := by
  have hz := canonical_baseTransitionGates honestSampled honestProduction honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestMemoryPins honestMemoryNodes_aligned honestMemoryDenominatorsSafe honestReadMemoryIndex
    ((foldedBaseTransitionGates basis73).get ⟨5, by simp [foldedBaseTransitionGates_length]⟩)
    (List.get_mem _ _)
  simp [foldedBaseTransitionGates, semanticBaseTail, sampledTerminalCoord, mutateCurrentTrace,
    extCoord, CoeffExpr.eval] at hz ⊢
  linear_combination hz

/-- Pre-W2 base gate `8` (first sampled accumulator coordinate). Previously committed in
`baseTransitionGates`. -/
theorem honest_wrong_accumulator_gate :
    ((foldedBaseTransitionGates basis73).get ⟨8, by simp [foldedBaseTransitionGates_length]⟩).eval
      (mutateCurrentTrace
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 138 1) = 1 := by
  have hz := canonical_baseTransitionGates honestSampled honestProduction honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestMemoryPins honestMemoryNodes_aligned honestMemoryDenominatorsSafe honestReadMemoryIndex
    ((foldedBaseTransitionGates basis73).get ⟨8, by simp [foldedBaseTransitionGates_length]⟩)
    (List.get_mem _ _)
  simp [foldedBaseTransitionGates, semanticBaseTail, sampledAccumulatorCoord, mutateCurrentTrace,
    extCoord, CoeffExpr.eval] at hz ⊢
  linear_combination hz

/-- The mixed chain gate's coordinate `0` rejects a current-row intermediate mutation. -/
theorem honest_wrong_intermediate_current_mixed_gate :
    (MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
      (chainMixed (F := F73)) 0).eval
      (mutateCurrentTrace
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 90 1) = 1 := by
  have hz := canonical_chainCoord_zero honestSampled honestProduction honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestMemoryNodes_aligned honestReadMemoryIndex 0
  have hb5 := canonical_base_current honestSampled honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestReadMemoryIndex (5 : Fin 6)
  have hb5zero :
      (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73 honestMemoryChalVal
        honestMemoryPubVal strictOrbit honestReadMemoryIndex).trace 5 = 0 := by
    rw [show (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
      honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex).trace 5 =
        (encodedRowAt (F := F73) honestSampled honestReadMemoryIndex).base 5 by
          simpa using hb5]
    simp [encodedRowAt, encode, encodeBase, semanticRowAt, lastMask, honestReadMemoryIndex]
    have hne : ¬ 2 = honestLegacyFamily.problem.cfg.memRows := by
      change ¬ 2 = (ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows
      norm_num [ConcreteStrictPackage.cfg]
    simp [hne]
  simp [MixedCoordinateCompiler.mixedCompile, chainMixed, memoryCol0, bcur, chainCoord,
    extCoord, mutateCurrentTrace, CoeffExpr.eval, hb5zero] at hz ⊢
  linear_combination hz

/-- The mixed chain gate's coordinate `0` rejects a next-row intermediate mutation. -/
theorem honest_wrong_intermediate_next_mixed_gate :
    (MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
      (chainMixed (F := F73)) 0).eval
      (mutateNextTrace
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 87 1) = -1 := by
  have hz := canonical_chainCoord_zero honestSampled honestProduction honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestMemoryNodes_aligned honestReadMemoryIndex 0
  have hb5 := canonical_base_current honestSampled honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestReadMemoryIndex (5 : Fin 6)
  have hb5zero :
      (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73 honestMemoryChalVal
        honestMemoryPubVal strictOrbit honestReadMemoryIndex).trace 5 = 0 := by
    rw [show (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
      honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex).trace 5 =
        (encodedRowAt (F := F73) honestSampled honestReadMemoryIndex).base 5 by
          simpa using hb5]
    simp [encodedRowAt, encode, encodeBase, semanticRowAt, lastMask, honestReadMemoryIndex]
    have hne : ¬ 2 = honestLegacyFamily.problem.cfg.memRows := by
      change ¬ 2 = (ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows
      norm_num [ConcreteStrictPackage.cfg]
    simp [hne]
  simp [MixedCoordinateCompiler.mixedCompile, chainMixed, memoryCol0, bcur, chainCoord,
    extCoord, mutateNextTrace, CoeffExpr.eval, hb5zero] at hz ⊢
  linear_combination hz

/-- Wrong committed axis: the named active `verify_child` counts source rejects the coherent
axis-role mutation on the same canonical production row. -/
theorem honest_wrong_axis_named_gate_rejection
    : verifyAxisSource (K := K73cubic).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestVerifyMemoryIndex)
        26 1) ≠ 0 := by
  apply canonical_verify_axis_named_gate_rejects honestSampled honestProduction
    honestLegacyFamily.problem.memory_same_lambda
    honestMemoryNodes honestMemoryNodes_injective basis73 honestMemoryChalVal
    honestMemoryPubVal strictOrbit honestMemoryPins honestVerifyMemoryIndex
  · exact honest_verify_state
  · rw [exactMemoryRowEnv, Nock.Reified.memoryEnvFull_chal_lambda, MemoryTable.Pub.lambda]
    simp [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, honest_memoryRows,
      List.get_eq_getElem, ConcreteStrictPackage.dummyHaltRow, ConcreteStrictPackage.dummyHaltPub]
    exact honest_two_ne_zero
  · norm_num

/-- Wrong unique timestamp: the named active `read_root` indicator source rejects the coherent
timestamp-role mutation on the same canonical production row. -/
theorem honest_wrong_timestamp_named_gate_rejection
    : readTimestampSource (K := K73cubic).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
        26 1) ≠ 0 := by
  apply canonical_read_timestamp_named_gate_rejects honestSampled honestProduction
    honestLegacyFamily.problem.memory_same_lambda
    honestMemoryNodes honestMemoryNodes_injective basis73 honestMemoryChalVal
    honestMemoryPubVal strictOrbit honestMemoryPins honestReadMemoryIndex
  · exact honest_read_state
  · rw [exactMemoryRowEnv, Nock.Reified.memoryEnvFull_chal_lambda, MemoryTable.Pub.lambda]
    simp [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, honest_memoryRows,
      List.get_eq_getElem, ConcreteStrictPackage.dummyHaltRow, ConcreteStrictPackage.dummyHaltPub]
    exact honest_two_ne_zero
  · exact honest_read_axis_ne_zero
  · norm_num

def honestFoldChallenge : K73cubic := honestSampled.interPole

theorem honest_fold_challenge_eq (i : Fin honestLegacyFamily.problem.cfg.memRows) :
    foldChallenge.eval
      (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i) =
      honestFoldChallenge := by
  change (∑ k : Fin 3, honestMemoryChalVal (6 + 3 * 6 + (k : ℕ)) • basis73 k) =
    honestSampled.interPole
  exact honestMemoryPins.sampledInterPole

theorem honest_extension_source_zero
    (i : Fin honestLegacyFamily.problem.cfg.memRows)
    (q : Fin (extensionFoldSources (K := K73cubic)).length)
    (h23 : extensionFoldSources (K := K73cubic).get q ≠
      (MemoryFactorizationScope.mergedGate (K := K73cubic) 23).subst memorySubst)
    (h24 : extensionFoldSources (K := K73cubic).get q ≠
      (MemoryFactorizationScope.mergedGate (K := K73cubic) 24).subst memorySubst) :
    (extensionFoldSources (K := K73cubic).get q).eval
      (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i) = 0 :=
  canonical_transitionSources honestSampled honestProduction
    honestLegacyFamily.problem.memory_same_lambda honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestMemoryPins honestMemoryNodes_aligned honestMemoryDenominatorsSafe i
    (extensionFoldSources (K := K73cubic).get q)
    (extensionFoldSources_subset_transitionSources
      (extensionFoldSources (K := K73cubic).get q) (List.get_mem _ _)) h23 h24

set_option maxHeartbeats 2000000
/-- The wrong-timestamp mutation is rejected by actual extension fold ID `0` at the concrete
nonzero fold challenge. -/
theorem honest_wrong_timestamp_foldAt0
    : (foldAt (K := K73cubic) (0 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
        26 1) ≠ 0 := by
  let env := canonicalGatheredEnv honestSampled honestMemoryNodes basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex
  let bad := mutateExtensionTrace env 26 1
  have hcanonical := honest_extension_source_zero honestReadMemoryIndex
  have hsame := readTimestamp_fold_bucket_other_unchanged env
  have h0 : (extensionFoldSources (K := K73cubic).get ⟨0, by decide⟩).eval bad = 0 := by
    rw [show (extensionFoldSources (K := K73cubic).get ⟨0, by decide⟩).eval bad =
      (extensionFoldSources (K := K73cubic).get ⟨0, by decide⟩).eval env by simpa [bad] using hsame]
    exact hcanonical ⟨0, by decide⟩ (by decide) (by decide)
  have h21 : (extensionFoldSources (K := K73cubic).get ⟨21, by decide⟩).eval bad ≠ 0 := by
    rw [readTimestampSource_extension_index]
    exact honest_wrong_timestamp_named_gate_rejection
  rw [foldAt0_eval bad]
  have hchal : foldChallenge.eval bad = honestFoldChallenge := by
    change foldChallenge.eval env = honestFoldChallenge
    exact honest_fold_challenge_eq honestReadMemoryIndex
  rw [hchal, h0, zero_add]
  have hfold : honestFoldChallenge ≠ 0 := honest_two_ne_zero
  exact mul_ne_zero hfold h21

/-- Wrong aggregate initial count and root seed are rejected by named first-row forest gates. -/
theorem honest_wrong_forest_count_and_seed_named_gate_rejection :
    forestCountSource.eval
        (mutateExtensionTrace
          (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit
            ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩)
          32 1) ≠ 0 ∧
      forestSeedSource.eval
        (mutateExtensionTrace
          (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit
            ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩)
          33 1) ≠ 0 := by
  constructor
  · exact canonical_forest_count_named_gate_rejects honestSampled honestProduction
      honestMemoryNodes honestMemoryNodes_injective basis73 honestMemoryChalVal
      honestMemoryPubVal strictOrbit honestMemoryPins honestMemoryNodes_aligned 1 (by norm_num)
  · exact canonical_forest_seed_named_gate_rejects honestSampled honestProduction
      honestMemoryNodes honestMemoryNodes_injective basis73 honestMemoryChalVal
      honestMemoryPubVal strictOrbit honestMemoryPins honestMemoryNodes_aligned 1 (by norm_num)

/-- Wrong denominator and multiplicity values are rejected by sampled source IDs `0` and `1`. -/
theorem honest_wrong_denominator_and_multiplicity_named_gate_rejection
    : denominatorSource.eval
        (mutateExtensionTrace
          (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
          38 1) ≠ 0 ∧
      multiplicitySource.eval
        (mutateExtensionTrace
          (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
          39 1) ≠ 0 := by
  constructor
  · exact canonical_denominator_named_gate_rejects honestSampled honestProduction
      honestMemoryNodes honestMemoryNodes_injective basis73 honestMemoryChalVal
      honestMemoryPubVal strictOrbit honestMemoryPins honestMemoryDenominatorsSafe
      honestReadMemoryIndex
      1 (by norm_num)
  · apply canonical_multiplicity_named_gate_rejects honestSampled honestProduction
      honestMemoryNodes honestMemoryNodes_injective basis73 honestMemoryChalVal
      honestMemoryPubVal strictOrbit honestReadMemoryIndex
    · exact honest_response_active
    · have htwoBase : (2 : F73) ≠ 0 := by decide
      intro h
      apply htwoBase
      apply (algebraMap F73 K73cubic).injective
      simpa only [map_ofNat, map_zero] using h

private theorem honestFoldChallenge_ne_zero : honestFoldChallenge ≠ 0 :=
  honest_two_ne_zero

set_option maxHeartbeats 2000000 in
theorem honest_wrong_axis_foldAt17 :
    (foldAt (K := K73cubic) (17 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestVerifyMemoryIndex)
        26 1) ≠ 0 := by
  let env := canonicalGatheredEnv honestSampled honestMemoryNodes basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit honestVerifyMemoryIndex
  let bad := mutateExtensionTrace env 26 1
  have hs := axis_fold_bucket_other_unchanged env
  have h38 : (extensionFoldSources (K := K73cubic).get ⟨38, by decide⟩).eval bad = 0 := by
    calc
      _ = (extensionFoldSources (K := K73cubic).get ⟨38, by decide⟩).eval env := by
        simpa [bad] using hs
      _ = 0 := honest_extension_source_zero honestVerifyMemoryIndex ⟨38, by decide⟩
        (by decide) (by decide)
  have h17 : (extensionFoldSources (K := K73cubic).get ⟨17, by decide⟩).eval bad ≠ 0 := by
    rw [malformed_named_source_indices.1]
    exact honest_wrong_axis_named_gate_rejection
  rw [foldAt17_eval bad]
  have hchal : foldChallenge.eval bad = honestFoldChallenge := by
    change foldChallenge.eval env = honestFoldChallenge
    exact honest_fold_challenge_eq honestVerifyMemoryIndex
  rw [hchal, h38, mul_zero, add_zero]
  exact h17

set_option maxHeartbeats 2000000 in
theorem honest_wrong_forest_count_foldAt8 :
    (foldAt (K := K73cubic) (8 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit
          ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩)
        32 1) ≠ 0 := by
  let env := canonicalGatheredEnv honestSampled honestMemoryNodes basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit
    ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩
  let bad := mutateExtensionTrace env 32 1
  have hs := forestCount_fold_bucket_other_unchanged env
  have h8 : (extensionFoldSources (K := K73cubic).get ⟨8, by decide⟩).eval bad = 0 := by
    calc
      _ = (extensionFoldSources (K := K73cubic).get ⟨8, by decide⟩).eval env := by simpa [bad] using hs
      _ = 0 := honest_extension_source_zero ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩ ⟨8, by decide⟩
        (by decide) (by decide)
  have h29 : (extensionFoldSources (K := K73cubic).get ⟨29, by decide⟩).eval bad ≠ 0 := by
    rw [malformed_named_source_indices.2.1]
    exact honest_wrong_forest_count_and_seed_named_gate_rejection.1
  rw [foldAt8_eval bad]
  have hchal : foldChallenge.eval bad = honestFoldChallenge := by
    change foldChallenge.eval env = honestFoldChallenge
    exact honest_fold_challenge_eq ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩
  rw [hchal, h8, zero_add]
  exact mul_ne_zero honestFoldChallenge_ne_zero h29

set_option maxHeartbeats 2000000 in
theorem honest_wrong_forest_seed_foldAt9 :
    (foldAt (K := K73cubic) (9 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit
          ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩)
        33 1) ≠ 0 := by
  let env := canonicalGatheredEnv honestSampled honestMemoryNodes basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit
    ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩
  let bad := mutateExtensionTrace env 33 1
  have hs := forestSeed_fold_bucket_other_unchanged env
  have h9 : (extensionFoldSources (K := K73cubic).get ⟨9, by decide⟩).eval bad = 0 := by
    calc
      _ = (extensionFoldSources (K := K73cubic).get ⟨9, by decide⟩).eval env := by simpa [bad] using hs
      _ = 0 := honest_extension_source_zero ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩ ⟨9, by decide⟩
        (by decide) (by decide)
  have h30 : (extensionFoldSources (K := K73cubic).get ⟨30, by decide⟩).eval bad ≠ 0 := by
    rw [malformed_named_source_indices.2.2.1]
    exact honest_wrong_forest_count_and_seed_named_gate_rejection.2
  rw [foldAt9_eval bad]
  have hchal : foldChallenge.eval bad = honestFoldChallenge := by
    change foldChallenge.eval env = honestFoldChallenge
    exact honest_fold_challenge_eq ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩
  rw [hchal, h9, zero_add]
  exact mul_ne_zero honestFoldChallenge_ne_zero h30

set_option maxHeartbeats 2000000 in
theorem honest_wrong_denominator_foldAt13 :
    (foldAt (K := K73cubic) (13 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
        38 1) ≠ 0 := by
  let env := canonicalGatheredEnv honestSampled honestMemoryNodes basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex
  let bad := mutateExtensionTrace env 38 1
  have hs := denominator_fold_bucket_other_unchanged env
  have h13 : (extensionFoldSources (K := K73cubic).get ⟨13, by decide⟩).eval bad = 0 := by
    calc
      _ = (extensionFoldSources (K := K73cubic).get ⟨13, by decide⟩).eval env := by simpa [bad] using hs
      _ = 0 := honest_extension_source_zero honestReadMemoryIndex ⟨13, by decide⟩
        (by decide) (by decide)
  have h34 : (extensionFoldSources (K := K73cubic).get ⟨34, by decide⟩).eval bad ≠ 0 := by
    rw [malformed_named_source_indices.2.2.2.1]
    exact honest_wrong_denominator_and_multiplicity_named_gate_rejection.1
  rw [foldAt13_eval bad]
  have hchal : foldChallenge.eval bad = honestFoldChallenge := by
    change foldChallenge.eval env = honestFoldChallenge
    exact honest_fold_challenge_eq honestReadMemoryIndex
  rw [hchal, h13, zero_add]
  exact mul_ne_zero honestFoldChallenge_ne_zero h34

set_option maxHeartbeats 2000000 in
theorem honest_wrong_multiplicity_foldAt14 :
    (foldAt (K := K73cubic) (14 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
        39 1) ≠ 0 := by
  let env := canonicalGatheredEnv honestSampled honestMemoryNodes basis73
    honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex
  let bad := mutateExtensionTrace env 39 1
  have hs := multiplicity_fold_bucket_other_unchanged env
  have h14 : (extensionFoldSources (K := K73cubic).get ⟨14, by decide⟩).eval bad = 0 := by
    calc
      _ = (extensionFoldSources (K := K73cubic).get ⟨14, by decide⟩).eval env := by simpa [bad] using hs
      _ = 0 := honest_extension_source_zero honestReadMemoryIndex ⟨14, by decide⟩
        (by decide) (by decide)
  have h35 : (extensionFoldSources (K := K73cubic).get ⟨35, by decide⟩).eval bad ≠ 0 := by
    rw [malformed_named_source_indices.2.2.2.2]
    exact honest_wrong_denominator_and_multiplicity_named_gate_rejection.2
  rw [foldAt14_eval bad]
  have hchal : foldChallenge.eval bad = honestFoldChallenge := by
    change foldChallenge.eval env = honestFoldChallenge
    exact honest_fold_challenge_eq honestReadMemoryIndex
  rw [hchal, h14, zero_add]
  exact mul_ne_zero honestFoldChallenge_ne_zero h35

theorem semantic_mutation_has_nonzero_coordinate
    (actual wrong : K73cubic) (hbad : wrong ≠ actual) :
    ∃ k : Fin 3, coord basis73 (wrong - actual) k ≠ 0 := by
  by_contra h
  have hzero : ∀ k : Fin 3, coord basis73 (wrong - actual) k = 0 := by
    intro k
    by_contra hk
    exact h ⟨k, hk⟩
  apply hbad
  have hz : wrong - actual = 0 := by
    rw [← reconstruct_coord basis73 (wrong - actual)]
    simp [reconstruct, hzero]
  exact sub_eq_zero.mp hz

/-- Wrong carried axis values are detected by at least one compiled coordinate equality. -/
theorem honest_wrong_axis_control
    (actual wrongAxis : K73cubic) (hbad : wrongAxis ≠ actual) :
    ∃ k : Fin 3, coord basis73 (wrongAxis - actual) k ≠ 0 :=
  semantic_mutation_has_nonzero_coordinate actual wrongAxis hbad

/-- Wrong unique timestamps are detected by at least one compiled coordinate equality. -/
theorem honest_wrong_timestamp_control
    (actual wrongTimestamp : K73cubic) (hbad : wrongTimestamp ≠ actual) :
    ∃ k : Fin 3, coord basis73 (wrongTimestamp - actual) k ≠ 0 :=
  semantic_mutation_has_nonzero_coordinate actual wrongTimestamp hbad

/-- Wrong per-root intermediate values are detected by at least one compiled coordinate equality. -/
theorem honest_wrong_intermediate_control
    (actual wrongIntermediate : K73cubic) (hbad : wrongIntermediate ≠ actual) :
    ∃ k : Fin 3, coord basis73 (wrongIntermediate - actual) k ≠ 0 :=
  semantic_mutation_has_nonzero_coordinate actual wrongIntermediate hbad

/-- A wrong aggregate `Corr:forest` seed differs in at least one endpoint coordinate. -/
theorem honest_wrong_forest_seed_control
    (wrongSeed : K73cubic)
    (hbad : wrongSeed ≠ honestLegacyFamily.memoryWalkSeed) :
    ∃ k : Fin 3,
      coord basis73 (wrongSeed - honestLegacyFamily.memoryWalkSeed) k ≠ 0 :=
  semantic_mutation_has_nonzero_coordinate honestLegacyFamily.memoryWalkSeed wrongSeed hbad

theorem denominator_mutation_rejected
    {d wrong inv : K73cubic} (hpin : d * inv = 1) (hbad : wrong ≠ d) :
    wrong * inv - 1 ≠ 0 := by
  intro hwrong
  have hwrongPin : wrong * inv = 1 := sub_eq_zero.mp hwrong
  have hinv : inv ≠ 0 := by
    intro hz
    simp [hz] at hpin
  apply hbad
  apply mul_right_cancel₀ hinv
  rw [hwrongPin, hpin]

/-- Altering an active concrete response denominator while retaining its committed inverse fails
the sampled inverse gate. -/
theorem honest_wrong_denominator_control
    (i : Fin honestLegacyFamily.problem.cfg.memRows)
    (hactive : responseActive (K := K73cubic)
      (honestLegacyFamily.problem.exec.memoryPubAt i).ver = 1)
    (wrong : K73cubic) (hbad : wrong ≠ responseDenominator honestSampled i) :
    wrong * (safeResponseDenominator honestSampled i)⁻¹ - 1 ≠ 0 := by
  have hsafe := honestMemoryDenominatorsSafe i hactive
  have hsafeEq : safeResponseDenominator honestSampled i =
      responseDenominator honestSampled i := by
    simp [safeResponseDenominator, hactive]
  apply denominator_mutation_rejected
  · rw [hsafeEq]
    exact mul_inv_cancel₀ hsafe
  · exact hbad

theorem honest_multiplicity_eq_one (j : Fin honestSampled.sampled.records.responses.length) :
    honestSampled.sampled.witness.multiplicity j = 1 := by
  have hbool := honestSampled.sampled.accepts.multBool j
  have hpin := honestSampled.sampled.accepts.multInvPin j
  rcases mul_eq_zero.mp hbool with hz | hone
  · rw [hz, zero_mul] at hpin
    exact False.elim (zero_ne_one hpin)
  · exact sub_eq_zero.mp hone

/-- The malformed multiplicity `2` fails the concrete Boolean gate in characteristic `73`. -/
theorem honest_wrong_multiplicity_control :
    (2 : K73cubic) * (2 - 1) ≠ 0 := by
  have htwoBase : (2 : F73) ≠ 0 := by decide
  have htwo : (2 : K73cubic) ≠ 0 := by
    intro hk
    have hmap :
        algebraMap F73 K73cubic (2 : F73) =
          algebraMap F73 K73cubic (0 : F73) := by
      simpa only [map_ofNat, map_zero] using hk
    exact htwoBase ((algebraMap F73 K73cubic).injective hmap)
  simpa only [show (2 : K73cubic) - 1 = 1 by ring, mul_one] using htwo

/-- Any changed sampled terminal fails its endpoint equality. -/
theorem honest_wrong_terminal_control
    (wrong : K73cubic) (hbad : wrong ≠ honestSampled.witness10.terminal) :
    wrong - honestSampled.witness10.terminal ≠ 0 :=
  fun hz => hbad (sub_eq_zero.mp hz)

/-- Any trace that changes a designated fixed polynomial is rejected by the concrete final
fixed-preprocessing wrapper. -/
abbrev honestFinalMemoryRAP :=
  namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
    honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestLegacyFamily.problem.cfg.kMem

theorem honest_wrong_preprocessing_control
    (Q : Fin honestFinalMemoryRAP.rap.w → F73[X])
    (j : Fin honestFinalMemoryRAP.fixedCount)
    (hbad :
      Q (honestFinalMemoryRAP.preprocessingIndex j) ≠
        honestFinalMemoryRAP.preprocessing j) :
    ¬ RAP.SatisfiesWithPreprocessing honestFinalMemoryRAP Q := by
  intro hQ
  exact hbad (hQ.2 j)

theorem honest_selector_mirror_named_gate_rejection
    (s : Fin 4) :
    MixedCoordinateCompiler.mixedCompile basis73 memoryCol0 (selectorMixed (F := F73) s) 0
        ∈ foldedEqualityChecks basis73 ∧
      (MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
        (selectorMixed (F := F73) s) 0).eval
        (mutateCurrentTrace
          (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
          (6 + 3 * (51 + (s : ℕ))) 1) = 1 :=
  canonical_selector_mirror_named_gate_rejects honestSampled honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal
    strictOrbit honestReadMemoryIndex s

/-- The two endpoint-mask controls identify the exact fixed-preprocessing slots of the final RAP. -/
theorem honest_wrong_first_mask_preprocessing_rejected
    (Q : Fin honestFinalMemoryRAP.rap.w → F73[X])
    (hbad :
      Q (honestFinalMemoryRAP.preprocessingIndex ⟨0, by change 0 < 4; norm_num⟩) ≠
        honestFinalMemoryRAP.preprocessing ⟨0, by change 0 < 4; norm_num⟩) :
    ¬ RAP.SatisfiesWithPreprocessing honestFinalMemoryRAP Q :=
  honest_wrong_preprocessing_control Q ⟨0, by change 0 < 4; norm_num⟩ hbad

theorem honest_wrong_last_mask_preprocessing_rejected
    (Q : Fin honestFinalMemoryRAP.rap.w → F73[X])
    (hbad :
      Q (honestFinalMemoryRAP.preprocessingIndex ⟨1, by change 1 < 4; norm_num⟩) ≠
        honestFinalMemoryRAP.preprocessing ⟨1, by change 1 < 4; norm_num⟩) :
    ¬ RAP.SatisfiesWithPreprocessing honestFinalMemoryRAP Q :=
  honest_wrong_preprocessing_control Q ⟨1, by change 1 < 4; norm_num⟩ hbad

inductive MalformedMemoryClass
  | axis | timestamp | intermediateCurrent | intermediateNext
  | forestSeed | forestCount | denominator | multiplicity
  | accumulator | terminal | selectorMirror (s : Fin 4)
  | firstMask | lastMask

inductive MemoryProductionGateId
  | base (i : Fin 14)
  | extensionFold (i : Fin 21)
  | equality (i : Fin 4)
  | preprocessing (i : Fin 2)

def malformedMemoryGateId : MalformedMemoryClass → MemoryProductionGateId
  | .axis => .extensionFold 17
  | .timestamp => .extensionFold 0
  | .intermediateCurrent | .intermediateNext => .base 13
  | .forestSeed => .extensionFold 9
  | .forestCount => .extensionFold 8
  | .denominator => .extensionFold 13
  | .multiplicity => .extensionFold 14
  | .accumulator => .base 10
  | .terminal => .base 7
  | .selectorMirror s => .equality s
  | .firstMask => .preprocessing 0
  | .lastMask => .preprocessing 1

def DirectMalformedProductionReceipt : MalformedMemoryClass → Prop
  | .axis => (foldAt (K := K73cubic) (17 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestVerifyMemoryIndex) 26 1) ≠ 0
  | .timestamp => (foldAt (K := K73cubic) (0 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 26 1) ≠ 0
  | .intermediateCurrent =>
      (MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
        (chainMixed (F := F73)) 0).eval
        (mutateCurrentTrace
          (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 90 1) = 1
  | .intermediateNext =>
      (MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
        (chainMixed (F := F73)) 0).eval
        (mutateNextTrace
          (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 87 1) = -1
  | .forestSeed => (foldAt (K := K73cubic) (9 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit
          ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩) 33 1) ≠ 0
  | .forestCount => (foldAt (K := K73cubic) (8 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit
          ⟨0, honestLegacyFamily.problem.cfg.memRows_pos⟩) 32 1) ≠ 0
  | .denominator => (foldAt (K := K73cubic) (13 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 38 1) ≠ 0
  | .multiplicity => (foldAt (K := K73cubic) (14 : Fin 21)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 39 1) ≠ 0
  | .accumulator =>
      ((foldedBaseTransitionGates basis73).get ⟨8, by
        simp [foldedBaseTransitionGates_length]⟩).eval
        (mutateCurrentTrace
          (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 138 1) = 1
  | .terminal =>
      ((foldedBaseTransitionGates basis73).get ⟨5, by
        simp [foldedBaseTransitionGates_length]⟩).eval
        (mutateCurrentTrace
          (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) 126 1) = 1
  | .selectorMirror s =>
      MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
          (selectorMixed (F := F73) s) 0 ∈ foldedEqualityChecks basis73 ∧
        (MixedCoordinateCompiler.mixedCompile basis73 memoryCol0
          (selectorMixed (F := F73) s) 0).eval
          (mutateCurrentTrace
            (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
              honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
            (6 + 3 * (51 + (s : ℕ))) 1) = 1
  | .firstMask => ∀ Q : Fin honestFinalMemoryRAP.rap.w → F73[X],
      Q (honestFinalMemoryRAP.preprocessingIndex ⟨0, by change 0 < 4; norm_num⟩) ≠
        honestFinalMemoryRAP.preprocessing ⟨0, by change 0 < 4; norm_num⟩ →
      ¬ RAP.SatisfiesWithPreprocessing honestFinalMemoryRAP Q
  | .lastMask => ∀ Q : Fin honestFinalMemoryRAP.rap.w → F73[X],
      Q (honestFinalMemoryRAP.preprocessingIndex ⟨1, by change 1 < 4; norm_num⟩) ≠
        honestFinalMemoryRAP.preprocessing ⟨1, by change 1 < 4; norm_num⟩ →
      ¬ RAP.SatisfiesWithPreprocessing honestFinalMemoryRAP Q

theorem honest_direct_malformed_production_census
    (c : MalformedMemoryClass) : DirectMalformedProductionReceipt c := by
  cases c with
  | axis => exact honest_wrong_axis_foldAt17
  | timestamp => exact honest_wrong_timestamp_foldAt0
  | intermediateCurrent => exact honest_wrong_intermediate_current_mixed_gate
  | intermediateNext => exact honest_wrong_intermediate_next_mixed_gate
  | forestSeed => exact honest_wrong_forest_seed_foldAt9
  | forestCount => exact honest_wrong_forest_count_foldAt8
  | denominator => exact honest_wrong_denominator_foldAt13
  | multiplicity => exact honest_wrong_multiplicity_foldAt14
  | accumulator => exact honest_wrong_accumulator_gate
  | terminal => exact honest_wrong_terminal_gate
  | selectorMirror s => exact honest_selector_mirror_named_gate_rejection s
  | firstMask => exact fun Q => honest_wrong_first_mask_preprocessing_rejected Q
  | lastMask => exact fun Q => honest_wrong_last_mask_preprocessing_rejected Q

end
end Concrete
end OptimizedMemoryCanonicalSatisfaction
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete.honest_source_memory_satisfies
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete.honest_final_memory_satisfies
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete.honest_memory_realization
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete.honest_wrong_first_extension_mask_mixed_gate
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete.honest_wrong_intermediate_current_mixed_gate
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete.honest_selector_mirror_named_gate_rejection
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete.honest_direct_malformed_production_census
