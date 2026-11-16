/-
  Nock/NockVMROM/Thm54/RealProgramAxisWorkload.lean

  **Discharging the axis workload of `RealProgramSoundness`.**

  `RealProgramSoundness.soundness_for_execution` (`RealProgramSoundness.lean:672`) carries three
  inputs.  Two are settled: `hΛ` is the paper's leaf window, a *membership*
  condition of `NockProgram^Λ` and deliberately not derivable; `hp8` is discharged for any caller
  by `workload_le_p8Majorant` (`:236`).  The third, `hA : A ≤ 2^32`, was "the single input neither
  derived nor visibly forced".  This module closes it.

  ## What `A` actually is, and why `2^32` was the wrong shape

  `A` majorizes `ProductionP8Containment.fixedAxisWorkload` (`ProductionP8Containment.lean:579`),
  the supremum over nonzero seeds of `TemplateAxisCounting.templateAxisWorkload`
  (`TemplateAxisCounting.lean:387`) `= ∑_{i < kMem} (countsP (templateAxisTree …)).natDegree`.
  That is **one polynomial per memory root**, each of degree at most the largest timestamp
  exponent in that root's tree.  So its honest majorant is a
  **product** `kMem · B`, not a row count — and at the deployable maximum both factors are `2^32`,
  so `A ≤ 2^32` was never satisfiable at scale.

  `RealProgramSoundness` §5.1 fixes the shape: `A` enters the numerator linearly and once, and the
  coefficient budget is `511` (`sizeWorkQuad_not_lt_cardK_at_512`) against §4's `291`, so raising
  the allowance to `A ≤ 4·S²` costs `291 → 295` and **no bits**.  `b = 183 − 2r` is unchanged.

  ## The two factors

  * **`kMem`** — `RealProgramSoundness.kMem_le_memRows` (`:192`) derives `kMem ≤ memRows` for
    *every* execution: `memRows` is `(bfsForest memoryForest).length = totalSize memoryForest`
    and each root contributes at least itself.  §1 gives the same at the skeleton layer.
  * **`B`** — the largest committed timestamp exponent.  the paper: "this timestamp is
    unique and represents the line number of the compute table at which the memory record was
    requested".  `ExponentPinned.committedExponentWindow_of_lineNumbers`
    (`GenExponentPinned.lean:545`) derives `B = skeletonRecordCount T.skeleton`, the paper's `L`,
    from that identification (`LineNumberCommitment`, `:532`), and
    `TraceGen.generated_committedExponentWindow` (`GenExponentLineNumbers.lean:434`) discharges the
    identification outright on the generated path.  §1 then bounds `L ≤ 3 · compRows` from opcode
    arity (`Nock.Framework.recordCount ≤ 3`, `NockInstances.lean:61`), the same arity fact
    `RealProgramSoundness` §1 uses for the record count.

  So `A ≤ memRows · 3 · compRows ≤ 3 · 2^32 · 2^32 < 4 · 2^32 · 2^32`, and `hA` is gone.

  ## What remains carried

  `LineNumberCommitment` — and it is *not* a rename of a bound.  `ForestExponentWindow` §B
  (`forestExponentOrder_iff_intermediateExponentWindow`, `ForestExponentWindow.lean:249`) shows a Nat *bound* on the
  committed forest exponents is `ForestExponentOrder` under another name;
  `ExponentPinned.bound_does_not_imply_memoryLineNumbers`
  (`GenExponentPinned.lean:335`) shows the line-number *identification* is
  strictly stronger and is not implied by a bound.  It is the paper's own sentence at
  the paper, and on the generated path §5 discharges it.
-/
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.TraceGen.GenExponentPinned
import Nock.NockVMROM.Thm54.TraceGen.GenExponentLineNumbers

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54
namespace RealProgramAxisWorkload

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ExponentPinned
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.RealProgramSoundness

noncomputable section

/-! ## 1. Both factors of the axis product are row counts

`L ≤ 3 · |compute rows|` is opcode arity, the same fact `RealProgramSoundness` §1 uses for the
record count.  `kMem ≤ |memory rows|` is the BFS
flattening. -/

/-- **The paper's `L` is at most three times the compute-row count.**  `recordCount ≤ 3`. -/
theorem skeletonRecordCount_le_three_mul (base : SemanticStrategy.SemanticSkeleton) :
    skeletonRecordCount base ≤ 3 * (SemanticStrategy.computeSkeletonRows base).length := by
  simp only [skeletonRecordCount]
  induction (SemanticStrategy.computeSkeletonRows base) with
  | nil => simp
  | cons r t ih =>
      have hr : Nock.Framework.recordCount r.state ≤ 3 := by
        have := Nock.Framework.recordCount_le r.state
        simpa [Nock.NockVM.mem_record_arity] using this
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- The same for a committed compute-row list: `L ≤ 3 · |rows|`. -/
theorem totalRecordCount_le_three_mul (rows : List ComputeTimestampRow) :
    ForestExponentWindow.totalRecordCount rows ≤ 3 * rows.length := by
  induction rows with
  | nil => simp [ForestExponentWindow.totalRecordCount]
  | cons r t ih =>
      have hr : Nock.Framework.recordCount r.state ≤ 3 := by
        have := Nock.Framework.recordCount_le r.state
        simpa [Nock.NockVM.mem_record_arity] using this
      rw [ForestExponentWindow.totalRecordCount_cons, List.length_cons]
      omega

/-- **The memory-root count is a memory-row count.**  `memorySkeletonRows`
(`SemanticStrategy.lean:124`) is the BFS flattening of the forest, and every root contributes at
least itself (`Walk.totalSize_flatMap_children`, `Walk.lean:719`).  The execution-level
counterpart is `RealProgramSoundness.kMem_le_memRows`. -/
theorem memoryForest_length_le_memorySkeletonRows (base : SemanticStrategy.SemanticSkeleton) :
    base.memoryForest.length ≤ (SemanticStrategy.memorySkeletonRows base).length := by
  have h := Nock.Walk.totalSize_flatMap_children base.memoryForest
  simp only [SemanticStrategy.memorySkeletonRows, List.length_map,
    Nock.Walk.bfsForest_length]
  omega

/-! ## 2. The axis workload as a product of two row counts

`ExponentPinned.fixedAxisWorkload_le_skeletonRecordCount` (`GenExponentPinned.lean:565`) gives
`fixedAxisWorkload T ≤ |memoryForest| · L` under the line-number commitment.  §1 turns both
factors into skeleton row counts. -/

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **The axis majorant, from any exponent window.**  `GenWorkloadBounds.fixedAxisWorkload_le`
(`:350`) gives `kMem · B`; §1 turns `kMem` into a memory-row count.  Both consumers below go
through this: the line-number commitment supplies `B = L`, the generator supplies `B` outright. -/
theorem fixedAxisWorkload_le_memoryRows_mul
    (T : ProductionStrategy F K) (hb : T.BindsAll) (B : ℕ) (hw : CommittedExponentWindow T B) :
    fixedAxisWorkload T ≤ (SemanticStrategy.memorySkeletonRows T.skeleton).length * B :=
  le_trans (fixedAxisWorkload_le T hb B hw)
    (Nat.mul_le_mul_right B (memoryForest_length_le_memorySkeletonRows T.skeleton))

/-- **The axis majorant is at most `3 · M · R` under the line-number commitment.**  Every symbol
on the right is a skeleton row count: `M` memory rows, `R` compute rows.  This is the honest
quadratic shape of the axis workload — `kMem` polynomials of degree at most the largest line
number. -/
theorem fixedAxisWorkload_le_rows
    (T : ProductionStrategy F K) (hb : T.BindsAll) (C : LineNumberCommitment T) :
    fixedAxisWorkload T ≤
      3 * ((SemanticStrategy.memorySkeletonRows T.skeleton).length *
        (SemanticStrategy.computeSkeletonRows T.skeleton).length) := by
  refine le_trans
    (fixedAxisWorkload_le_memoryRows_mul T hb _ (committedExponentWindow_of_lineNumbers T C)) ?_
  have h2 := skeletonRecordCount_le_three_mul T.skeleton
  calc (SemanticStrategy.memorySkeletonRows T.skeleton).length * skeletonRecordCount T.skeleton
      ≤ (SemanticStrategy.memorySkeletonRows T.skeleton).length *
          (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) :=
        Nat.mul_le_mul_left _ h2
    _ = 3 * ((SemanticStrategy.memorySkeletonRows T.skeleton).length *
          (SemanticStrategy.computeSkeletonRows T.skeleton).length) := by ring

end Generic

/-! ## 3. At Goldilocks both row counts are capped by the orbit

`GoldilocksParameters.orbit_height_le` (`GoldilocksParameters.lean:203`) proves `v₂(p³ − 1) = 32`,
so `ExactConfig.compRows_le`/`memRows_le` (`Config.lean:112,114`) cap both counts at `2^32`.
`GenWorkloadBounds.specializedCfg_compRows`/`memRows` (`:258,266`) identify the specialized config's
counts with the skeleton's, at *every* challenge — so the cap is a cap on skeleton data. -/

section Goldilocks

open Nock.NockVMROM.Thm54.GoldilocksParameters

local instance realProgramAxisRingCharP :
    CharP Nock.Field.K (ringChar Nock.Field.K) := ringChar.charP _

variable {F : Type} [Field F] [Algebra F Nock.Field.K] [FiniteDimensional F Nock.Field.K]
variable (T : ProductionStrategy F Nock.Field.K) (hb : T.BindsAll)

include hb in
/-- The skeleton's compute-row count is capped by the orbit: `≤ 2^32`, derived. -/
theorem computeSkeletonRows_length_le :
    (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ 2 ^ 32 := by
  have hone : (1 : Nock.Field.K) ≠ 0 := one_ne_zero
  have h := specializedCfg_compRows T hb (1 : Nock.Field.K) hone (0 : Nock.Field.K) (0 : Nock.Field.K)
  rw [← h]
  exact compRows_le_two_pow_32' _

include hb in
/-- The skeleton's memory-row count is capped by the orbit: `≤ 2^32`, derived. -/
theorem memorySkeletonRows_length_le :
    (SemanticStrategy.memorySkeletonRows T.skeleton).length ≤ 2 ^ 32 := by
  have hone : (1 : Nock.Field.K) ≠ 0 := one_ne_zero
  have h := specializedCfg_memRows T hb (1 : Nock.Field.K) hone (0 : Nock.Field.K) (0 : Nock.Field.K)
  rw [← h]
  exact memRows_le_two_pow_32' _

/-! ## 4. `hA`, discharged -/

include hb in
/-- **The axis workload from any exponent window bounded by `3·2^32`.**  `kMem` is a row count
(§1) and is capped by the orbit; `B` is the largest committed timestamp exponent. -/
theorem fixedAxisWorkload_le_of_window (B : ℕ) (hw : CommittedExponentWindow T B)
    (hB : B ≤ 3 * 2 ^ 32) :
    fixedAxisWorkload T ≤ 3 * (2 ^ 32 * 2 ^ 32) := by
  refine le_trans (fixedAxisWorkload_le_memoryRows_mul T hb B hw) ?_
  calc (SemanticStrategy.memorySkeletonRows T.skeleton).length * B
      ≤ 2 ^ 32 * (3 * 2 ^ 32) := Nat.mul_le_mul (memorySkeletonRows_length_le T hb) hB
    _ = 3 * (2 ^ 32 * 2 ^ 32) := by ring

include hb in
/-- **The axis workload of a real Goldilocks strategy is at most `3·2^64`.**  Nothing here is
assumed about the workload: `kMem` is a row count (§1), the exponents are line numbers, and both row counts are capped by the
orbit's `v₂(p³−1) = 32`. -/
theorem fixedAxisWorkload_le_goldilocks (C : LineNumberCommitment T) :
    fixedAxisWorkload T ≤ 3 * (2 ^ 32 * 2 ^ 32) := by
  refine le_trans (fixedAxisWorkload_le_rows T hb C) ?_
  exact Nat.mul_le_mul_left 3
    (Nat.mul_le_mul (memorySkeletonRows_length_le T hb) (computeSkeletonRows_length_le T hb))

include hb in
/-- The form `RealProgramSoundness` §5.1 consumes. -/
theorem fixedAxisWorkload_le_quadBudget (C : LineNumberCommitment T) :
    fixedAxisWorkload T ≤ 4 * (2 ^ 32 * 2 ^ 32) :=
  le_trans (fixedAxisWorkload_le_goldilocks T hb C) (by norm_num)

/-! ## 5. The headline: `soundness_for_execution` with `hA` removed -/

include hb in
/-- **The threading step.**  `p8Work` is the actual `ProductionP8Containment.workload` at the
strategy's own two majorants, the row counts are the specialized configuration's own, and the
record counts are the execution's own derived IO lists.  `workload_le_p8Majorant`
(`RealProgramSoundness.lean:236`) discharges `hp8` here rather than in the caller, and
`fixedTopologyWorkload_eq` (`GenWorkloadBounds.lean:309`) discharges the topology majorant
exactly.  The two consumers below supply `haxis`. -/
theorem soundness_for_production_of_axisBound
    (haxis : fixedAxisWorkload T ≤ 3 * (2 ^ 32 * 2 ^ 32))
    (hformR : formRUniformWorkload T ≤ 4 * (2 ^ 32 * 2 ^ 32)) (Λ : ℕ) (hΛ : Λ ≤ 2 ^ 32)
    (hpair : reqPairWorkload T Λ ≤ 2 ^ 32 * 2 ^ 32)
    (z : Nock.Field.K) (hz : z ≠ 0) (α lmb : Nock.Field.K) :
    ExtensionChallenges.goldilocksFailureBoundK
        (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T))
        (FiniteIO.ioFailureUnionBound 8
          (T.specializedExec z hz α lmb).derivedRequestIO.length
          (T.specializedExec z hz α lmb).derivedResponseIO.length
          (Fintype.card Nock.Field.K))
        (T.specializedCfg z hz α lmb).compRows (T.specializedCfg z hz α lmb).memRows
      < 1 / (2 : ℚ) ^ 119 := by
  have hc : (T.specializedCfg z hz α lmb).compRows =
      (SemanticStrategy.computeSkeletonRows T.skeleton).length :=
    specializedCfg_compRows T hb z hz α lmb
  have hm : (T.specializedCfg z hz α lmb).memRows =
      (SemanticStrategy.memorySkeletonRows T.skeleton).length :=
    specializedCfg_memRows T hb z hz α lmb
  have htop : fixedTopologyWorkload T ≤
      24 * (T.specializedCfg z hz α lmb).compRows + 8 * (T.specializedCfg z hz α lmb).memRows := by
    rw [fixedTopologyWorkload_eq T hb, hc, hm]
  have hax : fixedAxisWorkload T + formRUniformWorkload T + reqPairWorkload T Λ ≤
      8 * (2 ^ 32 * 2 ^ 32) := by
    omega
  have hp8 : workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) ≤
      p8Majorant (T.specializedCfg z hz α lmb).compRows (T.specializedCfg z hz α lmb).memRows Λ
        (8 * (2 ^ 32 * 2 ^ 32)) :=
    workload_le_p8Majorant T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T)
      (T.specializedCfg z hz α lmb).compRows (T.specializedCfg z hz α lmb).memRows
      (8 * (2 ^ 32 * 2 ^ 32)) (le_of_eq hc.symm) htop hax
  exact soundness_for_execution_octAxis (T.specializedExec z hz α lmb) Λ
    (8 * (2 ^ 32 * 2 ^ 32))
    (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T)) hΛ (by norm_num) hp8


include hb in
/-- **`soundness_for_execution` with `hA` removed.**  For a real Goldilocks production strategy
carrying the paper's line-number identification, the false-acceptance bound at
the strategy's own workload, its own row counts and its own derived IO lists is below `2^-119`.
The only carried input is the leaf window. -/
theorem soundness_for_production
    (C : LineNumberCommitment T)
    (hformR : formRUniformWorkload T ≤ 4 * (2 ^ 32 * 2 ^ 32)) (Λ : ℕ) (hΛ : Λ ≤ 2 ^ 32)
    (hpair : reqPairWorkload T Λ ≤ 2 ^ 32 * 2 ^ 32)
    (z : Nock.Field.K) (hz : z ≠ 0) (α lmb : Nock.Field.K) :
    ExtensionChallenges.goldilocksFailureBoundK
        (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T))
        (FiniteIO.ioFailureUnionBound 8
          (T.specializedExec z hz α lmb).derivedRequestIO.length
          (T.specializedExec z hz α lmb).derivedResponseIO.length
          (Fintype.card Nock.Field.K))
        (T.specializedCfg z hz α lmb).compRows (T.specializedCfg z hz α lmb).memRows
      < 1 / (2 : ℚ) ^ 119 :=
  soundness_for_production_of_axisBound T hb (fixedAxisWorkload_le_goldilocks T hb C) hformR Λ hΛ
    hpair z hz α lmb

include hb in
/-- The same from an exponent window rather than the commitment condition — the form the
generated path uses. -/
theorem soundness_for_production_of_window
    (B : ℕ) (hw : CommittedExponentWindow T B) (hB : B ≤ 3 * 2 ^ 32)
    (hformR : formRUniformWorkload T ≤ 4 * (2 ^ 32 * 2 ^ 32))
    (Λ : ℕ) (hΛ : Λ ≤ 2 ^ 32)
    (hpair : reqPairWorkload T Λ ≤ 2 ^ 32 * 2 ^ 32)
    (z : Nock.Field.K) (hz : z ≠ 0) (α lmb : Nock.Field.K) :
    ExtensionChallenges.goldilocksFailureBoundK
        (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T))
        (FiniteIO.ioFailureUnionBound 8
          (T.specializedExec z hz α lmb).derivedRequestIO.length
          (T.specializedExec z hz α lmb).derivedResponseIO.length
          (Fintype.card Nock.Field.K))
        (T.specializedCfg z hz α lmb).compRows (T.specializedCfg z hz α lmb).memRows
      < 1 / (2 : ℚ) ^ 119 :=
  soundness_for_production_of_axisBound T hb
    (fixedAxisWorkload_le_of_window T hb B hw hB) hformR Λ hΛ hpair z hz α lmb


/-! ## 6. The generated path: `LineNumberCommitment` discharged too

`TraceGen.generated_committedExponentWindow` (`GenExponentLineNumbers.lean:434`) proves the
exponent window outright for a commitment whose memory nodes *are* the generator's served forest,
with `B = L = totalRecordCount (bfsStamps (bfsAssign (airReorder t)))`.  Composing it with §4
leaves **one** arithmetic residual, and it is the generator's own compute-row count against the
orbit cap — literally `genExactConfig`'s `hcomp` field
(`TraceGen/GenExactExecution.lean:77,89`) at `orbit.h ≤ 32`.  Nothing about the axis workload,
the memory forest, or the timestamps is left. -/

theorem soundness_for_generated
    {E : BuildableNockExecution F Nock.Field.K}
    (D : HonestCommitment.Data E) (hgt : 11 < ringChar Nock.Field.K)
    (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrowsB : 3 * E.cfg.compRows < ringChar Nock.Field.K ∧
      E.cfg.memRows < ringChar Nock.Field.K)
    (hgenF : GeneratedField.ClaimGenerated Nock.Field.K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (zg αg lmbg : Nock.Field.K) (inp : MemoryTable.Inputs Nock.Field.K)
    (t : NTree (TraceGen.GenComputeRow Nock.Field.K))
    (hmem : D.memoryNodes = TraceGen.genMemoryNodes zg αg lmbg inp t)
    (hrows : (TraceGen.bfsStamps (TraceGen.bfsAssign (TraceGen.airReorder t))).length ≤ 2 ^ 32)
    (hformR : formRUniformWorkload
      (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy ≤
        4 * (2 ^ 32 * 2 ^ 32))
    (Λ : ℕ) (hΛ : Λ ≤ 2 ^ 32)
    (hpair : reqPairWorkload
      (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy Λ ≤
        2 ^ 32 * 2 ^ 32)
    (z : Nock.Field.K) (hz : z ≠ 0) (α lmb : Nock.Field.K) :
    ExtensionChallenges.goldilocksFailureBoundK
        (workload (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy Λ
          (fixedTopologyWorkload (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy)
          (fixedAxisWorkload (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy))
        (FiniteIO.ioFailureUnionBound 8
          ((GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy.specializedExec
            z hz α lmb).derivedRequestIO.length
          ((GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy.specializedExec
            z hz α lmb).derivedResponseIO.length
          (Fintype.card Nock.Field.K))
        ((GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy.specializedCfg z hz α lmb).compRows
        ((GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).strategy.specializedCfg z hz α lmb).memRows
      < 1 / (2 : ℚ) ^ 119 := by
  refine soundness_for_production_of_window _
    (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrowsB hgenF hF).optimized.strategy_bindsAll
    (ForestExponentWindow.totalRecordCount
      (TraceGen.bfsStamps (TraceGen.bfsAssign (TraceGen.airReorder t))))
    (TraceGen.generated_committedExponentWindow D hgt I hprl hmore hord hordM hrowsB hgenF hF zg αg inp t hmem) ?_
    hformR Λ hΛ hpair z hz α lmb
  exact le_trans (totalRecordCount_le_three_mul _) (Nat.mul_le_mul_left 3 hrows)

end Goldilocks

end

end RealProgramAxisWorkload
end Nock.NockVMROM.Thm54

/-! ## Axiom receipts -/

-- [propext, Classical.choice, Quot.sound]
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.skeletonRecordCount_le_three_mul
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.memoryForest_length_le_memorySkeletonRows
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.fixedAxisWorkload_le_rows
-- [propext, Classical.choice, Quot.sound, Nock.Field.goldilocks_prime]
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.computeSkeletonRows_length_le
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.memorySkeletonRows_length_le
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.fixedAxisWorkload_le_goldilocks
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.soundness_for_production
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.soundness_for_production_of_window
#print axioms Nock.NockVMROM.Thm54.RealProgramAxisWorkload.soundness_for_generated
