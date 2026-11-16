/-
  Nock/NockVMROM/Thm54/TraceGen/GenSoundnessNumber.lean

  **An effective soundness error at a generated package: one number, written out.**

  `ProductionP8Containment.jointProbability_falseAcceptance_le` (`:921`) bounds the
  false-acceptance probability by `workload T Λ topologyBound axisWorkload / |K|`, and
  `OptimizedFullStrictNockVMROMPackage.p8_fixedField_falseAcceptance_le`
  (`OptimizedStrictFullPackage.lean:168`) instantiates it at the two canonical majorants
  `fixedTopologyWorkload` / `fixedAxisWorkload` with **every** containment premise discharged from
  package fields.  What was missing was the *number*: both majorants are suprema over challenges,
  so the numerator was not a function of trace data.

  * `GenWorkloadBounds.fixedTopologyWorkload_eq` — the topology majorant collapses to the exact
    `24 * compRows + 8 * memRows`, with no premise;
  * `GenExponentLineNumbers.generated_committedExponentWindow` /
    `generated_workload_le_explicit` — on the generated path the axis majorant is at most
    `memoryForest.length * L`, `L = totalRecordCount (bfsStamps (bfsAssign (airReorder t)))`, with
    `CommittedExponentWindow` **proved** rather than assumed.

  This module composes the three into a single inequality whose numerator contains nothing but
  compute-row count, memory-row count, committed memory-root count, `Λ` and `L`:

      |jointProbability (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lam)|
        ≤ (1 + (3 + 19 * C) * (2 * Λ - 1) + (24 * C + 8 * M) + R * L + Λ * (Λ + 1) / 2) / |K|

  with `C`/`M` the committed skeleton's compute/memory row counts, `R` its memory-root count.
  `Λ * (Λ + 1) / 2` is exact, not rounded: `sizeWindowRootBound_mul_two` says the numerator is
  even.

  ## Scope — read before quoting any of this

  * **§A is `∀ P : OptimizedFullStrictNockVMROMPackage F K hOrb`.**  It is pure numerator
    monotonicity over `p8_fixedField_falseAcceptance_le`, which takes no hypothesis beyond the
    package's own fields.  Here that premise is not assumed on a hostile
    strategy — it is the constructed package's `recordEquations` / `optimized.slotSemantics`
    fields, consumed once inside `OptimizedFullStrictNockVMROMPackage.containment`
    (`OptimizedStrictFullPackage.lean:149`).  Nothing below is a claim about an arbitrary
    `ProductionStrategy`.
  * **§B is the generated scope**, carried by the visible hypothesis
    `hnodes : D.memoryNodes = genMemoryNodes z α inp t`.  As
    `GenExponentLineNumbers.lean` §E records, `ForestExponentWindow.wrapDataExponents` *fails*
    that hypothesis, so the axis half of the numerator is false for a general commitment and is
    not being claimed for one.
  * **§C is §B at `Nock.Field.K`**, denominator `p^3`, `p = 2^64 - 2^32 + 1`; the only section that
    depends on the blessed `Nock.Field.goldilocks_prime` axiom.  `p ^ 3` is kept symbolic.
  * **§D instantiates `hnodes`** at `GenNockCompiles.genDataOfProgram`, i.e. over the program: the
    commitment there *is* the generator's served forest by definition of `genData`'s field
    (`GenHonestData.lean:389`), so the hypothesis is `rfl` and the numerator becomes a function of
    the program's own trace.  Field-generic: no `p = 769`, no fixture.

  ## Comparison with the paper's own accounting

  `1204` sets `ε_col := ε(Λ, 𝕂)`, requires `Λ, k ∈ negl(|𝕂|)`, instantiates
  `|𝕂| ≈ 2^192, Λ = 2^7, k = 2^32` and gives the security level as
  `log₂|𝕂| - 2 log₂ k - log₂ Λ - 1`, i.e. a numerator `k² · Λ` against `|𝕂|`.  Our numerator is
  **linear** in the row counts and in `L`, plus the `Λ(Λ+1)/2` size-window term — so it is
  `O(k · Λ + Λ²)` in the paper's variables where the paper carries `k² · Λ`, with `k` the row
  count.  The shapes therefore differ; ours is not a transcription of `1204`'s product and must
  not be quoted as one.  the paper states only the negligibility *condition* on `N, L` with
  no numerator at all, so it cannot be cited for a formula either.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenExponentLineNumbers
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompiles
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.Framework.Thm54

noncomputable section

/-! ## §0. The size-window term in closed form

`GenWorkloadBounds.sizeWindowRootBound_mul_two` says `sizeWindowRootBound Λ * 2 = Λ * (Λ + 1)`, so
the Gauss form below is exact and the `ℕ` division is not a rounding. -/

theorem sizeWindowRootBound_eq_gauss (n : ℕ) :
    n * (n + 1) / 2 = sizeWindowRootBound n :=
  Nat.div_eq_of_eq_mul_left (by norm_num) (sizeWindowRootBound_mul_two n).symm

/-! ## §A. Numerator monotonicity at a released package

`∀ P`.  `p8_fixedField_falseAcceptance_le` is used as-is; nothing here touches
`production_jointProbability_falseAcceptance_le` or its `hop`. -/

section AnyPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
variable {hOrb : ℕ}

/-- **Any upper bound on the canonical five-class workload is a soundness error.**  Pure
monotonicity of `· / |K|`; the containment, census and size-window inputs are the package's own
fields. -/
theorem falseAcceptance_le_of_workload_le
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) (N : ℕ) (lam : K)
    (hle : workload P.strategy P.optimized.Λ
        (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) ≤ N) :
    |jointProbability (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lam)| ≤
      (N : ℝ) / (Fintype.card K : ℝ) := by
  refine (P.p8_fixedField_falseAcceptance_le lam).trans ?_
  have hcard : (0 : ℝ) < (Fintype.card K : ℝ) := by
    have h : 0 < Fintype.card K := Fintype.card_pos
    exact_mod_cast h
  have hN : ((workload P.strategy P.optimized.Λ
      (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) : ℕ) : ℝ) ≤ (N : ℝ) :=
    Nat.cast_le.mpr hle
  rw [div_le_div_iff₀ hcard hcard]
  exact mul_le_mul_of_nonneg_right hN hcard.le

end AnyPackage

/-! ## §B. The generated package, numerator fully explicit

**Generated scope**: `hnodes` is `genData`'s own field definition and is *refuted* by
`wrapDataExponents`, so this is a statement about the generator's commitments and about no others.
-/

section GeneratedPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {lmb : K}
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
variable {E : BuildableNockExecution F K}

/-- **The soundness error at a generated package, with the numerator written out.**

Nothing on the right is a majorant, a supremum or a named residual: `C` and `M` are the committed
skeleton's compute/memory row counts, `R` its memory-root count, `Λ` the package's leaf window and
`L = totalRecordCount (bfsStamps (bfsAssign (airReorder t)))` the trace's own memory-record count.

Scope: generated.  `hnodes` is the hypothesis that makes the axis half true. -/
theorem generated_falseAcceptance_le_explicit
    (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (z α : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    (hnodes : D.memoryNodes = genMemoryNodes z α lmb inp t) (lam : K) :
    |jointProbability (FalseAcceptanceSet
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).q
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ lam)| ≤
      ((1 +
        (3 + 19 * (SemanticStrategy.computeSkeletonRows
            (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length) *
          (2 * (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length) +
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton.memoryForest.length *
          totalRecordCount (bfsStamps (bfsAssign (airReorder t))) +
        ProductionP8Containment.formRUniformWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy +
        ProductionP8Containment.reqPairWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ +
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ *
          ((GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ + 1) / 2 : ℕ) : ℝ) /
        (Fintype.card K : ℝ) := by
  refine falseAcceptance_le_of_workload_le _ _ lam ?_
  rw [sizeWindowRootBound_eq_gauss]
  exact generated_workload_le_explicit D hgt I hprl hmore hord hordM hrows hgenF hF z α inp t hnodes
    (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ

end GeneratedPackage

/-! ## §C. The same at the Goldilocks carrier, denominator `p^3`

⚠ This section mentions `Nock.Field.K` and therefore depends on the blessed
`Nock.Field.goldilocks_prime` axiom.  `p ^ 3` is symbolic throughout: no `decide`, no numeral
evaluation. -/

section GoldilocksPackage

variable {F : Type} [Field F] [Algebra F GK]
variable {lmb : GK}

/-- As in `GenWorkloadBounds` / `GenFailureUnionCounting`: Mathlib's `ringChar.charP` is low
priority, so the instance the package binder demands is installed locally.  `CharP` is a `Prop`;
this adds no assumption. -/
local instance genSoundnessNumberRingCharP : CharP GK (ringChar GK) := ringChar.charP _

/-- **The Goldilocks soundness error at a generated package.**  Denominator `p^3`,
`p = 2^64 - 2^32 + 1`, numerator as in §B.  Generated scope. -/
theorem generated_goldilocks_falseAcceptance_le_explicit
    [FiniteDimensional F GK] {E : BuildableNockExecution F GK}
    (D : Data E) (hgt : 11 < ringChar GK) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar GK ∧ E.cfg.memRows < ringChar GK)
    (hgenF : GeneratedField.ClaimGenerated GK D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (z α : GK) (inp : MemoryTable.Inputs GK) (t : NTree (GenComputeRow GK))
    (hnodes : D.memoryNodes = genMemoryNodes z α lmb inp t) (lam : GK) :
    |jointProbability (FalseAcceptanceSet
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).q
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ lam)| ≤
      ((1 +
        (3 + 19 * (SemanticStrategy.computeSkeletonRows
            (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length) *
          (2 * (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length) +
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton.memoryForest.length *
          totalRecordCount (bfsStamps (bfsAssign (airReorder t))) +
        ProductionP8Containment.formRUniformWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy +
        ProductionP8Containment.reqPairWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ +
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ *
          ((GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ + 1) / 2 : ℕ) : ℝ) /
        ((Nock.Field.p ^ 3 : ℕ) : ℝ) := by
  have h := generated_falseAcceptance_le_explicit D hgt I hprl hmore hord hordM hrows hgenF hF z α inp t hnodes lam
  rwa [Nock.Field.card_K] at h

end GoldilocksPackage

/-! ## §D. `hnodes` instantiated: over the program

`GenExponentLineNumbers.lean` §E carries `hmem : D.memoryNodes = genMemoryNodes z α inp t` and
nothing there instantiates it.  It is `genData`'s own field definition (`GenHonestData.lean:389`),
so at `GenNockCompiles.genDataOfProgram` — `genData` at the arguments `genBuildableOfProgram`
builds — it is `rfl`.  Both theorems below are field-generic: `K` is free, there is no fixture and
no `decide`. -/

section OverTheProgram

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable {lmb : K}
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **The generated-scope hypothesis, discharged over the program.**  `genDataOfProgram`'s
committed memory-node forest *is* the generator's served forest for the compute tree `t` at the
memory inputs `memInputs z`. -/
theorem genDataOfProgram_memoryNodes {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmemlen : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmemlen).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).memoryNodes =
      genMemoryNodes z α chal.lam (memInputs z) t :=
  rfl

/-- **The soundness error over the program.**  §B at `genDataOfProgram`, with the generated-scope
hypothesis discharged by `rfl` rather than carried.  `L` is the program's own record count. -/
theorem program_falseAcceptance_le_explicit {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmemlen : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmemlen).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hgt : 11 < ringChar K)
    (I : Inputs (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
      hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hprl : RowLayout.PairedRecordLayout
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) := by later_seed_zeros)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf I.computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf I.memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (lam : K) :
    |jointProbability (FalseAcceptanceSet
        (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
          hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          hgt I hprl hmore hord hordM hrows).strategy
        (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
          hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          hgt I hprl hmore hord hordM hrows).q
        (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
          hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          hgt I hprl hmore hord hordM hrows).optimized.Λ lam)| ≤
      ((1 +
        (3 + 19 * (SemanticStrategy.computeSkeletonRows
            (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz
              htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
              hmemlen B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
              hgt I hprl hmore hord hordM hrows).strategy.skeleton).length) *
          (2 * (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz
              htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
              hmemlen B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
              hgt I hprl hmore hord hordM hrows).optimized.Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows
              (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz
                htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
                hmemlen B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
                hmemCap hfirst) hgt I hprl hmore hord hordM hrows).strategy.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows
              (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz
                htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
                hmemlen B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
                hmemCap hfirst) hgt I hprl hmore hord hordM hrows).strategy.skeleton).length) +
        (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
            a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
            hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            hgt I hprl hmore hord hordM hrows).strategy.skeleton.memoryForest.length *
          totalRecordCount (bfsStamps (bfsAssign (airReorder t))) +
        ProductionP8Containment.formRUniformWorkload
          (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
            a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
            hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            hgt I hprl hmore hord hordM hrows).strategy +
        ProductionP8Containment.reqPairWorkload
          (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
            a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
            hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            hgt I hprl hmore hord hordM hrows).strategy
          (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
            a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
            hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            hgt I hprl hmore hord hordM hrows).optimized.Λ +
        (GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
            a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
            hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            hgt I hprl hmore hord hordM hrows).optimized.Λ *
          ((GenericHonestPackage.packageOf (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
              a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB
              hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
              hgt I hprl hmore hord hordM hrows).optimized.Λ + 1) / 2 : ℕ) : ℝ) /
        (Fintype.card K : ℝ) :=
  generated_falseAcceptance_le_explicit _ hgt I hprl hmore hord hordM hrows (genDataOfProgram_claimGeneratedD hG) hF z α (memInputs z) t
    (genDataOfProgram_memoryNodes (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmemlen B hB hwin hKsz hKsz2 hb hq
      hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) lam

end OverTheProgram

end

end Nock.NockVMROM.Thm54.TraceGen

/-! ## Axiom receipts

§0/§A/§B/§D are axiom-clean beyond the Lean/Mathlib triple; only §C pulls the blessed
`Nock.Field.goldilocks_prime`. -/

-- [propext, Classical.choice, Quot.sound]
#print axioms Nock.NockVMROM.Thm54.TraceGen.sizeWindowRootBound_eq_gauss
#print axioms Nock.NockVMROM.Thm54.TraceGen.falseAcceptance_le_of_workload_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_falseAcceptance_le_explicit
#print axioms Nock.NockVMROM.Thm54.TraceGen.genDataOfProgram_memoryNodes
#print axioms Nock.NockVMROM.Thm54.TraceGen.program_falseAcceptance_le_explicit
-- [propext, Classical.choice, Quot.sound, Nock.Field.goldilocks_prime]
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_goldilocks_falseAcceptance_le_explicit
