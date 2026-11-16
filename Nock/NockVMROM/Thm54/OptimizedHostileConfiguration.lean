import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.P8Core.OptimizedHostileConfiguration
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
The capstone's hostile IO conclusion
`OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO` takes four explicit hypotheses
no gate supplies — `hchar`, `hKp`, `hKreq`, `hKresp`.  This module discharges each from the
weakest configuration fact it follows from, and wraps the capstone as
`optimizedFullStrict_hostile_LIO_of_config`.

Paper: the paper (`[K]` range), `:557` (one response record per memory row), `:594-599`
(IO terminal), `:634` (one round, two elements), `:1097` (`Λ` window), `:1450-1495`
(Thm 5.4).
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedHostileConfiguration

open scoped Classical Polynomial
open Nock
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeCorrectedFinal
open OptimizedComputeHostileAccumulator
open OptimizedMemoryHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedHostileIOAssembly
open OptimizedStrictFullPackage
open OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
open OptimizedCanonicalHostileLists
open OptimizedComputeSemanticRealization
open OptimizedComputeFinalTrace
open ConcreteStrictPackage
open Module

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. `hchar` — characteristic, not a gate

`MD` F-2-2: `hchar ⇐ 11 < ringChar K`.  Re-proved here so production does not import
`Nock.RedTeam`.  Weaker still: `StateTagChar` (injectivity of `Nat.cast` on `{0,…,11}`,
`NodeEncoding.lean`) already implies `hchar`, and every package carries it as the field
`stateTagChar`. -/

/-- **`hchar` from `11 < ringChar K`.** -/
theorem hchar_of_lt_ringChar {K : Type} [Field K] (h : 11 < ringChar K) :
    ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1 := by
  intro n hn heq
  haveI : CharP K (ringChar K) := ringChar.charP K
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd heq (by simp)
  · have h' : ((n - 1 : ℕ) : K) = 0 := by
      rw [Nat.cast_sub hpos, Nat.cast_one, heq, sub_self]
    have hdvd := (CharP.cast_eq_zero_iff K (ringChar K) (n - 1)).mp h'
    rcases hdvd with ⟨m, hm⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · omega
    · have : ringChar K * 1 ≤ ringChar K * m := Nat.mul_le_mul_left _ hm0
      omega

/-! ## 2. Package-field derivations (no extra hypothesis) -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **`hKp` at the package's `Ksz` is `FiniteIOStrategy.charBound`.**  No extra hypothesis.
(`P.KszBound` is the same inequality for every specialisation; `sampled.sampled.charBound`
is the sampled copy.) -/
theorem hKp_of_package : P.objects.cfg.Ksz < ringChar K :=
  P.ioStrategy.charBound

/-! ## 3. Range premises from row-count majorants

`hKreq` is `IO.InRange Ksz |hostileRequests|` = `1 ≤ |req| ∧ |req| ≤ Ksz`.  The lower bound is a list fact (slot `0` is always active,
`activeMask_zero`; `compRows_pos`).  The upper bound is `hostileRequests_length_le ≤ 3N`
plus the configuration fact `3N ≤ Ksz` (`MD` F-7-2).

`hKresp` is `|hostileResponses| ≤ Ksz`.  `hostileResponses_length_le ≤ M` plus `M ≤ Ksz`.  `M ≤ Ksz` is **not** a package field — the
F73 fixture has `memRows = 5 > Ksz = 4`. -/

/-- **`hKreq` from `3 · N ≤ Ksz`.**  Lower bound from `hostileRequests_length_pos`; upper
bound from `hostileRequests_length_le`.  The configuration fact is not a package field. -/
theorem hKreq_of_three_mul_compRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (h3N : 3 * P.objects.cfg.compRows ≤ P.objects.cfg.Ksz) :
    IO.InRange P.objects.cfg.Ksz (P.hostileRequests Qc).length := by
  refine ⟨hostileRequests_length_pos P Qc, ?_⟩
  have hle := P.hostileRequests_length_le Qc
  rw [P.optimized.family_cfg] at hle
  exact hle.trans h3N

/-- **`hKresp` from `M ≤ Ksz`.**  `hostileResponses_length_le` for every trace.  The configuration fact is not a package field. -/
theorem hKresp_of_memRows_le
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hM : P.objects.cfg.memRows ≤ P.objects.cfg.Ksz) :
    (P.hostileResponses Qm).length ≤ P.objects.cfg.Ksz := by
  have hle := P.hostileResponses_length_le Qm
  rw [P.optimized.family_cfg] at hle
  exact hle.trans hM

/-! ## 4. The configuration corollary

Residual hypotheses against `optimizedFullStrict_hostile_LIO`:

| original | this corollary | §1 side condition |
|---|---|---|
| `S`, `hacc`, `hgood` | kept | (logical: statement / acceptance / coins) |
| `hchar` | `P.stateTagChar` | field `p > 11` (implicit in choosing `p`) |
| `hKp` | `P.ioStrategy.charBound` | `hrow`-shaped, on `Ksz` |
| `hKreq` | `3 · N ≤ Ksz` | with `hKp`: `3N < p`, `hrow`-shaped |
| `hKresp` | `M ≤ Ksz` | with `hKp`: `M < p`, `hrow`-shaped |

No new hypothesis is not a configuration fact of `P`/`K` or one of the five.  `horb` and
`hα` are not needed here (the priced α-event is inside `hgood`; `hΛ`/`hrun` live on
`nockCompiles`).

**Generated package (`GoodSeed.nockCompiles_of_grom_atRomSeed`).**  Existing binders
`hq : 11 < q` and `hchar : q = ringChar K` give `hchar`; `hKszChar : Ksz < ringChar K`
gives `hKp`.  They do **not** give `3 * (bfsForest [ct]).length ≤ Ksz` nor
`(bfsForest mf).length ≤ Ksz`.  Neighbours `hKsz : accAt ≤ Ksz` and
`hKsz2 : 2 * kMem ≤ Ksz` are honest-count / root-count bounds, not the hostile
majorants.  No corollary
is stated. -/

end

noncomputable section

/-! ## 5. F73 instantiation

`concrete73`: `N = 1`, `Ksz = 4`, so `3N ≤ Ksz` by `decide`.  `M = 5 ≰ 4`, so the full
`of_config` is uninhabited at this fixture; `of_config_requests` discharges `hKresp` from
the honest `responseRange` (a package field, `MA` §3 pattern).  `package73` shares the
same `ExactConfig` numerals; it has `statement73` but no production-acceptance receipt, so
only the numerals are instantiated. -/

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete
open Nock.NockVMROM.Thm54.BuildableConcrete
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open OptimizedStrictFullPackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- `11 < ringChar K73cubic` from `73 = ringChar`. -/
theorem concrete73_eleven_lt_ringChar : 11 < ringChar K73cubic := by
  rw [← q_eq_ringChar]
  norm_num

/-- `hchar` at F73 from `11 < ringChar`, independently of the package field. -/
theorem concrete73_hchar_of_lt_ringChar :
    ∀ n : ℕ, n ≤ 11 → (n : K73cubic) = 1 → n = 1 :=
  hchar_of_lt_ringChar concrete73_eleven_lt_ringChar

theorem concrete73_compRows :
    concreteOptimizedFullStrictPackage.objects.cfg.compRows = 1 := by
  rw [← concreteOptimizedFullStrictPackage.optimized.family_cfg]
  exact concrete73_rows

theorem concrete73_Ksz :
    concreteOptimizedFullStrictPackage.objects.cfg.Ksz = 4 := by
  change (ConcreteStrictPackage.cfg honestSeed honestAlpha).Ksz = 4
  rfl

theorem concrete73_memRows :
    concreteOptimizedFullStrictPackage.objects.cfg.memRows = 6 := by
  change (ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows = 6
  rfl

/-- `3 · N ≤ Ksz` at F73: `3 · 1 ≤ 4`. -/
theorem concrete73_three_mul_compRows_le_Ksz :
    3 * concreteOptimizedFullStrictPackage.objects.cfg.compRows ≤
      concreteOptimizedFullStrictPackage.objects.cfg.Ksz := by
  rw [concrete73_compRows, concrete73_Ksz]
  decide

/-- The majorant `M ≤ Ksz` **fails** at F73: `6 ≰ 4`.  Walk rows sit in `memRows`. -/
theorem concrete73_memRows_not_le_Ksz :
    ¬ (concreteOptimizedFullStrictPackage.objects.cfg.memRows ≤
        concreteOptimizedFullStrictPackage.objects.cfg.Ksz) := by
  rw [concrete73_memRows, concrete73_Ksz]
  decide

variable (hmore73 : LaterSeedZeros (F := F73) (K := K73cubic)
  BuildableConcrete.concreteExecution)
include hmore73

/-- `package73` has the same config numerals (`regression73`: `objects.cfg = concreteExecution.cfg`). -/
theorem package73_three_mul_compRows_le_Ksz
    (hax : FormRAxisBound (package73 hmore73).optimized.sampled (package73 hmore73).optimized.basis)
    (hbasis : FormRBasis (package73 hmore73).optimized.basis)
    (hwidth : FormRWidth F73) :
    3 * (package73 hmore73).objects.cfg.compRows ≤ (package73 hmore73).objects.cfg.Ksz := by
  have hcfg := (regression73 hmore73 hax hbasis hwidth).1
  rw [hcfg]
  change 3 * (BuildableConcrete.concreteExecution.cfg).compRows ≤
    BuildableConcrete.concreteExecution.cfg.Ksz
  decide

theorem package73_memRows_not_le_Ksz
    (hax : FormRAxisBound (package73 hmore73).optimized.sampled (package73 hmore73).optimized.basis)
    (hbasis : FormRBasis (package73 hmore73).optimized.basis)
    (hwidth : FormRWidth F73) :
    ¬ ((package73 hmore73).objects.cfg.memRows ≤ (package73 hmore73).objects.cfg.Ksz) := by
  have hcfg := (regression73 hmore73 hax hbasis hwidth).1
  rw [hcfg]
  change ¬ (BuildableConcrete.concreteExecution.cfg.memRows ≤
    BuildableConcrete.concreteExecution.cfg.Ksz)
  decide

theorem package73_hchar : ∀ n : ℕ, n ≤ 11 → (n : K73cubic) = 1 → n = 1 :=
  hchar_of_package (package73 hmore73)

theorem package73_hKp : (package73 hmore73).objects.cfg.Ksz < ringChar K73cubic :=
  hKp_of_package (package73 hmore73)

end F73

end

end OptimizedHostileConfiguration
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.hchar_of_lt_ringChar
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.hchar_of_stateTagChar
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.eleven_lt_ringChar_of_package
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.hchar_of_package
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.hKp_of_package
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.rowRequests_length_pos
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.hostileRequests_length_pos
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.hKreq_of_three_mul_compRows
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.hKresp_of_memRows_le
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.concrete73_eleven_lt_ringChar
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.concrete73_three_mul_compRows_le_Ksz
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.concrete73_memRows_not_le_Ksz
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.package73_three_mul_compRows_le_Ksz
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.package73_hchar
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileConfiguration.package73_hKp
