import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.MixedMemoryGates
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
import Nock.RedTeam.Batch271Thm54AnchoringReview
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper re-read at source: the paper (the accumulation
gate `ver · (RLC^α(x_mem(i,·)) − β) · (acc(i−1) − acc(i)) = …`), `:594` ("randomness `α, β` of
the computation table"), `:1483` (`24·e + 16` gates of degree at most `4`), `:1487`.

## A. The pin's convention (attack 2)

* `recordRLCExpr_eval`: the committed `recordRLCExpr` evaluates to `Walk.rlc (chal 4) (trace (19+·))`
  — exactly the `Σ_{c<8} γ^c · field_c` of `FiniteIO.compress`, with the exponent starting at `0`
  on role `19` (no shift, no inverse coin).
* `memoryEnvFull_cols_23_30_are_encRec`: the memory table's columns `23..30` (which
  `canonical_table_role` maps to roles `19..26`) are `NockVM.encRec mem` **in `encRec`'s order**,
  so the honest record roles are the record in the order the compute side compresses.
* `compress_eq_paper_form`: `compress ⟨γ, pole⟩ v = RLC^γ(v) − (−pole)` — the paper's
  `RLC^α − β` under the coin renaming `β ↦ −pole`, a bijection on the coin space; the compute
  side's `slotDenominator_eq_compress` uses the same `compress`, so `hostile_logUp_sums_agree`
  compares like with like (`compute_and_memory_same_convention`).
* `rival_conventions_distinct`: the three plausible slips — inverse coin, shifted exponent,
  subtractive pole — give values different from `compress` at a concrete `ℚ` instance, so the
  convention check above is not vacuous.

## B. At the consumed chip (attack 1)

* `role37_eq_compress_of_hsat_only`: for **any** package `P` and **any** trace `Qm` with
  `SatisfiesWithPreprocessing P.memoryChip Qm`, at **every** row `role 37 = compress
  (P's sampled coins) (record roles 19..26)` — **no acceptance structure, no
  `memory_sampled_coins`**, no fold hypothesis.  The production `hostile_role37_eq_compress`
  therefore smuggles nothing: its `memory_sampled_coins` premise is discharged by the package.
* `packageM_swap_rejected_concrete`: at the real F97 `(packageM hmoreM)`, rows `0`/`1`, `d₁' = d₁ + 1`,
  `d₂' = 0` — REJECTED at `(packageM hmoreM).memoryChip` (no compensation, `d₂'` not even nonzero).
* `package73_swap_rejected_concrete`: the same at the F73 `package73` (five rows, one response;
  `repaired_chip_rejects_denominator_swap` needs no `ver` hypothesis, so it IS statable there —
  `Batch271`'s `attackTrace_accepted` was not).
* `packageM_honest_accepted_and_pinned`, `package73_honest_accepted_and_pinned`: the honest
  traces of both deployed chips are accepted and satisfy the pin at every row (non-vacuity).

## C. The acceptance pin is a package-level tautology (attack 3)

* `AcceptanceSansPin` is `OptimizedHistoricalAcceptanceAt` with `memory_sampled_coins` deleted;
  `acceptance_sansPin_iff`: the two are equivalent for every `P`, `Qc`, `Qm`, `c`.  So the
  acceptance field is **not load-bearing**: a challenge slot is not a trace column, and
  `memoryCoordinatePins.sampledGamma/sampledPole` (a `Prop` field of
  `OptimizedStrictNockVMROMPackage`) already pins slots `4`/`5` for every candidate trace.  The load-bearing changes are the gate and the package pins.
* `coins_not_a_trace_column`: the slots `4`/`5` of `P.memorySourceEnv Qm i` do not depend on `Qm`.

## D. Degree and counts (attack 7)

* `denominatorPinMixed_degree_one` (by `MixedExpr.degree`, challenges at degree `0` — the AIR
  notion in which `:1483`'s "degree at most 4" is stated: the coins are verifier constants);
  `denominatorPinCoord_degree_le_one`: every compiled base-field coordinate body has degree `≤ 1`.
* `counts_89_88`, `packageM_numerals`: `26·3 + 11 = 89`, `24·3 + 16 = 88`, and the released
  capstone's numerals at `(packageM hmoreM)` are `196/113/4` (memory) and `199/127/4` (compute).
-/
namespace Nock.RedTeam.Batch273

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Module
open Polynomial

/-! ## A. Convention -/

section Convention

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The committed `recordRLCExpr` is `Walk.rlc γ record` with `γ = chal 4` and
`record c = trace (19 + c)`: exponent `c` on role `19 + c`, `c = 0..7`. -/
theorem recordRLCExpr_eval (env : Env K) :
    recordRLCExpr.eval env =
      Walk.rlc (env.chal 4) (OptimizedMemoryHostileAccumulator.memRowRecord env) := by
  simp [recordRLCExpr, Expr.eval, Walk.rlc,
    OptimizedMemoryHostileAccumulator.memRowRecord, Fin.sum_univ_succ]
  ring

omit [FiniteDimensional F K] in
/-- Hence the pin says exactly `role 37 = FiniteIO.compress ⟨chal 4, chal 5⟩ (record)` — reproved
here from `recordRLCExpr_eval` rather than by the production `simp`/`ring` close. -/
theorem pin_zero_iff (envK : Env K) (envF : Env F) :
    (denominatorPinMixed (F := F)).eval envK envF = 0 ↔
      envK.trace 37 =
        FiniteIO.compress ⟨envK.chal 4, envK.chal 5⟩
          (OptimizedMemoryHostileAccumulator.memRowRecord10 envK envF) := by
  rw [OptimizedMemoryHostileAccumulator.memRowRecord10, FiniteIO.compress,
    RecordCarrier.rlc_withExp]
  simp only [denominatorPinMixed, recordRLC, reqIdxRLCTerm, reqIdxCol, bcur,
    CoordinateCompiler.CoeffExpr.eval,
    MixedExpr.eval, MixedExpr.ofExpr_eval, recordRLCExpr_eval, sub_eq_zero]
  constructor <;> intro h <;> rw [h] <;> ring

/-- The memory table's columns `23..30` — the ones `canonical_table_role` sends to roles
`19..26` — are `NockVM.encRec mem` in `encRec`'s own order `(root.size, root.dyck, root.leaf,
child.size, child.dyck, child.leaf, axis, ts)`. -/
theorem memoryEnvFull_cols_23_30_are_encRec
    (minp : MemoryTable.Inputs K) (mop : MemoryTable.MState → K) (mrow : MemoryTable.Pub K)
    (mg : K) (c : Fin 8) :
    (memoryEnvFull minp mop mrow mg).trace (23 + (c : ℕ)) =
      NockVM.encRec mrow.mem (Fin.castSucc c) := by
  fin_cases c <;> rfl

/-- `compress ⟨γ, pole⟩ v = RLC^γ(v) − (−pole)`: the paper's `RLC^α(x) − β`
under `β ↦ −pole`, a bijection on the coin space. -/
theorem compress_eq_paper_form (coins : FiniteIO.IOCoins K) (v : Fin 8 → K) :
    FiniteIO.compress coins v = Walk.rlc coins.gamma v - (-coins.pole) := by
  simp [FiniteIO.compress]; ring

/-- Both chips' committed denominators are `FiniteIO.compress` of the row's coins and the row's
record: the memory pin (`pin_zero_iff`) and the compute slot denominators
(`OptimizedComputeHostileAccumulator.slotDenominator_eq_compress`).  Same function, same
convention — `hostile_logUp_sums_agree` compares like with like. -/
theorem compute_and_memory_same_convention
    (envK : Env K) (envF : Env F) (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K)
    (j : Fin 3) :
    ((denominatorPinMixed (F := F)).eval envK envF = 0 →
      envK.trace 37 = FiniteIO.compress (memRowCoins envK) (memRowRecord10 envK envF)) ∧
    OptimizedComputeHostileAccumulator.slotDenominator env j =
      FiniteIO.compress (OptimizedComputeHostileAccumulator.rowCoins env)
        (OptimizedComputeHostileAccumulator.rowRecord env j) :=
  ⟨fun h => (pin_zero_iff envK envF).1 h,
   OptimizedComputeHostileAccumulator.slotDenominator_eq_compress env j⟩

/-- Rival conventions a slip could have produced. -/
def rlcInv (γ : K) (v : Fin 8 → K) : K := ∑ c : Fin 8, γ⁻¹ ^ (c : ℕ) * v c
def rlcShift (γ : K) (v : Fin 8 → K) : K := ∑ c : Fin 8, γ ^ ((c : ℕ) + 1) * v c
def compressSub (coins : FiniteIO.IOCoins K) (v : Fin 8 → K) : K :=
  Walk.rlc coins.gamma v - coins.pole

/-- At `γ = 2`, `pole = 5`, `v = (1,…,1)` over `ℚ`: `compress = 260`, inverse-coin `5 + 255/128`,
shifted exponent `515`, subtractive pole `250`.  All three rivals differ from `compress`, so the convention
theorems above are checking something. -/
theorem rival_conventions_distinct :
    let coins : FiniteIO.IOCoins ℚ := ⟨2, 5⟩
    let v : Fin 8 → ℚ := fun _ => 1
    FiniteIO.compress coins v = 260 ∧
      coins.pole + rlcInv coins.gamma v ≠ FiniteIO.compress coins v ∧
      coins.pole + rlcShift coins.gamma v ≠ FiniteIO.compress coins v ∧
      compressSub coins v ≠ FiniteIO.compress coins v := by
  simp only [FiniteIO.compress, Walk.rlc, rlcInv, rlcShift, compressSub, Fin.sum_univ_eight]
  norm_num

end Convention

/-! ## B. At the consumed chip -/

section Consumed

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
    0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
      (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
        (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
include hmore

/-- **From `hsat` alone.**  For any trace `P.memoryChip` accepts, at every row, role `37` is the
compression of the row's record roles `19..26` at the **package's** sampled coins.  No
acceptance structure is consulted: the coin slots come from `memoryCoordinatePins`
(`memorySourceEnv_sampled_coins`), the pin from the mixed bucket. -/
theorem role37_eq_compress_of_hsat_only
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) (i : Fin (rows P)) :
    (rowEnvK P Qm i).trace 37 =
      FiniteIO.compress P.optimized.sampled.sampled.coins
        (OptimizedMemoryHostileAccumulator.memRowRecord10 (rowEnvK P Qm i) (rowEnvF P Qm i)) := by
  have h := hostile_role37_eq_compress_rowCoins P Qm hsat i
  obtain ⟨h4, h5⟩ := P.memorySourceEnv_sampled_coins Qm i
  rw [h, memRowCoins_eq, h4, h5]

/-- **At the honest trace of any package, roles `19..26` are `encRec` of the row's memory record,
in `encRec`'s order**, so the pin's `record` is the record the compute side compresses
(the paper `x_mem(i,·)`; `:2123`).  Through `canonical_memorySourceEnv`,
`canonical_table_role` (roles `19..26` = table columns `23..30`) and
`memoryEnvFull_cols_23_30_are_encRec`. -/
theorem honest_record_roles_are_encRec [Fintype F] [DecidableEq F] (i : Fin (rows P)) (c : Fin 8) :
    (rowEnvK P (canonicalMemoryTrace P) i).trace (19 + (c : ℕ)) =
      NockVM.encRec (P.optimized.family.problem.exec.memoryPubAt i).mem (Fin.castSucc c) := by
  have h := canonical_memorySourceEnv P i
  change (P.memorySourceEnv (canonicalMemoryTrace P) i).trace (19 + (c : ℕ)) = _
  rw [h]
  have ht := canonical_table_role P.optimized.sampled P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit P.optimized.memoryCoordinatePins i
    (23 + (c : ℕ)) (by omega) (by omega) (by omega)
  rw [show 23 + (c : ℕ) - 4 = 19 + (c : ℕ) by omega] at ht
  rw [ht]
  exact memoryEnvFull_cols_23_30_are_encRec _ _ _ _ c

theorem honest_role37_is_responseDenominator [Fintype F] [DecidableEq F]
    (hC : P.optimized.family.problem.exec.CprimeCoherent)
    (i : Fin (rows P)) :
    (rowEnvK P (canonicalMemoryTrace P) i).trace 37 =
      FiniteIO.compress P.optimized.sampled.sampled.coins
        (OptimizedMemoryHostileAccumulator.memRowRecord10
          (rowEnvK P (canonicalMemoryTrace P) i)
          (rowEnvF P (canonicalMemoryTrace P) i)) :=
  role37_eq_compress_of_hsat_only P hmore (canonicalMemoryTrace P)
    (canonicalMemoryTrace_satisfies P hmore hC) i

/-- The coin slots of `memorySourceEnv` do not depend on the trace at all. -/
theorem coins_not_a_trace_column
    (Qm Qm' : Fin P.memoryChip.rap.w → F[X]) (i : Fin (rows P)) :
    (P.memorySourceEnv Qm i).chal 4 = (P.memorySourceEnv Qm' i).chal 4 ∧
      (P.memorySourceEnv Qm i).chal 5 = (P.memorySourceEnv Qm' i).chal 5 := by
  obtain ⟨a4, a5⟩ := P.memorySourceEnv_sampled_coins Qm i
  obtain ⟨b4, b5⟩ := P.memorySourceEnv_sampled_coins Qm' i
  exact ⟨a4.trans b4.symm, a5.trans b5.symm⟩

end Consumed

section F97

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.RedTeam.Batch271

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance fintype97 : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance deq97 : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance charRing97 : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/- Concrete F97 packageM instance. -/
variable {hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution}
include hmoreM

theorem packageM_swap_rejected_concrete :
    ¬ RAP.SatisfiesWithPreprocessing (packageM hmoreM).memoryChip
      (attackTrace (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM)
        ((rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 37 + 1) 0
        (honestM hmoreM)) :=
  repaired_chip_rejects_denominator_swap (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM) _ 0
    (honestM hmoreM)
    (canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
        MultiRootServedFixture.execS_cprimeCoherent)
    (by change 1 < 2; decide)
    (by intro h; exact one_ne_zero (add_left_cancel (h.trans (add_zero _).symm)))

/-- The attack trace of `packageM_swap_rejected_concrete` really commits `d₁ + 1` at row `0`
with the record roles `19..26` of the honest trace at every row. -/
theorem packageM_swap_trace_values :
    (rowEnvK (packageM hmoreM) (attackTrace (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM)
        ((rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 37 + 1) 0
        (honestM hmoreM)) (rowM0 hmoreM)).trace 37 =
      (rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 37 + 1 ∧
    ∀ (j : Fin (rows (packageM hmoreM))) (c : Fin 8),
      (rowEnvK (packageM hmoreM) (attackTrace (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM)
        ((rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 37 + 1) 0
        (honestM hmoreM)) j).trace (19 + (c : ℕ)) =
        (rowEnvK (packageM hmoreM) (honestM hmoreM) j).trace (19 + (c : ℕ)) := by
  have hv := attackTrace_values (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM)
    ((rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 37 + 1) 0
    (honestM hmoreM) (by change 1 < 2; decide)
  refine ⟨hv.1, fun j c => hv.2.2 j (19 + (c : ℕ)) ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> omega

theorem packageM_honest_accepted_and_pinned :
    RAP.SatisfiesWithPreprocessing (packageM hmoreM).memoryChip (honestM hmoreM) ∧
      ∀ i : Fin (rows (packageM hmoreM)),
        (rowEnvK (packageM hmoreM) (honestM hmoreM) i).trace 37 =
          FiniteIO.compress (packageM hmoreM).optimized.sampled.sampled.coins
            (OptimizedMemoryHostileAccumulator.memRowRecord10
              (rowEnvK (packageM hmoreM) (honestM hmoreM) i)
              (rowEnvF (packageM hmoreM) (honestM hmoreM) i)) :=
  ⟨canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
      MultiRootServedFixture.execS_cprimeCoherent,
   fun i => role37_eq_compress_of_hsat_only (packageM hmoreM) hmoreM (honestM hmoreM)
     (canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
         MultiRootServedFixture.execS_cprimeCoherent) i⟩

set_option maxRecDepth 100000

/-- The released capstone's numerals, read at `(packageM hmoreM)`: `199/127/4` and `196/140/4`,
transition split `87` / `140`. -/
theorem packageM_numerals :
    ((packageM hmoreM).computeChip.rap.w = 303 ∧ (packageM hmoreM).computeChip.rap.s = 418 ∧
        (packageM hmoreM).computeChip.rap.d = 4 ∧ (packageM hmoreM).computeChip.rap.k = 2) ∧
      ((packageM hmoreM).memoryChip.rap.w = 205 ∧ (packageM hmoreM).memoryChip.rap.s = 156 ∧
        (packageM hmoreM).memoryChip.rap.d = 4 ∧ (packageM hmoreM).memoryChip.rap.k = 1) ∧
      ((packageM hmoreM).computeChip.rap.s - 44 = 374 ∧ (packageM hmoreM).memoryChip.rap.s - 0 =
        156) :=
  released_capstone_deployed_numerals (packageM hmoreM)

end F97

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete
open Nock.NockVMROM.Thm54.BuildableConcrete
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.RedTeam.Batch271

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

variable {hmore73 : BuildableAxisWitness.LaterSeedZeros (F := F73) (K := K73cubic)
  BuildableConcrete.concreteExecution}
include hmore73

abbrev row73_0 : Fin (rows (package73 hmore73)) := ⟨0, by
  change 0 < (package73 hmore73).optimized.family.problem.cfg.memRows
  rw [package73_memRows hmore73]; decide⟩
abbrev row73_1 : Fin (rows (package73 hmore73)) := ⟨1, by
  change 1 < (package73 hmore73).optimized.family.problem.cfg.memRows
  rw [package73_memRows hmore73]; decide⟩

/-- **The F73 instantiation `Batch271` could not state** (one response row, so the compensating
pair had nothing to compensate): the rejection needs no `ver` hypothesis, so at `package73`,
rows `0`/`1`, `d₁' = d₁ + 1`, `d₂' = 0`, the attack trace is REJECTED. -/
theorem package73_swap_rejected_concrete :
    ¬ RAP.SatisfiesWithPreprocessing (package73 hmore73).memoryChip
      (attackTrace (package73 hmore73) row73_0 row73_1
        ((rowEnvK (package73 hmore73) (honest73M hmore73) row73_0).trace 37 + 1) 0
        (honest73M hmore73)) :=
  repaired_chip_rejects_denominator_swap (package73 hmore73) row73_0 row73_1 _ 0
    (honest73M hmore73)
    (canonicalMemoryTrace_satisfies (package73 hmore73) hmore73
        (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha))
    (by change 0 < 1; decide)
    (by intro h; exact one_ne_zero (add_left_cancel (h.trans (add_zero _).symm)))

theorem package73_honest_accepted_and_pinned :
    RAP.SatisfiesWithPreprocessing (package73 hmore73).memoryChip (honest73M hmore73) ∧
      ∀ i : Fin (rows (package73 hmore73)),
        (rowEnvK (package73 hmore73) (honest73M hmore73) i).trace 37 =
          FiniteIO.compress (package73 hmore73).optimized.sampled.sampled.coins
            (OptimizedMemoryHostileAccumulator.memRowRecord10
              (rowEnvK (package73 hmore73) (honest73M hmore73) i)
              (rowEnvF (package73 hmore73) (honest73M hmore73) i)) :=
  ⟨canonicalMemoryTrace_satisfies (package73 hmore73) hmore73
      (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
      ConcreteStrictPackage.honestAlpha),
   fun i => role37_eq_compress_of_hsat_only (package73 hmore73) hmore73 (honest73M hmore73)
     (canonicalMemoryTrace_satisfies _ hmore73 (ConcreteStrictPackage.execution_cprimeCoherent
         ConcreteStrictPackage.honestSeed ConcreteStrictPackage.honestAlpha)) i⟩

end F73

/-! ## C. The acceptance field is derivable -/

section Acceptance

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [Fintype F] [DecidableEq F] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

structure AcceptanceSansPin
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  p8 : P.strategy.Accepts c.1 c.2.2.2.lambda
  same_problem : P.OptimizedSameProblemAt c.1 c.2.2.2.lambda
  sampled_io_coins :
    c.2.1 =
      (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)
  compute_satisfies :
    RAP.SatisfiesWithPreprocessing P.computeChip Qc
  memory_satisfies :
    RAP.SatisfiesWithPreprocessing P.memoryChip Qm

/-- **The A-mem-2 acceptance field is a consequence of `sampled_io_coins` for every package**:
the two acceptance predicates coincide on slots `4`/`5`. -/
theorem acceptance_sansPin_iff
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    AcceptanceSansPin P Qc Qm c ∧ c.2.2.2.interPole = P.packageInterPole ↔
      P.OptimizedHistoricalAcceptanceAt Qc Qm c := by
  constructor
  · intro ⟨h, hz⟩
    exact
      { p8 := h.p8
        same_problem := h.same_problem
        sampled_io_coins := h.sampled_io_coins
        memory_sampled_coins := by
          intro i
          obtain ⟨h4, h5⟩ := P.memorySourceEnv_sampled_coins Qm i
          rw [h.sampled_io_coins]
          exact ⟨h4, h5⟩
        memory_intermediate_pole := P.memory_intermediate_pole_of_tuple Qm _ hz
        compute_satisfies := h.compute_satisfies
        memory_satisfies := h.memory_satisfies }
  · intro h
    refine ⟨?_, ?_⟩
    · exact
      { p8 := h.p8
        same_problem := h.same_problem
        sampled_io_coins := h.sampled_io_coins
        compute_satisfies := h.compute_satisfies
        memory_satisfies := h.memory_satisfies }
    · have h6 := h.memory_intermediate_pole
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩
      exact h6.symm.trans (P.memorySourceEnv_inter_pole Qm _)

/-- The production `hostile_role37_eq_compress` restated with `AcceptanceSansPin`: the conclusion
with the tuple's coins `c.2.1` follows without the field. -/
theorem hostile_role37_eq_compress_sansPin
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : AcceptanceSansPin P Qc Qm c) (i : Fin (rows P)) :
    (rowEnvK P Qm i).trace 37 =
      FiniteIO.compress ⟨c.2.1.1, c.2.1.2⟩
        (memRowRecord10 (rowEnvK P Qm i) (rowEnvF P Qm i)) := by
  let c' : OptimizedProductionChallengeTuple K F :=
    (c.1, (c.2.1, (c.2.2.1, ⟨P.packageInterPole, c.2.2.2.lambda⟩)))
  have h' : AcceptanceSansPin P Qc Qm c' :=
    { p8 := h.p8
      same_problem := h.same_problem
      sampled_io_coins := h.sampled_io_coins
      compute_satisfies := h.compute_satisfies
      memory_satisfies := h.memory_satisfies }
  simpa [c'] using
    hostile_role37_eq_compress P Qm Qc c'
      (deployedAcceptance_of_historical ((acceptance_sansPin_iff P Qc Qm c').1 ⟨h', rfl⟩)) i

end Acceptance

/-! ## D. Degree and counts -/

section Degree

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

omit [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] in
/-- Degree `1` in the trace variables. -/
theorem denominatorPinMixed_degree_one : (denominatorPinMixed (F := F)).degree = 1 := rfl

/-- Every compiled base-field coordinate of the pin has degree `≤ 1` (the `powVec`/`mulVec`
expansion of `γ^c · field_c` multiplies challenge coordinates, which are constants). -/
theorem denominatorPinCoord_degree_le_one (b : Basis (Fin 3) F K) (k : Fin 3) :
    (MixedMemoryGates.denominatorPinCoord b k).degree ≤ 1 :=
  (mixedCompile_degree_le b (MixedMemoryGates.memCol0 b) (denominatorPinMixed (F := F)) k).trans
    (le_of_eq denominatorPinMixed_degree_one)

theorem counts_140 :
    Thm54Resources.memoryTransitionGates 3 = 156 ∧
      Thm54Resources.memoryTransitionGatesPaper 3 = 88 ∧
      Thm54Resources.memoryConstraints 3 = 156 ∧
      (∀ e, Thm54Resources.memoryTransitionGates e = Thm54Resources.memoryTransitionGatesPaper e
        ↔ False) := by
  refine ⟨by decide, by decide, by decide, fun e => ?_⟩
  simp only [Thm54Resources.memoryTransitionGates, Thm54Resources.memoryTransitionGatesPaper,
    iff_false]
  omega

/-- The deployed `mixedTransitionGates` list has 49 paper members, includes the
denominator pin, all degree `≤ 4`. -/
theorem mixed_bucket_shape (b : Basis (Fin 3) F K) :
    (mixedTransitionGates (F := F) (K := K) b).length = 50 ∧
      denominatorPinMixed (F := F) ∈ mixedTransitionGates (F := F) (K := K) b ∧
      ∀ g ∈ mixedTransitionGates (F := F) (K := K) b, g.degree ≤ 4 :=
  ⟨mixedTransitionGates_length b, denominatorPinMixed_mem b, mixedTransitionGates_degree b⟩

end Degree

end Nock.RedTeam.Batch273

#print axioms Nock.RedTeam.Batch273.recordRLCExpr_eval
#print axioms Nock.RedTeam.Batch273.pin_zero_iff
#print axioms Nock.RedTeam.Batch273.memoryEnvFull_cols_23_30_are_encRec
#print axioms Nock.RedTeam.Batch273.compute_and_memory_same_convention
#print axioms Nock.RedTeam.Batch273.rival_conventions_distinct
#print axioms Nock.RedTeam.Batch273.role37_eq_compress_of_hsat_only
#print axioms Nock.RedTeam.Batch273.honest_record_roles_are_encRec
#print axioms Nock.RedTeam.Batch273.honest_role37_is_responseDenominator
#print axioms Nock.RedTeam.Batch273.packageM_swap_rejected_concrete
#print axioms Nock.RedTeam.Batch273.packageM_swap_trace_values
#print axioms Nock.RedTeam.Batch273.packageM_honest_accepted_and_pinned
#print axioms Nock.RedTeam.Batch273.packageM_numerals
#print axioms Nock.RedTeam.Batch273.package73_swap_rejected_concrete
#print axioms Nock.RedTeam.Batch273.package73_honest_accepted_and_pinned
#print axioms Nock.RedTeam.Batch273.acceptance_sansPin_iff
#print axioms Nock.RedTeam.Batch273.hostile_role37_eq_compress_sansPin
#print axioms Nock.RedTeam.Batch273.denominatorPinCoord_degree_le_one
#print axioms Nock.RedTeam.Batch273.counts_140
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_role37_eq_compress
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_role37_eq_compress_rowCoins
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.memRowTerm_eq_record_form
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_denominatorPinMixed
#print axioms Nock.RedTeam.Batch271.repaired_chip_rejects_denominator_swap
#print axioms Nock.RedTeam.Batch271.packageM_denominator_attack_rejected
#print axioms Nock.RedTeam.Batch271.attackTrace_all_but_pin
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
