/-
  Nock/NockVMROM/Thm54/PreZComputeCensus.lean

  This module ties it to the staged view of the package's compute chip
  and proves the compute-side structure route B reads is pre-`z`:

  * **§1 — the staged-view form.**  `compView P` is `DeployedStaging.deployedComputeView` at the
    package's chip arguments (its RAP is `P.computeChip`'s); `compCC P` its column → coin map on
    `P.computeChip`'s columns, as `memCC P` is on the memory chip's.  `computeView_preZ_iff`
    (mirror of `memView_preZ_iff`): a compute column reads no `z` iff its B1 round is `0`;
    `preZAgreeOn_compCC_iff`: `PreSeedCensus.PreZAgreeOn (compCC P)` IS `PreZAgreeOnC`, and
    `preZReadsFnOn_compCC_iff` the same for functions.
  * **§2 — the structure is pre-`z`.**  At every row: the base environment on round-0 columns
    (`computeBaseEnv_trace_congr`), the per-row structure `selectors 0..10 / certificate
    202..270 / S` (`preZComputeStructure_preZReads`), the decoded state `computeStateOf ∘
    decodeSource` (`computeState_preZReads`) and so `fanoutComp` (`computeFanout_preZReads`), the
    request activity masks (`activeMask_preZReads`), the row arity (`rowArity_preZReads`), the
    prefix exponent `S(m) = Σ_{k<m} arity(k)` (`prefixExp_preZReads`), the slot exponents
    `expOf i j = S(i) + j + 1` (`expOf_preZReads`, the locator `k ↦ (a, j)` of route B) and the
    committed carrier `expCol` (`expCol_preZReads`).
  * **§3 — positive control.**  The base-env read of a round-1 column (`𝕂` role `0`, column `13`)
    is NOT pre-`z` at the package (`not_preZReads_role0`).
-/
import Nock.NockVMROM.Thm54.PreSeedCensus
import Nock.NockVMROM.Thm54.PreZComputeCore
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.PreZComputeCensus

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.PreZComputeCore
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps

noncomputable section

/-! ## §1  The staged-view form -/

/-- The core's copy of the B1 compute round map is `DeployedStaging`'s. -/
theorem compRoleRound_eq : compRoleRound = computeRoleRound := rfl

/-- The core's copy of the B1 compute round map is `DeployedStaging`'s. -/
theorem compColRound_eq : compColRound = computeColRound := rfl

section View

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Module.Basis (Fin 3) F K)
  (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h)

/-- **At the deployed compute view, a column reads no `z` iff its B1 round is `0`** (the mirror of
`PreSeedCensus.memView_preZ_iff`). -/
theorem computeView_preZ_iff (c : Fin 303) :
    zIdx ∉ (deployedComputeView hn nodes b chalVal pubVal orbit).columnChallenges c ↔
      computeColRound c = 0 := by
  show zIdx ∉ roundChallenges (computeRoundFin c) ↔ _
  rw [zIdx_mem_roundChallenges_iff]
  simp [computeRoundFin]

end View

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The staged view of the package's compute chip (`P.computeChip` is this view's RAP). -/
abbrev compView : StagedRAPView F 3 deployedChronology :=
  deployedComputeView P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit

/-- **`compCC`**: `DeployedStaging`'s column → coin map, read on the package's compute trace
columns (the twin of `PreSeedCensus.memCC`). -/
def compCC (col : Fin P.computeChip.rap.w) : Finset (Fin deployedChronology.numChallenges) :=
  (compView P).columnChallenges (Fin.cast (compView P).hw col)

theorem compCC_preZ_iff (col : Fin P.computeChip.rap.w) :
    zIdx ∉ compCC P col ↔ compColRound col.val = 0 := by
  rw [compColRound_eq]
  exact computeView_preZ_iff _ _ _ _ _ _ (Fin.cast (compView P).hw col)

/-- **The staged-view form IS the core predicate**: `PreZAgreeOn (compCC P)` on the compute
chip's columns is `PreZAgreeOnC`. -/
theorem preZAgreeOn_compCC_iff {α : Type*} (Qc Qc' : Fin P.computeChip.rap.w → α) :
    PreZAgreeOn (compCC P) Qc Qc' ↔ PreZAgreeOnC Qc Qc' := by
  constructor
  · intro h c hc; exact h c ((compCC_preZ_iff P c).2 hc)
  · intro h c hc; exact h c ((compCC_preZ_iff P c).1 hc)

theorem preZReadsFnOn_compCC_iff {α : Type*} {β : Type*}
    (f : (Fin P.computeChip.rap.w → α) → β) :
    PreZReadsFnOn (compCC P) f ↔ PreZReadsC f := by
  constructor
  · intro h Q Q' hag; exact h Q Q' ((preZAgreeOn_compCC_iff P Q Q').2 hag)
  · intro h Q Q' hag; exact h Q Q' ((preZAgreeOn_compCC_iff P Q Q').1 hag)

/-! ## §2  The compute-side structure is pre-`z` -/

variable {P}

theorem computeBaseEnv_trace_congr {Qc Qc' : Fin P.computeChip.rap.w → F[X]}
    (hag : PreZAgreeOn (compCC P) Qc Qc') (i : Fin P.optimized.family.problem.cfg.compRows)
    {j : ℕ} (hj : compColRound j = 0) :
    (P.computeBaseEnv Qc i).trace j = (P.computeBaseEnv Qc' i).trace j :=
  envOfTrace_trace_congr ((preZAgreeOn_compCC_iff P Qc Qc').1 hag) _ _ _ _ hj

theorem computeBaseEnv_traceNext_congr {Qc Qc' : Fin P.computeChip.rap.w → F[X]}
    (hag : PreZAgreeOn (compCC P) Qc Qc') (i : Fin P.optimized.family.problem.cfg.compRows)
    {j : ℕ} (hj : compColRound j = 0) :
    (P.computeBaseEnv Qc i).traceNext j = (P.computeBaseEnv Qc' i).traceNext j :=
  envOfTrace_traceNext_congr ((preZAgreeOn_compCC_iff P Qc Qc').1 hag) _ _ _ _ hj

variable (P)

/-- **The compute-side structure of the committed trace**: per row, selectors `0..10`,
certificate block `202..270`, carrier `S` (col `302`). -/
def preZComputeStructure (Qc : Fin P.computeChip.rap.w → F[X]) :
    Fin P.optimized.family.problem.cfg.compRows → PreZComputeRow F :=
  preZComputeRows P.optimized.orbit.ω P.optimized.computeNodes P.optimized.computeChallenge
    P.optimized.computePublic Qc

/-- **The compute-side structure is pre-`z`.** -/
theorem preZComputeStructure_preZReads : PreZReadsFnOn (compCC P) (preZComputeStructure P) :=
  (preZReadsFnOn_compCC_iff P _).2 (preZComputeRows_preZReadsC _ _ _ _)

theorem rowEnv_source_trace_congr {Qc Qc' : Fin P.computeChip.rap.w → F[X]}
    (hag : PreZAgreeOn (compCC P) Qc Qc') (i : Fin P.optimized.family.problem.cfg.compRows)
    {j : ℕ} (hj3 : j < 303) (hj : compColRound j = 0) :
    (rowEnv P Qc i).toSourceEnv.trace j = (rowEnv P Qc' i).toSourceEnv.trace j :=
  sourceEnv_trace_congr (K := K) P.optimized.basis ((preZAgreeOn_compCC_iff P Qc Qc').1 hag) _ _ _
    _ hj3 hj

/-- `decodeSource` passes the selectors `0..10` through unchanged (`computeTraceSubst`). -/
theorem decodeSource_trace_sel (env : CorrectedFinalTypedEnv F K) {j : ℕ} (hj : j < 11) :
    (decodeSource env).trace j = env.toSourceEnv.trace j := by
  simp [decodeSource, Env.ofSubst, computeSubst, computeTraceSubst, hj, Expr.eval]

theorem decodeSource_sel_congr {Qc Qc' : Fin P.computeChip.rap.w → F[X]}
    (hag : PreZAgreeOn (compCC P) Qc Qc') (i : Fin P.optimized.family.problem.cfg.compRows)
    {j : ℕ} (hj : j < 11) :
    (decodeSource (rowEnv P Qc i)).trace j = (decodeSource (rowEnv P Qc' i)).trace j := by
  rw [decodeSource_trace_sel _ hj, decodeSource_trace_sel _ hj]
  exact rowEnv_source_trace_congr P hag i (by omega) (compColRound_base (by omega))

/-- **The decoded compute state is pre-`z`** (selectors `1..10` through `computeStateOf`). -/
theorem computeState_preZReads (i : Fin P.optimized.family.problem.cfg.compRows) :
    PreZReadsFnOn (compCC P)
      (fun Qc : Fin P.computeChip.rap.w → F[X] => computeStateOf (decodeSource (rowEnv P Qc i))) := by
  intro Qc Qc' hag
  have e : ∀ j, j < 11 → (decodeSource (rowEnv P Qc i)).trace j =
      (decodeSource (rowEnv P Qc' i)).trace j := fun j hj => decodeSource_sel_congr P hag i hj
  simp only [computeStateOf, e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
    e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega),
    e 10 (by omega)]

/-- The tree shape (`fanoutComp` of the decoded state) is pre-`z`. -/
theorem computeFanout_preZReads (i : Fin P.optimized.family.problem.cfg.compRows) :
    PreZReadsFnOn (compCC P)
      (fun Qc : Fin P.computeChip.rap.w → F[X] =>
        fanoutComp (computeStateOf (decodeSource (rowEnv P Qc i)))) := by
  intro Qc Qc' hag
  exact congrArg fanoutComp (computeState_preZReads P i Qc Qc' hag)

/-- **The request activity masks are pre-`z`** (`sampledActive` reads selectors `0, 2, 5..9`). -/
theorem activeMask_preZReads (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3) :
    PreZReadsFnOn (compCC P)
      (fun Qc : Fin P.computeChip.rap.w → F[X] => activeMask (rowEnv P Qc i) j) := by
  intro Qc Qc' hag
  have e : ∀ c, c < 13 → (rowEnv P Qc i).toSourceEnv.trace c =
      (rowEnv P Qc' i).toSourceEnv.trace c :=
    fun c hc => rowEnv_source_trace_congr P hag i (by omega) (compColRound_base hc)
  fin_cases j <;>
    simp [activeMask, sampledActive, Expr.eval, e 0 (by omega), e 2 (by omega), e 5 (by omega),
      e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega)]

/-- The row arity (`3` if slot `2` is active, `2` if slot `1`, else `1`) is pre-`z`. -/
theorem rowArity_preZReads (i : Fin P.optimized.family.problem.cfg.compRows) :
    PreZReadsFnOn (compCC P)
      (fun Qc : Fin P.computeChip.rap.w → F[X] => rowArity (rowEnv P Qc i)) := by
  intro Qc Qc' hag
  show rowArity _ = rowArity _
  have e2 : activeMask (rowEnv P Qc i) 2 = activeMask (rowEnv P Qc' i) 2 :=
    activeMask_preZReads P i 2 Qc Qc' hag
  have e1 : activeMask (rowEnv P Qc i) 1 = activeMask (rowEnv P Qc' i) 1 :=
    activeMask_preZReads P i 1 Qc Qc' hag
  unfold rowArity
  rw [e2, e1]

/-- **The prefix exponent `S(m) = Σ_{k<m} arity(k)` is pre-`z`.** -/
theorem prefixExp_preZReads (m : ℕ) :
    PreZReadsFnOn (compCC P) (fun Qc : Fin P.computeChip.rap.w → F[X] => prefixExp P Qc m) := by
  intro Qc Qc' hag
  show prefixExp P Qc m = prefixExp P Qc' m
  unfold prefixExp
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · exact rowArity_preZReads P ⟨k, hk⟩ Qc Qc' hag
  · rfl

/-- **The slot exponents `expOf i j = S(i) + j + 1` are pre-`z`**: route B's locator
`k ↦ (a, j)` reads only round-0 compute data. -/
theorem expOf_preZReads (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3) :
    PreZReadsFnOn (compCC P) (fun Qc : Fin P.computeChip.rap.w → F[X] => expOf P Qc i j) := by
  intro Qc Qc' hag
  have e : prefixExp P Qc i = prefixExp P Qc' i := prefixExp_preZReads P i Qc Qc' hag
  show prefixExp P Qc i + (j : ℕ) + 1 = prefixExp P Qc' i + (j : ℕ) + 1
  rw [e]

/-- The committed carrier `S` (column `302`) of every row is pre-`z`. -/
theorem expCol_preZReads (i : Fin P.optimized.family.problem.cfg.compRows) :
    PreZReadsFnOn (compCC P) (fun Qc : Fin P.computeChip.rap.w → F[X] => (rowEnv P Qc i).expCol) :=
  fun _ _ hag => typedEnv_expCol_congr (K := K) P.optimized.basis
    ((preZAgreeOn_compCC_iff P _ _).1 hag) _ _ _ _

/-- The certificate base block (`202..295`) of every row is pre-`z`. -/
theorem certBase_preZReads (i : Fin P.optimized.family.problem.cfg.compRows) :
    PreZReadsFnOn (compCC P)
      (fun Qc : Fin P.computeChip.rap.w → F[X] => (rowEnv P Qc i).certBase) :=
  fun _ _ hag => funext fun k => typedEnv_certBase_congr (K := K) P.optimized.basis
    ((preZAgreeOn_compCC_iff P _ _).1 hag) _ _ _ _ k

/-! ## §3  Positive control -/

/-- **A round-1 column is NOT pre-`z`**: the base-env read of `𝕂` role `0` (column `13`) at row
`0` separates two traces that agree on every round-0 column. -/
theorem not_preZReads_role0 :
    ¬ PreZReadsFnOn (compCC P)
      (fun Qc : Fin P.computeChip.rap.w → F[X] =>
        (P.computeBaseEnv Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).trace 13) := by
  classical
  intro hR
  have hw : (13 : ℕ) < P.computeChip.rap.w := by
    show 13 < 303; decide
  let Q : Fin P.computeChip.rap.w → F[X] := fun _ => 0
  let Q' : Fin P.computeChip.rap.w → F[X] := fun c => if (c : ℕ) = 13 then Polynomial.C 1 else 0
  have hag : PreZAgreeOn (compCC P) Q Q' := by
    rw [preZAgreeOn_compCC_iff]
    intro c hc
    have hne : (c : ℕ) ≠ 13 := by
      intro h13; rw [h13, compColRound_role0] at hc; exact one_ne_zero hc
    simp [Q, Q', hne]
  have := hR Q Q' hag
  simp [Q, Q', OptimizedFullStrictNockVMROMPackage.computeBaseEnv, envOfTrace, hw] at this

end Package

end

end Nock.NockVMROM.Thm54.PreZComputeCensus
