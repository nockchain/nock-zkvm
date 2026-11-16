import Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.OptimizedCanonicalTraces
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
`OptimizedComputeHostileAccumulator` reads the compute chip's denominator pins hostilely: at every
row of any accepted trace the committed safe denominator of slot `j` is
`aⱼ · slotDenominator + (1 − aⱼ)`, where `slotDenominator` is `pole + RLC^γ(recordⱼ)` decoded from
the row's own columns.  Its telescoping theorems carry the **active-slot
pole-hit exclusion** `hpole` as a hypothesis — faithfully so, since with two active records both
hitting the pole the gate is `0 = 0` (`Batch271.double_pole_frees_step`).

This module is the bridge.  It is **additive** — no production definition moves.

* `canonical_slotDenominator`: at the gathered honest row, `slotDenominator … j` **is** the
  sampled witness's denominator `FiniteIO.compress coins (encRec mrⱼ)` of the row's `j`-th
  request register.  The proof is a footprint argument: the decoder expression reads only
  current-row trace columns `< 71` (base `0..12`, extension core roles `< 58`) and challenges
  `< 12` (`Expr.eval_eq_of_rowScoped`, the scope checked by `decide`), and on exactly those the
  gathered canonical row agrees with `exactFinalCurrentEnv` (`canonical_gather_base_current`,
  `canonical_gather_ext_core`, `canonical_gather_challenge`).
* `canonical_activeMask`: the same footprint argument for the activity masks, so at the honest
  row `aⱼ ∈ {0, 1}` is *known*, not derived from `hchar`.
* `canonical_slotDenominator_ne_zero` / `canonical_pole_excluded`: an active slot's record is in
  the sampled request list (`activeRequestRecords`, `derivedRequestIO`, `requests_eq`), and the
  package's sampled assignment carries `poleHitGood : pole ∉ IOPoleHitEvent records γ` — the
  completeness-side statement of the paper's `RLC^α(IO) − β ≠ 0`.  So the
  honest denominators are nonzero **and `hpole` is discharged at every package**.
* **`canonical_hostile_logUp_sums_agree (P)`**: `hostile_logUp_sums_agree`'s conclusion at the
  honest traces of **any** package, with **no** hypothesis — not even `hchar`, since the masks are
  boolean by inspection at the honest row.
* **`canonical_requests_eq_sum_over_records (P)`**: the record-form request identity
  (`hostile_requests_eq_sum_over_records`) at the honest trace, likewise hypothesis-free.
* §F73: `package73_logUp_sums_agree` — `Batch271.package73_logUp_sums_agree_of_pole` with
  `hpole` gone.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeCanonicalDenominator

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates
open OptimizedComputeSemanticRealization
open OptimizedComputeSameExecution
open OptimizedComputeSampledTrace
open OptimizedComputeCanonicalSatisfaction
open OptimizedComputeHostileAccumulator
open StrictExtension
open OptimizedStrictFullPackage
open MultiRootOptimizedAcceptance
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

/-! ## A. The read footprint of the slot decoders -/

/- The honest-row value is obtained through `canonical_rowRecord` (`OptimizedCanonicalHostileLists`)
and `slotDenominator_eq_compress` instead of a footprint argument. -/

/-- The activity masks read only the current-row selector columns. -/
theorem sampledActive_rowScoped (j : Fin 3) :
    (sampledActive .traceCur j).rowScoped 71 12 = true := by
  fin_cases j <;> decide


variable {F K : Type} [Field F]
  [Field K] [Algebra F K]

/-- Two typed environments agreeing on the current-row base columns, the extension core roles
`< 58` and the twelve challenges give the same value to every `rowScoped 71 12` source
expression. -/
theorem eval_eq_of_rowScoped_typed {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ q, a.baseTrace q = b.baseTrace q)
    (hext : ∀ r : Fin 63, (r : ℕ) < 58 → a.extTrace r = b.extTrace r)
    (hchal : ∀ q : Fin 12, a.chal q = b.chal q)
    (e : Expr) (he : e.rowScoped 71 12 = true) :
    e.eval a.toSourceEnv = e.eval b.toSourceEnv := by
  apply Expr.eval_eq_of_rowScoped he
  · intro n hn
    simp only [CorrectedFinalTypedEnv.toSourceEnv]
    by_cases h13 : n < 13
    · rw [dif_pos h13, dif_pos h13, hbase]
    · rw [dif_neg h13, dif_neg h13, dif_pos (by omega), dif_pos (by omega)]
      exact hext ⟨n - 13, by omega⟩ (by simp; omega)
  · intro n hn
    simp only [CorrectedFinalTypedEnv.toSourceEnv]
    rw [dif_pos hn, dif_pos hn, hchal]

/-! ## B. The gathered honest row agrees with the exact row on that footprint -/

section Deployed

variable [FiniteDimensional F K] [DecidableEq F]

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
    0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
      (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
        (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)

set_option maxHeartbeats 8000000

/-- The honest gathered compute row. -/
abbrev honestRow (i : Fin (rows P)) : CorrectedFinalTypedEnv F K :=
  rowEnv P (canonicalComputeTrace P) i

/-- The successor-free exact row of the package's own sampled assignment. -/
abbrev exactRow (i : Fin (rows P)) : CorrectedFinalTypedEnv F K :=
  exactFinalCurrentEnv P.optimized.sampled i

theorem honestRow_base (i : Fin (rows P)) (q : Fin 13) :
    (honestRow P i).baseTrace q = (exactRow P i).baseTrace q := by
  show (rowEnv P (canonicalComputeTrace P) i).baseTrace q =
    OptimizedComputeFinalTrace.finalBaseCell P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos i q
  unfold canonicalComputeTrace
  exact canonical_gather_base_current P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
      P.optimized.computePublic P.optimized.orbit i q

theorem honestRow_ext_core (i : Fin (rows P)) (r : Fin 63) (hr : (r : ℕ) < 58) :
    (honestRow P i).extTrace r = (exactRow P i).extTrace r := by
  have hc := canonical_gather_ext_core P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit i ⟨r, hr⟩
  have he : (exactRow P i).extTrace r =
      OptimizedComputeFinalTrace.coreExtensionValue (encodedRowAt P.optimized.sampled i)
        ⟨r, hr⟩ := by
    simp [exactRow, exactFinalCurrentEnv, exactFinalExtensionRow, hr]
  rw [he]
  show (rowEnv P (canonicalComputeTrace P) i).extTrace r = _
  unfold canonicalComputeTrace
  exact hc

theorem honestRow_chal (i : Fin (rows P)) (q : Fin 12) :
    (honestRow P i).chal q = (exactRow P i).chal q := by
  have hc := canonical_gather_challenge P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit
    P.optimized.computeChallengePins i q
  show (rowEnv P (canonicalComputeTrace P) i).chal q = exactFinalChallenge P.optimized.sampled q
  unfold canonicalComputeTrace
  exact hc

/-- Any `rowScoped 71 12` source expression evaluates the same on the gathered honest row and on
the exact row. -/
theorem honestRow_eval_eq (i : Fin (rows P)) (e : Expr) (he : e.rowScoped 71 12 = true) :
    e.eval (honestRow P i).toSourceEnv = e.eval (exactRow P i).toSourceEnv :=
  eval_eq_of_rowScoped_typed (honestRow_base P i) (honestRow_ext_core P i) (honestRow_chal P i)
    e he

/-! ## C. The slot denominators and masks at the honest row -/

/-- The `j`-th request register of compute row `i` of the package's execution. -/
abbrev requestRegister (i : Fin (rows P)) (j : Fin 3) : ComputeTable.MemRec K :=
  match j with
  | 0 => (P.optimized.family.problem.exec.computePubAt i).mr1
  | 1 => (P.optimized.family.problem.exec.computePubAt i).mr2
  | 2 => (P.optimized.family.problem.exec.computePubAt i).mr3

/-- The coins the gathered honest row reads are the package's sampled coins. -/
theorem honestRow_rowCoins (i : Fin (rows P)) :
    rowCoins (honestRow P i) = P.optimized.sampled.sampled.coins := by
  have h7 := OptimizedCanonicalHostileLists.honestRow_chal P i 7
  have h8 := OptimizedCanonicalHostileLists.honestRow_chal P i 8
  unfold rowCoins
  simp only [CorrectedFinalTypedEnv.toSourceEnv, show (7 : ℕ) < 12 by omega,
    show (8 : ℕ) < 12 by omega, dif_pos]
  have e7 : (honestRow P i).chal 7 = P.optimized.sampled.sampled.coins.gamma :=
    h7.trans (by simp [OptimizedCanonicalHostileLists.exactRow, exactFinalCurrentEnv,
      exactFinalChallenge])
  have e8 : (honestRow P i).chal 8 = P.optimized.sampled.sampled.coins.pole :=
    h8.trans (by simp [OptimizedCanonicalHostileLists.exactRow, exactFinalCurrentEnv,
      exactFinalChallenge])
  show (⟨(honestRow P i).chal 7, (honestRow P i).chal 8⟩ : FiniteIO.IOCoins K) = _
  rw [e7, e8]

/-- **`canonical_slotDenominator` (F-1-4).**  At the honest gathered compute row, the slot
denominator the hostile theorems quantify over **is** the sampled witness's compressed record
`pole + RLC^γ(encRecFormR mrⱼ)` at the package's sampled coins. -/
theorem canonical_slotDenominator
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F)
    (i : Fin (rows P)) (j : Fin 3)
    (hact : OptimizedComputeFormRDenoms.slotActive P.optimized.family i j = 1) :
    slotDenominator (honestRow P i) j =
      P.optimized.sampled.compress10
        (NockVM.encRecFormR (requestRegister P i j) P.optimized.family.problem.cfg.challenges.lam) := by
  rw [slotDenominator_eq_compress, honestRow_rowCoins]
  have h := OptimizedCanonicalHostileLists.canonical_rowRecord P hax hwidth i j hact
  simp only [OptimizedCanonicalHostileLists.honestRow] at h
  rw [SampledIOSameExecutionAssignment.compress10]
  exact congrArg _ h

/-- At the honest gathered compute row the activity masks are the opcode's request-arity masks:
slot `0` always, slot `1` iff the state emits two records, slot `2` iff three. -/
theorem canonical_activeMask (i : Fin (rows P)) (j : Fin 3) :
    activeMask (honestRow P i) j =
      match j with
      | 0 => 1
      | 1 => secondRequestMask (P.optimized.family.problem.exec.computePubAt i).state
      | 2 => thirdRequestMask (P.optimized.family.problem.exec.computePubAt i).state := by
  unfold activeMask
  rw [honestRow_eval_eq P i _ (sampledActive_rowScoped j)]
  exact exactFinalCurrentEnv_sampledActive P.optimized.sampled i j

/-- The honest masks are boolean by inspection — no characteristic hypothesis. -/
theorem canonical_activeMask_bool (i : Fin (rows P)) (j : Fin 3) :
    activeMask (honestRow P i) j = 0 ∨ activeMask (honestRow P i) j = 1 := by
  rw [canonical_activeMask]
  fin_cases j
  · exact Or.inr rfl
  · cases (P.optimized.family.problem.exec.computePubAt i).state <;>
      simp [secondRequestMask]
  · cases (P.optimized.family.problem.exec.computePubAt i).state <;>
      simp [thirdRequestMask]

/-- An active slot's register is one of the row's emitted request records
(`activeRequestRecords`: "exactly the first `regs(op)` memory records are non-zero",
the paper). -/
theorem requestRegister_mem_active (i : Fin (rows P)) (j : Fin 3)
    (hact : activeMask (honestRow P i) j = 1) :
    requestRegister P i j ∈
      NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i) := by
  rw [canonical_activeMask] at hact
  fin_cases j
  · cases hs : (P.optimized.family.problem.exec.computePubAt i).state <;>
      simp [requestRegister, NockVM.activeRequestRecords, hs]
  · cases hs : (P.optimized.family.problem.exec.computePubAt i).state <;>
      simp [hs, secondRequestMask] at hact <;>
      simp [requestRegister, NockVM.activeRequestRecords, hs]
  · cases hs : (P.optimized.family.problem.exec.computePubAt i).state <;>
      simp [hs, thirdRequestMask] at hact <;>
      simp [requestRegister, NockVM.activeRequestRecords, hs]

/-- The honest mask is the Form R slot-activity function. -/
theorem slotActive_of_activeMask (i : Fin (rows P)) (j : Fin 3)
    (hact : activeMask (honestRow P i) j = 1) :
    OptimizedComputeFormRDenoms.slotActive P.optimized.family i j = 1 := by
  rw [canonical_activeMask] at hact
  fin_cases j <;> exact hact

/-- An active slot's encoded register is in the sampled request list. -/
theorem encRec_requestRegister_mem (i : Fin (rows P)) (j : Fin 3)
    (hact : activeMask (honestRow P i) j = 1) :
    NockVM.encRecFormR (requestRegister P i j) P.optimized.family.problem.cfg.challenges.lam ∈
      P.optimized.sampled.sampled.records.requests := by
  rw [P.optimized.sampled.requests_eq, ExactExecution.derivedRequestIO,
    ExactExecution.rawRequests_eq_computeRows, List.mem_map]
  refine ⟨requestRegister P i j, ?_, rfl⟩
  rw [List.mem_flatMap]
  exact ⟨_, ExactExecution.computeRowAt_mem _ i, requestRegister_mem_active P i j hact⟩

/-- **The honest active denominators are nonzero.**  The package's sampled assignment carries
`poleHitGood : pole ∉ IOPoleHitEvent records γ` — the completeness-side form of the paper's
`RLC^α(IO) − β ≠ 0` for the emitted records. -/
theorem canonical_slotDenominator_ne_zero
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F)
    (i : Fin (rows P)) (j : Fin 3)
    (hact : activeMask (honestRow P i) j = 1) :
    slotDenominator (honestRow P i) j ≠ 0 := by
  rw [canonical_slotDenominator P hax hwidth i j (slotActive_of_activeMask P i j hact)]
  refine P.optimized.sampled.compress10_ne_zero ?_
  have h := encRec_requestRegister_mem P i j hact
  rwa [P.optimized.sampled.requests_eq] at h

/-- **`hpole` discharged at the honest trace of every package.** -/
theorem canonical_pole_excluded
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F) :
    ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnv P (canonicalComputeTrace P) i) j = 1 →
      slotDenominator (rowEnv P (canonicalComputeTrace P) i) j ≠ 0 :=
  fun i j hact => canonical_slotDenominator_ne_zero P hax hwidth i j hact

/-! ## D. The honest identities, hypothesis-free -/

variable [Fintype F] [DecidableEq F]

/-- The compute-side LogUp telescoping at the honest trace, with no hypothesis. -/
theorem canonical_requests_eq_sum_logUp
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    (honestRow P (lastRow P)).extensionPublic 2 =
      ∑ i : Fin (rows P), logUpRowTerm (honestRow P i) :=
  hostile_requests_eq_sum_logUp P (canonicalComputeTrace P)
    (canonicalComputeTrace_satisfies P hax hbasis hwidth)
    (canonical_activeMask_bool P) (canonical_pole_excluded P hax hwidth)

/-- The record-form request identity (`hostile_requests_eq_sum_over_records`) at the honest
trace: `requests = Σ_{r ∈ hostileRequests} (compress chipCoins r)⁻¹`, with no hypothesis. -/
theorem canonical_requests_eq_sum_over_records
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    (honestRow P (lastRow P)).extensionPublic 2 =
      ((hostileRequests P (canonicalComputeTrace P)).map
        fun r => (FiniteIO.compress (chipCoins P) r)⁻¹).sum := by
  rw [canonical_requests_eq_sum_logUp P hax hbasis hwidth, hostileRequests, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logUpRowTerm_eq_rowRequests P (canonicalComputeTrace P) i (canonical_activeMask_bool P i),
    rowCoins_const]
  rfl

/-- The memory side's fold-collision exclusion at the honest memory trace, from the package's own
`canonical_memory_collision_good` (`rowEnvK P Qm i = P.memorySourceEnv Qm i` is `rfl`). -/
theorem canonical_fold_excluded
    (i : Fin (OptimizedMemoryHostileAccumulator.rows P))
    (hinter : P.optimized.sampled.interPole ≠ 0) :
    OptimizedMemoryGateBasis.FoldCollisionExcluded
      (OptimizedMemoryHostileAccumulator.rowEnvK P (canonicalMemoryTrace P) i) :=
  (canonical_memory_collision_good P i hinter).1

/-- **`hostile_logUp_sums_agree` at the honest traces of any package, hypothesis-free.**  The
request-side LogUp sum read off the honest compute trace equals the response-side sum read off
the honest memory trace — `hchar`, `hpole` and `hfold` all discharged. -/
theorem canonical_hostile_logUp_sums_agree
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    (∑ i : Fin (rows P), logUpRowTerm (rowEnv P (canonicalComputeTrace P) i)) =
      ∑ i : Fin (OptimizedMemoryHostileAccumulator.rows P),
        OptimizedMemoryHostileAccumulator.memRowTerm
          (OptimizedMemoryHostileAccumulator.rowEnvK P (canonicalMemoryTrace P) i) := by
  rw [← OptimizedMemoryHostileAccumulator.hostile_requests_public_eq_sum_memRowTerms P
      (canonicalMemoryTrace P) (canonicalMemoryTrace_satisfies P hmore hC),
    ← OptimizedMemoryHostileAccumulator.compute_requests_eq_memory_requests P,
    ← gathered_requests P (canonicalComputeTrace P) (lastRow P)]
  exact (canonical_requests_eq_sum_logUp P hax hbasis hwidth).symm

end Deployed

/-! ## F73.

`Batch271.package73_logUp_sums_agree_of_pole` left `hpole` open at the honest F73 traces
(F-1-4).  This is that theorem with no hypothesis — a **fixture instance** of
`canonical_hostile_logUp_sums_agree`, nothing more; the generic theorem above is the result. -/

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildableConcrete
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

variable (hmore73 : BuildableAxisWitness.LaterSeedZeros (F := F73) (K := K73cubic)
  BuildableConcrete.concreteExecution)

/-- `hpole` at the honest F73 compute trace. -/
theorem package73_pole_excluded
    (hax : FormRAxisBound (package73 hmore73).optimized.sampled
      (package73 hmore73).optimized.basis)
    (hwidth : FormRWidth F73) :
    ∀ (i : Fin (rows (package73 hmore73))) (j : Fin 3),
      activeMask (rowEnv (package73 hmore73) (canonicalComputeTrace (package73 hmore73)) i) j = 1 →
      slotDenominator (rowEnv (package73 hmore73) (canonicalComputeTrace (package73 hmore73)) i) j ≠ 0 :=
  canonical_pole_excluded (package73 hmore73) hax hwidth

/-- **`Batch271.package73_logUp_sums_agree_of_pole` with `hpole` discharged**: at the honest F73
traces the two chips' LogUp sums agree, no hypothesis open. -/
theorem package73_logUp_sums_agree
    (hax : FormRAxisBound (package73 hmore73).optimized.sampled
      (package73 hmore73).optimized.basis)
    (hbasis : FormRBasis (package73 hmore73).optimized.basis)
    (hwidth : FormRWidth F73) :
    (∑ i : Fin (rows (package73 hmore73)),
        logUpRowTerm (rowEnv (package73 hmore73) (canonicalComputeTrace (package73 hmore73)) i)) =
      ∑ i : Fin (OptimizedMemoryHostileAccumulator.rows (package73 hmore73)),
        OptimizedMemoryHostileAccumulator.memRowTerm
          (OptimizedMemoryHostileAccumulator.rowEnvK (package73 hmore73)
            (canonicalMemoryTrace (package73 hmore73)) i) :=
  canonical_hostile_logUp_sums_agree (package73 hmore73) hax hbasis hwidth hmore73
    (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
      ConcreteStrictPackage.honestAlpha)

end F73

end
end OptimizedComputeCanonicalDenominator
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedComputeCanonicalDenominator.canonical_slotDenominator
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeCanonicalDenominator.canonical_activeMask
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeCanonicalDenominator.canonical_slotDenominator_ne_zero
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeCanonicalDenominator.canonical_pole_excluded
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeCanonicalDenominator.canonical_requests_eq_sum_over_records
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeCanonicalDenominator.canonical_hostile_logUp_sums_agree
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeCanonicalDenominator.package73_logUp_sums_agree
