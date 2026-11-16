/-
  Nock/NockVMROM/Thm54/P8Core/PartAColumnsToEnvs.lean

* `StagedVec colRound Q` — a prover strategy on the twelve-coin vector: every committed column
    `j` is a function of the coins sampled strictly before its block `colRound j`
    (`repartitionedChronology.sampledAfter`).  B0 columns are therefore constant
    (`staged_B0_const`).
  * `readsOn_of_colCongr₂` — the generic link: a bad set that depends on the two committed traces
    only through their columns of round `≤ s`, and on the coins directly only through `D`, is,
    as a function of the coin vector, `ReadsOn (D ∪ coinsBefore s)`.  For a coin `i` with
    `sampledAfter i = s` this is `cylinder_card_le`'s premise with `i ∉ dep`
    (`coinsBefore_sched`).
  * `truncQc` — a 309-column compute trace read at the landed 303 columns (the six walk columns
    `303..308` are block B2, and no consumed summand reads them; `trunc_base_trace`).
  * `computeSourceEnv_agree` / `memorySourceEnv_agree` / `memoryBaseEnv_agree` — **gap 1**: two
    traces agreeing on every column of round `≤ s` have row environments agreeing on every source
    index / `𝕂` role / base column of round `≤ s` (`srcRoundW`, `newMemoryRoleRound`,
    `newMemoryColRound`).  The environments' challenge and public fields are the package's fixed
    `computeChallenge` / `memoryChallenge`, not the coins: there is no coin dependence beyond the
    round map.
  * `memoryAdaptiveEnvs` / `computeAdaptiveEnvs` — L1's `AdaptiveEnvs` built from a staged
    strategy's committed columns, with `K_reads` / `F_reads` PROVED from the round maps.

  Scope: every statement here is about the repartitioned schedule and the parallel package; none
  is about `deployedChronology`.  -- the paper
-/
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.PartAStaged

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock.NockVMROM.Thm54.PartA12
open scoped Polynomial

noncomputable section

/-! ## 1. Staged strategies on the twelve-coin vector -/

/-- The repartitioned schedule as a function on the twelve coins. -/
abbrev sched (i : Fin 12) : ℕ := (repartitionedChronology.sampledAfter i : ℕ)

theorem sched_eq : sched = ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1] := by
  funext i; fin_cases i <;> rfl

/-- The coins sampled strictly before block `s`. -/
def coinsBefore (s : ℕ) : Finset (Fin 12) := Finset.univ.filter fun i => sched i < s

theorem coinsBefore_zero : coinsBefore 0 = ∅ := by decide
/-- Before block 1: exactly message M1 = `{αM, z, a, b, c, λ}`. -/
theorem coinsBefore_one : coinsBefore 1 = {2, 3, 6, 7, 8, 10} := by decide

/-- `priorCoords` of a coin is `coinsBefore` its own block. -/
theorem coinsBefore_sched (i : Fin 12) : priorCoords sched i = coinsBefore (sched i) := rfl

theorem not_mem_coinsBefore_sched (i : Fin 12) : i ∉ coinsBefore (sched i) := by
  simp [coinsBefore]

section Generic

variable {K : Type}

/-- **A staged prover strategy on the coin vector**: column `j` is a function of the coins sampled
strictly before its block `colRound j`. -/
def StagedVec {ι β : Type*} (colRound : ι → ℕ) (Q : (Fin 12 → K) → ι → β) : Prop :=
  ∀ j χ χ', (∀ i : Fin 12, sched i < colRound j → χ i = χ' i) → Q χ j = Q χ' j

/-- Agreement on the coins before block `s` gives agreement on every column of round `≤ s`. -/
theorem staged_agree {ι β : Type*} {colRound : ι → ℕ} {Q : (Fin 12 → K) → ι → β}
    (hst : StagedVec colRound Q) (s : ℕ) {χ χ' : Fin 12 → K}
    (h : ∀ i ∈ coinsBefore s, χ i = χ' i) : ∀ j, colRound j ≤ s → Q χ j = Q χ' j := by
  intro j hj
  apply hst j χ χ'
  intro i hi
  exact h i (by simp only [coinsBefore, Finset.mem_filter, Finset.mem_univ, true_and]; omega)

/-- **B0 columns are constant** (no coin is sampled before block 0). -/
theorem staged_B0_const {ι β : Type*} {colRound : ι → ℕ} {Q : (Fin 12 → K) → ι → β}
    (hst : StagedVec colRound Q) (χ χ' : Fin 12 → K) :
    ∀ j, colRound j = 0 → Q χ j = Q χ' j := fun j hj =>
  hst j χ χ' (fun i hi => absurd hi (by omega))

/-- **The generic column-to-coin link, two traces.**  If the bad set depends on the two committed
traces only through their columns of round `≤ s`, and on the coin vector directly only through
`D`, then along a staged strategy it is `ReadsOn (D ∪ coinsBefore s)`. -/
theorem readsOn_of_colCongr₂ {ι₁ β₁ ι₂ β₂ X : Type*}
    {colRound₁ : ι₁ → ℕ} {colRound₂ : ι₂ → ℕ}
    {Q₁ : (Fin 12 → K) → ι₁ → β₁} {Q₂ : (Fin 12 → K) → ι₂ → β₂}
    (hst₁ : StagedVec colRound₁ Q₁) (hst₂ : StagedVec colRound₂ Q₂) (s : ℕ)
    (D : Finset (Fin 12)) (Bad : (ι₁ → β₁) → (ι₂ → β₂) → (Fin 12 → K) → X)
    (hcol : ∀ q₁ q₁' q₂ q₂', (∀ j, colRound₁ j ≤ s → q₁ j = q₁' j) →
      (∀ j, colRound₂ j ≤ s → q₂ j = q₂' j) → Bad q₁ q₂ = Bad q₁' q₂')
    (hcoin : ∀ q₁ q₂, ReadsOn (C := K) D (Bad q₁ q₂)) :
    ReadsOn (C := K) (D ∪ coinsBefore s) (fun χ => Bad (Q₁ χ) (Q₂ χ) χ) := by
  intro χ χ' h
  have hp : ∀ i ∈ coinsBefore s, χ i = χ' i := fun i hi => h i (Finset.mem_union_right _ hi)
  show Bad (Q₁ χ) (Q₂ χ) χ = Bad (Q₁ χ') (Q₂ χ') χ'
  rw [hcol (Q₁ χ) (Q₁ χ') (Q₂ χ) (Q₂ χ') (staged_agree hst₁ s hp) (staged_agree hst₂ s hp)]
  exact hcoin _ _ χ χ' (fun j hj => h j (Finset.mem_union_left _ hj))

/-- **The B0 form**: an event depending on the two traces only through their B0 columns is the
same set along the whole staged strategy. -/
theorem const_of_colCongr₂ {ι₁ β₁ ι₂ β₂ X : Type*}
    {colRound₁ : ι₁ → ℕ} {colRound₂ : ι₂ → ℕ}
    {Q₁ : (Fin 12 → K) → ι₁ → β₁} {Q₂ : (Fin 12 → K) → ι₂ → β₂}
    (hst₁ : StagedVec colRound₁ Q₁) (hst₂ : StagedVec colRound₂ Q₂)
    (E : (ι₁ → β₁) → (ι₂ → β₂) → X)
    (hcol : ∀ q₁ q₁' q₂ q₂', (∀ j, colRound₁ j = 0 → q₁ j = q₁' j) →
      (∀ j, colRound₂ j = 0 → q₂ j = q₂' j) → E q₁ q₂ = E q₁' q₂')
    (χ χ' : Fin 12 → K) : E (Q₁ χ) (Q₂ χ) = E (Q₁ χ') (Q₂ χ') :=
  hcol _ _ _ _ (staged_B0_const hst₁ χ χ') (staged_B0_const hst₂ χ χ')

end Generic

/-! ## 2. Staging on the tuple (L3's `Staged12`) is staging on the vector -/

section TupleVec

variable {K F : Type} [Fintype K] [Fintype F]

theorem landedVec12_tuple12OfVec (x : Fin 12 → K) : landedVec12 (tuple12OfVec (F := F) x) = x :=
  (tuple12VecEquiv (K := K) (F := F)).right_inv x

theorem tuple12OfVec_landedVec12 (c : OptimizedProductionChallengeTuple12 K F) :
    tuple12OfVec (landedVec12 c) = c :=
  (tuple12VecEquiv (K := K) (F := F)).left_inv c

/-- `Staged12` (L3, design §5's `StagedTraces` half) is `StagedVec` of the vector form. -/
theorem stagedVec_of_staged12 {ι β : Type*} {colRound : ι → ℕ}
    {Q : OptimizedProductionChallengeTuple12 K F → ι → β} (h : Staged12 colRound Q) :
    StagedVec colRound (fun x => Q (tuple12OfVec x)) := by
  intro j χ χ' hχ
  apply h j
  intro i hi
  rw [landedVec12_tuple12OfVec, landedVec12_tuple12OfVec]
  exact hχ i hi

theorem staged12_of_stagedVec {ι β : Type*} {colRound : ι → ℕ}
    {Q : OptimizedProductionChallengeTuple12 K F → ι → β}
    (h : StagedVec colRound (fun x => Q (tuple12OfVec x))) : Staged12 colRound Q := by
  intro j c c' hc
  have := h j (landedVec12 c) (landedVec12 c') hc
  simpa only [tuple12OfVec_landedVec12] using this

/-- Counting over the tuple is counting over the coin vector. -/
theorem card_filter_tuple12 [DecidableEq K] (p : OptimizedProductionChallengeTuple12 K F → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card =
      (Finset.univ.filter fun x : Fin 12 → K => p (tuple12OfVec x)).card := by
  refine Finset.card_bij (fun c _ => landedVec12 c) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rwa [tuple12OfVec_landedVec12]
  · intro a _ b _ h
    have := congrArg (tuple12OfVec (F := F)) h
    rwa [tuple12OfVec_landedVec12, tuple12OfVec_landedVec12] at this
  · intro x hx
    refine ⟨tuple12OfVec x, ?_, landedVec12_tuple12OfVec x⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx

end TupleVec

/-! ## 3. Gap 1: committed columns → row environments, at the parallel package -/

/-- Compute **source index** → round at the repartitioned schedule (the landed decoder's layout,
`CorrectedFinalTypedEnv.toSourceEnv`, plus the two walk sources `303`/`306` of the 309 decoder):
`< 13` base (B0); `13..75` the `𝕂`-role `s − 13`; `202..295` Form R base (B0); `296`, `299` the
`H`/`T` helpers (B1); `302` the carrier `S` (B0); `303`, `306` the walk columns (B2); every other
index is the constant `0`. -/
def srcRoundW (s : ℕ) : ℕ :=
  if s < 13 then 0 else if s < 76 then newComputeRoleRound (s - 13)
  else if 202 ≤ s ∧ s < 296 then 0 else if s = 296 ∨ s = 299 then 1
  else if s = 303 ∨ s = 306 then 2 else 0

theorem newComputeRoleRound_eq (r : ℕ) :
    newComputeRoleRound r = if 32 ≤ r ∧ r ≤ 35 then 2 else if r < 58 then 1 else 2 := by
  unfold newComputeRoleRound
  by_cases h : 32 ≤ r ∧ r ≤ 35
  · have : r ∈ [32, 33, 34, 35] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
    simp [this, h]
  · have : r ∉ [32, 33, 34, 35] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
    simp [this, h]

/-- Every physical column a source index reads has round at most the source's round. -/
theorem physOf_round_le (j c : ℕ) (h : Unhosted309.physOf j c) :
    newComputeColRound c ≤ srcRoundW j := by
  unfold Unhosted309.physOf at h
  unfold newComputeColRound srcRoundW
  rw [newComputeRoleRound_eq, newComputeRoleRound_eq]
  split_ifs <;> omega

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem computeWidth303 : P.computeChip.rap.w = 303 := P.optimized.exact_chip_resources.1

/-- **A 309-column compute trace read at the landed 303 columns.**  The six appended walk columns
`303..308` (B2) are dropped; no consumed summand reads them. -/
def truncQc (Qc : Fin 309 → F[X]) : Fin P.computeChip.rap.w → F[X] :=
  fun j => Qc ⟨j, by have h1 := j.isLt; have h2 := computeWidth303 P; omega⟩

/-- Two 309 traces agree on every column of round `≤ s`. -/
def AgreeC309 (s : ℕ) (Qc Qc' : Fin 309 → F[X]) : Prop :=
  ∀ j : Fin 309, newComputeColRound j ≤ s → Qc j = Qc' j

/-- Two memory traces agree on every column of round `≤ s`. -/
def AgreeM (s : ℕ) (Qm Qm' : Fin P.memoryChip.rap.w → F[X]) : Prop :=
  ∀ j : Fin P.memoryChip.rap.w, newMemoryColRound j ≤ s → Qm j = Qm' j

/-- The base environment of a truncated trace, at a column of round `≤ s` (or any column
`≥ 303`, where both read `0`). -/
theorem trunc_base_trace {s : ℕ} {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 s Qc Qc')
    (ω x : F) (ch pb : ℕ → F) (c : ℕ) (hc : newComputeColRound c ≤ s ∨ 303 ≤ c) :
    (envOfTrace (truncQc P Qc) ω x ch pb).trace c =
      (envOfTrace (truncQc P Qc') ω x ch pb).trace c ∧
    (envOfTrace (truncQc P Qc) ω x ch pb).traceNext c =
      (envOfTrace (truncQc P Qc') ω x ch pb).traceNext c := by
  simp only [envOfTrace]
  by_cases hw : c < P.computeChip.rap.w
  · have h303 : c < 303 := by have := computeWidth303 P; omega
    have hr : newComputeColRound c ≤ s := by omega
    simp only [dif_pos hw]
    constructor <;> (congr 1; exact h _ hr)
  · simp only [dif_neg hw]
    exact ⟨trivial, trivial⟩

/-- The landed decoder's source trace reads exactly `physOf`'s physical columns (mirror of L2's
`src_trace_congr` for `gather309`). -/
theorem landed_src_trace_congr (b : Module.Basis (Fin 3) F K) {E₁ E₂ : Env F} (j : ℕ)
    (h : ∀ c, Unhosted309.physOf j c → E₁.trace c = E₂.trace c) :
    (gatherCorrectedFinalTypedEnv b E₁).toSourceEnv.trace j =
      (gatherCorrectedFinalTypedEnv b E₂).toSourceEnv.trace j := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv,
    correctedFinalExtCoordIndex]
  split_ifs <;>
    first
    | rfl
    | (rw [h j (by unfold Unhosted309.physOf; omega)])
    | (apply Finset.sum_congr rfl; intro k _
       rw [h _ (by unfold Unhosted309.physOf; have := k.isLt; omega)])
    | (rw [h _ (by unfold Unhosted309.physOf; omega)])

theorem landed_src_traceNext_congr (b : Module.Basis (Fin 3) F K) {E₁ E₂ : Env F} (j : ℕ)
    (h : ∀ c, Unhosted309.physOf j c → E₁.traceNext c = E₂.traceNext c) :
    (gatherCorrectedFinalTypedEnv b E₁).toSourceEnv.traceNext j =
      (gatherCorrectedFinalTypedEnv b E₂).toSourceEnv.traceNext j := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv,
    correctedFinalExtCoordIndex]
  split_ifs <;>
    first
    | rfl
    | (rw [h j (by unfold Unhosted309.physOf; omega)])
    | (apply Finset.sum_congr rfl; intro k _
       rw [h _ (by unfold Unhosted309.physOf; have := k.isLt; omega)])
    | (rw [h _ (by unfold Unhosted309.physOf; omega)])

/-- **Gap 1, compute.**  Two 309 traces agreeing on every column of round `≤ s` give typed source
environments (at ANY challenge / public maps, so also the family environments at any tuple) whose
source traces agree at every source index of round `≤ s`. -/
theorem computeSource_agree (b : Module.Basis (Fin 3) F K) {s : ℕ} {Qc Qc' : Fin 309 → F[X]}
    (h : AgreeC309 s Qc Qc') (ω x : F) (ch pb : ℕ → F) (j : ℕ) (hj : srcRoundW j ≤ s) :
    (gatherCorrectedFinalTypedEnv b (envOfTrace (truncQc P Qc) ω x ch pb)).toSourceEnv.trace j =
      (gatherCorrectedFinalTypedEnv b (envOfTrace (truncQc P Qc') ω x ch pb)).toSourceEnv.trace j ∧
    (gatherCorrectedFinalTypedEnv b (envOfTrace (truncQc P Qc) ω x ch pb)).toSourceEnv.traceNext j =
      (gatherCorrectedFinalTypedEnv b (envOfTrace (truncQc P Qc') ω x ch pb)).toSourceEnv.traceNext j := by
  have hc : ∀ c, Unhosted309.physOf j c → newComputeColRound c ≤ s ∨ 303 ≤ c :=
    fun c hc => Or.inl ((physOf_round_le j c hc).trans hj)
  exact ⟨landed_src_trace_congr b j fun c hc' => (trunc_base_trace P h ω x ch pb c (hc c hc')).1,
    landed_src_traceNext_congr b j fun c hc' => (trunc_base_trace P h ω x ch pb c (hc c hc')).2⟩

/-- The package's compute source environment of a truncated trace. -/
theorem computeSourceEnv_agree {s : ℕ} {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 s Qc Qc')
    (i : Fin P.optimized.family.problem.cfg.compRows) (j : ℕ) (hj : srcRoundW j ≤ s) :
    (P.computeSourceEnv (truncQc P Qc) i).trace j = (P.computeSourceEnv (truncQc P Qc') i).trace j ∧
      (P.computeSourceEnv (truncQc P Qc) i).traceNext j =
        (P.computeSourceEnv (truncQc P Qc') i).traceNext j :=
  computeSource_agree P P.optimized.basis h _ _ _ _ j hj

/-- **Gap 1, memory base.**  The base environment reads the physical column of the same index
(the source projection `projectTrace` is the column inclusion `Fin.castAdd`); its challenge and
public maps are the package's fixed ones. -/
theorem memoryBaseEnv_agree {s : ℕ} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (h : AgreeM P s Qm Qm')
    (i : Fin P.optimized.family.problem.cfg.memRows) (b : ℕ) (hb : newMemoryColRound b ≤ s) :
    (P.memoryBaseEnv Qm i).trace b = (P.memoryBaseEnv Qm' i).trace b ∧
      (P.memoryBaseEnv Qm i).traceNext b = (P.memoryBaseEnv Qm' i).traceNext b := by
  simp only [OptimizedFullStrictNockVMROMPackage.memoryBaseEnv, envOfTrace,
    OptimizedFullStrictNockVMROMPackage.memorySourceTrace, RAPPadding.projectTrace]
  split_ifs with hw
  · constructor <;> (congr 1; apply h; exact hb)
  · exact ⟨rfl, rfl⟩

theorem memorySourceTemplate_baseCols (b : Module.Basis (Fin 3) F K) :
    (OptimizedMemoryGateBasis.memorySourceTemplate b).baseCols = 6 := by
  simp [MonolithicRAP.ChipTemplate.baseCols, OptimizedMemoryGateBasis.memorySourceTemplate]
  rfl

/-- The three physical columns of memory `𝕂`-role `r` have round at most the role's. -/
theorem memoryRoleCols_round_le (r k : ℕ) (hk : k < 3) :
    newMemoryColRound (6 + 3 * r + k) ≤ newMemoryRoleRound r := by
  unfold newMemoryColRound
  have hd : (6 + 3 * r + k - 6) / 3 = r := by omega
  split_ifs with h1 h2 h3
  · omega
  · exact Nat.zero_le _
  · rw [hd]
  · exact Nat.zero_le _

/-- **Gap 1, memory `𝕂` roles.**  Two memory traces agreeing on every column of round `≤ s` give
gathered source environments agreeing on every `𝕂`-role of round `≤ s`. -/
theorem memorySourceEnv_agree {s : ℕ} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (h : AgreeM P s Qm Qm') (i : Fin P.optimized.family.problem.cfg.memRows) (r : ℕ)
    (hr : newMemoryRoleRound r ≤ s) :
    (P.memorySourceEnv Qm i).trace r = (P.memorySourceEnv Qm' i).trace r ∧
      (P.memorySourceEnv Qm i).traceNext r = (P.memorySourceEnv Qm' i).traceNext r := by
  simp only [OptimizedFullStrictNockVMROMPackage.memorySourceEnv, MonolithicRAP.gatherEnv,
    MonolithicRAP.ChipTemplate.col0, memorySourceTemplate_baseCols]
  constructor
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [(memoryBaseEnv_agree P h i _ ((memoryRoleCols_round_le r k k.isLt).trans hr)).1]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [(memoryBaseEnv_agree P h i _ ((memoryRoleCols_round_le r k k.isLt).trans hr)).2]

/-! ### L1's `AdaptiveEnvs`, built from a staged strategy's committed columns -/

/-- **Gap 1, memory: the adaptive memory environments of a staged strategy.**  `K_reads` and
`F_reads` are PROVED from the round map (`memorySourceEnv_agree`, `memoryBaseEnv_agree`): a row
environment's role / base column depends on the coins only through those sampled before its
block. -/
def memoryAdaptiveEnvs (Qm : (Fin 12 → K) → Fin P.memoryChip.rap.w → F[X])
    (hst : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) Qm) :
    AdaptiveEnvs 12 P.optimized.family.problem.cfg.memRows K F where
  roleRound := newMemoryRoleRound
  baseRound := newMemoryColRound
  sampledAfter := sched
  envK χ := P.memorySourceEnv (Qm χ)
  envF χ := P.memoryBaseEnv (Qm χ)
  K_reads r χ χ' h i := (memorySourceEnv_agree P (staged_agree hst _ (fun j hj => h j (by
    simpa [coinsBefore] using hj))) i r le_rfl).1
  F_reads b χ χ' h i := (memoryBaseEnv_agree P (staged_agree hst _ (fun j hj => h j (by
    simpa [coinsBefore] using hj))) i b le_rfl).1

/-- **Gap 1, compute: the adaptive compute environments of a staged 309 strategy** (read at the
landed 303 columns), source-index rounds `srcRoundW`, base-column rounds `newComputeColRound`. -/
def computeAdaptiveEnvs (Qc : (Fin 12 → K) → Fin 309 → F[X])
    (hst : StagedVec (fun j : Fin 309 => newComputeColRound j) Qc) :
    AdaptiveEnvs 12 P.optimized.family.problem.cfg.compRows K F where
  roleRound := srcRoundW
  baseRound := newComputeColRound
  sampledAfter := sched
  envK χ := P.computeSourceEnv (truncQc P (Qc χ))
  envF χ := P.computeBaseEnv (truncQc P (Qc χ))
  K_reads r χ χ' h i := (computeSourceEnv_agree P (staged_agree hst _ (fun j hj => h j (by
    simpa [coinsBefore] using hj))) i r le_rfl).1
  F_reads b χ χ' h i := (trunc_base_trace P (staged_agree hst _ (fun j hj => h j (by
    simpa [coinsBefore] using hj))) _ _ _ _ b (Or.inl le_rfl)).1

end Package

end

end Nock.NockVMROM.Thm54.PartAStaged
