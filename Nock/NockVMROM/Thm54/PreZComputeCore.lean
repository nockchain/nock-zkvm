/-
  Nock/NockVMROM/Thm54/PreZComputeCore.lean

  This module is that
  compute twin, at the B1 column → round map of `DeployedStaging`.

  * **§1 — the B1 compute round map, copied verbatim** as `compRoleRound` / `compColRound`.
  * **§2 — the predicate.**  `PreZAgreeOnC Q Q'`: two compute column assignments of any width
    agree on every column whose B1 round is `0`; `PreZReadsC f`: `f` is invariant under it.  The
    width is a parameter, so the same predicate reads `P.computeChip`'s columns and the family
    chips' (`computeChipAt c`, whose width is not definitionally `303`, `computeChipAt_width`)
    with no `Fin.cast`.  At the package's staged view it IS `PreZAgreeOn (compCC P)`
    (`PreZComputeCensus.preZAgreeOn_compCC_iff`), the exact twin of `memCC`.
  * **§3 — the round-0 compute columns are exactly** the base block `0..12` (selectors `0..10`,
    the two masks), the Form R certificate base block `202..295` and the carrier `S` (`302`)
    (`compColRound_eq_zero_iff`); every `𝕂` role (`13..201`) and the helper block `296..301`
    are round `≥ 1`.
  * **§4 — the environments.**  `envOfTrace` and the gathered typed environment
    (`gatherCorrectedFinalTypedEnv`) read pre-`z` data on those columns: selectors
    (`baseTrace` / `baseTraceNext`), certificate base (`certBase` / `certBaseNext`), carrier
    (`expCol` / `expColNext`), and the source environment's `trace` on the same indices.
  * **§5 — the compute-side structure of the built skeleton.**  `PreZComputeRow`: selectors
    `0..10`, the certificate block `202..270` and `S`, per row; `preZComputeRows` over the trace
    domain is `PreZReadsC` (`preZComputeRows_preZReadsC`).  Positive control: a round-1 column
    (`𝕂` role `0`, column `13`) is NOT `PreZReadsC` (`not_preZReadsC_role0`).
  * **§6 — the served lookup.**  `servedNounOfEnvs`: the pre-`z` decoded noun of the first memory
    row in state `st` whose committed `reqIdx` names exponent `k` (`RecordCarrier.natLift`), the
    read-set skeleton of route B's served decomposition (C2 may refine it); its env read set is
    the memory base columns `0, 1, 2, 180, 181` (`servedNounOfEnvs_congr`).
-/
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.Framework.NockInstances

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.PreZComputeCore

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Module

noncomputable section

/-! ## §1  The B1 compute round map (a verbatim copy of `DeployedStaging`'s)

`PreZComputeCensus.compColRound_eq` proves the copy equal to the original
(`rfl`). -/

/-- Compute `𝕂`-role → round (roles `0..62`, physical columns `13 + 3r + k`); verbatim
`DeployedStaging.computeRoleRound`. -/
def compRoleRound (r : ℕ) : ℕ :=
  if r ∈ [6, 7, 9, 10, 18, 19, 27, 28, 32, 33, 34, 35] then 2
  else if r < 54 then 1
  else if r = 54 ∨ r = 55 then 2
  else if r = 56 ∨ r = 57 then 1
  else 2

/-- Compute physical column → round; verbatim `DeployedStaging.computeColRound`. -/
def compColRound (c : ℕ) : ℕ :=
  if c < 13 then 0
  else if c < 202 then compRoleRound ((c - 13) / 3)
  else if c < 296 then 0
  else if c < 302 then 2
  else 0

/-! ## §2  The predicate -/

section Generic

variable {w : ℕ} {α β γ : Type*}

/-- **The compute twin of `PreZAgreeOn`**: `Q`, `Q'` agree on every compute column of B1 round
`0` (the columns committed before `z, a, b, c` are sampled). -/
def PreZAgreeOnC (Q Q' : Fin w → α) : Prop :=
  ∀ c : Fin w, compColRound c = 0 → Q c = Q' c

/-- A function of the compute columns reads only pre-`z` data. -/
def PreZReadsC (f : (Fin w → α) → β) : Prop :=
  ∀ Q Q', PreZAgreeOnC Q Q' → f Q = f Q'

theorem PreZAgreeOnC.refl (Q : Fin w → α) : PreZAgreeOnC Q Q := fun _ _ => rfl

theorem PreZAgreeOnC.symm {Q Q' : Fin w → α} (h : PreZAgreeOnC Q Q') : PreZAgreeOnC Q' Q :=
  fun c hc => (h c hc).symm

theorem PreZAgreeOnC.trans {Q Q' Q'' : Fin w → α} (h : PreZAgreeOnC Q Q')
    (h' : PreZAgreeOnC Q' Q'') : PreZAgreeOnC Q Q'' :=
  fun c hc => (h c hc).trans (h' c hc)

theorem preZReadsC_const (b : β) : PreZReadsC (fun _ : Fin w → α => b) := fun _ _ _ => rfl

theorem PreZReadsC.comp {f : (Fin w → α) → β} (hf : PreZReadsC f) (g : β → γ) :
    PreZReadsC (fun Q => g (f Q)) := fun Q Q' h => by
  show g (f Q) = g (f Q'); rw [hf Q Q' h]

theorem PreZReadsC.pair {f : (Fin w → α) → β} {g : (Fin w → α) → γ} (hf : PreZReadsC f)
    (hg : PreZReadsC g) : PreZReadsC (fun Q => (f Q, g Q)) := fun Q Q' h => by
  show (f Q, g Q) = (f Q', g Q'); rw [hf Q Q' h, hg Q Q' h]

/-- A function reading only a set `D` of round-0 columns is `PreZReadsC`. -/
theorem preZReadsC_of_readsOnly (D : Finset (Fin w)) (hD : ∀ c ∈ D, compColRound c = 0)
    (f : (Fin w → α) → β) (hf : ∀ Q Q' : Fin w → α, (∀ c ∈ D, Q c = Q' c) → f Q = f Q') :
    PreZReadsC f :=
  fun Q Q' h => hf Q Q' fun c hc => h c (hD c hc)

/-- A pair of `PreZAgreeOnC` tuples separated by `f` refutes `PreZReadsC f`. -/
theorem not_preZReadsC_of_witness (f : (Fin w → α) → β) (Q Q' : Fin w → α)
    (hag : PreZAgreeOnC Q Q') (hne : f Q ≠ f Q') : ¬ PreZReadsC f :=
  fun h => hne (h Q Q' hag)

end Generic

/-! ## §3  Which compute columns are round `0` -/

theorem compRoleRound_pos (r : ℕ) : 0 < compRoleRound r := by
  unfold compRoleRound; split_ifs <;> omega

/-- **The round-0 compute columns** (width `303`): base `0..12`, certificate base `202..295`,
carrier `S = 302`.  Every `𝕂` role (`13..201`) and the helper block `296..301` is round `≥ 1`. -/
theorem compColRound_eq_zero_iff (c : ℕ) (hc : c < 303) :
    compColRound c = 0 ↔ c < 13 ∨ (202 ≤ c ∧ c < 296) ∨ c = 302 := by
  have hr : compRoleRound ((c - 13) / 3) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (compRoleRound_pos _)
  unfold compColRound
  by_cases h1 : c < 13
  · simp [h1]
  by_cases h2 : c < 202
  · have e1 : ¬ (202 ≤ c) := by omega
    have e2 : c ≠ 302 := by omega
    simp [h1, h2, hr, e1, e2]
  by_cases h3 : c < 296
  · have e1 : 202 ≤ c := by omega
    simp [h1, h2, h3, e1]
  by_cases h4 : c < 302
  · have e2 : c ≠ 302 := by omega
    simp [h1, h2, h3, h4, e2]
  · have e2 : c = 302 := by omega
    simp [e2]

theorem compColRound_base {c : ℕ} (hc : c < 13) : compColRound c = 0 := by
  unfold compColRound; simp [hc]

theorem compColRound_cert {c : ℕ} (h1 : 202 ≤ c) (h2 : c < 296) : compColRound c = 0 := by
  unfold compColRound
  have : ¬ c < 13 := by omega
  have : ¬ c < 202 := by omega
  simp [*]

theorem compColRound_S : compColRound 302 = 0 := by decide

/-- `𝕂` role `0` (column `13`) is round `1`: the positive control's column. -/
theorem compColRound_role0 : compColRound 13 = 1 := by decide

/-! ## §4  The environments read pre-`z` data on round-0 columns -/

section Env

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {w : ℕ}

theorem envOfTrace_trace_congr {Q Q' : Fin w → F[X]} (h : PreZAgreeOnC Q Q') (ω x : F)
    (chal pub : ℕ → F) {i : ℕ} (hi : compColRound i = 0) :
    (envOfTrace Q ω x chal pub).trace i = (envOfTrace Q' ω x chal pub).trace i := by
  simp only [envOfTrace]
  split_ifs with hlt
  · rw [h ⟨i, hlt⟩ hi]
  · rfl

theorem envOfTrace_traceNext_congr {Q Q' : Fin w → F[X]} (h : PreZAgreeOnC Q Q') (ω x : F)
    (chal pub : ℕ → F) {i : ℕ} (hi : compColRound i = 0) :
    (envOfTrace Q ω x chal pub).traceNext i = (envOfTrace Q' ω x chal pub).traceNext i := by
  simp only [envOfTrace]
  split_ifs with hlt
  · rw [h ⟨i, hlt⟩ hi]
  · rfl

variable (b : Basis (Fin 3) F K) {Q Q' : Fin w → F[X]} (h : PreZAgreeOnC Q Q') (ω x : F)
  (chal pub : ℕ → F)
include h

/-- The gathered typed environment of a compute row, at fixed point / challenges / publics. -/
abbrev typedEnvOf (Q : Fin w → F[X]) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv b (envOfTrace Q ω x chal pub)

theorem typedEnv_baseTrace_congr (i : Fin 13) :
    (typedEnvOf b ω x chal pub Q).baseTrace i = (typedEnvOf b ω x chal pub Q').baseTrace i :=
  envOfTrace_trace_congr h ω x chal pub (compColRound_base i.isLt)

theorem typedEnv_baseTraceNext_congr (i : Fin 13) :
    (typedEnvOf b ω x chal pub Q).baseTraceNext i =
      (typedEnvOf b ω x chal pub Q').baseTraceNext i :=
  envOfTrace_traceNext_congr h ω x chal pub (compColRound_base i.isLt)

theorem typedEnv_certBase_congr (i : Fin 94) :
    (typedEnvOf b ω x chal pub Q).certBase i = (typedEnvOf b ω x chal pub Q').certBase i :=
  envOfTrace_trace_congr h ω x chal pub (compColRound_cert (by omega) (by omega))

theorem typedEnv_certBaseNext_congr (i : Fin 94) :
    (typedEnvOf b ω x chal pub Q).certBaseNext i =
      (typedEnvOf b ω x chal pub Q').certBaseNext i :=
  envOfTrace_traceNext_congr h ω x chal pub (compColRound_cert (by omega) (by omega))

theorem typedEnv_expCol_congr :
    (typedEnvOf b ω x chal pub Q).expCol = (typedEnvOf b ω x chal pub Q').expCol :=
  envOfTrace_trace_congr h ω x chal pub compColRound_S

theorem typedEnv_expColNext_congr :
    (typedEnvOf b ω x chal pub Q).expColNext = (typedEnvOf b ω x chal pub Q').expColNext :=
  envOfTrace_traceNext_congr h ω x chal pub compColRound_S

/-- The source environment (what every compute decoder evaluates `Expr`s in) reads pre-`z` data on
every round-0 index (`toSourceEnv` sends `i < 13` to `baseTrace`, `202 ≤ i < 296` to `certBase`,
`302` to `expCol`). -/
theorem sourceEnv_trace_congr {i : ℕ} (hi : i < 303) (h0 : compColRound i = 0) :
    (typedEnvOf b ω x chal pub Q).toSourceEnv.trace i =
      (typedEnvOf b ω x chal pub Q').toSourceEnv.trace i := by
  rcases (compColRound_eq_zero_iff i hi).1 h0 with h13 | ⟨h1, h2⟩ | h302
  · simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos h13]
    rw [typedEnv_baseTrace_congr b h ω x chal pub ⟨i, h13⟩]
  · have hn13 : ¬ i < 13 := by omega
    have hn76 : ¬ i < 76 := by omega
    simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_neg hn13, dif_neg hn76,
      dif_pos (And.intro h1 h2)]
    rw [typedEnv_certBase_congr b h ω x chal pub ⟨i - 202, by omega⟩]
  · subst h302
    simp only [CorrectedFinalTypedEnv.toSourceEnv]
    simp only [show ¬ (302 : ℕ) < 13 by decide, show ¬ (302 : ℕ) < 76 by decide,
      show ¬ ((202 : ℕ) ≤ 302 ∧ 302 < 296) by decide, dite_false, if_false,
      show ((302 : ℕ) = 296) = False by decide, show ((302 : ℕ) = 299) = False by decide,
      if_true]
    rw [typedEnv_expCol_congr b h ω x chal pub]

theorem sourceEnv_traceNext_congr {i : ℕ} (hi : i < 303) (h0 : compColRound i = 0) :
    (typedEnvOf b ω x chal pub Q).toSourceEnv.traceNext i =
      (typedEnvOf b ω x chal pub Q').toSourceEnv.traceNext i := by
  rcases (compColRound_eq_zero_iff i hi).1 h0 with h13 | ⟨h1, h2⟩ | h302
  · simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos h13]
    rw [typedEnv_baseTraceNext_congr b h ω x chal pub ⟨i, h13⟩]
  · have hn13 : ¬ i < 13 := by omega
    have hn76 : ¬ i < 76 := by omega
    simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_neg hn13, dif_neg hn76,
      dif_pos (And.intro h1 h2)]
    rw [typedEnv_certBaseNext_congr b h ω x chal pub ⟨i - 202, by omega⟩]
  · subst h302
    simp only [CorrectedFinalTypedEnv.toSourceEnv]
    simp only [show ¬ (302 : ℕ) < 13 by decide, show ¬ (302 : ℕ) < 76 by decide,
      show ¬ ((202 : ℕ) ≤ 302 ∧ 302 < 296) by decide, dite_false, if_false,
      show ((302 : ℕ) = 296) = False by decide, show ((302 : ℕ) = 299) = False by decide,
      if_true]
    rw [typedEnv_expColNext_congr b h ω x chal pub]

end Env

/-! ## §5  The compute-side structure of the built skeleton -/

@[ext]
structure PreZComputeRow (F : Type*) where
  sel : Fin 11 → F
  cert : Fin 69 → F
  S : F

/-- The pre-`z` structure of a compute row, read off its base environment. -/
def preZComputeRowOfEnv {F : Type*} (env : Env F) : PreZComputeRow F where
  sel i := env.trace i
  cert i := env.trace (202 + (i : ℕ))
  S := env.trace 302

section Rows

variable {F : Type*} [Field F] {w n : ℕ}

/-- The compute-side structure of the whole committed trace: row `i` at trace-domain point
`nodes i`, with the challenge / public maps fixed (they are not trace columns). -/
def preZComputeRows (ω : F) (nodes : Fin n → F) (chal pub : ℕ → F) (Q : Fin w → F[X]) :
    Fin n → PreZComputeRow F :=
  fun i => preZComputeRowOfEnv (envOfTrace Q ω (nodes i) chal pub)

/-- **The compute-side structure is pre-`z`**: selectors `0..10`, certificate block `202..270`
and `S` read only round-0 columns. -/
theorem preZComputeRows_preZReadsC (ω : F) (nodes : Fin n → F) (chal pub : ℕ → F) :
    PreZReadsC (preZComputeRows (w := w) ω nodes chal pub) := by
  intro Q Q' h
  funext i
  ext j
  · exact envOfTrace_trace_congr h ω _ chal pub
      (compColRound_base (by have := j.isLt; omega))
  · exact envOfTrace_trace_congr h ω _ chal pub
      (compColRound_cert (by omega) (by have := j.isLt; omega))
  · exact envOfTrace_trace_congr h ω _ chal pub compColRound_S

/-- **Positive control**: the value of `𝕂` role `0` (column `13`, round `1`) at a point is NOT
pre-`z` (width `303`, any point). -/
theorem not_preZReadsC_role0 (x : F) :
    ¬ PreZReadsC (fun Q : Fin 303 → F[X] => (Q ⟨13, by decide⟩).eval x) := by
  classical
  refine not_preZReadsC_of_witness _ (fun _ => 0)
    (fun c => if (c : ℕ) = 13 then Polynomial.C 1 else 0) ?_ ?_
  · intro c hc
    have hne : (c : ℕ) ≠ 13 := by
      intro h13; rw [h13, compColRound_role0] at hc; exact one_ne_zero hc
    simp [hne]
  · simp

end Rows

/-! ## §6  The served lookup (route B's served decomposition, read-set skeleton) -/

namespace Served

open Nock.MemoryTable
open Nock.NockVMROM.Thm54.PreSeedCensus

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ}

/-- The 1-indexed memory rows in state `st` whose committed `reqIdx` names exponent `k`. -/
def servedRowsOfEnvs (envs : Fin M → Env F) (hM : 0 < M) (st : MState) (k : ℕ) : List ℕ :=
  (List.range' 1 M).filter fun j =>
    decide ((preLblOfEnvs envs hM j).1 = st) &&
      decide (RecordCarrier.natLift (preReqIdxOfEnvs envs hM j) = k)

/-- **The served noun at exponent `k`**: the pre-`z` decoded noun (`preZNounOfEnvs`) of the first
row in state `st` whose `reqIdx` names `k`; `atom 0` if none.  This is the read-set skeleton of
route B's served decomposition (`f_t`, `f_th`, `f_tth` read off served rows by `reqIdx`,
`scratchpad/s3-scope` §3, option B); C2 may refine the choice rule, not the read set. -/
def servedNounOfEnvs (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (st : MState) (k : ℕ) : Noun :=
  match servedRowsOfEnvs envs hM st k with
  | [] => Noun.atom 0
  | j :: _ => preZNounOfEnvs K q kroots envs hM j

/-- The memory base columns the env-parametric pre-`z` decoder reads: selectors `0, 1, 2`,
`atom` (`180`), `reqIdx` (`181`). -/
def preZMemCols : List ℕ := [0, 1, 2, OptimizedMemoryGateBasis.atomCol,
  OptimizedMemoryGateBasis.reqIdxCol]

theorem preStateOfEnvs_congr {envs envs' : Fin M → Env F}
    (h : ∀ i, ∀ c ∈ preZMemCols, (envs i).trace c = (envs' i).trace c) (i : Fin M) :
    preStateOfEnvs envs i = preStateOfEnvs envs' i := by
  simp only [preStateOfEnvs, StrategyOfTraces.memoryStateOf,
    h i 0 (by simp [preZMemCols]), h i 1 (by simp [preZMemCols]), h i 2 (by simp [preZMemCols])]

theorem preLblOfEnvs_congr {envs envs' : Fin M → Env F}
    (h : ∀ i, ∀ c ∈ preZMemCols, (envs i).trace c = (envs' i).trace c) (hM : 0 < M) :
    preLblOfEnvs envs hM = preLblOfEnvs envs' hM := by
  funext j
  have ha : ∀ i, preAtomOfEnvs envs i = preAtomOfEnvs envs' i := fun i =>
    h i _ (by simp [preZMemCols])
  unfold preLblOfEnvs
  split_ifs <;> rw [preStateOfEnvs_congr h, ha]

theorem preReqIdxOfEnvs_congr {envs envs' : Fin M → Env F}
    (h : ∀ i, ∀ c ∈ preZMemCols, (envs i).trace c = (envs' i).trace c) (hM : 0 < M) :
    preReqIdxOfEnvs envs hM = preReqIdxOfEnvs envs' hM := by
  funext j
  unfold preReqIdxOfEnvs
  split_ifs <;> exact h _ _ (by simp [preZMemCols])

theorem preZNounOfEnvs_congr (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    {envs envs' : Fin M → Env F}
    (h : ∀ i, ∀ c ∈ preZMemCols, (envs i).trace c = (envs' i).trace c) (hM : 0 < M) :
    preZNounOfEnvs K q kroots envs hM = preZNounOfEnvs K q kroots envs' hM := by
  funext i
  unfold preZNounOfEnvs preFoOfEnvs
  rw [preLblOfEnvs_congr h hM]

/-- **The served lookup reads only the memory pre-`z` columns** `0, 1, 2, 180, 181`. -/
theorem servedNounOfEnvs_congr (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    {envs envs' : Fin M → Env F}
    (h : ∀ i, ∀ c ∈ preZMemCols, (envs i).trace c = (envs' i).trace c) (hM : 0 < M) :
    servedNounOfEnvs K q kroots envs hM = servedNounOfEnvs K q kroots envs' hM := by
  funext st k
  simp only [servedNounOfEnvs, servedRowsOfEnvs, preLblOfEnvs_congr h hM,
    preReqIdxOfEnvs_congr h hM, preZNounOfEnvs_congr K q kroots h hM]

/-- `reqTgtOfEnvs` (route B's target at a fixed `T`) reads only the same columns. -/
theorem reqTgtOfEnvs_congr {envs envs' : Fin M → Env F}
    (h : ∀ i, ∀ c ∈ preZMemCols, (envs i).trace c = (envs' i).trace c) (hM : 0 < M)
    (T : MState → ℕ → Noun) :
    reqTgtOfEnvs envs hM T = reqTgtOfEnvs envs' hM T := by
  unfold reqTgtOfEnvs
  rw [preLblOfEnvs_congr h hM, preReqIdxOfEnvs_congr h hM]

end Served

end

end Nock.NockVMROM.Thm54.PreZComputeCore
