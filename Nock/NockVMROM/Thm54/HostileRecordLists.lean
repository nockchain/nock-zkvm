import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness

/-!
# The record lists a trace pair commits to, and the timestamp-collision event — upstream of the
capstone

* `OptimizedComputeHostileAccumulator.activeMask` / `rowRecord` / `rowRequests` — the records a
  compute row emits, hostilely: slot `j`'s decoded eight-scalar record exactly when its activity
  mask is `1` (the paper: "exactly the first `regs(op)` memory records are non-zero").
* `OptimizedMemoryHostileAccumulator.rowRecord` / `rowDenominator` / `rowResponseTerms` /
  `rowResponses` — the record a memory row serves, hostilely: its roles `19..26` exactly when
  `ver` (role `39`) is `1`.
* `OptimizedHostileTimestamps.TimestampCollisionEvent D` and its degree count
  `TimestampCollisionEvent_card_le : card ≤ 1 + D(D−1)/2`.

New here: the per-row length bounds `rowRequests_length_le : ≤ 3` and `rowResponses_length_le :
≤ 1`, which are what makes `|hostileRequests| ≤ 3·N` and `|hostileResponses| ≤ M` provable from
the list definitions for **every** trace, so the consumed bound can be stated at the row-count
majorants; and the closed-form numeral `timestampCollisionBound D = 1 + D(D−1)/2` with its
monotonicity, the α-summand's numerator.

The per-package lists `hostileRequests P Qc` / `hostileResponses P Qm` themselves are defined in
`OptimizedStrictFullPackage` (they need the package); the accumulator modules' definitions are
kept and are definitionally the same lists (`OptimizedHostileIOAssembly.hostileRecords_eq_package`).
-/

namespace Nock.NockVMROM.Thm54

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeCorrectedFinal
open OptimizedComputeSubstitution

noncomputable section

/-! ## A. The compute chip's per-row request list -/

namespace OptimizedComputeHostileAccumulator

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The activity mask of request slot `j`, as the selector-derived source decoder reads it
(`sampledActive`: slot `0` always, slot `1` for the two/three-record states, slot `2` for OP6/OP9). -/
def activeMask (env : CorrectedFinalTypedEnv F K) (j : Fin 3) : K :=
  (sampledActive .traceCur (j : ℕ)).eval env.toSourceEnv

def rowRecord (env : CorrectedFinalTypedEnv F K) (j : Fin 3) : Fin 10 → K :=
  fun c =>
    if (c : ℕ) = 9 then
      ((sampledSlotE .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace).eval
        env.toSourceEnv
    else if (c : ℕ) = 6 then
      ((sampledSlotT .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace).eval
        env.toSourceEnv
    else if (c : ℕ) = 8 then
      ((sampledSlotC .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace).eval
        env.toSourceEnv
    else
      ((computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).subst
        finalSampledNamespace).eval env.toSourceEnv

/-- The records a row emits, hostilely: slot `j`'s decoded record exactly when its activity mask is
`1` (the paper: "exactly the first `regs(op)` memory records are non-zero"). -/
def rowRequests [DecidableEq K] (env : CorrectedFinalTypedEnv F K) : List (Fin 10 → K) :=
  (List.finRange 3).filterMap fun j =>
    if activeMask env j = 1 then some (rowRecord env j) else none

/-- **A row emits at most three records** — one per request slot. -/
theorem rowRequests_length_le [DecidableEq K] (env : CorrectedFinalTypedEnv F K) :
    (rowRequests env).length ≤ 3 :=
  (List.length_filterMap_le _ _).trans (by simp)

end OptimizedComputeHostileAccumulator

/-! ## B. The memory chip's per-row response list -/

namespace OptimizedMemoryHostileAccumulator

variable {F K : Type} [Field F] [Field K] [Algebra F K]

def rowRecord (envK : Env K) (envF : Env F) : Fin 10 → K :=
  fun c => if h : (c : ℕ) < 8 then envK.trace (19 + (c : ℕ))
    else if (c : ℕ) = 8 then envK.trace 57
    else algebraMap F K (envF.trace 181)

/-- The committed response denominator of a row: role `37`. -/
def rowDenominator (envK : Env K) : K := envK.trace 37

/-- The `(record, committed denominator)` pairs a row serves, hostilely: its record exactly when
`ver` (role `39`) is `1` (the paper: a row contributes iff `ver(i) = 1`). -/
def rowResponseTerms [DecidableEq K] (envK : Env K) (envF : Env F) :
    List ((Fin 10 → K) × K) :=
  if envK.trace 39 = 1 then [(rowRecord envK envF, rowDenominator envK)] else []

/-- The records a row serves, hostilely. -/
def rowResponses [DecidableEq K] (envK : Env K) (envF : Env F) : List (Fin 10 → K) :=
  (rowResponseTerms envK envF).map Prod.fst

/-- **A row serves at most one record**. -/
theorem rowResponses_length_le [DecidableEq K] (envK : Env K) (envF : Env F) :
    (rowResponses envK envF).length ≤ 1 := by
  unfold rowResponses rowResponseTerms
  split_ifs <;> simp

end OptimizedMemoryHostileAccumulator

/-! ## C. -/

namespace OptimizedHostileTimestamps

section Event

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

open Classical in
/-- **The timestamp collision event.**  The bases `α` for which two distinct exponents in `1..D`
give the same power — the coins under which two distinct request slots can share a committed
timestamp.  Contains `α = 0`. -/
def TimestampCollisionEvent (D : ℕ) : Finset K :=
  Finset.univ.filter (fun α : K =>
    ∃ e ∈ Finset.Icc 1 D, ∃ e' ∈ Finset.Icc 1 D, e < e' ∧ α ^ e = α ^ e')

omit [DecidableEq K] in
theorem mem_timestampCollisionEvent {D : ℕ} {α : K} :
    α ∈ TimestampCollisionEvent D ↔
      ∃ e ∈ Finset.Icc 1 D, ∃ e' ∈ Finset.Icc 1 D, e < e' ∧ α ^ e = α ^ e' := by
  simp [TimestampCollisionEvent]

omit [DecidableEq K] in
/-- Outside the event, powers with exponents in `1..D` are injective. -/
theorem pow_inj_of_not_collision {D : ℕ} {α : K} (hα : α ∉ TimestampCollisionEvent D)
    {e e' : ℕ} (he : 1 ≤ e) (heD : e ≤ D) (he' : 1 ≤ e') (he'D : e' ≤ D)
    (h : α ^ e = α ^ e') : e = e' := by
  by_contra hne
  apply hα
  rw [mem_timestampCollisionEvent]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨e, Finset.mem_Icc.mpr ⟨he, heD⟩, e', Finset.mem_Icc.mpr ⟨he', he'D⟩, hlt, h⟩
  · exact ⟨e', Finset.mem_Icc.mpr ⟨he', he'D⟩, e, Finset.mem_Icc.mpr ⟨he, heD⟩, hgt, h.symm⟩

open Polynomial in
/-- The event is `{0}` together with the roots of `X^d − 1`, `1 ≤ d ≤ D − 1`. -/
theorem timestampCollisionEvent_subset (D : ℕ) :
    TimestampCollisionEvent (K := K) D ⊆
      {0} ∪ (Finset.Icc 1 (D - 1)).biUnion (fun d => (nthRoots d (1 : K)).toFinset) := by
  intro α hα
  rw [mem_timestampCollisionEvent] at hα
  obtain ⟨e, he, e', he', hlt, heq⟩ := hα
  rw [Finset.mem_Icc] at he he'
  rw [Finset.mem_union, Finset.mem_singleton]
  by_cases h0 : α = 0
  · exact Or.inl h0
  · right
    rw [Finset.mem_biUnion]
    refine ⟨e' - e, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [Multiset.mem_toFinset, mem_nthRoots (by omega)]
    have hsplit : α ^ e' = α ^ e * α ^ (e' - e) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit] at heq
    have hne : α ^ e ≠ 0 := pow_ne_zero _ h0
    exact mul_left_cancel₀ hne (heq.symm.trans (mul_one _).symm)

open Polynomial in
/-- **`TimestampCollisionEvent_card_le` — the degree count.**  `card ≤ 1 + Σ_{d=1}^{D−1} d`: one
point for `α = 0` and, for each exponent gap `d`, the at most `d` roots of `X^d − 1`. -/
theorem TimestampCollisionEvent_card_le_sum (D : ℕ) :
    (TimestampCollisionEvent (K := K) D).card ≤ 1 + ∑ d ∈ Finset.Icc 1 (D - 1), d := by
  refine le_trans (Finset.card_le_card (timestampCollisionEvent_subset D)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.card_singleton]
  refine Nat.add_le_add_left ?_ 1
  refine le_trans Finset.card_biUnion_le ?_
  refine Finset.sum_le_sum fun d _ => ?_
  exact le_trans (Multiset.toFinset_card_le _) (card_nthRoots d 1)

/-- The closed form: `card ≤ 1 + D(D−1)/2`. -/
theorem TimestampCollisionEvent_card_le (D : ℕ) :
    (TimestampCollisionEvent (K := K) D).card ≤ 1 + D * (D - 1) / 2 := by
  refine le_trans (TimestampCollisionEvent_card_le_sum D) ?_
  have h : (∑ d ∈ Finset.Icc 1 (D - 1), d) = ∑ d ∈ Finset.range D, d := by
    rcases D with _ | D
    · simp
    · rw [Nat.add_sub_cancel]
      induction D with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
  rw [h, Finset.sum_range_id]

omit [DecidableEq K] in
theorem not_mem_event_of_le_orderOf {D : ℕ} {α : K} (hα0 : α ≠ 0) (hord : D ≤ orderOf α) :
    α ∉ TimestampCollisionEvent D := by
  intro h
  rw [mem_timestampCollisionEvent] at h
  obtain ⟨e, he, e', he', hlt, heq⟩ := h
  rw [Finset.mem_Icc] at he he'
  have hsplit : α ^ e' = α ^ e * α ^ (e' - e) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at heq
  have hne : α ^ e ≠ 0 := pow_ne_zero _ hα0
  have h1 : α ^ (e' - e) = 1 := mul_left_cancel₀ hne (heq.symm.trans (mul_one _).symm)
  exact pow_ne_one_of_lt_orderOf (by omega) (by omega) h1

end Event

/-! ### The α-summand's numerator, as a numeral -/

/-- `1 + D(D−1)/2` — the degree count of `TimestampCollisionEvent D`, as the numeral the consumed
bound carries (`OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound`). -/
def timestampCollisionBound (D : ℕ) : ℕ := 1 + D * (D - 1) / 2

theorem timestampCollisionBound_mono {D D' : ℕ} (h : D ≤ D') :
    timestampCollisionBound D ≤ timestampCollisionBound D' := by
  unfold timestampCollisionBound
  have : D * (D - 1) ≤ D' * (D' - 1) := Nat.mul_le_mul h (by omega)
  have := Nat.div_le_div_right (c := 2) this
  omega

/-- `2 · timestampCollisionBound D ≤ D² + 2`: the form the size majorants use, with no natural
division. -/
theorem two_mul_timestampCollisionBound_le (D : ℕ) :
    2 * timestampCollisionBound D ≤ D * D + 2 := by
  unfold timestampCollisionBound
  have h1 : 2 * (D * (D - 1) / 2) ≤ D * (D - 1) := Nat.mul_div_le _ _
  have h2 : D * (D - 1) ≤ D * D := Nat.mul_le_mul_left D (Nat.sub_le _ _)
  omega

theorem TimestampCollisionEvent_card_le_bound {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (D : ℕ) :
    (TimestampCollisionEvent (K := K) D).card ≤ timestampCollisionBound D :=
  TimestampCollisionEvent_card_le D

end OptimizedHostileTimestamps

end
end Nock.NockVMROM.Thm54
