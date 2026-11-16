/-
  Nock/NockVMROM/Thm54/WalkTilingEvents.lean

  **Walk tiling events.**  The terminal queue-gate's priced events, read off a
  committed fanout column.  Compute: `{αc | αc^(1+Sf) = αc^h ∧ 1+Sf ≠ h}`.  Memory forest:
  `{αm | αm^(k+Sf) = αm^h ∧ k+Sf ≠ h}`.

  These are functions of the TRACE (the fanout column) and live in the consumed union beside
  the walk-root events.  Queue-validity needs no coin event.
-/
import Nock.Walk
import Nock.NockVM
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.WalkTilingEvents

open scoped Classical
open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents

noncomputable section

/-- Compute tiling bound at arity 3: `|1+Sf−h|+1 ≤ 2h+2`. -/
def computeTilingBound (N : ℕ) : ℕ := 2 * N + 2

/-- Memory tiling bound at arity 2: `|k+Sf−h|+1 ≤ k+h+1`; at `k ≤ M`, `h = M` this is `2M+1`. -/
def memoryTilingBound (M : ℕ) : ℕ := 2 * M + 1

section PowCard
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `#{α : α^d = 1} ≤ d` for `d ≥ 1`. -/
theorem card_nthRoots_one_le {d : ℕ} (hd : 0 < d) :
    (Finset.univ.filter (fun a : K => a ^ d = 1)).card ≤ d := by
  have hset : (Finset.univ.filter (fun a : K => a ^ d = 1)) =
      (nthRoots d (1 : K)).toFinset := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_nthRoots hd]
  rw [hset]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots d 1)

/-- `α^{i+d} = α^i` and `α ≠ 0` give `α^d = 1`. -/
theorem pow_eq_one_of_pow_add_eq {α : K} (hα : α ≠ 0) {i d : ℕ}
    (h : α ^ (i + d) = α ^ i) : α ^ d = 1 := by
  rw [pow_add] at h
  have hi : α ^ i ≠ 0 := pow_ne_zero i hα
  have : α ^ i * α ^ d = α ^ i * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel₀ hi this

/-- On `{α : α^a = α^b}` with `a ≠ b`, the set is inside `{0} ∪ {α : α^{|a-b|} = 1}`. -/
theorem pow_eq_pow_card_le {a b : ℕ} (hne : a ≠ b) :
    (Finset.univ.filter (fun x : K => x ^ a = x ^ b)).card ≤ (a - b) + (b - a) + 1 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hd : 0 < b - a := Nat.sub_pos_of_lt hlt
    have hsub : Finset.univ.filter (fun x : K => x ^ a = x ^ b) ⊆
        (Finset.univ.filter (fun x : K => x ^ (b - a) = 1)) ∪ {0} := by
      intro x hx
      have hx' : x ^ a = x ^ b := (Finset.mem_filter.mp hx).2
      obtain ⟨d, hd'⟩ : ∃ d, b = a + d := ⟨b - a, (Nat.add_sub_of_le (le_of_lt hlt)).symm⟩
      have hdab : b - a = d := by omega
      rw [hdab] at hd ⊢
      rw [hd'] at hx'
      by_cases hx0 : x = 0
      · exact Finset.mem_union_right _ (by simp [hx0])
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, pow_eq_one_of_pow_add_eq hx0 hx'.symm⟩)
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have := card_nthRoots_one_le (K := K) hd
    simp only [Finset.card_singleton]
    have : a - b = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
    omega
  · have hd : 0 < a - b := Nat.sub_pos_of_lt hgt
    have hsub : Finset.univ.filter (fun x : K => x ^ a = x ^ b) ⊆
        (Finset.univ.filter (fun x : K => x ^ (a - b) = 1)) ∪ {0} := by
      intro x hx
      have hx' : x ^ a = x ^ b := (Finset.mem_filter.mp hx).2
      obtain ⟨d, hd'⟩ : ∃ d, a = b + d := ⟨a - b, (Nat.add_sub_of_le (le_of_lt hgt)).symm⟩
      have hdab : a - b = d := by omega
      rw [hdab] at hd ⊢
      rw [hd'] at hx'
      by_cases hx0 : x = 0
      · exact Finset.mem_union_right _ (by simp [hx0])
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, pow_eq_one_of_pow_add_eq hx0 hx'⟩)
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have := card_nthRoots_one_le (K := K) hd
    simp only [Finset.card_singleton]
    have : b - a = 0 := Nat.sub_eq_zero_of_le (le_of_lt hgt)
    omega

end PowCard

/-! ## Compute tiling event (`αc`) -/

/-- Terminal-accepting coins on a non-tiling committed compute fanout column. -/
def computeTilingEvent {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (h : ℕ) : Finset (JointCoins K) :=
  Finset.univ.filter (fun ω : JointCoins K =>
    alphaC ω ^ (1 + Sf fo h) = alphaC ω ^ h ∧ 1 + Sf fo h ≠ h)

theorem mem_computeTilingEvent_iff {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (h : ℕ) (ω : JointCoins K) :
    ω ∈ computeTilingEvent fo h ↔
      alphaC ω ^ (1 + Sf fo h) = alphaC ω ^ h ∧ 1 + Sf fo h ≠ h := by
  simp [computeTilingEvent]

theorem computeTilingEvent_empty_of_tiling {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) {h : ℕ} (htile : 1 + Sf fo h = h) :
    computeTilingEvent (K := K) fo h = ∅ := by
  ext ω
  simp [computeTilingEvent, htile]

/-- `|1+Sf−h| ≤ 2h+1` at arity 3, so the fibre is `≤ 2h+2`. -/
theorem compute_overshoot_le {fo : ℕ → ℕ} (hfo : ∀ i, fo i ≤ 3) (h : ℕ) :
    (1 + Sf fo h - h) + (h - (1 + Sf fo h)) ≤ 2 * h + 1 := by
  have hSf : Sf fo h ≤ 3 * h := ComputeWalkRootEvents.Sf_le_three_mul hfo h
  omega

theorem card_computeTilingAlphas_le {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (hfo : ∀ i, fo i ≤ 3) (h : ℕ) :
    (Finset.univ.filter (fun a : K =>
      a ^ (1 + Sf fo h) = a ^ h ∧ 1 + Sf fo h ≠ h)).card ≤ computeTilingBound h := by
  by_cases htile : 1 + Sf fo h = h
  · have : (Finset.univ.filter (fun a : K =>
        a ^ (1 + Sf fo h) = a ^ h ∧ 1 + Sf fo h ≠ h)) = ∅ := by
      ext a
      simp [htile]
    rw [this]
    exact Nat.zero_le _
  · have hsub : Finset.univ.filter (fun a : K =>
        a ^ (1 + Sf fo h) = a ^ h ∧ 1 + Sf fo h ≠ h) ⊆
        Finset.univ.filter (fun a : K => a ^ (1 + Sf fo h) = a ^ h) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1⟩
    refine (Finset.card_le_card hsub).trans ?_
    refine (pow_eq_pow_card_le (K := K) htile).trans ?_
    have := compute_overshoot_le hfo h
    simp only [computeTilingBound]
    omega

theorem card_computeTilingEvent_le {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (hfo : ∀ i, fo i ≤ 3) (h : ℕ) :
    (computeTilingEvent (K := K) fo h).card ≤
      computeTilingBound h * Fintype.card K ^ 3 := by
  let bad : K → K × K → Finset K := fun _ _ =>
    Finset.univ.filter (fun a : K =>
      a ^ (1 + Sf fo h) = a ^ h ∧ 1 + Sf fo h ≠ h)
  have hω : computeTilingEvent (K := K) fo h =
      Finset.univ.filter (fun ω : JointCoins K => alphaC ω ∈ bad (gamma ω) ω.2) := by
    ext ω
    simp [computeTilingEvent, bad]
  rw [hω]
  exact card_filter_alphaC_le bad (computeTilingBound h)
    (fun _ _ => card_computeTilingAlphas_le fo hfo h)

/-! ## Memory tiling event (`αm`) -/

/-- Terminal-accepting coins on a non-tiling committed forest fanout column. -/
def memoryTilingEvent {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (k h : ℕ) : Finset (JointCoins K) :=
  Finset.univ.filter (fun ω : JointCoins K =>
    alphaM ω ^ (k + Sf fo h) = alphaM ω ^ h ∧ k + Sf fo h ≠ h)

theorem mem_memoryTilingEvent_iff {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (k h : ℕ) (ω : JointCoins K) :
    ω ∈ memoryTilingEvent fo k h ↔
      alphaM ω ^ (k + Sf fo h) = alphaM ω ^ h ∧ k + Sf fo h ≠ h := by
  simp [memoryTilingEvent]

theorem memoryTilingEvent_empty_of_tiling {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (k : ℕ) {h : ℕ} (htile : k + Sf fo h = h) :
    memoryTilingEvent (K := K) fo k h = ∅ := by
  ext ω
  simp [memoryTilingEvent, htile]

/-- `|k+Sf−h| ≤ k+h` at arity 2. -/
theorem memory_overshoot_le {fo : ℕ → ℕ} (hfo : ∀ i, fo i ≤ 2) (k h : ℕ) :
    (k + Sf fo h - h) + (h - (k + Sf fo h)) ≤ k + h := by
  have hSf : Sf fo h ≤ 2 * h := by
    unfold Sf
    calc ∑ i ∈ Finset.Icc 1 h, fo i ≤ ∑ _i ∈ Finset.Icc 1 h, 2 :=
          Finset.sum_le_sum fun i _ => hfo i
      _ = 2 * h := by simp [Finset.sum_const, Nat.card_Icc]; ring
  omega

theorem card_memoryTilingAlphas_le {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (hfo : ∀ i, fo i ≤ 2) (k h : ℕ) :
    (Finset.univ.filter (fun a : K =>
      a ^ (k + Sf fo h) = a ^ h ∧ k + Sf fo h ≠ h)).card ≤ k + h + 1 := by
  by_cases htile : k + Sf fo h = h
  · have : (Finset.univ.filter (fun a : K =>
        a ^ (k + Sf fo h) = a ^ h ∧ k + Sf fo h ≠ h)) = ∅ := by
      ext a
      simp [htile]
    rw [this]
    exact Nat.zero_le _
  · have hsub : Finset.univ.filter (fun a : K =>
        a ^ (k + Sf fo h) = a ^ h ∧ k + Sf fo h ≠ h) ⊆
        Finset.univ.filter (fun a : K => a ^ (k + Sf fo h) = a ^ h) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1⟩
    refine (Finset.card_le_card hsub).trans ?_
    refine (pow_eq_pow_card_le (K := K) htile).trans ?_
    have := memory_overshoot_le hfo k h
    omega

/-- A filter on the `αm` coordinate whose fibre over `(αc, γ, z)` has at most `d` elements. -/
theorem card_filter_alphaM_le {K : Type} [Fintype K] [DecidableEq K]
    (bad : Finset K) (d : ℕ) (hb : bad.card ≤ d) :
    (Finset.univ.filter (fun ω : JointCoins K => alphaM ω ∈ bad)).card ≤
      d * Fintype.card K ^ 3 := by
  have hsub : Finset.univ.filter (fun ω : JointCoins K => alphaM ω ∈ bad) ⊆
      (Finset.univ : Finset (K × K × K)).biUnion
        (fun t => bad.image (fun m => ((t.1, t.2.1), (m, t.2.2)))) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine Finset.mem_biUnion.mpr ⟨(ω.1.1, ω.1.2, ω.2.2), Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨ω.2.1, hω, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (fun _ _ => Finset.card_image_le.trans hb)).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring_nf
  exact le_rfl

theorem card_memoryTilingEvent_le {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (fo : ℕ → ℕ) (hfo : ∀ i, fo i ≤ 2) (k h : ℕ) (hk : k ≤ h) :
    (memoryTilingEvent (K := K) fo k h).card ≤
      memoryTilingBound h * Fintype.card K ^ 3 := by
  let bad : Finset K :=
    Finset.univ.filter (fun a : K =>
      a ^ (k + Sf fo h) = a ^ h ∧ k + Sf fo h ≠ h)
  have hω : memoryTilingEvent (K := K) fo k h =
      Finset.univ.filter (fun ω : JointCoins K => alphaM ω ∈ bad) := by
    ext ω
    simp [memoryTilingEvent, bad]
  rw [hω]
  refine card_filter_alphaM_le bad (memoryTilingBound h) ?_
  refine (card_memoryTilingAlphas_le fo hfo k h).trans ?_
  simp only [memoryTilingBound]
  omega

/-- Memory row state from the three selector columns (`StrategyOfTraces.memoryStateOf`). -/
def memRowStateOf {F : Type} [Zero F] [One F] [DecidableEq F] (E : Env F) : MemoryTable.MState :=
  if E.trace 0 = 1 then .decompose
  else if E.trace 1 = 1 then .halt
  else if E.trace 2 = 1 then .read_root
  else .verify_child

/-- Trace-only memory fanout, 1-indexed like `foOf`. -/
def foOfMem {F : Type} [Zero F] [One F] [DecidableEq F] {M : ℕ}
    (envs : Fin M → Env F) (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i - 1 < M then MemoryTable.fanoutMem (memRowStateOf (envs ⟨i - 1, h.2⟩)) else 0

theorem foOfMem_le_two {F : Type} [Zero F] [One F] [DecidableEq F] {M : ℕ}
    (envs : Fin M → Env F) (i : ℕ) : foOfMem envs i ≤ 2 := by
  unfold foOfMem
  split_ifs
  · cases memRowStateOf (envs ⟨i - 1, (by omega)⟩) <;> decide
  · exact Nat.zero_le _

end

end Nock.NockVMROM.Thm54.WalkTilingEvents
