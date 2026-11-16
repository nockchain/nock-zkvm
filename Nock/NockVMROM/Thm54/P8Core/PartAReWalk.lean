/-
  Nock/NockVMROM/Thm54/P8Core/PartAReWalk.lean

  R-T re-runs the memory walk at the timestamp coin `α`.

  Scope: `repartitionedChronology` and the parallel package; nothing here is about
  `deployedChronology`
-/
import Nock.WalkInGate
import Nock.WalkPrefix
import Nock.NockVMROM.Thm54.HostileRecordLists

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.PartAReWalk

open Nock Nock.Walk
open Polynomial

noncomputable section

section Abstract

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem gap_ne_of_not_collision (α : K) (M : ℕ)
    (hα : α ∉ OptimizedHostileTimestamps.TimestampCollisionEvent M)
    (e e' : ℕ) (he : 1 ≤ e) (hlt : e < e') (he' : e' ≤ M) : α ^ e' ≠ α ^ e := by
  intro heq
  apply hα
  rw [OptimizedHostileTimestamps.mem_timestampCollisionEvent]
  exact ⟨e, Finset.mem_Icc.mpr ⟨he, by omega⟩, e', Finset.mem_Icc.mpr ⟨by omega, he'⟩, hlt,
    heq.symm⟩

/-- The honest walk line `ln(i) = α^i`. -/
def lnOf (α : K) (i : ℕ) : K := α ^ i

/-- The honest walk count `count(i) = α^{kMem}·α^{Sf(i)}`. -/
def countOf (fo : ℕ → ℕ) (α : K) (kMem i : ℕ) : K := α ^ kMem * α ^ Sf fo i

/-- The honest queue inverse `walk_inv(i) = (count(i) − ln(i))⁻¹`. -/
def invOf (fo : ℕ → ℕ) (α : K) (kMem i : ℕ) : K := (countOf fo α kMem i - lnOf α i)⁻¹

/-- The forest full-BFT identity is the forest accepting identity at the in-gate seed. -/
theorem forestAccepts_of_isForestFullBFT {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {α : K} {kMem M : ℕ} (hbft : IsForestFullBFT cur chld' fo kMem M) :
    ForestAccepts cur chld' fo α ((nodeListP cur kMem).eval α) (α ^ kMem) M := by
  unfold ForestAccepts
  have h := congrArg (fun p : K[X] => p.eval α) hbft

  rw [h, forestQueueP_eval]

/-- Given the forest facts at the
decoded labels and the order premise at `α`, the honest columns satisfy all nine walk gates. -/
theorem walkCompleteness12 (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α : K)
    (kMem M : ℕ) (hk : 1 ≤ kMem) (hkM : kMem ≤ M)
    (hbft : IsForestFullBFT cur chld' fo kMem M)
    (htile : kMem + Sf fo M = M)
    (hvalid : BFSValidF kMem fo M)
    (hα : α ∉ OptimizedHostileTimestamps.TimestampCollisionEvent M) (_hα0 : α ≠ 0) :
    ∃ ln count acc inv : ℕ → K,
      WalkSatInGate cur chld' fo ln count acc α (α ^ kMem) kMem M ∧
      acc M = 0 ∧
      (∀ i, 1 ≤ i → i < M → inv i * (count i - ln i) = 1) ∧
      count M = ln M ∧
      (∀ i, ln i = lnOf α i) ∧ (∀ i, count i = countOf fo α kMem i) ∧
      (∀ i, acc i = accInGate cur chld' fo α (α ^ kMem) kMem i) ∧
      (∀ i, inv i = invOf fo α kMem i) := by
  have hM : 1 ≤ M := le_trans hk hkM
  have hw : WalkSatInGate cur chld' fo (lnOf α) (countOf fo α kMem)
      (fun k => accInGate cur chld' fo α (α ^ kMem) kMem k) α (α ^ kMem) kMem M := by
    refine
      { hpos := hM, kpos := hk, kle := hkM
        ln1 := by simp [lnOf]
        lnInc := fun i _ _ => by simp only [lnOf]; rw [pow_succ]; ring
        count1 := by simp only [countOf]; rw [Sf_one]
        countInc := fun i _ _ => by simp only [countOf]; rw [Sf_succ, pow_add]; ring
        accInit := ?_
        accStep := ?_ }
    · have hmin : (1 : ℕ) ⊓ kMem = 1 := min_eq_left hk
      have hnl : (nodeListP cur 1).eval α = cur 1 * α := by rw [nodeListP_eval]; simp
      have hsum : (∑ i ∈ Finset.Icc 1 1, childSum chld' fo α i) = childSum chld' fo α 1 := by
        simp
      simp only [accInGate, hmin, hnl, hsum, sub_self, zero_add]
      exact (childSum_scale_init chld' fo α (α ^ kMem)).symm
    · intro i _ _
      have h := accInGate_accStep cur chld' fo α (α ^ kMem) kMem i
      simp only [lnOf, countOf]
      exact h
  have hacc0 : accInGate cur chld' fo α (α ^ kMem) kMem M = 0 := by
    have h := walkSatInGate_completeness hw (forestAccepts_of_isForestFullBFT hbft)
    exact h
  have hne : ∀ i, 1 ≤ i → i < M → countOf fo α kMem i - lnOf α i ≠ 0 := by
    intro i hi1 hiM
    have hv := hvalid (i + 1) (by omega) (by omega)
    have hsub : i + 1 - 1 = i := by omega
    rw [hsub] at hv
    have hmono : Sf fo i ≤ Sf fo M := Sf_mono fo (by omega)
    have hle : kMem + Sf fo i ≤ M := by omega
    have h := gap_ne_of_not_collision α M hα i (kMem + Sf fo i) hi1 (by omega) hle
    intro h0
    apply h
    simp only [countOf, lnOf] at h0
    rw [pow_add]
    exact sub_eq_zero.mp h0
  refine ⟨lnOf α, countOf fo α kMem, fun k => accInGate cur chld' fo α (α ^ kMem) kMem k,
    invOf fo α kMem, hw, hacc0, ?_, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · intro i hi1 hiM
    simp only [invOf]
    exact inv_mul_cancel₀ (hne i hi1 hiM)
  · simp only [countOf, lnOf]
    rw [← pow_add, htile]

theorem queue_gate_fails_at_one {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {kMem M : ℕ}
    (hw : WalkSatInGate cur chld' fo ln count acc 1 ((1 : K) ^ kMem) kMem M) (h2 : 2 ≤ M)
    (inv : ℕ → K) : ¬ (∀ i, 1 ≤ i → i < M → inv i * (count i - ln i) = 1) := by
  intro hq
  have h := hq 1 le_rfl (by omega)
  rw [WalkSatInGate.count_closed hw 1 le_rfl (by omega),
    WalkSatInGate.ln_closed hw 1 le_rfl (by omega)] at h
  simp at h

/-- At `α = 1` with `2 ≤ M` the order premise itself fails (`1 ∈ TimestampCollisionEvent M`), so
`walkCompleteness12` is never applied there: the control and the premise agree. -/
theorem one_mem_collision (M : ℕ) (h2 : 2 ≤ M) :
    (1 : K) ∈ OptimizedHostileTimestamps.TimestampCollisionEvent M := by
  rw [OptimizedHostileTimestamps.mem_timestampCollisionEvent]
  exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, 2, Finset.mem_Icc.mpr ⟨by omega, h2⟩,
    by omega, by simp⟩

end Abstract

end

end Nock.NockVMROM.Thm54.PartAReWalk
