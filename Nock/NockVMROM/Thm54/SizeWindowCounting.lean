import Mathlib.Algebra.Polynomial.Roots
import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.NockVMROM.Thm54.JointSoundness

/-!
# Counted size-window failures for the fixed semantic skeleton

OP3, OP4, and OP6 need a multiplicative-order window for one seed-independent noun.  Such a
window cannot hold at every nonzero seed because `orderOf (1 : K) = 1`.  This module records the
exact nonzero seeds where one of those fixed nouns fails its window and bounds them by the union of
the polynomial root sets `z ^ d = 1`, `1 ≤ d ≤ Λ`.
-/

namespace Nock.NockVMROM.Thm54.SizeWindowCounting

open scoped Classical BigOperators
open Nock
open Polynomial

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The one fixed noun whose size window is consumed in each relevant opcode row. -/
def requiredSizeWindowNouns
    (s : SemanticStrategy.ComputeRowSkeleton) : List Noun :=
  match s.state with
  | .s3 | .s4 => [P8Census.skeletonSubformula s 0 .result]
  | .s6 => [P8Census.skeletonSubformula s 1 .result]
  | _ => []

/-- All required size-window nouns, with chronology fixed by the pre-seed skeleton BFS order. -/
def skeletonSizeWindowNouns
    (S : SemanticStrategy.SemanticSkeleton) : List Noun :=
  (SemanticStrategy.computeSkeletonRows S).flatMap requiredSizeWindowNouns

/-- The explicit leaf bound used by the root count. -/
def SizeWindowNounsBoundedBy
    (S : SemanticStrategy.SemanticSkeleton) (Λ : ℕ) : Prop :=
  ∀ n ∈ skeletonSizeWindowNouns S, n.leaves ≤ Λ

/-- Exact nonzero seed filter where at least one required fixed noun lacks its size window.

The `z ≠ 0` conjunct keeps the existing zero-seed event separate. -/
def sizeWindowFailureSeeds
    (S : SemanticStrategy.SemanticSkeleton) : Finset K :=
  Finset.univ.filter fun z =>
    z ≠ 0 ∧ ∃ n ∈ skeletonSizeWindowNouns S,
      ¬ OpcodeSemantics.SizeWindow z n

@[simp] theorem mem_sizeWindowFailureSeeds_iff
    (S : SemanticStrategy.SemanticSkeleton) (z : K) :
    z ∈ sizeWindowFailureSeeds (K := K) S ↔
      z ≠ 0 ∧ ∃ n ∈ skeletonSizeWindowNouns S,
        ¬ OpcodeSemantics.SizeWindow z n := by
  simp [sizeWindowFailureSeeds]

/-- Fifth production event: lift the exact bad-seed filter while leaving the other three
challenges unrestricted. -/
def SizeWindowFailure
    (S : SemanticStrategy.SemanticSkeleton) : Finset (JointCoins K) :=
  liftSeed (sizeWindowFailureSeeds (K := K) S)

@[simp] theorem mem_SizeWindowFailure_iff
    (S : SemanticStrategy.SemanticSkeleton) (ω : JointCoins K) :
    ω ∈ SizeWindowFailure (K := K) S ↔
      nprSeed ω ≠ 0 ∧
        ∃ n ∈ skeletonSizeWindowNouns S,
          ¬ OpcodeSemantics.SizeWindow (nprSeed ω) n := by
  simp [SizeWindowFailure]

theorem s3_window_noun_mem
    (S : SemanticStrategy.SemanticSkeleton)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S)
    (hstate : s.state = .s3) :
    P8Census.skeletonSubformula s 0 .result ∈ skeletonSizeWindowNouns S := by
  rw [skeletonSizeWindowNouns, List.mem_flatMap]
  exact ⟨s, hs, by simp [requiredSizeWindowNouns, hstate]⟩

theorem s4_window_noun_mem
    (S : SemanticStrategy.SemanticSkeleton)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S)
    (hstate : s.state = .s4) :
    P8Census.skeletonSubformula s 0 .result ∈ skeletonSizeWindowNouns S := by
  rw [skeletonSizeWindowNouns, List.mem_flatMap]
  exact ⟨s, hs, by simp [requiredSizeWindowNouns, hstate]⟩

theorem s6_window_noun_mem
    (S : SemanticStrategy.SemanticSkeleton)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S)
    (hstate : s.state = .s6) :
    P8Census.skeletonSubformula s 1 .result ∈ skeletonSizeWindowNouns S := by
  rw [skeletonSizeWindowNouns, List.mem_flatMap]
  exact ⟨s, hs, by simp [requiredSizeWindowNouns, hstate]⟩

/-- **The bare-seed form of `windows_of_not_mem_SizeWindowFailure`.**

The counting is the same object either way —
`sizeWindowFailureSeeds` (`:45`) and `sizeWindowFailureSeeds_card_le` already exist at bare `z`;
only this projection was missing. -/
theorem windows_of_not_mem_sizeWindowFailureSeeds
    (S : SemanticStrategy.SemanticSkeleton)
    {z : K} (hz : z ≠ 0)
    (hout : z ∉ sizeWindowFailureSeeds (K := K) S)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S) :
    BoundSemanticTrace.SkeletonSizeWindowPremises z s where
  s3_window hstate := by
    by_contra hwindow
    exact hout ((mem_sizeWindowFailureSeeds_iff S z).mpr
      ⟨hz, _, s3_window_noun_mem S s hs hstate, hwindow⟩)
  s4_window hstate := by
    by_contra hwindow
    exact hout ((mem_sizeWindowFailureSeeds_iff S z).mpr
      ⟨hz, _, s4_window_noun_mem S s hs hstate, hwindow⟩)
  s6_window hstate := by
    by_contra hwindow
    exact hout ((mem_sizeWindowFailureSeeds_iff S z).mpr
      ⟨hz, _, s6_window_noun_mem S s hs hstate, hwindow⟩)

/-- Outside the exact event, the actual OP3/OP4/OP6 windows are available to local scheduling. -/
theorem windows_of_not_mem_SizeWindowFailure
    (S : SemanticStrategy.SemanticSkeleton)
    (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0)
    (hout : ω ∉ SizeWindowFailure (K := K) S)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S) :
    BoundSemanticTrace.SkeletonSizeWindowPremises (nprSeed ω) s where
  s3_window hstate := by
    by_contra hwindow
    apply hout
    rw [mem_SizeWindowFailure_iff]
    exact ⟨hz, P8Census.skeletonSubformula s 0 .result,
      s3_window_noun_mem S s hs hstate, hwindow⟩
  s4_window hstate := by
    by_contra hwindow
    apply hout
    rw [mem_SizeWindowFailure_iff]
    exact ⟨hz, P8Census.skeletonSubformula s 0 .result,
      s4_window_noun_mem S s hs hstate, hwindow⟩
  s6_window hstate := by
    by_contra hwindow
    apply hout
    rw [mem_SizeWindowFailure_iff]
    exact ⟨hz, P8Census.skeletonSubformula s 1 .result,
      s6_window_noun_mem S s hs hstate, hwindow⟩

/-! ## Polynomial root count -/

/-- Root-union over all positive exponents through `Λ`. -/
def lowOrderRootSeeds (Λ : ℕ) : Finset K :=
  (Finset.Icc 1 Λ).biUnion fun d => nthRootsFinset d (1 : K)

/-- The explicit triangular root-count numerator `∑_{d=1}^Λ d`. -/
def sizeWindowRootBound (Λ : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 Λ, d

theorem nthRootsFinset_card_le (d : ℕ) :
    (nthRootsFinset d (1 : K)).card ≤ d := by
  rw [nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots d 1)

theorem lowOrderRootSeeds_card_le (Λ : ℕ) :
    (lowOrderRootSeeds (K := K) Λ).card ≤ sizeWindowRootBound Λ := by
  calc
    (lowOrderRootSeeds (K := K) Λ).card
        ≤ ∑ d ∈ Finset.Icc 1 Λ, (nthRootsFinset d (1 : K)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Finset.Icc 1 Λ, d := by
      exact Finset.sum_le_sum fun d _ => nthRootsFinset_card_le d
    _ = sizeWindowRootBound Λ := rfl

theorem sizeWindowRootBound_le_square (Λ : ℕ) :
    sizeWindowRootBound Λ ≤ Λ * Λ := by
  calc
    sizeWindowRootBound Λ
        ≤ ∑ _d ∈ Finset.Icc 1 Λ, Λ := by
      apply Finset.sum_le_sum
      intro d hd
      exact (Finset.mem_Icc.mp hd).2
    _ = (Finset.Icc 1 Λ).card * Λ := by simp
    _ ≤ Λ * Λ := by
      exact Nat.mul_le_mul_right Λ (by simp)

theorem sizeWindowFailureSeeds_subset_lowOrderRootSeeds
    (S : SemanticStrategy.SemanticSkeleton) (Λ : ℕ)
    (hbound : SizeWindowNounsBoundedBy S Λ) :
    sizeWindowFailureSeeds (K := K) S ⊆ lowOrderRootSeeds (K := K) Λ := by
  intro z hzbad
  obtain ⟨hz, n, hn, hwindow⟩ :=
    (mem_sizeWindowFailureSeeds_iff S z).1 hzbad
  have hcard : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  have horderPos : 0 < orderOf z := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨Fintype.card K - 1, hcard,
      FiniteField.pow_card_sub_one_eq_one z hz⟩
  have horderLeN : orderOf z ≤ n.leaves := by
    by_contra hle
    have hnlt : n.leaves < orderOf z := Nat.lt_of_not_ge hle
    exact hwindow ⟨n.one_le_leaves.trans_lt hnlt, hnlt⟩
  have horderLe : orderOf z ≤ Λ :=
    horderLeN.trans (hbound n hn)
  rw [lowOrderRootSeeds, Finset.mem_biUnion]
  refine ⟨orderOf z, Finset.mem_Icc.mpr ⟨horderPos, horderLe⟩, ?_⟩
  rw [mem_nthRootsFinset horderPos]
  exact pow_orderOf_eq_one z

theorem sizeWindowFailureSeeds_card_le
    (S : SemanticStrategy.SemanticSkeleton) (Λ : ℕ)
    (hbound : SizeWindowNounsBoundedBy S Λ) :
    (sizeWindowFailureSeeds (K := K) S).card ≤ sizeWindowRootBound Λ :=
  (Finset.card_le_card
    (sizeWindowFailureSeeds_subset_lowOrderRootSeeds S Λ hbound)).trans
      (lowOrderRootSeeds_card_le Λ)

theorem SizeWindowFailure_card_le
    (S : SemanticStrategy.SemanticSkeleton) (Λ : ℕ)
    (hbound : SizeWindowNounsBoundedBy S Λ) :
    (SizeWindowFailure (K := K) S).card ≤
      sizeWindowRootBound Λ * Fintype.card K ^ 3 := by
  rw [SizeWindowFailure, card_liftSeed]
  exact Nat.mul_le_mul_right _ (sizeWindowFailureSeeds_card_le S Λ hbound)

/-! ## Counter-regression for the former all-nonzero premise -/

theorem old_allNonzero_operational_impossible_of_window_state
    {q : ℕ} (s : SemanticStrategy.ComputeRowSkeleton)
    (hstate : s.state = .s3 ∨ s.state = .s4 ∨ s.state = .s6)
    (hop : ∀ (z : K), z ≠ 0 →
      BoundSemanticTrace.SkeletonOperationalPremises q z s) :
    False := by
  have hone : (1 : K) ≠ 0 := one_ne_zero
  rcases hstate with h3 | h4 | h6
  · have hw := (hop 1 hone).s3_window h3
    simpa using hw.one_lt_order
  · have hw := (hop 1 hone).s4_window h4
    simpa using hw.one_lt_order
  · have hw := (hop 1 hone).s6_window h6
    simpa using hw.one_lt_order

theorem old_allNonzero_operational_excludes_s3
    {q : ℕ} (s : SemanticStrategy.ComputeRowSkeleton)
    (hop : ∀ (z : K), z ≠ 0 →
      BoundSemanticTrace.SkeletonOperationalPremises q z s) :
    s.state ≠ .s3 :=
  fun h => old_allNonzero_operational_impossible_of_window_state s (Or.inl h) hop

theorem old_allNonzero_operational_excludes_s4
    {q : ℕ} (s : SemanticStrategy.ComputeRowSkeleton)
    (hop : ∀ (z : K), z ≠ 0 →
      BoundSemanticTrace.SkeletonOperationalPremises q z s) :
    s.state ≠ .s4 :=
  fun h => old_allNonzero_operational_impossible_of_window_state s
    (Or.inr (Or.inl h)) hop

theorem old_allNonzero_operational_excludes_s6
    {q : ℕ} (s : SemanticStrategy.ComputeRowSkeleton)
    (hop : ∀ (z : K), z ≠ 0 →
      BoundSemanticTrace.SkeletonOperationalPremises q z s) :
    s.state ≠ .s6 :=
  fun h => old_allNonzero_operational_impossible_of_window_state s
    (Or.inr (Or.inr h)) hop

end

end Nock.NockVMROM.Thm54.SizeWindowCounting

#print axioms Nock.NockVMROM.Thm54.SizeWindowCounting.SizeWindowFailure_card_le
#print axioms Nock.NockVMROM.Thm54.SizeWindowCounting.windows_of_not_mem_SizeWindowFailure
#print axioms Nock.NockVMROM.Thm54.SizeWindowCounting.old_allNonzero_operational_impossible_of_window_state
