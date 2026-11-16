import Nock.NockVMROM.Thm54.ProductionAsymptotic
import Nock.RedTeam.Batch14Thm54Production

/-!
# Low-order size-window repair

This compiled regression records why the former all-nonzero operational premise excluded every
semantic skeleton containing OP3, OP4, or OP6, and receipts the replacement exact counted event.
-/

namespace Nock.RedTeam

open scoped Classical
open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SizeWindowCounting

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Generic contradiction at `z = 1` for any row in one of the three window-consuming states. -/
theorem b15_old_allNonzero_impossible_generic
    {q : ℕ} (S : SemanticStrategy.SemanticSkeleton)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S)
    (hstate : s.state = .s3 ∨ s.state = .s4 ∨ s.state = .s6)
    (hop : ∀ (z : K), z ≠ 0 →
      ∀ r ∈ SemanticStrategy.computeSkeletonRows S,
        BoundSemanticTrace.SkeletonOperationalPremises q z r) :
    False :=
  old_allNonzero_operational_impossible_of_window_state s hstate
    (fun z hz => hop z hz s hs)

/-- OP3 specialization of the counter-regression. -/
theorem b15_old_allNonzero_excludes_s3
    {q : ℕ} (S : SemanticStrategy.SemanticSkeleton)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S)
    (hop : ∀ (z : K), z ≠ 0 →
      ∀ r ∈ SemanticStrategy.computeSkeletonRows S,
        BoundSemanticTrace.SkeletonOperationalPremises q z r) :
    s.state ≠ .s3 :=
  old_allNonzero_operational_excludes_s3 s (fun z hz => hop z hz s hs)

/-- OP4 specialization of the counter-regression. -/
theorem b15_old_allNonzero_excludes_s4
    {q : ℕ} (S : SemanticStrategy.SemanticSkeleton)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S)
    (hop : ∀ (z : K), z ≠ 0 →
      ∀ r ∈ SemanticStrategy.computeSkeletonRows S,
        BoundSemanticTrace.SkeletonOperationalPremises q z r) :
    s.state ≠ .s4 :=
  old_allNonzero_operational_excludes_s4 s (fun z hz => hop z hz s hs)

/-- OP6 specialization of the counter-regression. -/
theorem b15_old_allNonzero_excludes_s6
    {q : ℕ} (S : SemanticStrategy.SemanticSkeleton)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S)
    (hop : ∀ (z : K), z ≠ 0 →
      ∀ r ∈ SemanticStrategy.computeSkeletonRows S,
        BoundSemanticTrace.SkeletonOperationalPremises q z r) :
    s.state ≠ .s6 :=
  old_allNonzero_operational_excludes_s6 s (fun z hz => hop z hz s hs)

/-- Exact event receipt: zero is excluded here and remains in the separate zero-seed event. -/
theorem b15_sizeWindowFailure_exact
    (S : SemanticStrategy.SemanticSkeleton) (ω : JointCoins K) :
    ω ∈ SizeWindowFailure (K := K) S ↔
      nprSeed ω ≠ 0 ∧
        ∃ n ∈ skeletonSizeWindowNouns S,
          ¬ OpcodeSemantics.SizeWindow (nprSeed ω) n :=
  mem_SizeWindowFailure_iff S ω

/-- Triangular polynomial-root count, lifted by exactly the three unrestricted coordinates. -/
theorem b15_sizeWindowFailure_card_le
    (S : SemanticStrategy.SemanticSkeleton) (Λ : ℕ)
    (hbound : SizeWindowNounsBoundedBy S Λ) :
    (SizeWindowFailure (K := K) S).card ≤
      (∑ d ∈ Finset.Icc 1 Λ, d) * Fintype.card K ^ 3 := by
  simpa [sizeWindowRootBound] using SizeWindowFailure_card_le
    (K := K) S Λ hbound

/-- Outside the fifth event, the exact row-local OP3/OP4/OP6 facts are reconstructed. -/
theorem b15_windows_recovered_outside_event
    (S : SemanticStrategy.SemanticSkeleton) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0)
    (hout : ω ∉ SizeWindowFailure (K := K) S)
    (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s ∈ SemanticStrategy.computeSkeletonRows S) :
    BoundSemanticTrace.SkeletonSizeWindowPremises (nprSeed ω) s :=
  windows_of_not_mem_SizeWindowFailure S ω hz hout s hs

/-- The repaired production workload contains the triangular root numerator as its final term. -/
theorem b15_production_workload_exact
    {F : Type} [Field F] [Algebra F K]
    [CharP K (ringChar K)]
    (T : ProductionP8Containment.ProductionStrategy F K)
    (Λ topologyWorkload axisWorkload : ℕ) :
    ProductionP8Containment.workload T Λ topologyWorkload axisWorkload =
      1 +
        (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
          (2 * Λ - 1) +
        topologyWorkload + axisWorkload + ProductionP8Containment.formRUniformWorkload T +
        ProductionP8Containment.reqPairWorkload T Λ +
        (∑ d ∈ Finset.Icc 1 Λ, d) := by
  -- thirtieth move: `workload` carries the Form R λ-event summand beside the axis summand
  rfl

end

end Nock.RedTeam

#print axioms Nock.RedTeam.b15_old_allNonzero_impossible_generic
#print axioms Nock.RedTeam.b15_old_allNonzero_excludes_s3
#print axioms Nock.RedTeam.b15_old_allNonzero_excludes_s4
#print axioms Nock.RedTeam.b15_old_allNonzero_excludes_s6
#print axioms Nock.RedTeam.b15_sizeWindowFailure_exact
#print axioms Nock.RedTeam.b15_sizeWindowFailure_card_le
#print axioms Nock.RedTeam.b15_windows_recovered_outside_event
#print axioms Nock.RedTeam.b15_production_workload_exact
