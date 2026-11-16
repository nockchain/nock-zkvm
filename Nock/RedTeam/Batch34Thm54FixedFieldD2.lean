/-
  Nock/RedTeam/Batch34Thm54FixedFieldD2.lean

  Scope is deliberately narrow.  These receipts test the fixed-field event, workload, finite-field
  denominator, canonical workload majorants, the new local size-window premise, and the separation
  from the standalone varying-family and collision-only results.
-/

import Nock.NockVMROM.Thm54.StrictPackage

namespace Nock.RedTeam.Batch34

open scoped Classical
open Nock Nock.Walk Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.StrictPackage
open Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity

noncomputable section

/-! ## A. Exact threading of event, workload, and field -/

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb q Λ : ℕ}
  (P : StrictNockVMROMPackage F K hOrb q Λ)

/-- Its event, both workload majorants, and
denominator are all indexed by the package's own strategy and field. -/
abbrev D2FixedFieldClaim (lmb : K) : Prop :=
  |jointProbability (FalseAcceptanceSet P.strategy q Λ lmb)| ≤
    (workload P.strategy Λ
        (fixedTopologyWorkload P.strategy)
        (fixedAxisWorkload P.strategy) : ℝ) /
      (Fintype.card K : ℝ)

/-- **Threading receipt.**  Both the package theorem and the consumed strict capstone return the
exact proposition above, without a separately quantified strategy, event, workload, or field. -/
theorem b34_exact_package_and_capstone_threading
    (S : StrictThm54Statement P) (lmb : K) :
    D2FixedFieldClaim P lmb ∧ D2FixedFieldClaim P lmb :=
  ⟨P.fixedField_falseAcceptance_le lmb, S.fixed_field_soundness lmb⟩

/-- Transport to another strategy is available when, and explicitly because, an equality identifies
that strategy with the package strategy. -/
theorem b34_strategy_transport_uses_equality
    (U : ProductionStrategy F K) (hU : U = P.strategy) (lmb : K)
    (h : D2FixedFieldClaim P lmb) :
    |jointProbability (FalseAcceptanceSet U q Λ lmb)| ≤
      (workload U Λ (fixedTopologyWorkload U) (fixedAxisWorkload U) : ℝ) /
        (Fintype.card K : ℝ) := by
  subst U
  exact h

/-! ## B. Canonical majorants are universal and the topology one is nonzero -/

/-- Both canonical suprema majorize every specialization used by the production union bound. -/
theorem b34_canonical_majorants_cover_every_specialization
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    topologyWorkload
          (P.strategy.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤
        fixedTopologyWorkload P.strategy ∧
      TemplateAxisCounting.templateAxisWorkload
          (ProductionAxisStructureVerifier.committedTemplate
            P.strategy.verifier z hz) ≤
        fixedAxisWorkload P.strategy :=
  ⟨topologyWorkload_le_fixedTopologyWorkload P.strategy z hz α lmb,
    templateAxisWorkload_le_fixedAxisWorkload P.strategy z hz⟩

/-- The topology maximum is not an empty-domain/zero decoration.  Every exact specialization has
positive compute and memory row counts, and its exact topology workload is
`24 * compRows + 8 * memRows`; hence the canonical maximum is strictly positive. -/
theorem b34_fixedTopologyWorkload_positive :
    0 < fixedTopologyWorkload P.strategy := by
  let R :=
    (P.strategy.verifier.raw.afterAlphaM (1 : K) one_ne_zero 0 0).familyData.base
  have hR : 0 < topologyWorkload R := by
    rw [topology_gamma_workload_exact]
    have hc : 0 < R.cfg.compRows := R.cfg.compRows_pos
    have hm : 0 < R.cfg.memRows := R.cfg.memRows_pos
    omega
  exact hR.trans_le
    (topologyWorkload_le_fixedTopologyWorkload P.strategy (1 : K) one_ne_zero 0 0)

/-! ## C. Bit theorem and Goldilocks scope -/

/-- The package bit theorem can be reconstructed from the fixed-field inequality and the explicit
full-workload support inequality alone.  No collision-only Goldilocks theorem is an input. -/
theorem b34_bits_follow_from_fixed_claim_only
    (lmb : K) (b : ℕ)
    (hfixed : D2FixedFieldClaim P lmb)
    (hsupport :
      workload P.strategy Λ
          (fixedTopologyWorkload P.strategy)
          (fixedAxisWorkload P.strategy) * 2 ^ b ≤
        Fintype.card K) :
    |jointProbability (FalseAcceptanceSet P.strategy q Λ lmb)| ≤ 1 / 2 ^ b := by
  refine hfixed.trans ?_
  have hcard : (0 : ℝ) < (Fintype.card K : ℝ) := by positivity
  have hpow : (0 : ℝ) < 2 ^ b := by positivity
  have hreal :
      (workload P.strategy Λ
          (fixedTopologyWorkload P.strategy)
          (fixedAxisWorkload P.strategy) : ℝ) * 2 ^ b ≤
        (Fintype.card K : ℝ) := by
    exact_mod_cast hsupport
  rw [div_le_div_iff₀ hcard hpow]
  linarith

/-- The capstone's bit field has exactly the package event and full workload support premise. -/
theorem b34_capstone_bits_exact
    (S : StrictThm54Statement P) (lmb : K) (b : ℕ)
    (hsupport :
      workload P.strategy Λ
          (fixedTopologyWorkload P.strategy)
          (fixedAxisWorkload P.strategy) * 2 ^ b ≤
        Fintype.card K) :
    |jointProbability (FalseAcceptanceSet P.strategy q Λ lmb)| ≤ 1 / 2 ^ b :=
  S.fixed_field_bits lmb b hsupport

end Package

/-- Pure arithmetic discrimination: support for a smaller collision numerator at 120 bits does not
entail support for a larger production numerator.  A theorem promoting the former must therefore
establish the full workload inequality explicitly. -/
theorem b34_collision_support_does_not_promote_to_larger_workload :
    1 * 2 ^ 120 ≤ 2 ^ 120 ∧ ¬ 2 * 2 ^ 120 ≤ 2 ^ 120 := by
  constructor <;> norm_num

/-! ## D. The local size-window premise is satisfiable and distinct from atom boundedness -/

/-- An explicit OP3 row whose consumed size-window noun is a two-leaf cell. -/
def windowComputeRow : ComputeRowSkeleton where
  state := .s3
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ slot =>
    match slot with
    | .result => .cell (.atom 0) (.atom 0)
    | _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

/-- A concrete nonempty semantic skeleton with the OP3 row above. -/
def windowSkeleton : SemanticSkeleton where
  computeTree := .node windowComputeRow []
  memoryForest := []

theorem b34_windowSkeleton_computeRows :
    computeSkeletonRows windowSkeleton = [windowComputeRow] := by
  unfold computeSkeletonRows windowSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- The new proposition has a concrete nonempty, non-vacuous witness: its noun list contains the
two-leaf OP3 result and is bounded at `Λ = 2`. -/
theorem b34_sizeWindowBound_nonvacuous :
    skeletonSizeWindowNouns windowSkeleton =
        [.cell (.atom 0) (.atom 0)] ∧
      SizeWindowNounsBoundedBy windowSkeleton 2 := by
  have hlist :
      skeletonSizeWindowNouns windowSkeleton =
        [.cell (.atom 0) (.atom 0)] := by
    rw [skeletonSizeWindowNouns, b34_windowSkeleton_computeRows]
    rfl
  constructor
  · exact hlist
  · intro n hn
    rw [hlist] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    subst n
    decide

/-- Atom boundedness does not imply the size-window bound: every atom in this skeleton is below
`1`, while its required two-leaf noun exceeds `Λ = 1`. -/
theorem b34_atomBounded_does_not_imply_sizeWindowBound :
    windowSkeleton.BoundedBy 1 ∧
      ¬ SizeWindowNounsBoundedBy windowSkeleton 1 := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · rw [b34_windowSkeleton_computeRows]
      have hrow : ComputeRowSkeleton.BoundedBy 1 windowComputeRow := by
        refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
        · intro slot h
          simp [windowComputeRow]
        · intro i h slot
          cases slot <;> simp [windowComputeRow]
        · intro i h
          constructor <;> simp [windowComputeRow]
      simpa using hrow
    · simp [windowSkeleton, memorySkeletonRows, bfsForest_nil]
    · intro tree htree
      simp [windowSkeleton] at htree
  · intro h
    have hmem :
        .cell (.atom 0) (.atom 0) ∈ skeletonSizeWindowNouns windowSkeleton := by
      rw [b34_sizeWindowBound_nonvacuous.1]
      simp
    have hb := h (.cell (.atom 0) (.atom 0)) hmem
    norm_num [Noun.leaves] at hb

/-- Conversely, the sample commitment's size-window list is empty (its state is OP1), so it is
size-window bounded at `Λ = 0`, while its atom `2` is not bounded at `q = 1`.  The two package
premises are therefore logically distinct in both directions. -/
theorem b34_sizeWindowBound_does_not_imply_atomBounded :
    SizeWindowNounsBoundedBy sampleCommitment.skeleton 0 ∧
      ¬ sampleCommitment.skeleton.BoundedBy 1 := by
  constructor
  · intro n hn
    rw [skeletonSizeWindowNouns, sampleCommitment_computeRows] at hn
    simp [requiredSizeWindowNouns, sampleComputeRow] at hn
  · intro h
    have hrows := h.computeRows
    rw [sampleCommitment_computeRows] at hrows
    have hrow : ComputeRowSkeleton.BoundedBy 1 sampleComputeRow := by
      simpa using hrows
    exact (by decide : ¬ FieldEmbedding.BoundedBy 1 sampleComputeRow.formula) hrow.2.1

/-! ## E. Failure of unrelated-event transport -/

/-- A bare probability inequality cannot be transported to an unrelated event.  On `ZMod 3`, the
empty event satisfies the zero bound while the universal event does not.  This is the compiled
countermodel behind the equality premise in `b34_strategy_transport_uses_equality`. -/
theorem b34_unrelated_event_transport_is_false :
    ¬ (|jointProbability
          (∅ : Finset (JointCoins (ZMod 3)))| ≤ (0 : ℝ) / Fintype.card (ZMod 3) →
        |jointProbability
          (Finset.univ : Finset (JointCoins (ZMod 3)))| ≤
            (0 : ℝ) / Fintype.card (ZMod 3)) := by
  norm_num [jointProbability]

/-! ## F. Fixed versus asymptotic type scope, and consumed capstone scope -/

/-- Exact type pin for the new fixed-field package theorem.  This alias has one field `K` and one
strategy `P.strategy`; it does not purport to prove a syntactic absence result about arbitrary Lean
terms. -/
abbrev b34_fixed_field_signature := @StrictNockVMROMPackage.fixedField_falseAcceptance_le

/-- Exact type pin for the standalone varying-family theorem.  Keeping it separate makes the
`Tfam`/`FieldAt`/`HasExactAsymptoticSoundness` quantification visible at a different declaration. -/
abbrev b34_varying_family_signature :=
  @StrictAsymptoticSecurity.strict_asymptotic_soundness_of_strategyData

/-- Exact type pin for the collision-only Goldilocks 120-bit theorem, which is not the package bit
theorem and takes an arbitrary event plus a collision-workload cardinality premise. -/
abbrev b34_collision_120_signature :=
  @GoldilocksConcreteSecurity.goldilocks_concrete_falseAcceptance_le_two_pow_neg_120

def b34_strict_capstone_target
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictThm54Statement P :=
  strictNockVMROM_of_package P

theorem b34_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest := rfl

end

end Nock.RedTeam.Batch34

#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.fixedTopologyWorkload
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.topologyWorkload_le_fixedTopologyWorkload
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.fixedAxisWorkload
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.templateAxisWorkload_le_fixedAxisWorkload
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.two_ne_zero
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.fixedField_falseAcceptance_le
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.fixedField_falseAcceptance_le_two_pow_neg
#print axioms Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package

-- Independent receipts.
#print axioms Nock.RedTeam.Batch34.b34_exact_package_and_capstone_threading
#print axioms Nock.RedTeam.Batch34.b34_strategy_transport_uses_equality
#print axioms Nock.RedTeam.Batch34.b34_canonical_majorants_cover_every_specialization
#print axioms Nock.RedTeam.Batch34.b34_fixedTopologyWorkload_positive
#print axioms Nock.RedTeam.Batch34.b34_bits_follow_from_fixed_claim_only
#print axioms Nock.RedTeam.Batch34.b34_capstone_bits_exact
#print axioms Nock.RedTeam.Batch34.b34_collision_support_does_not_promote_to_larger_workload
#print axioms Nock.RedTeam.Batch34.b34_sizeWindowBound_nonvacuous
#print axioms Nock.RedTeam.Batch34.b34_atomBounded_does_not_imply_sizeWindowBound
#print axioms Nock.RedTeam.Batch34.b34_sizeWindowBound_does_not_imply_atomBounded
#print axioms Nock.RedTeam.Batch34.b34_unrelated_event_transport_is_false
#print axioms Nock.RedTeam.Batch34.b34_fixed_field_signature
#print axioms Nock.RedTeam.Batch34.b34_varying_family_signature
#print axioms Nock.RedTeam.Batch34.b34_collision_120_signature
#print axioms Nock.RedTeam.Batch34.b34_strict_capstone_target
#print axioms Nock.RedTeam.Batch34.b34_alias_remains_forest
