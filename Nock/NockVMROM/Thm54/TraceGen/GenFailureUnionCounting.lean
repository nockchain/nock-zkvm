/-
  Nock/NockVMROM/Thm54/TraceGen/GenFailureUnionCounting.lean

  **Existence of a coin outside the five-class failure union, by counting.**

  `ProductionP8Containment.accepted_outside_failureUnion` is generic in the production strategy
  `T : ProductionStrategy F K` and concludes `GenuineTargetAt T q Λ ω` from two premises about one
  coin: `T.Accepts ω` and `ω ∉ FailureUnion T C`.  The second premise is a *membership* condition
  on a counted finite set, so the natural way to supply it is cardinality, not construction — and
  two
  of the union's five summands (`specializedTopologyFailureEvent`, `guardedAxisFailureEvent`) are
  indexed by the committed `(z, α)` rather than by the honest fibre parameters, so they cannot be
  avoided by varying the fibre.

  This module does exactly one thing: it turns the existing cardinality estimate
  `failureUnion_card_le` (`ProductionP8Containment.lean:825`) into the statement that the failure
  union is a *proper* subset of the `|K|^4` joint challenge space, and hence that a coin outside it
  exists, under one explicit arithmetic side condition on the canonical fixed-field numerator:

  Nothing is constructed and no new event is counted: the two challenge-indexed majorants are the
  canonical ones already in the tree (`fixedTopologyWorkload` `:566`, `fixedAxisWorkload` `:579`,
  with their discharge lemmas at `:570` and `:586`), so the only remaining inputs are `(2 : K) ≠ 0`
  and the
  noun-size premise `SizeWindowNounsBoundedBy T.skeleton Λ`.

  ## Scope — what this is and, precisely, what it is not

  This is **existence by counting**, i.e. the finite-field form of the paper's soundness accounting.
  the paper (`Thm:NockVMROM`) states that "the verification of `N` opcodes and `L` memory
  records has perfect completeness and negligible soundness error if `N, L \in negl(K)`"; the same
  shape of side condition is spelled out for the collision error at the paper ("Requiring that
  `Λ, k \in negl(|K|)` means that the above scheme is sufficiently secure").  What the theorems below
  make explicit is the *numerator*: the union's density is at most
  `workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) / |K|`, so the union misses at least
  one coin as soon as that numerator is below `|K|`.

  It does **NOT** produce an *accepting* coin outside the union.
  `exists_coin_outside_failureUnion` gives some `ω` with `ω ∉ FailureUnion T C` and says nothing
  whatsoever about `T.Accepts ω`;
  combining "accepting" with "outside" is a strictly later step (it needs the acceptance set to be
  non-empty *and* to be large enough, or to intersect the complement, neither of which is counted
  here).  In particular no `GenuineTargetAt` conclusion follows from this module alone, and none is
  claimed.

  Also note: the side condition is on the *fixed-field* majorants, which are suprema over all
  nonzero seeds / all specializations of one fixed strategy.  It is a hypothesis, not a theorem:
  bounding `fixedTopologyWorkload`/`fixedAxisWorkload` for a concrete generated strategy is separate
  work and is not attempted here.
-/
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.TraceGen.GoldilocksTimestampBase
import Nock.Field

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting

noncomputable section

/-! ## A. The fixed-field cardinality bound

`failureUnion_card_le` takes the topology and axis majorants as parameters together with proofs
that they dominate every specialization.  At one fixed finite field those proofs are already in the
tree for the canonical suprema, so the parameterized form collapses to a bound with no external
input beyond `(2 : K) ≠ 0` and the noun-size premise. -/

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- `failureUnion_card_le` with both challenge-indexed majorants discharged by the canonical
fixed-field suprema.  The remaining inputs are exactly `h2` and the noun-size premise. -/
theorem failureUnion_card_le_fixed
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (Λ : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ) :
    (ProductionP8Containment.FailureUnion T C lmb).card ≤
      workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) *
        Fintype.card K ^ 3 :=
  ProductionP8Containment.failureUnion_card_le h2 T lmb C
    (fixedTopologyWorkload T) (fixedAxisWorkload T) hwindowBound
    (topologyWorkload_le_fixedTopologyWorkload T)
    (templateAxisWorkload_le_fixedAxisWorkload T)

/-- **The explicit error fraction.**  The failure union occupies at most
`workload / |K|` of the four-coordinate joint challenge space.  This is the density form of
`failureUnion_card_le_fixed`; it carries no acceptance or containment premise, so it is a statement
about the union itself and not yet about false acceptance. -/
theorem jointProbability_failureUnion_le_fixed
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (Λ : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ) :
    |jointProbability (ProductionP8Containment.FailureUnion T C lmb)| ≤
      (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) : ℝ) /
        (Fintype.card K : ℝ) :=
  jointProbability_le_workload_div_card (ProductionP8Containment.FailureUnion T C lmb)
    (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T))
    (failureUnion_card_le_fixed h2 T Λ C lmb hwindowBound)

/-! ## B. Strict inequality against `|K|^4`, and existence

`card_jointCoins` (`JointCoins.lean:115`) is `Fintype.card (JointCoins K) = Fintype.card K ^ 4`.
With the numerator strictly below `Fintype.card K` the bound of §A is strictly below that, so the
union cannot be all of `JointCoins K`. -/

/-- The counted union is strictly smaller than the joint challenge space whenever the canonical
fixed-field numerator is below `|K|`. -/
theorem failureUnion_card_lt_card_jointCoins
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (Λ : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (hsmall :
      workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) <
        Fintype.card K) :
    (ProductionP8Containment.FailureUnion T C lmb).card < Fintype.card (JointCoins K) := by
  have hpos : 0 < Fintype.card K ^ 3 := pow_pos Fintype.card_pos 3
  calc
    (ProductionP8Containment.FailureUnion T C lmb).card
        ≤ workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) *
            Fintype.card K ^ 3 :=
      failureUnion_card_le_fixed h2 T Λ C lmb hwindowBound
    _ < Fintype.card K * Fintype.card K ^ 3 :=
      Nat.mul_lt_mul_of_lt_of_le hsmall (le_refl _) hpos
    _ = Fintype.card (JointCoins K) := by
      rw [card_jointCoins]; ring

/-- The counted union is a proper subset of the whole challenge space. -/
theorem failureUnion_ne_univ
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (Λ : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (hsmall :
      workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) <
        Fintype.card K) :
    ProductionP8Containment.FailureUnion T C lmb ≠ (Finset.univ : Finset (JointCoins K)) := by
  intro hEq
  have hlt :=
    failureUnion_card_lt_card_jointCoins h2 T Λ C lmb hwindowBound hsmall
  rw [hEq, Finset.card_univ] at hlt
  exact absurd hlt (lt_irrefl _)

/-- **Existence by counting.**  Under the single explicit arithmetic side condition
`workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) < Fintype.card K`, some joint coin
lies outside the five-class failure union.

This supplies the `hout` premise of `accepted_outside_failureUnion` for *some* coin.  It says
nothing about `T.Accepts` at that coin; see the module docstring. -/
theorem exists_coin_outside_failureUnion
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (Λ : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (hsmall :
      workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) <
        Fintype.card K) :
    ∃ ω : JointCoins K, ω ∉ ProductionP8Containment.FailureUnion T C lmb := by
  have hss :
      ProductionP8Containment.FailureUnion T C lmb ⊂
        (Finset.univ : Finset (JointCoins K)) :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,
        failureUnion_ne_univ h2 T Λ C lmb hwindowBound hsmall⟩
  obtain ⟨ω, -, hω⟩ := Finset.exists_of_ssubset hss
  exact ⟨ω, hω⟩

end Generic

/-! ## C. The corollary at the Goldilocks cubic field

`Nock.Field.K = GaloisField p 3` with `p = 2^64 - 2^32 + 1`, so `Fintype.card K = p^3`.  `(2 : K) ≠ 0` is discharged from `CharP _ p` and the
primality of `p`, so at this field the side condition is the single numeric inequality
`workload … < p^3`.

⚠ Everything in this section mentions `Nock.Field.K` and therefore depends on the blessed
`Nock.Field.goldilocks_prime` axiom.  Section B above does not. -/

section Goldilocks

variable {F : Type} [Field F] [Algebra F Nock.Field.K]

/-- The `CharP K (ringChar K)` instance that `ProductionStrategy`'s binder demands, named at the
Goldilocks cubic carrier.  Mathlib's `ringChar.charP` is declared at low priority and is not picked
up by instance search here, so it is installed locally; this adds no assumption.  Note that with it
in scope `CharP Nock.Field.K Nock.Field.p` stops synthesizing, so anything needing the *numeral*
form must be stated before this point (or imported, as `goldilocks_ringChar_K` is). -/
local instance goldilocksRingCharP : CharP Nock.Field.K (ringChar Nock.Field.K) :=
  ringChar.charP _

/-- **Goldilocks corollary.**  At the deployed field the arithmetic side condition is
`workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) < p^3`, and under it a coin outside
the five-class failure union exists.  As in §B this is existence only, not an accepting coin. -/
theorem goldilocks_exists_coin_outside_failureUnion
    (T : ProductionStrategy F Nock.Field.K) (Λ : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus Nock.Field.K T.skeleton Λ)
    (lmb : Nock.Field.K)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (hsmall :
      workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) <
        Nock.Field.p ^ 3) :
    ∃ ω : JointCoins Nock.Field.K, ω ∉ ProductionP8Containment.FailureUnion T C lmb := by
  refine exists_coin_outside_failureUnion goldilocks_two_ne_zero T Λ C lmb hwindowBound ?_
  rw [Nock.Field.card_K]
  exact hsmall

/-- The Goldilocks error fraction, with the denominator as the actual field cardinality `p^3`. -/
theorem goldilocks_jointProbability_failureUnion_le
    (T : ProductionStrategy F Nock.Field.K) (Λ : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus Nock.Field.K T.skeleton Λ)
    (lmb : Nock.Field.K)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ) :
    |jointProbability (ProductionP8Containment.FailureUnion T C lmb)| ≤
      (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) : ℝ) /
        ((Nock.Field.p ^ 3 : ℕ) : ℝ) := by
  have h :=
    jointProbability_failureUnion_le_fixed goldilocks_two_ne_zero T Λ C lmb hwindowBound
  rwa [Nock.Field.card_K] at h

end Goldilocks

end

end Nock.NockVMROM.Thm54.TraceGen

/-! ## Axiom receipts

Section A/B are axiom-clean beyond the Lean/Mathlib triple; only the §C Goldilocks corollaries pull
the blessed `Nock.Field.goldilocks_prime`. -/

-- [propext, Classical.choice, Quot.sound]
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_coin_outside_failureUnion
#print axioms Nock.NockVMROM.Thm54.TraceGen.failureUnion_card_le_fixed
#print axioms Nock.NockVMROM.Thm54.TraceGen.jointProbability_failureUnion_le_fixed
-- [propext, Classical.choice, Quot.sound, Nock.Field.goldilocks_prime]
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocks_exists_coin_outside_failureUnion
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocks_jointProbability_failureUnion_le
