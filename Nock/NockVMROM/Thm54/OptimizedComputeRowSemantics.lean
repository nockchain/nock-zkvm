import Nock.NockVMROM.Thm54.OptimizedComputeBaseGates

/-!
# Row-local semantics of the repaired optimized transition basis

It is an exact biconditional to the complete reified source conjunction
under the explicit base-summary and finite-RLC collision exclusions.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeRowSemantics

open Nock
open Nock.Reified
open OptimizedComputeGateBasis
open OptimizedComputeBaseGates
open OptimizedComputeFiniteIOGates

variable {F K : Type*} [Field F] [Field K]

def RowTransitionSat (envF : Env F) (envK : Env K) : Prop :=
  (∀ g ∈ baseTransitionGates, g.eval envF = 0) ∧
    (∀ g ∈ extTransitionGates, g.eval envK = 0)

def CompleteSourceRow (envF : Env F) (envK : Env K) : Prop :=
  (∀ g ∈ baseSourceGates, g.eval envF = 0) ∧
    (∀ e ∈ sourceFamilies20.flatten, e.eval envK = 0) ∧
    (∀ g ∈ legacySampledIOTransitionGates, g.eval envK = 0)

theorem rowTransitionSat_iff_completeSource
    (envF : Env F) (envK : Env K)
    (hbase : SummaryCollisionFree envF)
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree envK es) :
    RowTransitionSat envF envK ↔ CompleteSourceRow envF envK := by
  rw [RowTransitionSat, CompleteSourceRow,
    baseTransitionGates_eval_iff envF hbase]
  constructor
  · rintro ⟨hb, hext⟩
    have hs :
        (∀ g ∈ nonIOTransitionGates, g.eval envK = 0) ∧
          (∀ g ∈ legacySampledIOTransitionGates, g.eval envK = 0) := by
      constructor
      · intro g hg
        exact hext g (by simp [extTransitionGates, hg])
      · intro g hg
        exact hext g (by simp [extTransitionGates, hg])
    exact ⟨hb, (nonIOTransitionGates_eval_iff envK hfold).1 hs.1, hs.2⟩
  · rintro ⟨hb, hnonIO, hio⟩
    refine ⟨hb, ?_⟩
    intro g hg
    simp only [extTransitionGates, List.mem_append] at hg
    rcases hg with hg | hg
    · exact (nonIOTransitionGates_eval_iff envK hfold).2 hnonIO g hg
    · exact hio g hg

/-- Any malformed source equation is rejected by at least one repaired transition gate, provided
the same explicit collision exclusions hold. -/
theorem malformed_source_rejected
    (envF : Env F) (envK : Env K)
    (hbase : SummaryCollisionFree envF)
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree envK es)
    (hbad : ¬ CompleteSourceRow envF envK) :
    ¬ RowTransitionSat envF envK :=
  fun hsat => hbad ((rowTransitionSat_iff_completeSource envF envK hbase hfold).1 hsat)

#print axioms rowTransitionSat_iff_completeSource
#print axioms malformed_source_rejected

end OptimizedComputeRowSemantics
end Nock.NockVMROM.Thm54
