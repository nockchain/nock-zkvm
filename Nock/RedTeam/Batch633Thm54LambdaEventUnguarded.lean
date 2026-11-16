/-
  Nock/RedTeam/Batch633Thm54LambdaEventUnguarded.lean

  That condition fires, at the authorized object:

  * `formRGuardedAxisFailureEvent E i E'` (`FormRAxisEvent.lean`) carries **no guard**: it is
    `{c | (αM, λ) ∈ formRRootBad (formRTemplatePolynomial E i) E'}`.  When the tree's Form R
    polynomial is `0`, the envelope is identically `0` and the root set is every pair
    (`formRRootBad_zero`), so the event is the whole `|𝕂|¹¹` tuple space
    (`event_eq_univ_of_poly_zero`, `event_card_of_poly_zero`).
  * The polynomial IS `0` exactly when the tree passes the Form R identity (A2,
    `formRTemplate_identity_iff_path`): every tree whose paths are valid
    (`event_eq_univ_of_path_valid`), i.e. every honest tree, and unconditionally every tree whose
    root row is `halt` — an atom root, whose `axis_counts` the paper sets to zero.
  * So one such tree makes the union total (`union_eq_univ_of_poly_zero`), and the lifted union
    over `afterSeed z` contains every tuple of that seed (`lifted_contains_seed_slice`).
  * `degY_le` / `formR_event_card` need `B_{e₀} ≠ 0` (`hB`): the R2 shape
    `card ≤ |𝕂|⁹·Σ_i |𝕂|(deg_i + E')` holds only for trees with a nonzero coefficient at an
    exponent `≤ E'`.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch633

open Nock
open Nock.AxisBatching
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Polynomial

open scoped Classical

noncomputable section

/-! ## 1. A zero Form R polynomial has a total root set -/

section Zero

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem formREnvelope_zero (E : ℕ) (α lmb : K) :
    formREnvelope (0 : Polynomial (Polynomial K)) E α lmb = 0 := by
  simp [formREnvelope, Nock.RedTeam.Batch556.F]

/-- **The unguarded root set of the zero polynomial is every pair.** -/
theorem formRRootBad_zero (E : ℕ) :
    formRRootBad (0 : Polynomial (Polynomial K)) E = Finset.univ := by
  ext p
  simp [formRRootBad, formREnvelope_zero]

/-- `formRCounts.halt = 0`, at every certificate. -/
theorem formRPolyOfCert_halt (A : ℕ → ℕ) :
    formRPolyOfCert A (MTree.halt : MTree K) = 0 := by
  simp [formRPolyOfCert, Nock.RedTeam.Batch575.formRCounts]

end Zero

/-! ## 2. The authorized per-tree event is the whole tuple space at such a tree -/

section Event

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [Fintype F]

theorem event_eq_univ_of_poly_zero {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ)
    (h : formRTemplatePolynomial E i = 0) :
    formRGuardedAxisFailureEvent (F := F) E i E' = Finset.univ := by
  ext c
  simp only [formRGuardedAxisFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]
  rw [formRBadAt_eq_template, h, formRRootBad_zero]
  exact Finset.mem_univ _

theorem event_card_of_poly_zero {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ)
    (h : formRTemplatePolynomial E i = 0) :
    (formRGuardedAxisFailureEvent (F := F) E i E').card = Fintype.card K ^ 11 := by
  rw [event_eq_univ_of_poly_zero E i E' h, Finset.card_univ,
    card_optimizedProductionChallengeTuple]

/-- Every tree that PASSES the Form R identity (A2: valid paths) makes the event total. -/
theorem event_eq_univ_of_path_valid {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ)
    (hU : Nock.RedTeam.Batch575.UniqueExponents (templateAxisTree (templateMemoryTreeAt E i)))
    (hA : CertInRange K (templateCertAxis (templateMemoryTreeAt E i)))
    (hpath : FormRPathValid (templateCertAxis (templateMemoryTreeAt E i))
      (templateAxisTree (templateMemoryTreeAt E i))) :
    formRGuardedAxisFailureEvent (F := F) E i E' = Finset.univ :=
  event_eq_univ_of_poly_zero E i E' ((formRTemplate_identity_iff_path E i hU hA).2 hpath)

/-- Unconditionally: a tree whose root row is `halt`. -/
theorem halt_root_event_eq_univ {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ)
    (hhalt : templateAxisTree (templateMemoryTreeAt E i) = MTree.halt) :
    formRGuardedAxisFailureEvent (F := F) E i E' = Finset.univ := by
  apply event_eq_univ_of_poly_zero
  rw [formRTemplatePolynomial, hhalt, formRPolyOfCert_halt]

/-- `templateAxisTree` sends a `halt` root to `MTree.halt`, whatever its children. -/
theorem templateAxisTree_halt (row : MemoryRowTemplate (K := K))
    (ch : List (Nock.Walk.NTree (MemoryRowTemplate (K := K))))
    (h : row.timestamp.state = .halt) :
    templateAxisTree (Nock.Walk.NTree.node row ch) = MTree.halt := by
  simp [templateAxisTree, h]

/-- The union over the trees of one template. -/
def templateUnion {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.biUnion fun i : Fin T.kMem => formRGuardedAxisFailureEvent E i E'

theorem union_eq_univ_of_poly_zero {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (E' : ℕ) (i : Fin T.kMem)
    (h : formRTemplatePolynomial E i = 0) :
    templateUnion (F := F) E E' = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro c
  simp only [templateUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, by rw [event_eq_univ_of_poly_zero E i E' h]; exact Finset.mem_univ _⟩

theorem not_bounded_of_poly_zero {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (E' : ℕ) (i : Fin T.kMem)
    (h : formRTemplatePolynomial E i = 0) (X : ℕ) (hX : X < Fintype.card K) :
    ¬ (templateUnion (F := F) E E').card ≤ Fintype.card K ^ 10 * X := by
  rw [union_eq_univ_of_poly_zero E E' i h, Finset.card_univ,
    card_optimizedProductionChallengeTuple]
  intro hle
  have hpos : 0 < Fintype.card K ^ 10 := pow_pos Fintype.card_pos 10
  have : Fintype.card K ^ 10 * Fintype.card K ≤ Fintype.card K ^ 10 * X := by
    simpa [pow_succ] using hle
  have := Nat.le_of_mul_le_mul_left this hpos
  omega

theorem not_bounded_at_true_figure {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (E' : ℕ) (i : Fin T.kMem)
    (h : formRTemplatePolynomial E i = 0) (N M kMem : ℕ)
    (hX : M + kMem * (3 * N + 129) < Fintype.card K) :
    ¬ (templateUnion (F := F) E E').card ≤
        Fintype.card K ^ 10 * (M + kMem * (3 * N + 129)) :=
  not_bounded_of_poly_zero E E' i h _ hX

/-- The lifted union of the authority, over the strategy's post-seed templates. -/
def liftedUnion (S : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)) (E' : ℕ) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    ∃ hz : nprSeed c.1 ≠ 0,
      c ∈ templateUnion (S.afterSeed ⟨nprSeed c.1, hz⟩).executionTemplate E'

/-- At a seed whose template has one tree with zero Form R polynomial, the lifted union contains
every tuple of that seed. -/
theorem lifted_contains_seed_slice
    (S : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)) (E' : ℕ)
    (z : K) (hz : z ≠ 0)
    (i : Fin (S.afterSeed ⟨z, hz⟩).configTemplate.kMem)
    (h : formRTemplatePolynomial (S.afterSeed ⟨z, hz⟩).executionTemplate i = 0)
    (c : OptimizedProductionChallengeTuple K F) (hc : nprSeed c.1 = z) :
    c ∈ liftedUnion S E' := by
  subst hc
  simp only [liftedUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hz, ?_⟩
  rw [union_eq_univ_of_poly_zero _ E' i h]
  exact Finset.mem_univ _

end Event

/-! ## 3. What a guard would buy (shape of a repair; NOT built into production) -/

section Guarded

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- A tree with a nonzero coefficient at an exponent `≤ E'` satisfies the R2 per-tree shape
`card ≤ |𝕂|·(2(n−1) + nodeCount + E')` (`formR_event_card` + `degY_le`).  This is what the
authority's numeral prices; the authorized set does not carry the guard. -/
theorem guarded_tree_card_le (A : ℕ → ℕ) (t : MTree K) (E' e₀ : ℕ)
    (hB : (formRPolyOfCert A t).coeff e₀ ≠ 0) (hE0 : e₀ ≤ E')
    (hA : CertInRange K A) :
    (formRRootBad (formRPolyOfCert A t) E').card ≤
      Fintype.card K * (2 * (formRN K - 1) + Nock.RedTeam.Batch575.nodeCount t + E') := by
  refine (formRRootBad_card_le A t e₀ E' hB hE0).trans (Nat.mul_le_mul_left _ ?_)
  have := Nock.RedTeam.Batch575.degY_le (K := K) (formRN K) (certShiftOf A) (certBitsOf A)
    hA e₀ t
  simp only [formRPolyOfCert] at this ⊢
  omega

end Guarded

end

end Nock.RedTeam.Batch633

#print axioms Nock.RedTeam.Batch633.formRRootBad_zero
#print axioms Nock.RedTeam.Batch633.event_eq_univ_of_path_valid
#print axioms Nock.RedTeam.Batch633.halt_root_event_eq_univ
#print axioms Nock.RedTeam.Batch633.not_bounded_at_true_figure
#print axioms Nock.RedTeam.Batch633.lifted_contains_seed_slice
#print axioms Nock.RedTeam.Batch633.guarded_tree_card_le
