/-
  Nock/NockVMROM/Thm54/TraceGen/GenRowShape.lean

  **From `SeedGood`'s abstract per-row bound down to the concrete bounds of `DD`/`DE`/`DF`.**

  `seedBad_card_le` counts a trace's bad seeds as `rows.length * B`, taking the
  per-row bound `B` as a hypothesis.  This module discharges that hypothesis from the three concrete
  bounds, leaving exactly one thing open: the **shape** facts about what the generator emits per
  state.

  Why the shape facts are needed rather than incidental:

  * At a `cons` row, `hdyck` asks `(encC z (formulaHead s.formula)).dyck ≠ 0`.  If the formula head
    were an *atom* this is false at **every** seed, so there would be no bound at all.  The condition is meaningful only because
    the generator emits a `cons` row exactly when the formula is `[[a b] c]`, making the head a cell.
  * At an OP5 row, `hncol` is free when the two operand results are the same noun, and otherwise
    needs `DF`'s atom bound to turn noun distinctness into distinct fingerprint vectors.
  * At an OP3 row, `hsz` is free when the call result is an atom (`op3CallSizeOk` is then `True` by
    definition) and otherwise needs `DE`'s orbit count.

  `RowCellIdentities.formula_cons` (`CensusExtraClosure.lean:1326`) gives
  `s.formula =.cell (skeletonDec s.f_h) (skeletonDec s.f_t)` for every row, so the formula *is* a
  cell -- but its head `f_h` is the opcode atom at an opcode row, and nothing in the repo derives
  "at a `cons` row the head is a cell".

  So this module takes the shape facts as hypotheses and does everything else.  The constant is not
  tight -- a row has only one state, so at most one of the three conditions is ever non-vacuous and
  `2Λ - 1` would suffice -- but a union of three is proved here because it is simpler and the
  constant is irrelevant to the eventual probability statement.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenDyckBadSeed

-- A missing import otherwise becomes a silent type variable rather than an error;
-- that cost real debugging time on this module family.
set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-! ## The per-row bound from the three shape facts -/

/-- **Per-row bad-seed bound, given the row's shape.**

Discharges the hypothesis `seedBad_card_le` takes, from `DD`/`DE`/`DF`.  Each hypothesis says what
the generator must emit at that state for the corresponding condition to be boundable at all; see
the module header for why each is required rather than convenient. -/
theorem rowBad_card_le_of_shape {q : ℕ} (hq : q ≤ ringChar K) (Λ : ℕ)
    (g : GenComputeRow K)
    (hcons : g.skel.state = State.cons →
      ∃ a b, formulaHead g.skel.formula = Noun.cell a b ∧
        (Noun.cell a b).leaves ≤ Λ)
    (h5 : g.skel.state = State.s5 →
      P8Census.skeletonSubformula g.skel 0 TripleSlot.result =
          P8Census.skeletonSubformula g.skel 1 TripleSlot.result ∨
        ((P8Census.skeletonSubformula g.skel 0 TripleSlot.result).leaves ≤ Λ ∧
          (P8Census.skeletonSubformula g.skel 1 TripleSlot.result).leaves ≤ Λ ∧
          FieldEmbedding.BoundedBy q (P8Census.skeletonSubformula g.skel 0 TripleSlot.result) ∧
          FieldEmbedding.BoundedBy q (P8Census.skeletonSubformula g.skel 1 TripleSlot.result)))
    (h3 : g.skel.state = State.s3 →
      ∀ x y, P8Census.skeletonSubformula g.skel 0 TripleSlot.result = Noun.cell x y →
        (Noun.cell x y).leaves ≤ Λ) :
    (Finset.univ.filter (fun z : K => ¬ RowSeedGood z g)).card ≤ 3 * (2 * Λ - 1) := by
  classical
  -- the three component bad sets
  set A : Finset K :=
    Finset.univ.filter
      (fun z : K => g.skel.state = State.cons ∧ (encC z (formulaHead g.skel.formula)).dyck = 0)
    with hA
  set B : Finset K :=
    Finset.univ.filter
      (fun z : K => g.skel.state = State.s5 ∧ ¬ op5ResultsAgree z g.skel) with hB
  set C : Finset K :=
    Finset.univ.filter
      (fun z : K => g.skel.state = State.s3 ∧ ¬ op3CallSizeOk z g.skel) with hC
  have hsub : (Finset.univ.filter (fun z : K => ¬ RowSeedGood z g)) ⊆ A ∪ B ∪ C := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    -- classically, failing a conjunction of implications means one antecedent held and its
    -- consequent failed; which one is pure propositional logic
    have hcase :
        (g.skel.state = State.cons ∧ (encC z (formulaHead g.skel.formula)).dyck = 0) ∨
          (g.skel.state = State.s5 ∧ ¬ op5ResultsAgree z g.skel) ∨
          (g.skel.state = State.s3 ∧ ¬ op3CallSizeOk z g.skel) := by
      simp only [RowSeedGood] at hz
      tauto
    rcases hcase with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by
        simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]; exact h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]; exact h))
    · exact Finset.mem_union_right _ (by
        simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
  -- each component is either empty (wrong state, or the condition is free) or bounded
  have hAcard : A.card ≤ 2 * Λ - 1 := by
    by_cases hst : g.skel.state = State.cons
    · obtain ⟨a, b, hhead, hlen⟩ := hcons hst
      refine le_trans (Finset.card_le_card ?_)
        (consHead_dyck_zero_card_le_window (K := K) Λ a b hlen)
      intro z hz
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hhead]; exact hz.2
    · have : A = ∅ := by
        simp only [hA, Finset.filter_eq_empty_iff]
        intro z _ hcon
        exact hst hcon.1
      simp [this]
  have hBcard : B.card ≤ 2 * Λ - 1 := by
    by_cases hst : g.skel.state = State.s5
    · rcases h5 hst with heq | ⟨hl1, hl2, hb1, hb2⟩
      · have : B = ∅ := by
          simp only [hB, Finset.filter_eq_empty_iff]
          intro z _ hcon
          exact hcon.2 (Or.inl heq)
        simp [this]
      · by_cases hne : P8Census.skeletonSubformula g.skel 0 TripleSlot.result =
            P8Census.skeletonSubformula g.skel 1 TripleSlot.result
        · have : B = ∅ := by
            simp only [hB, Finset.filter_eq_empty_iff]
            intro z _ hcon
            exact hcon.2 (Or.inl hne)
          simp [this]
        · refine le_trans (Finset.card_le_card ?_)
            (op5ResultsAgree_bad_card_le_of_ne (K := K) hq Λ g.skel hl1 hl2 hb1 hb2 hne)
          intro z hz
          simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hz.2
    · have : B = ∅ := by
        simp only [hB, Finset.filter_eq_empty_iff]
        intro z _ hcon
        exact hst hcon.1
      simp [this]
  have hCcard : C.card ≤ 2 * Λ - 1 := by
    by_cases hst : g.skel.state = State.s3
    · by_cases hcell :
          ∃ x y, P8Census.skeletonSubformula g.skel 0 TripleSlot.result = Noun.cell x y
      · obtain ⟨x, y, hres⟩ := hcell
        refine le_trans (Finset.card_le_card ?_)
          (le_trans (op3CallSize_bad_card_le (K := K) Λ x y (h3 hst x y hres)) (by omega))
        intro z hz
        simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h2 := hz.2
        simp only [op3CallSizeOk, hres, not_not] at h2
        exact h2
      · have hempty : C = ∅ := by
          simp only [hC, Finset.filter_eq_empty_iff]
          intro z _ hcon
          refine hcon.2 ?_
          have hatom : ∃ k, P8Census.skeletonSubformula g.skel 0 TripleSlot.result = Noun.atom k := by
            cases hsf : P8Census.skeletonSubformula g.skel 0 TripleSlot.result with
            | atom k => exact ⟨k, rfl⟩
            | cell x y => exact absurd ⟨x, y, hsf⟩ hcell
          obtain ⟨k, hk⟩ := hatom
          simp only [op3CallSizeOk, hk]
        simp [hempty]
    · have hempty : C = ∅ := by
        simp only [hC, Finset.filter_eq_empty_iff]
        intro z _ hcon
        exact hst hcon.1
      simp [hempty]
  refine le_trans (Finset.card_le_card hsub) ?_
  have hu1 := Finset.card_union_le (A ∪ B) C
  have hu2 := Finset.card_union_le A B
  omega

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.rowBad_card_le_of_shape
