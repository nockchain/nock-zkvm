/-
  FOURTH-PASS ADVERSARIAL REVIEW of plan §D1b.  Part 2:
   (4) "padding is unconditional"        — the Lean `RAP` does not tie `H.card` to `2^h`.
   (3) A2' mispriced                     — `Satisfies` is `k`/`wRAP`-blind; an unpinned
                                           selector is a SOUNDNESS hole, not a cost item.
-/
import Nock.Framework
import Nock.AIR
import Nock.Counts
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

namespace Rev2

open Nock Nock.Framework Nock.Framework.Reify Nock.Reified
open scoped Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 4.  "Padding is unconditional" — FALSE for the Lean model as shipped.

  `RAP.h` and `RAP.H` are independent fields.  The ONLY coupling is
  `I_bound : ∀ q ∈ I, q.2 < 2^h`, and `airToRAP` puts `I = univ ×ˢ {0,1}`, so it needs only
  `1 ≤ h`.  Nothing anywhere requires `H.card = 2^h`.  Hence there are no padding rows, hence
  no `.row` constraint ever needs gating. -/

/-- The domain of an `airToRAP` RAP is a free parameter of arbitrary cardinality, unrelated to
    `2 ^ h`.  Here `h = 1` (`2^h = 2`) with a 3-element domain. -/
theorem rap_domain_card_free (air : Reified.AIR) (chalVal pubVal : ℕ → ℚ) (eDeg : ℕ) (ω : ℚ) :
    (airToRAP air chalVal pubVal eDeg 1 ω 1 ({0, 1, 2} : Finset ℚ) one_ne_zero le_rfl).H.card = 3
    ∧ 2 ^ (airToRAP air chalVal pubVal eDeg 1 ω 1 ({0, 1, 2} : Finset ℚ)
            one_ne_zero le_rfl).h = 2 := by
  refine ⟨?_, rfl⟩
  show ({0, 1, 2} : Finset ℚ).card = 3
  norm_num

/-- The domain the SHIPPED bridges actually use (`computeTable_reified_iff`,
    `nock_hasCanonicalRAP.progSatisfiable`, `nockCompletenessModel`) is
    `Finset.image nodes univ`, whose cardinality is exactly the number of real rows `n` —
    no padding, for any `n`. -/
theorem shipped_domain_card_is_exactly_n {n : ℕ} (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) :
    (Finset.image nodes Finset.univ).card = n := by
  rw [Finset.card_image_of_injective _ hnodes, Finset.card_univ, Fintype.card_fin]

/-- Concretely: 527 real compute rows, `h = 1`.  `H.card = 527` is not a power of two and the
    `RAP` is still well-formed — `airToRAP` accepts it.  So "`compRows < 2^h` therefore the 526
    degree-4 `.row` gates must be selector-gated" has a false antecedent in the Lean model. -/
theorem no_power_of_two_obligation (air : Reified.AIR) (chalVal pubVal : ℕ → ℚ)
    (nodes : Fin 527 → ℚ) (hnodes : Function.Injective nodes) :
    (airToRAP air chalVal pubVal 1 1 1 1 (Finset.image nodes Finset.univ)
        one_ne_zero le_rfl).H.card = 527 :=
  shipped_domain_card_is_exactly_n nodes hnodes

/-- Excluding the last row
    from the `.transition` segment is `Finset.erase`, a plain `Finset` operation — it costs zero
    columns and zero degree.  (`H.erase xlast` is exactly the transition domain of option E.) -/
theorem erase_is_the_gate (H : Finset F) (xlast : F) (hmem : xlast ∈ H) :
    (H.erase xlast).card + 1 = H.card ∧ xlast ∉ H.erase xlast :=
  ⟨Finset.card_erase_add_one hmem, Finset.notMem_erase _ _⟩

/-! ## 3.  A2′ IS MISPRICED — twice.

  (a) `RAP.Satisfies` is blind to `k` and `wRAP`.  A "preprocessed segment (`k ≥ 2`)" therefore
      pins NOTHING: it is pure bookkeeping unless `RAP.Satisfies` itself changes.  The plan's
      cost row lists `RAP.mk` arity and `airToRAP` forking, but not the `Satisfies` change —
      and `Satisfies` is the field every downstream theorem quantifies over. -/

theorem satisfies_is_k_and_wRAP_blind (R : RAP F) (k' : ℕ) (w' : Fin k' → ℕ)
    (hw : R.w = ∑ i, w' i) (P : Fin R.w → F[X]) :
    R.Satisfies P ↔ ({R with k := k', wRAP := w', w_eq := hw} : RAP F).Satisfies P := Iff.rfl

/-- (b) An UNPINNED selector column is not merely "not a pin" — it is a **soundness hole**.
    If the gated constraint is `(Y_sel,0 − c)·Q`, the prover (who freely chooses `P`) sets the
    selector column to the constant `c` and EVERY gated constraint vanishes at EVERY point of
    `H`, whatever `Q` is.  So under A2′ the pin must be enforced by `Satisfies`; it cannot be
    left as documentation. -/
theorem unpinned_selector_kills_every_gate (R : RAP F) (P : Fin R.w → F[X]) (sel : Fin R.w)
    (c : F) (hsel : P sel = Polynomial.C c) (i : Fin R.s) (Q : MvPolynomial (Fin R.w × ℕ) F)
    (hC : R.C i = (MvPolynomial.X (sel, 0) - MvPolynomial.C c) * Q) (x : F) :
    (R.compose P i).eval x = 0 := by
  rw [compose_eval, hC]
  simp [hsel]

/-- (c) The claimed `d : 4 → 5` for A2′ is wrong when only the `.transition` segment is gated.
    `4 → 4`, not `4 → 5`. -/
theorem lnChain_is_degree_one : Reified.Trans.lnChainExpr.degree = 1 := by rfl

set_option maxRecDepth 200000 in
theorem gating_only_the_transition_keeps_maxDegree_four :
    (Reified.AIR.maxDegree
      { Reified.computeAIR with
        constraints := Reified.computeAIR.constraints ++
          [⟨.transition, .Mul (Reified.tc 93) Reified.Trans.lnChainExpr⟩] }) = 4 := by
  rfl

/-- Whereas gating a degree-4 `.row` gate DOES cost `+1` — which is why the `d : 4 → 5` charge is
    real only under the padding regime that §4 above shows is not forced. -/
theorem gating_a_deg4_expr_costs_one' (e : Reified.Expr) (he : e.degree = 4) (j : ℕ) :
    (Reified.Expr.Mul (Reified.tc j) e).degree = 5 := by
  simp [Reified.Expr.degree, Reified.tc, he]

end Rev2

section Audit
#print axioms Rev2.rap_domain_card_free
#print axioms Rev2.shipped_domain_card_is_exactly_n
#print axioms Rev2.no_power_of_two_obligation
#print axioms Rev2.erase_is_the_gate
#print axioms Rev2.satisfies_is_k_and_wRAP_blind
#print axioms Rev2.unpinned_selector_kills_every_gate
#print axioms Rev2.lnChain_is_degree_one
#print axioms Rev2.gating_only_the_transition_keeps_maxDegree_four
#print axioms Rev2.gating_a_deg4_expr_costs_one'
end Audit
