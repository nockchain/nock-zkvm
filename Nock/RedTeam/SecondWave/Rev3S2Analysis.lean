/-
  FOURTH-PASS ADVERSARIAL REVIEW of plan §D1b.  Part 3: the S2 / F2 analysis.
    * the S6 sub-claim, REFUTED;
    * `Rprog` is not merely unread — it is VACUOUSLY SATISFIED;
    * what a genuinely load-bearing S2 looks like, inhabited by real Nock data.
-/
import Nock.Framework
import Nock.AIR
import Nock.NockVMROM.CanonicalRAP
import Nock.NockVMROM.Completeness

namespace Rev3

open Nock Nock.Framework Nock.Framework.Reify Nock.Reified Nock.NockVMROM Nock.ComputeTable
open scoped Polynomial
open Classical

/-! ## 2a.  The stored `Rprog` is not just "unread" — its domain is EMPTY, so it is satisfied by
    every conceivable trace, including the zero trace.  `Rprog` carries no information at all. -/

theorem stored_Rprog_satisfied_by_everything
    (P : Fin (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rprog.w → ℚ[X]) :
    (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rprog.Satisfies P := by
  intro i x hx
  exact absurd hx (Finset.notMem_empty x)

theorem stored_Rmem_satisfied_by_everything
    (P : Fin (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rmem.w → ℚ[X]) :
    (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rmem.Satisfies P := by
  intro i x hx
  exact absurd hx (Finset.notMem_empty x)

/-! ## 2b.  `Rprog`/`Rmem` are free slots: the shipped instance's ENTIRE content survives replacing
    them by ARBITRARY RAPs. -/

@[reducible] noncomputable def anyRAPs_same_content (R R' : RAP ℚ) :
    HasCanonicalRAP (Tag ℚ ℚ 0 1 1) (nmrMEF ℚ ℚ) ℚ :=
  { nock_hasCanonicalRAP ℚ ℚ 0 1 1 with Rprog := R, Rmem := R' }

theorem content_is_Rprog_independent (R R' : RAP ℚ) (p : ComputeProblem ℚ) :
    ((anyRAPs_same_content R R').progAccepts p ↔ (anyRAPs_same_content R R').progSatisfiable p)
      ↔ ((nock_hasCanonicalRAP ℚ ℚ 0 1 1).progAccepts p
          ↔ (nock_hasCanonicalRAP ℚ ℚ 0 1 1).progSatisfiable p) := Iff.rfl

/-! ## 2c.  The plan says S5/S6/S7 "reference no
    RAP object"; it only checked `TwoRAP.lean`.  S6's `nockCompletenessModel` DOES reference an
    `airToRAP` object and its `RAP.Satisfies`, definitionally. -/

theorem s6_does_reference_a_rap (p : ComputeProblem ℚ) :
    (nockCompletenessModel ℚ ℚ 0 1 1).hasSatisfyingAssignment p
      ↔ (nock_hasCanonicalRAP ℚ ℚ 0 1 1).progSatisfiable p := Iff.rfl

/-- …and that predicate is literally a `RAP.Satisfies` of an `airToRAP` object: it is the S2
    `progSatisfiable`, whose unfolding is the `airToRAP computeAIR …` satisfaction (see
    `Nock/NockVMROM/CanonicalRAP.lean:79-82`, `Nock/NockVMROM/Completeness.lean:29-30`). -/
theorem s6_rap_is_nonvacuous_shape (p : ComputeProblem ℚ) :
    (nockCompletenessModel ℚ ℚ 0 1 1).hasSatisfyingAssignment p
      ↔ (nock_hasCanonicalRAP ℚ ℚ 0 1 1).progAccepts p :=
  ((nock_hasCanonicalRAP ℚ ℚ 0 1 1).compute_iff p).symm

/-! ## 2d.  WHAT A LOAD-BEARING S2 WOULD HAVE TO LOOK LIKE.

  The defect is NOT that `Rprog` is a single RAP rather than two dependent ones.  It is that
  `compute_iff` relates two *instance-chosen* predicates. -/

class HasCanonicalRAP2 (ι : Type u) [VMSystem ι] (M : MEF) (F : Type*) [Field F] where
  air : Reified.AIR
  ProgProblem : Type*
  /-- Per-problem auxiliary (prover) witness type. -/
  Aux : ProgProblem → Type*
  /-- The RAP is a FUNCTION of the problem (per-problem `chalVal/e/h/ω/β/H`). -/
  Rprog : ProgProblem → RAP F
  /-- Anti-degeneracy: the RAP really is the reification of `air`. -/
  Rprog_pinned : ∀ p, ∃ (chalVal pubVal : ℕ → F) (eDeg hExp : ℕ) (ω β : F) (H : Finset F)
      (hβ : β ≠ 0) (hh1 : 1 ≤ hExp),
      Rprog p = airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1
  encodeProg : (p : ProgProblem) → Aux p → (Fin (Rprog p).w → F[X])
  progAccepts : ProgProblem → Prop
  /-- The load-bearing iff: the RHS is FORCED to be RAP satisfaction of the stored RAP. -/
  compute_iff : ∀ p, progAccepts p ↔ ∃ a : Aux p, (Rprog p).Satisfies (encodeProg p a)

/-- **And it is inhabited by the real Nock data, with no new mathematics** — `computeTable_reified_iff`
    discharges it verbatim.  So the load-bearing S2 is available today at zero proof cost; the
    obstruction was only the class SHAPE. -/
noncomputable instance nock_hasCanonicalRAP2 (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    HasCanonicalRAP2 (Tag F K α β Ksz) (nmrMEF F K) K where
  air := computeAIR
  ProgProblem := ComputeProblem K
  Aux p := Fin p.n → ComputeTable.Extra K
  Rprog p := airToRAP computeAIR p.chalVal (fun _ => 0) p.eDeg p.hExp p.ω p.β
      (Finset.image p.nodes Finset.univ) p.hβ p.hh1
  Rprog_pinned p := ⟨p.chalVal, fun _ => 0, p.eDeg, p.hExp, p.ω, p.β,
      Finset.image p.nodes Finset.univ, p.hβ, p.hh1, rfl⟩
  encodeProg p ex := encodeComputeTrace
      (fun k => computeEnvFull (p.inp k) (opSel (p.pub k).state) (p.pub k) (p.dec k) (ex k)) p.nodes
  progAccepts p := ∀ k, ComputeTable.Vcomp (p.inp k) (p.pub k) (p.dec k)
  compute_iff p := computeTable_reified_iff p.inp p.pub p.dec p.nodes p.hnodes p.chalVal p.eDeg
      p.hExp p.ω p.β p.hβ p.hh1 p.hchal p.hwf p.hz

end Rev3

section Audit
#print axioms Rev3.stored_Rprog_satisfied_by_everything
#print axioms Rev3.stored_Rmem_satisfied_by_everything
#print axioms Rev3.content_is_Rprog_independent
#print axioms Rev3.s6_does_reference_a_rap
#print axioms Rev3.s6_rap_is_nonvacuous_shape
#print axioms Rev3.nock_hasCanonicalRAP2
end Audit
