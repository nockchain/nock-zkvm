/-
  Nock/NockVMROM/Thm54/P8Core/TraceGen/GenTraceConfined.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/TraceGen/GenTraceConfined.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable
variable {K : Type} [Field K]

/-- One row's own three nouns lie within the leaf window.  Decidable: three `Nat` comparisons. -/
def RowNounsConfined (Λ : ℕ) (g : GenComputeRow K) : Prop :=
  g.skel.subject.leaves ≤ Λ ∧ g.skel.formula.leaves ≤ Λ ∧ g.skel.evaluation.leaves ≤ Λ

/-- **The Λ-confinement premise** — the generator-side image of the `λ ≤ Λ` clause in
`FiniteTransitions^Λ`.

Stated over `bfsRows` rather than over `InTree` so that it is a `List` quantifier and therefore
carries a `Decidable` instance.  See the module docstring for why that instance does not reduce
under `decide` at the released carriers, and what discharges it instead. -/
def TraceConfined (Λ : ℕ) (t : NTree (GenComputeRow K)) : Prop :=
  ∀ g ∈ bfsRows t, RowNounsConfined Λ g

/-- `TraceConfined` read at an `InTree` node, which is the form the projection consumes. -/
theorem confined_inTree {Λ : ℕ} {t u : NTree (GenComputeRow K)}
    (h : TraceConfined Λ t) (hu : InTree t u) : RowNounsConfined Λ u.label := by
  refine h u.label ?_
  have hmem : u ∈ bfsForest [t] := (mem_bfsForest [t] u).mpr ⟨t, List.mem_singleton_self t, hu⟩
  exact List.mem_map.mpr ⟨u, hmem, rfl⟩

/-- One row's window numeral: max of subject / formula / evaluation leaves. -/
def rowNounsBound (g : GenComputeRow K) : ℕ :=
  g.skel.subject.leaves ⊔ g.skel.formula.leaves ⊔ g.skel.evaluation.leaves

theorem rowNounsConfined_iff_bound {Λ : ℕ} {g : GenComputeRow K} :
    RowNounsConfined Λ g ↔ rowNounsBound g ≤ Λ := by
  simp [RowNounsConfined, rowNounsBound]

/-- Fold of `⊔` starting at `acc` bounds `acc` and every `f x`. -/
theorem foldl_sup_le_of_le_aux {α : Type} (l : List α) (f : α → ℕ)
    (acc Λ : ℕ) (h : l.foldl (fun a x => a ⊔ f x) acc ≤ Λ) :
    acc ≤ Λ ∧ ∀ x ∈ l, f x ≤ Λ := by
  induction l generalizing acc with
  | nil =>
    exact ⟨h, fun _ hx => by cases hx⟩
  | cons a rest ih =>
    have hr := ih (acc ⊔ f a) (by simpa [List.foldl_cons] using h)
    have hacc : acc ≤ Λ ∧ f a ≤ Λ := max_le_iff.mp hr.1
    refine ⟨hacc.1, ?_⟩
    intro x hx
    simp [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hacc.2
    · exact hr.2 x hx

theorem foldl_sup_le_of_le {α : Type} (l : List α) (f : α → ℕ) {Λ : ℕ}
    (h : l.foldl (fun acc x => acc ⊔ f x) 0 ≤ Λ) :
    ∀ x ∈ l, f x ≤ Λ :=
  (foldl_sup_le_of_le_aux l f 0 Λ h).2

/-- The numeric `leafBound` of a generated compute tree. -/
def programLeafBound (t : NTree (GenComputeRow K)) : ℕ :=
  (bfsRows t).foldl (fun acc g => acc ⊔ rowNounsBound g) 0

/-- **`TraceConfined` from §1's window hyp.**  No growth invariant. -/
theorem traceConfined_of_leafBound {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (h : programLeafBound t ≤ Λ) : TraceConfined Λ t := by
  intro g hg
  rw [rowNounsConfined_iff_bound]
  exact foldl_sup_le_of_le (bfsRows t) rowNounsBound h g hg

end Nock.NockVMROM.Thm54.TraceGen
