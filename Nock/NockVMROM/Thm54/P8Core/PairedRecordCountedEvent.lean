/-
  Nock/NockVMROM/Thm54/P8Core/PairedRecordCountedEvent.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.PairedRecordCountedEvent`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/PairedRecordCountedEvent.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Nock.NockVMROM.Thm54.PairedRecordCountedEvent

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54

noncomputable section

section Generic

variable {A B : Type*}

/-- A `List.Perm` of images un-maps along a function injective **only on the two lists' own
elements** — exactly the strength `FiniteIO.rlc_inj_of_not_collision` delivers off the counted
RLC-collision event.  Proven by multiplicity counting, so no global injectivity is needed. -/
theorem perm_of_perm_map_of_injOn [DecidableEq A] [DecidableEq B]
    (f : A → B) {l l' : List A}
    (hinj : ∀ u ∈ l ++ l', ∀ v ∈ l ++ l', f u = f v → u = v)
    (h : (l.map f).Perm (l'.map f)) : l.Perm l' := by
  classical
  refine List.perm_iff_count.mpr (fun a => ?_)
  by_cases ha : a ∈ l ++ l'
  · have key : ∀ m : List A, (∀ x ∈ m, x ∈ l ++ l') →
        (m.map f).count (f a) = m.count a := by
      intro m
      induction m with
      | nil => simp
      | cons b t ih =>
          intro hm
          have hb : b ∈ l ++ l' := hm b List.mem_cons_self
          have ht : ∀ x ∈ t, x ∈ l ++ l' := fun x hx => hm x (List.mem_cons_of_mem _ hx)
          by_cases hba : b = a
          · subst hba
            simp [ih ht]
          · have hfba : f b ≠ f a := fun he => hba (hinj b hb a ha he)
            simp [ih ht, hba, hfba]
    rw [← key l (fun x hx => List.mem_append_left _ hx),
      ← key l' (fun x hx => List.mem_append_right _ hx)]
    exact h.count_eq (f a)
  · have h1 : a ∉ l := fun hx => ha (List.mem_append_left _ hx)
    have h2 : a ∉ l' := fun hx => ha (List.mem_append_right _ hx)
    rw [List.count_eq_zero.mpr h1, List.count_eq_zero.mpr h2]

/-- The `Fin`-indexed product over a list's positions is the mapped list product. -/
theorem prod_map_eq_prod_fin {M' : Type*} [CommMonoid M'] (g : A → M') :
    ∀ l : List A, (l.map g).prod = ∏ i : Fin l.length, g (l.get i) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ih, Fin.prod_univ_succ]
      simp

end Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- The `Fin`-indexed multiplicative set-equality product of a compressed column is the mapped list
product, regrouped as a multiset product — the form `IO.prodXaddC_ms_inj` consumes. -/
theorem denomP_eq_ms_prod {m : ℕ} (γ : K) (l : List (Fin m → K)) :
    FiniteIO.denomP (fun i : Fin l.length => Walk.rlc γ (l.get i))
      = (((l.map (Walk.rlc γ) : List K) : Multiset K).map
          (fun c => Polynomial.X + Polynomial.C c)).prod := by
  rw [FiniteIO.denomP,
    ← prod_map_eq_prod_fin (fun v => Polynomial.X + Polynomial.C (Walk.rlc γ v)) l,
    Multiset.map_coe, Multiset.prod_coe, List.map_map]
  rfl

end

end Nock.NockVMROM.Thm54.PairedRecordCountedEvent
