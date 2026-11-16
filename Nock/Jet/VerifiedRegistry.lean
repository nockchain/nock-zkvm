/-
  Nock/Jet/VerifiedRegistry.lean

  * `VerifiedRegistry`: a `Registry` bundled with `Registry.Faithful` (every entry is faithful AND complete
    against plain `evalN`, `JetSpec.Faithful` = `Faithful ∧ Complete`).
  * `VerifiedRegistry.empty`: no jets.
  * `VerifiedRegistry.ofCompiled p hp Rt regs hwt`: the registry of compiled templates (id `n ∈ regs` ↦
    `((Rt n).toTemplate p, compile p (Rt n))`); its proof is automatic from `compile_jetSpec_faithful`, given
    only that each template is well typed.
  * `VerifiedRegistry.add V n j hj`: register one more entry (e.g. a hand-written Hoon jet); the caller MUST
    supply `hj : j.Faithful` (faithfulness and completeness of that entry). There is no way to add an entry
    without it.
-/
import Nock.Jet.Semantics
import Nock.Jet.Autogen

set_option autoImplicit false

namespace Nock.Jet

/-- A registry together with the proof that every registered entry is faithful and complete. -/
structure VerifiedRegistry where
  R : Registry
  faithful : R.Faithful

namespace VerifiedRegistry

/-- The empty registry (no jets). -/
def empty : VerifiedRegistry where
  R := fun _ => none
  faithful := fun _ _ h => by cases h

open Nock.Jet.Autogen in
/-- The registry of compiled, well-typed templates: the faithfulness proof is a theorem, not an assumption. -/
def ofCompiled (p : ℕ) (hp : 0 < p) (Rt : ℕ → Tpl) (regs : List ℕ)
    (hwt : ∀ n ∈ regs, (Rt n).WellTyped p) : VerifiedRegistry where
  R := fun n => if n ∈ regs then some ⟨(Rt n).toTemplate p, compile p (Rt n)⟩ else none
  faithful := by
    intro n j h
    by_cases hn : n ∈ regs
    · simp only [hn, if_true, Option.some.injEq] at h
      subst h
      exact compile_jetSpec_faithful hp (Rt n) (hwt n hn)
    · simp only [hn, if_false] at h
      cases h

/-- Register one more entry. The entry's faithfulness and completeness proof is REQUIRED. -/
def add (V : VerifiedRegistry) (n : ℕ) (j : JetSpec) (hj : j.Faithful) : VerifiedRegistry where
  R := fun m => if m = n then some j else V.R m
  faithful := by
    intro m j' h
    by_cases hm : m = n
    · simp only [hm, if_true, Option.some.injEq] at h
      subst h
      exact hj
    · simp only [hm, if_false] at h
      exact V.faithful m j' h

end VerifiedRegistry

end Nock.Jet
