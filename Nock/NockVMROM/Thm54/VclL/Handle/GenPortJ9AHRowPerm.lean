import Mathlib

/-!

One generic statement behind the walk / atom-walk row-permutation bridges: a family that is a
`flatMap` over the rows, a bad-event predicate over the family, and a sum over the rows are all
invariant under a permutation of the rows. -/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRowPerm

theorem fam_perm_of_flatMap {α β : Type} {g : β → List α} {L L' : List β} {F F' : List α}
    (hF : F = L.flatMap g) (hF' : F' = L'.flatMap g) (hp : L'.Perm L) : F'.Perm F := by
  subst hF hF'
  exact hp.flatMap_right _

theorem good_of_fam_perm {α C : Type} (ev : α → Set C) {F F' : List α} (hp : F'.Perm F) (χ : C)
    (h : ∀ e ∈ F, χ ∉ ev e) : ∀ e ∈ F', χ ∉ ev e :=
  fun e he => h e (hp.subset he)

theorem sum_perm_of_map {β M : Type} [AddCommMonoid M] (g : β → M) {L L' : List β} (hp : L'.Perm L) :
    (L'.map g).sum = (L.map g).sum :=
  (hp.map g).sum_eq

#print axioms fam_perm_of_flatMap
#print axioms good_of_fam_perm
#print axioms sum_perm_of_map

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRowPerm
