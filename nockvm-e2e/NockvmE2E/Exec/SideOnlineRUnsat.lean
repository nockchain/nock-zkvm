/-
 the kernel half of "the old `hglue` is unsatisfiable".

The old `hglue` (`exec_e2e_J8V''`/`'''`) has, as its first conjunct, `decS (sideOf g o).1 = ⟨[], fixCtx π ζ, vF⟩` with `[Finite Stmt']`.
`old_hglue_bounds_roots` (KERNEL): that conjunct, assumed on a set `P` of outputs, forces `π.roots[0]!.length` to be bounded on `P`.

WHAT THIS IS NOT: it is a reduction, not an unsatisfiability proof.  That `FixFail'` (SoundOnlineP.lean; it checks only `ctx.all based`)
really has outputs with unboundedly long `roots[0]` is ARGUED, not kernel-checked: it needs a concrete accepting side proof
(table `gF` constant on the FRI-node queries, honest VK opening, F1-recipe consistency), which was judged too costly.  The restated event
`FixFailR` (SideOnlineR.lean) bounds the roots (`FixFailR.roots_len`: every root has 5 limbs).
-/
import NockvmE2E.Exec.SideStmt
import NockvmE2E.Exec.SoundOnlineP

set_option autoImplicit false

namespace NockvmE2E.Exec.SideOnlineR
open NockvmE2E.Exec NockvmE2E.Exec.V

theorem len_le_flatMap (L : List (List Nat)) (a : List Nat) (h : a ∈ L) : a.length ≤ (L.flatMap id).length := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.flatMap_cons, id, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

/-- `roots[0]` is a block of the context -/
theorem fixCtx_length_ge (π : FlatProof) (ζ : VF.K3) : (π.roots[0]!).length ≤ (fixCtx π ζ).length := by
  unfold fixCtx
  rw [List.length_append]
  refine le_trans ?_ (Nat.le_add_right _ _)
  by_cases h : 0 < π.roots.size
  · have hmem : π.roots[0]! ∈ (π.roots.extract 0 4).toList := by
      have hs : 0 < (π.roots.extract 0 4).size := by simp; omega
      have : (π.roots.extract 0 4)[0]'hs = π.roots[0]! := by
        rw [getElem!_pos π.roots 0 h]; simp
      rw [← this]
      exact Array.getElem_mem_toList hs
    exact len_le_flatMap _ _ hmem
  · rw [getElem!_neg π.roots 0 h]
    exact Nat.zero_le _

/-- **Reduction (kernel).**  If the first conjunct of the old `hglue` holds on a set `P` of outputs `i` of an experiment index type `ι`
(`i` = `(g, gF, o)`), with `[Finite Stmt']`, then the root lengths of all outputs in `P` are bounded.  (`FixFail'` has no such bound --
ARGUED, not kernel-checked -- so the old `hglue` is unsatisfiable.) -/
theorem old_hglue_bounds_roots {ι Stmt' : Type} [Finite Stmt'] (decS : Stmt' → SideStmt) (P : ι → Prop) (sideStmt : ι → Stmt')
    (π : ι → FlatProof) (ζ : ι → VF.K3) (vF : ι → Array (Array VF.K3))
    (h : ∀ i, P i → decS (sideStmt i) = ⟨[], fixCtx (π i) (ζ i), vF i⟩) :
    ∃ B : ℕ, ∀ i, P i → (π i).roots[0]!.length ≤ B := by
  classical
  haveI : Fintype Stmt' := Fintype.ofFinite _
  refine ⟨Finset.univ.sup (fun s : Stmt' => (decS s).ctx.length), fun i hi => ?_⟩
  have h1 := h i hi
  have h2 : (decS (sideStmt i)).ctx = fixCtx (π i) (ζ i) := by rw [h1]
  refine le_trans (fixCtx_length_ge (π i) (ζ i)) ?_
  rw [← h2]
  exact Finset.le_sup (f := fun s : Stmt' => (decS s).ctx.length) (Finset.mem_univ _)

end NockvmE2E.Exec.SideOnlineR

#print axioms NockvmE2E.Exec.SideOnlineR.old_hglue_bounds_roots
