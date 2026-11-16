import Mathlib.LinearAlgebra.Lagrange
import Nock.Framework.FixedPreprocessingRAP

/-!
# Exact endpoint preprocessing masks

These are the verifier-fixed Lagrange selector polynomials used to mask boundary, terminal, and
last-row transition equations on an arbitrary finite row-node family.  They work uniformly for a
singleton trace (where both masks evaluate to one) and for multirow traces.
-/

namespace Nock.Framework

open scoped Polynomial

noncomputable section

variable {F : Type*} [Field F]

/-- The finite set of actual row nodes underlying the endpoint selectors. -/
def rowNodeSet {n : ℕ} (nodes : Fin n → F) : Finset F := by
  classical
  exact Finset.image nodes Finset.univ

/-- Exact first-row Lagrange selector on the supplied row nodes. -/
def firstRowMask {n : ℕ} (nodes : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ nodes
    (fun i => if (i : ℕ) = 0 then 1 else 0)

/-- Exact last-row Lagrange selector on a positive row family. -/
def lastRowMask {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ nodes
    (fun i => if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0)

theorem firstRowMask_eval {n : ℕ} (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) (i : Fin n) :
    (firstRowMask nodes).eval (nodes i) = if (i : ℕ) = 0 then 1 else 0 := by
  exact Lagrange.eval_interpolate_at_node
    (fun i : Fin n => if (i : ℕ) = 0 then 1 else 0)
    hnodes.injOn (Finset.mem_univ i)

theorem lastRowMask_eval {n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) (i : Fin n) :
    (lastRowMask hn nodes).eval (nodes i) =
      if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 := by
  exact Lagrange.eval_interpolate_at_node
    (fun i : Fin n =>
      if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0)
    hnodes.injOn (Finset.mem_univ i)

theorem firstRowMask_first {n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) :
    (firstRowMask nodes).eval (nodes ⟨0, hn⟩) = 1 := by
  simp [firstRowMask_eval nodes hnodes]

theorem lastRowMask_last {n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) :
    (lastRowMask hn nodes).eval
      (nodes ⟨n - 1, Nat.sub_lt hn (by omega)⟩) = 1 := by
  simp [lastRowMask_eval hn nodes hnodes]

/-- In a singleton trace the unique row is both endpoints. -/
theorem singleton_endpoint_masks (nodes : Fin 1 → F) :
    (firstRowMask nodes).eval (nodes 0) = 1 ∧
      (lastRowMask (by norm_num) nodes).eval (nodes 0) = 1 := by
  have hinj : Function.Injective nodes := fun i j _ => Subsingleton.elim i j
  exact ⟨firstRowMask_first (by norm_num) nodes hinj,
    lastRowMask_last (by norm_num) nodes hinj⟩

/-- On a multirow injective family the two selectors are disjoint at every row node. -/
theorem endpoint_masks_disjoint_at_nodes {n : ℕ} (hn : 1 < n)
    (nodes : Fin n → F) (hnodes : Function.Injective nodes) (i : Fin n) :
    (firstRowMask nodes).eval (nodes i) * (lastRowMask (by omega) nodes).eval (nodes i) = 0 := by
  rw [firstRowMask_eval nodes hnodes, lastRowMask_eval (by omega) nodes hnodes]
  by_cases hfirst : (i : ℕ) = 0
  · have hnotlast : i ≠ ⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩ := by
      intro hlast
      have hlastval := congrArg Fin.val hlast
      simp only at hlastval
      omega
    simp [hfirst, hnotlast]
  · simp [hfirst]

end

end Nock.Framework

#print axioms Nock.Framework.firstRowMask_eval
#print axioms Nock.Framework.lastRowMask_eval
#print axioms Nock.Framework.singleton_endpoint_masks
#print axioms Nock.Framework.endpoint_masks_disjoint_at_nodes
