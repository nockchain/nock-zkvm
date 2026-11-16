import Nock.Framework.NockInstances

/-!
# Orbit-prefix domains for Theorem 5.4

This module packages the single multiplicative generator used both by `RAP.ω` and by
`Reify.envOfTrace`'s adjacent-row read.  Active domains are prefixes of that orbit, rather than
full padded cosets.

`transitionDomain` and `terminalDomain` require `0 < n`.  This makes their last active point
explicit and prevents truncated subtraction at `n = 0` from silently selecting `βcoset`.
-/

namespace Nock.Framework.Thm54

open Nock.Framework.Reify
open scoped Polynomial

variable {K : Type*} [Field K]

/-- A single-generator multiplicative orbit of capacity `2 ^ h`.

`βcoset` is the nonzero shift used by `Framework.RAP.β`; it is distinct from the LogUp pole
challenge called `β` in the memory table.
-/
structure OrbitDomain (K : Type*) [Field K] where
  h : ℕ
  ω : K
  βcoset : K
  βcoset_ne_zero : βcoset ≠ 0
  order_ω : orderOf ω = 2 ^ h

namespace OrbitDomain

/-- The `i`th point of the shifted `ω`-orbit. -/
def orbitPoint (D : OrbitDomain K) (i : ℕ) : K :=
  D.βcoset * D.ω ^ i

/-- The first `n` points of the shifted orbit.  At `n = 0` this is empty. -/
noncomputable def rowDomain (D : OrbitDomain K) (n : ℕ) : Finset K := by
  classical
  exact Finset.image (fun i : Fin n => D.orbitPoint i) Finset.univ

/-- The last valid index of a positive-length active prefix. -/
def lastIndex (_D : OrbitDomain K) (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn (by omega)⟩

/-- The last point of a positive-length active prefix. -/
def terminalPoint (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) : K :=
  D.orbitPoint (D.lastIndex n hn)

/-- Active transition points: the row prefix with its last point erased.

The positivity proof is intentionally part of the API: no meaning is assigned to `n - 1` at
zero length.
-/
noncomputable def transitionDomain (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) : Finset K := by
  classical
  exact (D.rowDomain n).erase (D.terminalPoint n hn)

/-- The boundary gate is evaluated at the first orbit point. -/
noncomputable def boundaryDomain (D : OrbitDomain K) : Finset K := by
  classical
  exact {D.βcoset}

/-- The terminal gate is evaluated at the last point of a positive active prefix. -/
noncomputable def terminalDomain (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) : Finset K := by
  classical
  exact {D.terminalPoint n hn}

@[simp]
theorem rowDomain_zero (D : OrbitDomain K) : D.rowDomain 0 = ∅ := by
  classical
  simp [rowDomain]

@[simp]
theorem orbitPoint_zero (D : OrbitDomain K) : D.orbitPoint 0 = D.βcoset := by
  simp [orbitPoint]

theorem orbitPoint_succ (D : OrbitDomain K) (i : ℕ) :
    D.ω * D.orbitPoint i = D.orbitPoint (i + 1) := by
  simp [orbitPoint, pow_succ]
  ring

/-- The order certificate forces the generator to be nonzero. -/
theorem omega_ne_zero (D : OrbitDomain K) : D.ω ≠ 0 := by
  intro hω
  have hord := D.order_ω
  simp [hω] at hord
  exact (Nat.ne_of_gt (Nat.two_pow_pos D.h)) hord.symm

/-- Orbit powers, and hence shifted orbit points, are injective below the certified capacity. -/
theorem orbitPoint_injective (D : OrbitDomain K) {n : ℕ} (hcap : n ≤ 2 ^ D.h) :
    Function.Injective (fun i : Fin n => D.orbitPoint i) := by
  intro i j hij
  apply Fin.ext
  have hp : D.ω ^ (i : ℕ) = D.ω ^ (j : ℕ) :=
    mul_left_cancel₀ D.βcoset_ne_zero hij
  let u : Kˣ := Units.mk0 D.ω D.omega_ne_zero
  have hpu : u ^ (i : ℕ) = u ^ (j : ℕ) := by
    apply Units.ext
    simpa [u] using hp
  have huorder : orderOf u = 2 ^ D.h := by
    rw [← orderOf_units]
    simpa [u] using D.order_ω
  have hiorder : (i : ℕ) < orderOf u := by
    rw [huorder]
    exact i.isLt.trans_le hcap
  have hjorder : (j : ℕ) < orderOf u := by
    rw [huorder]
    exact j.isLt.trans_le hcap
  have hmod : (i : ℕ) % orderOf u = (j : ℕ) % orderOf u :=
    pow_inj_mod.mp hpu
  simpa [Nat.mod_eq_of_lt hiorder, Nat.mod_eq_of_lt hjorder] using hmod

theorem orbitPoint_mem_rowDomain (D : OrbitDomain K) {n : ℕ} (i : Fin n) :
    D.orbitPoint i ∈ D.rowDomain n := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem boundaryPoint_mem_rowDomain (D : OrbitDomain K) {n : ℕ} (hn : 0 < n) :
    D.βcoset ∈ D.rowDomain n := by
  classical
  simpa using D.orbitPoint_mem_rowDomain (⟨0, hn⟩ : Fin n)

theorem terminalPoint_mem_rowDomain (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) :
    D.terminalPoint n hn ∈ D.rowDomain n := by
  classical
  exact D.orbitPoint_mem_rowDomain (D.lastIndex n hn)

theorem terminalPoint_not_mem_transitionDomain (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) :
    D.terminalPoint n hn ∉ D.transitionDomain n hn := by
  classical
  exact Finset.notMem_erase _ _

theorem transitionDomain_subset_rowDomain (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) :
    D.transitionDomain n hn ⊆ D.rowDomain n := by
  classical
  exact Finset.erase_subset _ _

/-- Every active point except the last belongs to the transition domain. -/
theorem orbitPoint_mem_transitionDomain (D : OrbitDomain K) {n : ℕ} (hn : 0 < n)
    (hcap : n ≤ 2 ^ D.h) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    D.orbitPoint i ∈ D.transitionDomain n hn := by
  classical
  rw [transitionDomain, Finset.mem_erase]
  refine ⟨?_, D.orbitPoint_mem_rowDomain i⟩
  intro heq
  have hfin : i = D.lastIndex n hn :=
    D.orbitPoint_injective hcap heq
  have hlast : (D.lastIndex n hn : ℕ) + 1 = n := by
    simp [lastIndex, Nat.sub_add_cancel hn]
  rw [hfin, hlast] at hi
  omega

@[simp]
theorem boundaryPoint_mem_boundaryDomain (D : OrbitDomain K) :
    D.βcoset ∈ D.boundaryDomain := by
  classical
  simp [boundaryDomain]

@[simp]
theorem terminalPoint_mem_terminalDomain (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) :
    D.terminalPoint n hn ∈ D.terminalDomain n hn := by
  classical
  simp [terminalDomain]

/-- A prefix within the certified orbit capacity has exactly its active length many points. -/
theorem rowDomain_card (D : OrbitDomain K) {n : ℕ} (hcap : n ≤ 2 ^ D.h) :
    (D.rowDomain n).card = n := by
  classical
  rw [rowDomain, Finset.card_image_of_injective _ (D.orbitPoint_injective hcap),
    Finset.card_univ, Fintype.card_fin]

/-- Erasing the last active point leaves exactly `n - 1` transition points. -/
theorem transitionDomain_card (D : OrbitDomain K) (n : ℕ) (hn : 0 < n)
    (hcap : n ≤ 2 ^ D.h) :
    (D.transitionDomain n hn).card = n - 1 := by
  classical
  rw [transitionDomain, Finset.card_erase_of_mem (D.terminalPoint_mem_rowDomain n hn),
    D.rowDomain_card hcap]

/-- The orbit-prefix replacement for a padded cyclic domain: it has `n` rows and its last row is
not a transition point. -/
theorem prefix_domain_excludes_wrap (D : OrbitDomain K) (n : ℕ) (hn : 0 < n)
    (hcap : n ≤ 2 ^ D.h) :
    (D.rowDomain n).card = n ∧
      D.terminalPoint n hn ∉ D.transitionDomain n hn :=
  ⟨D.rowDomain_card hcap, D.terminalPoint_not_mem_transitionDomain n hn⟩

/-- Reading `traceNext` at an orbit point evaluates the trace polynomial at the next orbit point. -/
theorem orbitPoint_gives_adjacency (D : OrbitDomain K) {w : ℕ} (P : Fin w → K[X]) (k : ℕ)
    (chalVal pubVal : ℕ → K) (i : ℕ) (hi : i < w) :
    (envOfTrace P D.ω (D.orbitPoint k) chalVal pubVal).traceNext i =
      (P ⟨i, hi⟩).eval (D.orbitPoint (k + 1)) := by
  simp only [envOfTrace, dif_pos hi]
  rw [← D.orbitPoint_succ]

/-- A node map identified with the orbit prefix has genuine adjacent-row `envOfTrace` reads. -/
theorem orbit_gives_adjacency (D : OrbitDomain K) {w : ℕ} (P : Fin w → K[X]) (k : ℕ)
    (chalVal pubVal : ℕ → K) (nodes : ℕ → K)
    (nodes_spec : ∀ j, nodes j = D.orbitPoint j) (i : ℕ) (hi : i < w) :
    (envOfTrace P D.ω (nodes k) chalVal pubVal).traceNext i =
      (P ⟨i, hi⟩).eval (nodes (k + 1)) := by
  rw [nodes_spec k, nodes_spec (k + 1)]
  exact D.orbitPoint_gives_adjacency P k chalVal pubVal i hi

end OrbitDomain

end Nock.Framework.Thm54

#print axioms Nock.Framework.Thm54.OrbitDomain.orbitPoint_injective
#print axioms Nock.Framework.Thm54.OrbitDomain.orbitPoint_mem_transitionDomain
#print axioms Nock.Framework.Thm54.OrbitDomain.prefix_domain_excludes_wrap
#print axioms Nock.Framework.Thm54.OrbitDomain.orbit_gives_adjacency
