import Nock.NockVMROM.Thm54.ExtensionField
import Nock.Framework.Thm54.OrbitDomain

/-!
# Strict-orbit active prefixes

The paper fixes physical column capacity `2^h` while the strict RAP generator has order
`e * 2^h`.  This module exposes the first `n` strict-orbit points as the
active domain and proves its cardinality, adjacency, and terminal no-wrap properties for
`n ≤ 2^h`.
-/

namespace Nock.NockVMROM.Thm54
namespace StrictExtension

open Nock.Framework.Reify
open scoped Polynomial

noncomputable section

variable {F : Type*} [Field F] {e h : ℕ}

/-- The `i`th point in the shifted strict orbit. -/
def strictOrbitPoint (D : StrictOrbitDomain F e h) (i : ℕ) : F :=
  D.βcoset * D.ω ^ i

/-- The exact active prefix of length `n`; the physical capacity remains `2^h`. -/
def strictRowDomain (D : StrictOrbitDomain F e h) (n : ℕ) : Finset F := by
  classical
  exact Finset.image (fun i : Fin n => strictOrbitPoint D i) Finset.univ

/-- The full physical trace domain of `2^h` points, distinct from a shorter active prefix. -/
def strictFullDomain (D : StrictOrbitDomain F e h) : Finset F := by
  classical
  exact strictRowDomain D (2 ^ h)

/-- Last valid index of a positive strict active prefix. -/
def strictLastIndex (_D : StrictOrbitDomain F e h) (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn (by omega)⟩

/-- Last point of a positive strict active prefix. -/
def strictTerminalPoint (D : StrictOrbitDomain F e h) (n : ℕ) (hn : 0 < n) : F :=
  strictOrbitPoint D (strictLastIndex D n hn)

/-- Active transition points, with the last active point removed. -/
def strictTransitionDomain (D : StrictOrbitDomain F e h) (n : ℕ) (hn : 0 < n) :
    Finset F := by
  classical
  exact (strictRowDomain D n).erase (strictTerminalPoint D n hn)

/-- Boundary domain at the first strict-orbit point. -/
def strictBoundaryDomain (D : StrictOrbitDomain F e h) : Finset F := by
  classical
  exact {D.βcoset}

/-- Terminal domain at the final point of a positive active prefix. -/
def strictTerminalDomain (D : StrictOrbitDomain F e h) (n : ℕ) (hn : 0 < n) :
    Finset F := by
  classical
  exact {strictTerminalPoint D n hn}

@[simp]
theorem strictRowDomain_zero (D : StrictOrbitDomain F e h) :
    strictRowDomain D 0 = ∅ := by
  classical
  simp [strictRowDomain]

@[simp]
theorem strictOrbitPoint_zero (D : StrictOrbitDomain F e h) :
    strictOrbitPoint D 0 = D.βcoset := by
  simp [strictOrbitPoint]

theorem strictOrbitPoint_succ (D : StrictOrbitDomain F e h) (i : ℕ) :
    D.ω * strictOrbitPoint D i = strictOrbitPoint D (i + 1) := by
  simp [strictOrbitPoint, pow_succ]
  ring

/-- Exact positive order forces the strict generator to be nonzero. -/
theorem strictOmega_ne_zero (D : StrictOrbitDomain F e h) : D.ω ≠ 0 := by
  intro hω
  have hord := D.order_ω
  simp [hω] at hord
  exact (Nat.ne_of_gt D.e_pos) hord

/-- The physical capacity lies below the strict generator's exact order. -/
theorem physicalCapacity_le_order (D : StrictOrbitDomain F e h) :
    2 ^ h ≤ orderOf D.ω := by
  rw [D.order_ω]
  calc
    2 ^ h = 1 * 2 ^ h := by simp
    _ ≤ e * 2 ^ h := Nat.mul_le_mul_right (2 ^ h) D.e_pos

/-- Strict-orbit points are injective throughout every active prefix fitting in `2^h`. -/
theorem strictOrbitPoint_injective (D : StrictOrbitDomain F e h) {n : ℕ}
    (hcap : n ≤ 2 ^ h) :
    Function.Injective (fun i : Fin n => strictOrbitPoint D i) := by
  intro i j hij
  apply Fin.ext
  have hp : D.ω ^ (i : ℕ) = D.ω ^ (j : ℕ) :=
    mul_left_cancel₀ D.βcoset_ne_zero hij
  let u : Fˣ := Units.mk0 D.ω (strictOmega_ne_zero D)
  have hpu : u ^ (i : ℕ) = u ^ (j : ℕ) := by
    apply Units.ext
    simpa [u] using hp
  have huorder : orderOf u = e * 2 ^ h := by
    rw [← orderOf_units]
    simpa [u] using D.order_ω
  have hphys : 2 ^ h ≤ e * 2 ^ h := by
    calc
      2 ^ h = 1 * 2 ^ h := by simp
      _ ≤ e * 2 ^ h := Nat.mul_le_mul_right (2 ^ h) D.e_pos
  have hiorder : (i : ℕ) < orderOf u := by
    rw [huorder]
    exact i.isLt.trans_le (hcap.trans hphys)
  have hjorder : (j : ℕ) < orderOf u := by
    rw [huorder]
    exact j.isLt.trans_le (hcap.trans hphys)
  have hmod : (i : ℕ) % orderOf u = (j : ℕ) % orderOf u :=
    pow_inj_mod.mp hpu
  simpa [Nat.mod_eq_of_lt hiorder, Nat.mod_eq_of_lt hjorder] using hmod

theorem strictOrbitPoint_mem_rowDomain (D : StrictOrbitDomain F e h) {n : ℕ} (i : Fin n) :
    strictOrbitPoint D i ∈ strictRowDomain D n := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Membership in the active domain is exactly representation by one bounded row index. -/
theorem mem_strictRowDomain_iff (D : StrictOrbitDomain F e h) {n : ℕ} (x : F) :
    x ∈ strictRowDomain D n ↔ ∃ i : Fin n, strictOrbitPoint D i = x := by
  classical
  simp [strictRowDomain]

/-- A shorter active prefix is a subset of every longer prefix. -/
theorem strictRowDomain_mono (D : StrictOrbitDomain F e h) {m n : ℕ} (hmn : m ≤ n) :
    strictRowDomain D m ⊆ strictRowDomain D n := by
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_strictRowDomain_iff D _).mp hx
  simpa using strictOrbitPoint_mem_rowDomain D (Fin.castLE hmn i)

theorem strictBoundaryPoint_mem_rowDomain (D : StrictOrbitDomain F e h) {n : ℕ}
    (hn : 0 < n) :
    D.βcoset ∈ strictRowDomain D n := by
  simpa using strictOrbitPoint_mem_rowDomain D (⟨0, hn⟩ : Fin n)

theorem strictTerminalPoint_mem_rowDomain (D : StrictOrbitDomain F e h) (n : ℕ)
    (hn : 0 < n) :
    strictTerminalPoint D n hn ∈ strictRowDomain D n :=
  strictOrbitPoint_mem_rowDomain D (strictLastIndex D n hn)

theorem strictTerminalPoint_not_mem_transitionDomain (D : StrictOrbitDomain F e h) (n : ℕ)
    (hn : 0 < n) :
    strictTerminalPoint D n hn ∉ strictTransitionDomain D n hn := by
  classical
  exact Finset.notMem_erase _ _

theorem strictTransitionDomain_subset_rowDomain (D : StrictOrbitDomain F e h) (n : ℕ)
    (hn : 0 < n) :
    strictTransitionDomain D n hn ⊆ strictRowDomain D n := by
  classical
  exact Finset.erase_subset _ _

/-- Every active point strictly before the last belongs to the transition domain. -/
theorem strictOrbitPoint_mem_transitionDomain (D : StrictOrbitDomain F e h) {n : ℕ}
    (hn : 0 < n) (hcap : n ≤ 2 ^ h) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    strictOrbitPoint D i ∈ strictTransitionDomain D n hn := by
  classical
  rw [strictTransitionDomain, Finset.mem_erase]
  refine ⟨?_, strictOrbitPoint_mem_rowDomain D i⟩
  intro heq
  have hfin : i = strictLastIndex D n hn :=
    strictOrbitPoint_injective D hcap heq
  have hlast : (strictLastIndex D n hn : ℕ) + 1 = n := by
    simp [strictLastIndex, Nat.sub_add_cancel hn]
  rw [hfin, hlast] at hi
  omega

@[simp]
theorem strictBoundaryPoint_mem_boundaryDomain (D : StrictOrbitDomain F e h) :
    D.βcoset ∈ strictBoundaryDomain D := by
  classical
  simp [strictBoundaryDomain]

@[simp]
theorem strictTerminalPoint_mem_terminalDomain (D : StrictOrbitDomain F e h) (n : ℕ)
    (hn : 0 < n) :
    strictTerminalPoint D n hn ∈ strictTerminalDomain D n hn := by
  classical
  simp [strictTerminalDomain]

/-- An active strict-orbit prefix has exactly its declared number of rows. -/
theorem strictRowDomain_card (D : StrictOrbitDomain F e h) {n : ℕ}
    (hcap : n ≤ 2 ^ h) :
    (strictRowDomain D n).card = n := by
  classical
  rw [strictRowDomain,
    Finset.card_image_of_injective _ (strictOrbitPoint_injective D hcap),
    Finset.card_univ, Fintype.card_fin]

/-- The full physical domain has exactly `2^h` points. -/
theorem strictFullDomain_card (D : StrictOrbitDomain F e h) :
    (strictFullDomain D).card = 2 ^ h :=
  strictRowDomain_card D le_rfl

/-- Removing the terminal point leaves exactly `n - 1` transition points. -/
theorem strictTransitionDomain_card (D : StrictOrbitDomain F e h) (n : ℕ) (hn : 0 < n)
    (hcap : n ≤ 2 ^ h) :
    (strictTransitionDomain D n hn).card = n - 1 := by
  classical
  rw [strictTransitionDomain,
    Finset.card_erase_of_mem (strictTerminalPoint_mem_rowDomain D n hn),
    strictRowDomain_card D hcap]

/-- The active prefix has exact cardinality and excludes its terminal row from transitions:
there is no active-domain wraparound. -/
theorem strictPrefix_domain_excludes_wrap (D : StrictOrbitDomain F e h) (n : ℕ)
    (hn : 0 < n) (hcap : n ≤ 2 ^ h) :
    (strictRowDomain D n).card = n ∧
      strictTerminalPoint D n hn ∉ strictTransitionDomain D n hn :=
  ⟨strictRowDomain_card D hcap, strictTerminalPoint_not_mem_transitionDomain D n hn⟩

/-- A next-row read at a strict-orbit point evaluates at the actual adjacent orbit point. -/
theorem strictOrbitPoint_gives_adjacency (D : StrictOrbitDomain F e h) {w : ℕ}
    (P : Fin w → F[X]) (k : ℕ) (chalVal pubVal : ℕ → F) (i : ℕ) (hi : i < w) :
    (envOfTrace P D.ω (strictOrbitPoint D k) chalVal pubVal).traceNext i =
      (P ⟨i, hi⟩).eval (strictOrbitPoint D (k + 1)) := by
  simp only [envOfTrace, dif_pos hi]
  rw [← strictOrbitPoint_succ]

end

end StrictExtension
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.StrictExtension.strictOrbitPoint_injective
#print axioms Nock.NockVMROM.Thm54.StrictExtension.strictRowDomain_card
#print axioms Nock.NockVMROM.Thm54.StrictExtension.strictPrefix_domain_excludes_wrap
#print axioms Nock.NockVMROM.Thm54.StrictExtension.strictOrbitPoint_gives_adjacency
