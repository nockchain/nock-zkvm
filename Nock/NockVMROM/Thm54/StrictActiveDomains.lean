import Nock.NockVMROM.Thm54.StrictOrbitPrefix
import Nock.NockVMROM.Thm54.CoordinateRAPCore

/-!
# Strict active domains for monolithic Theorem 5.4 chips

The physical polynomial capacity is `2^h`, while the two active domains have
exactly `N` and `M + 2L` rows.  This module derives both `Framework.RAP.H`
values from one strict orbit, so callers of `expandChip` do not choose arbitrary row Finsets.
-/

namespace Nock.NockVMROM.Thm54
namespace StrictExtension

open Nock.Framework
open Nock.NockVMROM.Thm54.MonolithicRAP
open Module

noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable {e h : ℕ}

/-- Capacity certificates for the two exact active row counts in Theorem 5.4. -/
structure MonolithicActiveDomains (orbit : StrictOrbitDomain F e h) (N M L : ℕ) : Prop where
  /-- The compute active prefix has `N` rows. -/
  computeCapacity : N ≤ 2 ^ h
  /-- The memory active prefix has `M + 2L` rows. -/
  memoryCapacity : M + 2 * L ≤ 2 ^ h

namespace MonolithicActiveDomains

variable {orbit : StrictOrbitDomain F e h} {N M L : ℕ}
/-- Exact compute active domain, definitionally the first `N` strict-orbit points. -/
def computeH (_D : MonolithicActiveDomains orbit N M L) : Finset F :=
  strictRowDomain orbit N

/-- Exact memory active domain, definitionally the first `M + 2L` strict-orbit points. -/
def memoryH (_D : MonolithicActiveDomains orbit N M L) : Finset F :=
  strictRowDomain orbit (M + 2 * L)

/-- Compute active cardinality is exactly `N`. -/
theorem computeH_card (D : MonolithicActiveDomains orbit N M L) :
    (computeH D).card = N :=
  strictRowDomain_card orbit D.computeCapacity

/-- Memory active cardinality is exactly `M + 2L`. -/
theorem memoryH_card (D : MonolithicActiveDomains orbit N M L) :
    (memoryH D).card = M + 2 * L :=
  strictRowDomain_card orbit D.memoryCapacity

/-- Both active domains fit in the full physical domain of `2^h` points. -/
theorem active_card_le_full_card (D : MonolithicActiveDomains orbit N M L) :
    (computeH D).card ≤ (strictFullDomain orbit).card ∧
      (memoryH D).card ≤ (strictFullDomain orbit).card := by
  rw [computeH_card D, memoryH_card D, strictFullDomain_card]
  exact ⟨D.computeCapacity, D.memoryCapacity⟩

/-- Both exact active domains are subsets of the full `2^h` physical domain. -/
theorem active_subset_full (D : MonolithicActiveDomains orbit N M L) :
    computeH D ⊆ strictFullDomain orbit ∧
      memoryH D ⊆ strictFullDomain orbit :=
  ⟨strictRowDomain_mono orbit D.computeCapacity,
    strictRowDomain_mono orbit D.memoryCapacity⟩

end MonolithicActiveDomains

variable {orbit : StrictOrbitDomain F e h} {N M L : ℕ}

/-- Coordinate-expand a chip directly on the strict active prefix of length `n`.
The resulting `Framework.RAP.H` is definitionally derived, not caller-supplied. -/
def expandChipOnStrictPrefix (T : ChipTemplate F) (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (n : ℕ) : RAP F :=
  expandChip T b chalVal pubVal orbit (strictRowDomain orbit n)

theorem expandChipOnStrictPrefix_H (T : ChipTemplate F) (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (n : ℕ) :
    (expandChipOnStrictPrefix T b chalVal pubVal orbit n).H = strictRowDomain orbit n :=
  rfl

theorem expandChipOnStrictPrefix_H_card (T : ChipTemplate F) (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (n : ℕ)
    (hcap : n ≤ 2 ^ h) :
    (expandChipOnStrictPrefix T b chalVal pubVal orbit n).H.card = n :=
  strictRowDomain_card orbit hcap

theorem expandChipOnStrictPrefix_order (T : ChipTemplate F) (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (n : ℕ) :
    orderOf (expandChipOnStrictPrefix T b chalVal pubVal orbit n).ω =
      (expandChipOnStrictPrefix T b chalVal pubVal orbit n).e *
        2 ^ (expandChipOnStrictPrefix T b chalVal pubVal orbit n).h :=
  orbit.order_ω

/-- Compute chip constructor whose `H` is definitionally the exact `N`-row active prefix. -/
def expandChipOnComputeDomain (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F) : RAP F :=
  expandChip T b chalVal pubVal orbit (MonolithicActiveDomains.computeH D)

/-- Memory chip constructor whose `H` is definitionally the exact `M + 2L` active prefix. -/
def expandChipOnMemoryDomain (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F) : RAP F :=
  expandChip T b chalVal pubVal orbit (MonolithicActiveDomains.memoryH D)

theorem expandChipOnComputeDomain_H_card (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F) :
    (expandChipOnComputeDomain D T b chalVal pubVal).H.card = N :=
  MonolithicActiveDomains.computeH_card D

theorem expandChipOnMemoryDomain_H_card (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F) :
    (expandChipOnMemoryDomain D T b chalVal pubVal).H.card = M + 2 * L :=
  MonolithicActiveDomains.memoryH_card D

end

end StrictExtension
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.StrictExtension.MonolithicActiveDomains.computeH_card
#print axioms Nock.NockVMROM.Thm54.StrictExtension.MonolithicActiveDomains.memoryH_card
#print axioms Nock.NockVMROM.Thm54.StrictExtension.expandChipOnStrictPrefix_H_card
#print axioms Nock.NockVMROM.Thm54.StrictExtension.expandChipOnStrictPrefix_order
