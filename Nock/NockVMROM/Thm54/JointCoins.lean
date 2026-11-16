import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Joint challenge space for Theorem 5.4

This module places the compute-pair, memory-pair, and NPR-seed bad events in one finite
four-coordinate space.  Compute and memory use the same `γ` coordinate by construction.

All bounds are cardinality bounds.  In particular, none of them assumes independence between
the compute, memory, or seed events.
-/

open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54

/-! ## Joint space and named projections -/

/-- The four joint coins, arranged as `((αc, γ), (αm, z))`.

The nested product is intentional: the compute pair is the first component, while the memory pair
is obtained by pairing `αm` with the already-present shared `γ`. -/
abbrev JointCoins (K : Type*) := (K × K) × (K × K)

/-- Compute-walk challenge `αc`. -/
def alphaC {K : Type*} (ω : JointCoins K) : K := ω.1.1

/-- The timestamp coin `αm` (`α`): the base of the committed timestamps `α^k`. -/
def alphaM {K : Type*} (ω : JointCoins K) : K := ω.2.1

/-- The single node-RLC challenge shared by the compute and memory experiments. -/
def gamma {K : Type*} (ω : JointCoins K) : K := ω.1.2

/-- NPR seed `z`. -/
def nprSeed {K : Type*} (ω : JointCoins K) : K := ω.2.2

/-- The compute experiment reads `(αc, γ)`. -/
def computeCoins {K : Type*} (ω : JointCoins K) : K × K :=
  (alphaC ω, gamma ω)

/-- The memory experiment reads `(αm, γ)`, reusing the joint experiment's one `γ`. -/
def memoryCoins {K : Type*} (ω : JointCoins K) : K × K :=
  (alphaM ω, gamma ω)

@[simp] theorem computeCoins_gamma {K : Type*} (ω : JointCoins K) :
    (computeCoins ω).2 = gamma ω := rfl

@[simp] theorem memoryCoins_gamma {K : Type*} (ω : JointCoins K) :
    (memoryCoins ω).2 = gamma ω := rfl

/-- The compute and memory pair projections share their second coordinate definitionally. -/
theorem compute_memory_shared_gamma {K : Type*} (ω : JointCoins K) :
    (computeCoins ω).2 = (memoryCoins ω).2 := rfl

/-- Reorder `((αm, γ), (αc, z))` into the canonical joint layout
`((αc, γ), (αm, z))`. -/
def memoryReorder (K : Type*) :
    ((K × K) × (K × K)) ≃ JointCoins K where
  toFun ω := ((ω.2.1, ω.1.2), (ω.1.1, ω.2.2))
  invFun ω := ((ω.2.1, ω.1.2), (ω.1.1, ω.2.2))
  left_inv := by
    rintro ⟨⟨αm, γ⟩, ⟨αc, z⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨αc, γ⟩, ⟨αm, z⟩⟩
    rfl

/-! ## Cardinal union bounds -/

/-- Union bound for two events in the common joint space. -/
theorem card_union_le {K : Type*} (E F : Finset (JointCoins K)) :
    (E ∪ F).card ≤ E.card + F.card :=
  Finset.card_union_le E F

/-- Finite-family union bound in the common joint space. -/
theorem card_biUnion_le {K ι : Type*} (s : Finset ι)
    (E : ι → Finset (JointCoins K)) :
    (s.biUnion E).card ≤ ∑ i ∈ s, (E i).card :=
  Finset.card_biUnion_le

/-! ## Event lifts and exact extension factors -/

section Finite

variable {K : Type*} [Fintype K]

/-- Lift a two-coin compute event, leaving `(αm, z)` unrestricted. -/
noncomputable def liftCompute (A : Finset (K × K)) : Finset (JointCoins K) :=
  A ×ˢ (Finset.univ : Finset (K × K))

/-- Lift a two-coin memory event.  The reordering puts its `γ` in the shared joint slot. -/
noncomputable def liftMemory (A : Finset (K × K)) : Finset (JointCoins K) :=
  (A ×ˢ (Finset.univ : Finset (K × K))).map (memoryReorder K).toEmbedding

/-- Lift an NPR-seed event, leaving `(αc, γ, αm)` unrestricted. -/
noncomputable def liftSeed (B : Finset K) : Finset (JointCoins K) :=
  (Finset.univ : Finset (K × K)) ×ˢ ((Finset.univ : Finset K) ×ˢ B)

@[simp] theorem mem_liftCompute_iff (A : Finset (K × K)) (ω : JointCoins K) :
    ω ∈ liftCompute A ↔ computeCoins ω ∈ A := by
  simp [liftCompute, computeCoins, alphaC, gamma]

@[simp] theorem mem_liftMemory_iff (A : Finset (K × K)) (ω : JointCoins K) :
    ω ∈ liftMemory A ↔ memoryCoins ω ∈ A := by
  rw [liftMemory, Finset.mem_map_equiv]
  simp [memoryReorder, memoryCoins, alphaM, gamma]

@[simp] theorem mem_liftSeed_iff (B : Finset K) (ω : JointCoins K) :
    ω ∈ liftSeed B ↔ nprSeed ω ∈ B := by
  simp [liftSeed, nprSeed]

/-- The joint sample space has exactly `|K|⁴` elements. -/
theorem card_jointCoins :
    Fintype.card (JointCoins K) = Fintype.card K ^ 4 := by
  simp only [JointCoins, Fintype.card_prod]
  ring

/-- Exact extension count: each compute pair has `|K|²` joint completions. -/
theorem card_liftCompute (A : Finset (K × K)) :
    (liftCompute A).card = A.card * Fintype.card K ^ 2 := by
  simp only [liftCompute, Finset.card_product, Finset.card_univ, Fintype.card_prod]
  ring

/-- Exact extension count: each memory pair has `|K|²` joint completions, despite sharing `γ`
with the compute projection. -/
theorem card_liftMemory (A : Finset (K × K)) :
    (liftMemory A).card = A.card * Fintype.card K ^ 2 := by
  simp only [liftMemory, Finset.card_map, Finset.card_product, Finset.card_univ,
    Fintype.card_prod]
  ring

/-- Exact extension count: each NPR seed has `|K|³` joint completions. -/
theorem card_liftSeed (B : Finset K) :
    (liftSeed B).card = B.card * Fintype.card K ^ 3 := by
  simp only [liftSeed, Finset.card_product, Finset.card_univ, Fintype.card_prod]
  ring

/-! ## Lifted-event bounds -/

/-- Compute and memory both read the single shared `γ`; their cardinal union bound still needs no
independence premise. -/
theorem sharedGamma_union_bound (Ac Am : Finset (K × K)) :
    (liftCompute Ac ∪ liftMemory Am).card ≤
      Ac.card * Fintype.card K ^ 2 + Am.card * Fintype.card K ^ 2 := by
  calc
    (liftCompute Ac ∪ liftMemory Am).card ≤
        (liftCompute Ac).card + (liftMemory Am).card :=
      Finset.card_union_le _ _
    _ = Ac.card * Fintype.card K ^ 2 + Am.card * Fintype.card K ^ 2 := by
      rw [card_liftCompute, card_liftMemory]

/-- Union bound for one lifted two-coin compute event and one lifted one-coin seed event. -/
theorem pair_seed_union_bound (A : Finset (K × K)) (B : Finset K) :
    (liftCompute A ∪ liftSeed B).card ≤
      A.card * Fintype.card K ^ 2 + B.card * Fintype.card K ^ 3 := by
  calc
    (liftCompute A ∪ liftSeed B).card ≤
        (liftCompute A).card + (liftSeed B).card :=
      Finset.card_union_le _ _
    _ = A.card * Fintype.card K ^ 2 + B.card * Fintype.card K ^ 3 := by
      rw [card_liftCompute, card_liftSeed]

/-- Finite-family union bound for lifted two-coin compute events, with the exact `|K|²`
extension factor exposed. -/
theorem compute_family_union_bound {ι : Type*} (s : Finset ι)
    (A : ι → Finset (K × K)) :
    (s.biUnion fun i => liftCompute (A i)).card ≤
      ∑ i ∈ s, (A i).card * Fintype.card K ^ 2 := by
  calc
    (s.biUnion fun i => liftCompute (A i)).card ≤
        ∑ i ∈ s, (liftCompute (A i)).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ s, (A i).card * Fintype.card K ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact card_liftCompute (A i)

/-- Joint union bound for the compute-pair, memory-pair, and NPR-seed event classes. -/
theorem all_event_union_bound (Ac Am : Finset (K × K)) (B : Finset K) :
    ((liftCompute Ac ∪ liftMemory Am) ∪ liftSeed B).card ≤
      Ac.card * Fintype.card K ^ 2 +
        Am.card * Fintype.card K ^ 2 +
          B.card * Fintype.card K ^ 3 := by
  calc
    ((liftCompute Ac ∪ liftMemory Am) ∪ liftSeed B).card ≤
        (liftCompute Ac ∪ liftMemory Am).card + (liftSeed B).card :=
      Finset.card_union_le _ _
    _ ≤ (Ac.card * Fintype.card K ^ 2 + Am.card * Fintype.card K ^ 2) +
        (liftSeed B).card := Nat.add_le_add_right (sharedGamma_union_bound Ac Am) _
    _ = Ac.card * Fintype.card K ^ 2 +
        Am.card * Fintype.card K ^ 2 +
          B.card * Fintype.card K ^ 3 := by
      rw [card_liftSeed]

/-! ## Density reconciliation -/

section Density

variable [Nonempty K]

/-- Normalizing a lifted compute count by `|K|⁴` recovers the original two-coin density
`|A| / |K|²`. -/
theorem compute_density_reconcile (A : Finset (K × K)) :
    ((liftCompute A).card : ℚ) / (Fintype.card (JointCoins K) : ℚ) =
      (A.card : ℚ) / (Fintype.card K : ℚ) ^ 2 := by
  rw [card_liftCompute, card_jointCoins]
  push_cast
  have hK : (Fintype.card K : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Normalizing a lifted shared-`γ` memory count by `|K|⁴` recovers the original two-coin
density `|A| / |K|²`. -/
theorem memory_density_reconcile (A : Finset (K × K)) :
    ((liftMemory A).card : ℚ) / (Fintype.card (JointCoins K) : ℚ) =
      (A.card : ℚ) / (Fintype.card K : ℚ) ^ 2 := by
  rw [card_liftMemory, card_jointCoins]
  push_cast
  have hK : (Fintype.card K : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Normalizing a lifted seed count by `|K|⁴` recovers the original seed density
`|B| / |K|`. -/
theorem seed_density_reconcile (B : Finset K) :
    ((liftSeed B).card : ℚ) / (Fintype.card (JointCoins K) : ℚ) =
      (B.card : ℚ) / (Fintype.card K : ℚ) := by
  rw [card_liftSeed, card_jointCoins]
  push_cast
  have hK : (Fintype.card K : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end Density
end Finite

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.compute_memory_shared_gamma
#print axioms Nock.NockVMROM.Thm54.mem_liftCompute_iff
#print axioms Nock.NockVMROM.Thm54.mem_liftMemory_iff
#print axioms Nock.NockVMROM.Thm54.mem_liftSeed_iff
#print axioms Nock.NockVMROM.Thm54.card_jointCoins
#print axioms Nock.NockVMROM.Thm54.card_liftCompute
#print axioms Nock.NockVMROM.Thm54.card_liftMemory
#print axioms Nock.NockVMROM.Thm54.card_liftSeed
#print axioms Nock.NockVMROM.Thm54.sharedGamma_union_bound
#print axioms Nock.NockVMROM.Thm54.pair_seed_union_bound
#print axioms Nock.NockVMROM.Thm54.card_biUnion_le
#print axioms Nock.NockVMROM.Thm54.compute_family_union_bound
#print axioms Nock.NockVMROM.Thm54.all_event_union_bound
#print axioms Nock.NockVMROM.Thm54.compute_density_reconcile
#print axioms Nock.NockVMROM.Thm54.memory_density_reconcile
#print axioms Nock.NockVMROM.Thm54.seed_density_reconcile
