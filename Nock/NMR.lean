import Nock.Field
import Nock.NPR
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Nock Memory Representation (NMR) — `Def:NMR_poly` / `Def:NMR` / `Corr:NMR_size`

The polynomial Nock memory representation, its
extension-field evaluation, and the dimension bound
`NMR ⊆ 𝔽^{7·e+1}`, where `e = [𝕂 : 𝔽]` is the extension
degree.

A memory record is a triple `(a, v, t) ∈ 𝒜 × 𝒱𝒟 × 𝒯`.  For the NMR:
  * `𝒜 = axis ∈ 𝔽`                               — the address is the axis label;
  * `𝒱𝒟 = (root_fn, child_fn)`                    — two NPR fingerprints;
  * `𝒯 = timestamp`                               — `β^k ∈ 𝕂`.

For `pNMR` the fingerprints are the NPR *polynomials* `Φ(·) ∈ 𝔽[X]³` and the timestamp is the
monomial `X^k ∈ 𝔽[X]`.  For `NMR` they are the NPR *evaluations*
`fn(·;α) ∈ 𝕂³` and the timestamp is `β^k ∈ 𝕂`.  Both reuse `Nock.NPR`.
-/

open Polynomial

namespace Nock.NMR

/-! ### `Def:NMR_poly` — the polynomial NMR `pNMR(𝔽)` -/

/-- **`Def:NMR_poly`.**  The polynomial Nock Memory Representation `pNMR(𝔽)`:
    a memory record `(axis, (root_fn, child_fn), timestamp)` whose value domain is a pair of
    NPR polynomial fingerprints `Φ(·) ∈ 𝔽[X]³`, whose address is the axis
    label `∈ 𝔽`, and whose timestamp is a monomial `X^k ∈ 𝔽[X]`. -/
structure PolyRec (F : Type*) [Field F] where
  /-- Root noun fingerprint `Φ(root)[X] ∈ 𝔽[X]³`. -/
  root_fn : F[X] × F[X] × F[X]
  /-- Referenced-noun fingerprint `Φ(child)[X] ∈ 𝔽[X]³`. -/
  child_fn : F[X] × F[X] × F[X]
  /-- Axis label `axis_root(child) ∈ 𝔽`. -/
  axis : F
  /-- Timestamp `X^k ∈ 𝔽[X]` — `k` encoded as a unit-coefficient monomial. -/
  timestamp : F[X]

/-- The `pNMR` record of a memory access: root noun `root`, referenced noun `child`, axis label
    `axis`, and access time `k`, using the NPR `Φ`. -/
noncomputable def PolyRec.of {F : Type*} [Field F]
    (root child : Noun) (axis : F) (k : ℕ) : PolyRec F :=
  { root_fn := NPR.Φ root, child_fn := NPR.Φ child, axis := axis, timestamp := X ^ k }

/-! ### `Def:NMR` — the extension-field NMR `NMR^{α,β}(𝔽,𝕂)` -/

/-- **`Def:NMR`.**  The Nock Memory Representation `NMR^{α,β}(𝔽,𝕂)`: a memory
    record `(axis, (root_fn, child_fn), timestamp)` whose value domain is a pair of NPR
    fingerprints evaluated at `α ∈ 𝕂`, `fn(·;α) ∈ 𝕂³`, whose address is the
    axis label `∈ 𝔽`, and whose timestamp is `β^k ∈ 𝕂`. -/
structure Rec (F K : Type*) [Field F] [Field K] where
  /-- Root noun fingerprint `fn(root;α) ∈ 𝕂³`. -/
  root_fn : K × K × K
  /-- Referenced-noun fingerprint `fn(child;α) ∈ 𝕂³`. -/
  child_fn : K × K × K
  /-- Axis label `axis_root(child) ∈ 𝔽`. -/
  axis : F
  /-- Timestamp `β^k ∈ 𝕂` — integer `k` encoded as a power of `β`. -/
  timestamp : K

/-- The `NMR^{α,β}` record of a memory access, using the NPR fingerprint `fn(·;α)`. -/
noncomputable def Rec.of {F K : Type*} [Field F] [Field K]
    (root child : Noun) (α : K) (axis : F) (β : K) (k : ℕ) : Rec F K :=
  { root_fn := NPR.fn root α, child_fn := NPR.fn child α, axis := axis, timestamp := β ^ k }

/-! ### `Corr:NMR_size` — the dimension bound `NMR ⊆ 𝔽^{7e+1}`

    The NMR record `(axis, (root_fn, child_fn), timestamp) ∈ 𝔽 × (𝕂³ × 𝕂³) × 𝕂` is, as an
    `𝔽`-vector space, `Space 𝔽 𝕂`.  Counting `𝔽`-coordinates: `axis` is `1`, each of the two
    fingerprints is `𝕂³ = 3e`, and the timestamp is `𝕂 = e`, for a total of
    `1 + 3e + 3e + e = 7e + 1`.  Hence `NMR ⊆ 𝔽^{7e+1}` (`nmr_embeds`). -/

/-- The `𝔽`-vector space carrier of an `NMR` record: `𝒜 × 𝒱𝒟 × 𝒯 = 𝔽 × (𝕂³ × 𝕂³) × 𝕂`. -/
abbrev Space (F K : Type*) [Field F] [Field K] [Algebra F K] : Type _ :=
  F × ((K × K × K) × (K × K × K)) × K

/-- The `NMR` record is (definitionally) the tuple of its components, i.e. an element of
    `Space 𝔽 𝕂`.  This certifies that `Space` is exactly the record's underlying `𝔽`-vector
    space, over which `Corr:NMR_size` is stated. -/
@[simp] def equivSpace {F K : Type*} [Field F] [Field K] [Algebra F K] :
    Rec F K ≃ Space F K where
  toFun r := (r.axis, (r.root_fn, r.child_fn), r.timestamp)
  invFun s := { axis := s.1, root_fn := s.2.1.1, child_fn := s.2.1.2, timestamp := s.2.2 }
  left_inv := by rintro ⟨_, _, _, _⟩; rfl
  right_inv := by rintro ⟨_, _, _⟩; rfl

/-- **`Corr:NMR_size`, dimension form.**  Over a field `𝔽` and an extension
    `𝕂` of degree `e = [𝕂 : 𝔽]`, the `NMR^{α,β}(𝔽,𝕂)` value space has `𝔽`-dimension `7e + 1`. -/
theorem nmr_size (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Module.finrank F (Space F K) = 7 * Module.finrank F K + 1 := by
  simp only [Space, Module.finrank_prod, Module.finrank_self]
  omega

/-- **`Corr:NMR_size`, embedding form.**  `NMR^{α,β}(𝔽,𝕂) ⊆ 𝔽^{7e+1}`: the
    value space is `𝔽`-linearly isomorphic to `𝔽^{7e+1}` (`e = [𝕂 : 𝔽]`), hence embeds into it. -/
theorem nmr_embeds (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Nonempty (Space F K ≃ₗ[F] (Fin (7 * Module.finrank F K + 1) → F)) :=
  FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by
    rw [nmr_size, Module.finrank_pi, Fintype.card_fin])

end Nock.NMR
