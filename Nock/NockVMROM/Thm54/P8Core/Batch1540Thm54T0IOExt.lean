/-
  Nock/NockVMROM/Thm54/P8Core/Batch1540Thm54T0IOExt.lean

  **The record-level IO failure bound at records over an
  EXTENSION of the coin field.**

  `FiniteIO.IOFailureEvent_card_le` is stated for records over the coin field `K`.  Records are then vectors over `L = 𝕂′`, the compression
  `RLC^γ(v) = Σ γ^c v_c` has `γ ∈ 𝕂 ⊆ 𝕂′`, and the pole `z ∈ 𝕂` is compared against `L`-values.

  Here `IOFailureEventExt` is the preimage, under the coin embedding `K → L`, of the EXISTING
  `FiniteIO.IOFailureEvent` of `L`-records at `L`-coins.  The three component bounds of the
  existing file are field-size free (`n² (m−1)`, `n`, `n`); injectivity of `K → L` moves them to
  `K`, and the union argument of `IOFailureEvent_card_le` then goes through with `|K|` coins.  The
  numeral is **the same** `ioFailureUnionBound m k₁ k₂ |K|`.

  Paper: the paper (`RLC^γ`), `:1007-1016` (LogUp over the IO records).
-/
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness

namespace Nock.NockVMROM.Thm54.T0IOExt

open Nock
open Nock.NockVMROM.Thm54.FiniteIO
open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Fintype K]
  [Fintype L] [DecidableEq L] {m : ℕ}

open Classical in
/-- The failure set of `(γ, pole) ∈ K × K` for `L`-valued records: the coin pair embedded in
`L × L` lies in the existing `IOFailureEvent`. -/
noncomputable def IOFailureEventExt (K : Type*) [Field K] [Algebra K L] [Fintype K]
    (records : PreChallengeRecords L m) : Finset (K × K) :=
  Finset.univ.filter
    (fun q => (algebraMap K L q.1, algebraMap K L q.2) ∈ IOFailureEvent records)

theorem mem_IOFailureEventExt {records : PreChallengeRecords L m} {γ pole : K} :
    (γ, pole) ∈ IOFailureEventExt K records ↔
      algebraMap K L γ ∈ IORLCCollisionEvent records ∨
      algebraMap K L pole ∈ IOPoleHitEvent records (algebraMap K L γ) ∨
      algebraMap K L pole ∈ IOLogDerivEvent records (algebraMap K L γ) := by
  simp [IOFailureEventExt, mem_IOFailureEvent_iff]

omit [Fintype L] in
/-- A finset of `L` pulled back along the injective coin embedding is no larger. -/
theorem card_preimage_algebraMap_le (S : Finset L) :
    (Finset.univ.filter (fun x : K => algebraMap K L x ∈ S)).card ≤ S.card := by
  refine Finset.card_le_card_of_injOn (algebraMap K L) ?_ ?_
  · intro x hx
    simpa using hx
  · exact (algebraMap K L).injective.injOn

/-- **The ioFUB twin.**  At records over an extension `L` of the coin field `K`, with coins `γ,
pole ∈ K`, the failure set has at most `ioFailureUnionBound m k₁ k₂ |K|` elements — the same
numeral as `FiniteIO.IOFailureEvent_card_le` at records over `K`. -/
theorem IOFailureEventExt_card_le (records : PreChallengeRecords L m) :
    (IOFailureEventExt K records).card
      ≤ ioFailureUnionBound m records.requests.length records.responses.length
          (Fintype.card K) := by
  classical
  set k₁ := records.requests.length with hk₁
  set k₂ := records.responses.length with hk₂
  set S : Finset (K × K) :=
    (Finset.univ.filter (fun γ : K => algebraMap K L γ ∈ IORLCCollisionEvent records)) ×ˢ Finset.univ with hS
  set T : Finset (K × K) := Finset.univ.biUnion (fun γ : K =>
    ({γ} : Finset K) ×ˢ
      (Finset.univ.filter (fun z : K =>
        algebraMap K L z ∈ IOPoleHitEvent records (algebraMap K L γ) ∪ IOLogDerivEvent records (algebraMap K L γ)))) with hT
  have hsub : IOFailureEventExt K records ⊆ S ∪ T := by
    intro q hq
    obtain ⟨γ, pole⟩ := q
    rw [mem_IOFailureEventExt] at hq
    rcases hq with h1 | h2 | h3
    · exact Finset.mem_union_left _ (by simp [hS, h1])
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_biUnion.mpr ⟨γ, Finset.mem_univ _, ?_⟩
      simp [Finset.mem_union, h2]
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_biUnion.mpr ⟨γ, Finset.mem_univ _, ?_⟩
      simp [Finset.mem_union, h3]
  have hScard : S.card ≤ (k₁ + k₂) * (k₁ + k₂) * (m - 1) * Fintype.card K := by
    rw [hS, Finset.card_product, Finset.card_univ]
    exact Nat.mul_le_mul_right _
      (le_trans (card_preimage_algebraMap_le _) (IORLCCollisionEvent_card_le records))
  have hTcard : T.card ≤ Fintype.card K * (2 * (k₁ + k₂)) := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : K => 2 * (k₁ + k₂))
      (fun γ (_ : γ ∈ Finset.univ) => ?_)) ?_
    · rw [Finset.card_product, Finset.card_singleton, one_mul]
      refine le_trans (card_preimage_algebraMap_le _) ?_
      refine le_trans (Finset.card_union_le _ _) ?_
      have := IOPoleHitEvent_card_le records (algebraMap K L γ)
      have := IOLogDerivEvent_card_le records (algebraMap K L γ)
      omega
    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc (IOFailureEventExt K records).card ≤ (S ∪ T).card := Finset.card_le_card hsub
    _ ≤ S.card + T.card := Finset.card_union_le _ _
    _ ≤ (k₁ + k₂) * (k₁ + k₂) * (m - 1) * Fintype.card K
          + Fintype.card K * (2 * (k₁ + k₂)) := Nat.add_le_add hScard hTcard
    _ = ioFailureUnionBound m k₁ k₂ (Fintype.card K) := rfl

end Nock.NockVMROM.Thm54.T0IOExt

namespace Nock.NockVMROM.Thm54.T0IOExt

/-- Consistency with the base case: at `L = F` the extension event is the existing one. -/
theorem IOFailureEventExt_self {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
    (records : FiniteIO.PreChallengeRecords F m) :
    IOFailureEventExt F records = FiniteIO.IOFailureEvent records := by
  ext ⟨γ, pole⟩
  simp [IOFailureEventExt]

end Nock.NockVMROM.Thm54.T0IOExt
