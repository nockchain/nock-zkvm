/-
  Nock/RedTeam/Batch610Thm54PreseedFreshForgeries.lean

  Notes only; not a pass.

  * (a) A NON-`halt` row carrying a free leaf: `decodeNoun` never reads the data of a
    `decompose` / `read_root` / `verify_child` node (`nonhalt_decode_ignores_data`), and a `halt`
    node with children decodes to the constant `atom 0` (`halt_with_children_decodes_zero`).
    So a free `𝕂` leaf on a non-`halt` row never reaches a decoded atom.  STOPPED.
  * (b) A `halt` row whose selector is zero: not decoded as `halt`
    (`Batch608.selector_ne_one_not_halt`).  STOPPED (it is a non-`halt` row, case (a)).
  * (c) **Adaptive four-leaf collision (C2 shape) against the memory-only gate.**  For EVERY seed
    `z ≠ 0` of every cubic `𝕂 / ZMod p`, there are two distinct four-leaf nouns, every leaf a
    base-field atom `< p` (so every `halt` row passes `haltAtomMixed` with `atom := leaf`), with
    EQUAL `enc z` fingerprints (`adaptive_base_leaf_collision`).  The gate only forces
    `leaf ∈ 𝔽`; it does not order the atoms before `z`.  What would stop it is the pre-seed
    ORDER (atoms fixed before `z`; then the pair collides on `≤ 2Λ − 1` seeds,
    `NPR.collision_card_le_tight`), and no chip-level object carries that order
    (`Batch608.every_source_column_is_round_zero`, `satisfaction_round_blind`).
-/
import Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
import Nock.RedTeam.Batch578Thm54AdaptiveAtomForgery

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch610

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.GlobalCarryRecognizer

noncomputable section

/-! ## (a) Non-`halt` rows: the decoder never reads their data -/

section Decode

variable {K : Type} [Field K]

theorem nonhalt_decode_ignores_data (q : ℕ) (st : MState) (hst : st ≠ .halt)
    (d d' : DTmem K) (cs : List (Walk.NTree (MState × DTmem K))) :
    HostileSkeletonDecoding.decodeNoun q (.node (st, d) cs) =
      HostileSkeletonDecoding.decodeNoun q (.node (st, d') cs) := by
  cases st with
  | halt => exact absurd rfl hst
  | decompose =>
      rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp [HostileSkeletonDecoding.decodeNoun]
  | read_root =>
      rcases cs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [HostileSkeletonDecoding.decodeNoun]
  | verify_child =>
      rcases cs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [HostileSkeletonDecoding.decodeNoun]

theorem halt_with_children_decodes_zero (q : ℕ) (d : DTmem K)
    (c : Walk.NTree (MState × DTmem K)) (cs : List (Walk.NTree (MState × DTmem K))) :
    HostileSkeletonDecoding.decodeNoun q (.node (.halt, d) (c :: cs)) = Noun.atom 0 := by
  simp [HostileSkeletonDecoding.decodeNoun]

end Decode

/-! ## (c) Adaptive base-field four-leaf collision -/

def nest4 (a : Fin 4 → ℕ) : Noun := Batch578.nest4 (a 0) (a 1) (a 2) (a 3)

section Collision

variable {K : Type} [Field K]

/-- `enc` of a right comb of four atoms, through `enc_cons` / `enc_atom`. -/
theorem enc_nest4 {z : K} (hz : z ≠ 0) (a : Fin 4 → ℕ) :
    enc z (nest4 a) =
      ComputeTable.FP.cons z (ComputeTable.FP.atomFP z (a 0 : K))
        (ComputeTable.FP.cons z (ComputeTable.FP.atomFP z (a 1 : K))
          (ComputeTable.FP.cons z (ComputeTable.FP.atomFP z (a 2 : K))
            (ComputeTable.FP.atomFP z (a 3 : K)))) := by
  simp only [nest4, Batch578.nest4, enc_cons hz, enc_atom]

/-- Two combs with the same shape have equal `enc` iff their leaf polynomials agree. -/
theorem enc_nest4_eq_of_leaf {z : K} (hz : z ≠ 0) (a b : Fin 4 → ℕ)
    (h : (a 0 : K) + z * ((a 1 : K) + z * ((a 2 : K) + z * (a 3 : K))) =
      (b 0 : K) + z * ((b 1 : K) + z * ((b 2 : K) + z * (b 3 : K)))) :
    enc z (nest4 a) = enc z (nest4 b) := by
  rw [enc_nest4 hz, enc_nest4 hz]
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · simp [ComputeTable.FP.cons, ComputeTable.FP.atomFP]
  · simp [ComputeTable.FP.cons, ComputeTable.FP.atomFP]
  · simp only [ComputeTable.FP.cons, ComputeTable.FP.atomFP]
    linear_combination h

end Collision

/-- **Fresh forgery, memory-only form.**  At every cubic extension `K / ZMod p` and every seed
`z ≠ 0` there are two DISTINCT four-atom nouns, all atoms `< p` (so every `halt` leaf is
`algebraMap` of a base value and the `halt`-row atom gate holds with `atom := leaf`), whose
NPR fingerprints at `z` are EQUAL.  The witness depends on `z`: it is the adaptive (post-`z`)
choice the pre-seed ORDER is meant to forbid, and that order is not a chip constraint. -/
theorem adaptive_base_leaf_collision {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Algebra (ZMod p) K] (hK : Module.finrank (ZMod p) K = 3) (z : K) (hz : z ≠ 0) :
    ∃ a b : Fin 4 → ℕ, (∀ i, a i < p) ∧ (∀ i, b i < p) ∧ nest4 a ≠ nest4 b ∧
      enc z (nest4 a) = enc z (nest4 b) ∧
      (∀ i, ∃ x : ZMod p, algebraMap (ZMod p) K x = (enc z (Noun.atom (a i))).leaf) ∧
      (∀ i, ∃ x : ZMod p, algebraMap (ZMod p) K x = (enc z (Noun.atom (b i))).leaf) := by
  haveI : FiniteDimensional (ZMod p) K := Module.finite_of_finrank_eq_succ hK
  obtain ⟨δ, hδne, hδ⟩ := Batch578.four_atoms_kernel (F := ZMod p) (K := K) hK z
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let a : Fin 4 → ℕ := fun i => (δ i).val
  let b : Fin 4 → ℕ := fun _ => 0
  have hcast : ∀ i, ((a i : ℕ) : K) = algebraMap (ZMod p) K (δ i) := fun i => by
    show (((δ i).val : ℕ) : K) = _
    rw [← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_zmod_val]
  have hlt : ∀ i, a i < p := fun i => ZMod.val_lt (δ i)
  refine ⟨a, b, hlt, fun _ => hp, ?_, ?_, ?_, ?_⟩
  · -- distinct: some `δ i ≠ 0`, so `a i ≠ 0 = b i`
    intro heq
    apply hδne
    funext i
    have hall : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 := by
      simpa [nest4, Batch578.nest4, Noun.leafList, b] using congrArg Noun.leafList heq
    obtain ⟨h0, h1, h2, h3⟩ := hall
    have hleaf : ∀ j : Fin 4, a j = 0 := by
      intro j
      fin_cases j
      exacts [h0, h1, h2, h3]
    have := hleaf i
    simpa [a, ZMod.val_eq_zero] using this
  · apply enc_nest4_eq_of_leaf hz
    have hsum := hδ
    simp only [Batch578.leafEval, Fin.sum_univ_four, Algebra.smul_def] at hsum
    rw [hcast 0, hcast 1, hcast 2, hcast 3]
    simp only [b, Nat.cast_zero, Fin.val_zero, Fin.val_one, Fin.val_two] at hsum ⊢
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [h3] at hsum
    linear_combination hsum
  · intro i
    exact ⟨δ i, by rw [enc_atom, ComputeTable.FP.atomFP_leaf, hcast i]⟩
  · intro i
    exact ⟨0, by simp [b, enc_atom]⟩

end

end Nock.RedTeam.Batch610

#print axioms Nock.RedTeam.Batch610.nonhalt_decode_ignores_data
#print axioms Nock.RedTeam.Batch610.halt_with_children_decodes_zero
#print axioms Nock.RedTeam.Batch610.enc_nest4_eq_of_leaf
#print axioms Nock.RedTeam.Batch610.adaptive_base_leaf_collision
