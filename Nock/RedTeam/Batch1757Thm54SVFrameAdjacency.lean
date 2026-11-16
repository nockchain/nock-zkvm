/-
  Nock/RedTeam/Batch1757Thm54SVFrameAdjacency.lean

  Production: `P8Core/SVFrame/MemSoundnessFamily.lean`.

  §A   Route: the THEOREM route is closed — `VerifierData.computeNodes : Fin N → F` and
      `memNodes t` are free data (not built as `β·ω^i`), so a datum with a permuted node list IS
      constructible.  The CHECK route: `Checks.hadjC : V.AdjacentC`, `Checks.hadjM : ∀ t,
      V.AdjacentM t` (the package's `computeAdjacentOrbit` / `memoryAdjacentOrbit`), decidable from
      `V` alone (`VerifierData.decAdjacentC` / `decAdjacentM`, no trace).  Negative controls: a
      datum whose compute (resp. memory) node list is the adjacent one with rows `0`, `1` swapped is
      still injective but is REJECTED by the adjacency check (`swapC_rejected`, `swapM_rejected`);
      concrete `decide` instance at `ZMod 7`, `ω = 3`.
  §B   Exposure: `Checks.computeAdjacent` (V4T's `D.Adjacent` shape at
      `nodes := V.computeNodes`, `orbit := V.orbitC`), `Checks.memAdjacent` (R-V2's memory twin),
      closed forms `AdjacentC.nodes_eq_pow` / `AdjacentM.nodes_eq_pow`; `standalone_generic` /
      `_at` / `_fixed` unchanged in type (no new hypothesis); axioms.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1757

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension

/-! ## §A  Negative controls -/

/-- The orbit generator is not a square root of one: its order is `3·2^h ≥ 3`. -/
theorem orbit_sq_ne_one {F : Type} [Field F] {h : ℕ} (O : StrictOrbitDomain F 3 h) :
    O.ω ^ 2 ≠ 1 := by
  intro h2
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [O.order_ω] at hd
  have hle := Nat.le_of_dvd (by norm_num) hd
  have := Nat.one_le_two_pow (n := h)
  omega

/-- Swapping two adjacent nonzero nodes `a`, `ω·a` would force `ω² = 1`. -/
theorem sq_eq_one_of_swap {F : Type} [Field F] {ω a : F} (ha : a ≠ 0)
    (h : a = ω * (ω * a)) : ω ^ 2 = 1 := by
  have h0 : (ω ^ 2 - 1) * a = 0 := by
    have : ω ^ 2 * a = a := by rw [pow_two, mul_assoc]; exact h.symm
    rw [sub_mul, one_mul, this, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 ha

section Swap

variable {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ} {S : MemShape}

/-- The swap of rows `0` and `1` (needs two rows). -/
def swap01 {n : ℕ} (hn : 2 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩

/-- **The permuted compute datum**: `V` with compute rows `0` and `1` exchanged.  Constructible —
the node list is free data, so the theorem route is closed. -/
def swapC (V : VerifierData F K hC S) (hN : 2 ≤ V.N) : VerifierData F K hC S :=
  { V with computeNodes := V.computeNodes ∘ swap01 hN }

theorem swapC_injective (V : VerifierData F K hC S) (hN : 2 ≤ V.N)
    (hinj : Function.Injective V.computeNodes) :
    Function.Injective (swapC V hN).computeNodes :=
  hinj.comp (swap01 hN).injective

/-- **NC (compute):** if `V` passes the adjacency and injectivity checks, the datum with rows
`0`, `1` swapped FAILS the adjacency check. -/
theorem swapC_rejected (V : VerifierData F K hC S) (hN : 2 ≤ V.N) (hadj : V.AdjacentC)
    (hinj : Function.Injective V.computeNodes) : ¬ (swapC V hN).AdjacentC := by
  intro h'
  have h0 : 0 < V.N := by omega
  have h1 : V.computeNodes ⟨1, hN⟩ = V.orbitC.ω * V.computeNodes ⟨0, h0⟩ := hadj ⟨0, h0⟩ hN
  have ha : V.computeNodes ⟨0, h0⟩ ≠ 0 := by
    intro ha0
    have : V.computeNodes ⟨1, hN⟩ = V.computeNodes ⟨0, h0⟩ := by rw [h1, ha0, mul_zero]
    exact absurd (congrArg Fin.val (hinj this)) (by simp)
  have hs := h' ⟨0, h0⟩ hN
  simp only [swapC, Function.comp_apply, swap01] at hs
  rw [Equiv.swap_apply_right, Equiv.swap_apply_left, h1] at hs
  exact orbit_sq_ne_one V.orbitC (sq_eq_one_of_swap ha hs)

/-- **The permuted memory datum**: every table's rows `0` and `1` exchanged. -/
def swapM (V : VerifierData F K hC S) (hM : ∀ t, 2 ≤ V.memRows t) : VerifierData F K hC S :=
  { V with memNodes := fun t => V.memNodes t ∘ swap01 (hM t) }

theorem swapM_injective (V : VerifierData F K hC S) (hM : ∀ t, 2 ≤ V.memRows t)
    (hinj : ∀ t, Function.Injective (V.memNodes t)) (t : Fin S.k) :
    Function.Injective ((swapM V hM).memNodes t) :=
  (hinj t).comp (swap01 (hM t)).injective

/-- **NC (memory):** the swapped memory datum FAILS the adjacency check at every table. -/
theorem swapM_rejected (V : VerifierData F K hC S) (hM : ∀ t, 2 ≤ V.memRows t) (t : Fin S.k)
    (hadj : V.AdjacentM t) (hinj : Function.Injective (V.memNodes t)) :
    ¬ (swapM V hM).AdjacentM t := by
  intro h'
  have h2 := hM t
  have h0 : 0 < V.memRows t := by omega
  have h1 : V.memNodes t ⟨1, h2⟩ = V.memNodes t ⟨0, h0⟩ * (V.orbitM t).ω := hadj ⟨0, h0⟩ h2
  have ha : V.memNodes t ⟨0, h0⟩ ≠ 0 := by
    intro ha0
    have : V.memNodes t ⟨1, h2⟩ = V.memNodes t ⟨0, h0⟩ := by rw [h1, ha0, zero_mul]
    exact absurd (congrArg Fin.val (hinj this)) (by simp)
  have hs := h' ⟨0, h0⟩ h2
  simp only [swapM, Function.comp_apply, swap01] at hs
  rw [Equiv.swap_apply_right, Equiv.swap_apply_left, h1] at hs
  refine orbit_sq_ne_one (V.orbitM t) (sq_eq_one_of_swap ha ?_)
  linear_combination hs

/-- **NC at `Checks`:** no permuted compute datum passes the checks. -/
theorem checks_reject_swapC (V : VerifierData F K hC S) (hN : 2 ≤ V.N) {nAcc : ℕ}
    {cb : Fin nAcc → ℕ} {pIO : ℕ} (hV : V.Checks cb pIO) : ¬ (swapC V hN).Checks cb pIO :=
  fun h => swapC_rejected V hN hV.hadjC hV.computeNodes_injective h.hadjC

/-- **NC at `Checks`:** no permuted memory datum passes the checks. -/
theorem checks_reject_swapM (V : VerifierData F K hC S) (hM : ∀ t, 2 ≤ V.memRows t)
    (t : Fin S.k) {nAcc : ℕ} {cb : Fin nAcc → ℕ} {pIO : ℕ} (hV : V.Checks cb pIO) :
    ¬ (swapM V hM).Checks cb pIO :=
  fun h => swapM_rejected V hM t (hV.hadjM t) (hV.memNodes_injective t) (h.hadjM t)

end Swap

/-- Concrete (`decide`): at `ZMod 7`, `ω = 3` (order `6 = 3·2`), the node list `1, 3, 2` is
adjacent (`x_{i+1} = ω·x_i`), and its `0 ↔ 1` permutation `3, 1, 2` is not. -/
theorem concrete_adjacent_and_swap_rejected :
    (∀ i : Fin 2, (![1, 3, 2] : Fin 3 → ZMod 7) i.succ = 3 * (![1, 3, 2] : Fin 3 → ZMod 7) i.castSucc) ∧
      ¬ (∀ i : Fin 2, (![3, 1, 2] : Fin 3 → ZMod 7) i.succ =
        3 * (![3, 1, 2] : Fin 3 → ZMod 7) i.castSucc) := by
  decide

/-- Concrete (`decide`): `3` has order `6` in `ZMod 7` (`3^6 = 1`, `3^2, 3^3 ≠ 1`). -/
theorem concrete_three_order_six :
    (3 : ZMod 7) ^ 6 = 1 ∧ (3 : ZMod 7) ^ 2 ≠ 1 ∧ (3 : ZMod 7) ^ 3 ≠ 1 := by
  decide

/-! ## §B  Exposure and threading -/

#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.AdjacentC
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.AdjacentM
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks.hadjC
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks.hadjM
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks.computeAdjacent
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks.memAdjacent
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.AdjacentC.nodes_eq_pow
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.AdjacentM.nodes_eq_pow
#check @Nock.NockVMROM.Thm54.SVFrame.standalone_generic

/-- The adjacency checks are decidable from `V` alone (no trace): instance search succeeds. -/
example {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] {hC : ℕ} {S : MemShape}
    (V : VerifierData F K hC S) : Decidable (V.AdjacentC ∧ ∀ t, V.AdjacentM t) := inferInstance

#print axioms Nock.RedTeam.Batch1757.orbit_sq_ne_one
#print axioms Nock.RedTeam.Batch1757.swapC_rejected
#print axioms Nock.RedTeam.Batch1757.swapM_rejected
#print axioms Nock.RedTeam.Batch1757.checks_reject_swapC
#print axioms Nock.RedTeam.Batch1757.checks_reject_swapM
#print axioms Nock.RedTeam.Batch1757.concrete_adjacent_and_swap_rejected
#print axioms Nock.RedTeam.Batch1757.concrete_three_order_six
#print axioms Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks.computeAdjacent
#print axioms Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks.memAdjacent
#print axioms Nock.NockVMROM.Thm54.SVFrame.VerifierData.AdjacentC.nodes_eq_pow
#print axioms Nock.NockVMROM.Thm54.SVFrame.VerifierData.AdjacentM.nodes_eq_pow
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_generic
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_generic_at
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_fixed

end Nock.RedTeam.Batch1757
