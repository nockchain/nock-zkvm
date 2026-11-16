/-
  Nock/NockVMROM/Thm54/P8Core/Batch971Thm54Round0WrapForestCover.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch971Thm54Round0WrapForestCover`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch971Thm54Round0WrapForestCover.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.DecodedLambdaEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch971

open Nock Nock.Walk Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch575

section Forest

variable {F K : Type} [Field F] [Field K] [DecidableEq F] {M : ℕ}
variable (envsK : Fin M → Reified.Env K) (envsF : Fin M → Reified.Env F) (kroots : ℕ)

/-- A followed child is in its parent's reach set. -/
theorem child_mem_reach (x l : ℕ) (hx : 1 ≤ x ∧ x ≤ M) (hl1 : 1 ≤ l)
    (hl : l ≤ foOfMem envsF x) (hc : x < childIdx envsF kroots x l)
    (hcM : childIdx envsF kroots x l ≤ M) :
    childIdx envsF kroots x l ∈ reachRows envsF kroots x := by
  have hfo2 := foOfMem_le_two envsF x
  have hself := self_mem_reach envsF kroots (childIdx envsF kroots x l) ⟨by omega, hcM⟩
  rw [reach_eq envsF kroots x hx]
  simp only [Finset.mem_union]
  rcases (show l = 1 ∨ l = 2 by omega) with rfl | rfl
  · right; left; rw [if_pos ⟨hl, hc⟩]; exact hself
  · right; right; rw [if_pos ⟨hl, hc⟩]; exact hself

/-- Reach sets are transitive. -/
theorem reach_trans : ∀ x y z, y ∈ reachRows envsF kroots x → z ∈ reachRows envsF kroots y →
    z ∈ reachRows envsF kroots x := by
  refine measure_induction (M := M) _ fun x ih => ?_
  intro y z hy hz
  by_cases h : 1 ≤ x ∧ x ≤ M
  · have hy' := hy
    rw [reach_eq envsF kroots x h] at hy'
    simp only [Finset.mem_union, Finset.mem_singleton] at hy'
    rcases hy' with rfl | hy' | hy'
    · exact hz
    · split_ifs at hy' with hc
      · have := ih _ hc.2 h.1 h.2 y z hy' hz
        rw [reach_eq envsF kroots x h]
        simp only [Finset.mem_union]
        right; left; rw [if_pos hc]; exact this
      · simp at hy'
    · split_ifs at hy' with hc
      · have := ih _ hc.2 h.1 h.2 y z hy' hz
        rw [reach_eq envsF kroots x h]
        simp only [Finset.mem_union]
        right; right; rw [if_pos hc]; exact this
      · simp at hy'
  · rw [reach_out envsF kroots x h] at hy; simp at hy

/-- **Coverage**: under the BFS tiling every row lies in the reach set of some root. -/
theorem reach_cover (htile : kroots + Sf (foOfMem envsF) M = M)
    (hv : BFSValidF kroots (foOfMem envsF) M) :
    ∀ i, 1 ≤ i → i ≤ M → ∃ r, 1 ≤ r ∧ r ≤ kroots ∧ i ∈ reachRows envsF kroots r := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi1 hiM
  by_cases hik : i ≤ kroots
  · exact ⟨i, hi1, hik, self_mem_reach envsF kroots i ⟨hi1, hiM⟩⟩
  · push_neg at hik
    have hex : ∃ p, i ≤ kroots + Sf (foOfMem envsF) p := ⟨M, by omega⟩
    have hp : i ≤ kroots + Sf (foOfMem envsF) (Nat.find hex) := Nat.find_spec hex
    have hpM : Nat.find hex ≤ M := Nat.find_min' hex (by omega)
    have hp1 : 1 ≤ Nat.find hex := by
      by_contra h0
      have h00 : Nat.find hex = 0 := by omega
      rw [h00] at hp
      simp [Sf] at hp
      omega
    have hprev : kroots + Sf (foOfMem envsF) (Nat.find hex - 1) < i := by
      have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      omega
    have hsucc := Sf_succ (foOfMem envsF) (Nat.find hex) hp1
    have hval := hv (Nat.find hex) hp1 hpM
    have hl1 : 1 ≤ i - kroots - Sf (foOfMem envsF) (Nat.find hex - 1) := by omega
    have hl : i - kroots - Sf (foOfMem envsF) (Nat.find hex - 1) ≤
        foOfMem envsF (Nat.find hex) := by omega
    have hci : childIdx envsF kroots (Nat.find hex)
        (i - kroots - Sf (foOfMem envsF) (Nat.find hex - 1)) = i := by
      unfold childIdx; omega
    have hpi : Nat.find hex < i := by omega
    obtain ⟨r, hr1, hrk, hpr⟩ := ih (Nat.find hex) hpi hp1 hpM
    have hmem := child_mem_reach envsF kroots (Nat.find hex)
      (i - kroots - Sf (foOfMem envsF) (Nat.find hex - 1)) ⟨hp1, hpM⟩ hl1 hl
      (by rw [hci]; exact hpi) (by rw [hci]; exact hiM)
    rw [hci] at hmem
    exact ⟨r, hr1, hrk, reach_trans envsF kroots r (Nat.find hex) i hpr hmem⟩

/-- **A `read_root` row reachable from `x` contributes a read of its exponent to the decoded tree
of `x`.** -/
theorem readCount_pos_of_reach : ∀ x i, i ∈ reachRows envsF kroots x →
    ∀ hi : 1 ≤ i ∧ i ≤ M, memRowStateOf (envsF ⟨i - 1, by omega⟩) = .read_root →
    1 ≤ readCount (rowExp envsF ⟨i - 1, by omega⟩) (decodedMTreeOfEnvs envsK envsF kroots x) := by
  refine measure_induction (M := M) _ fun x ih => ?_
  intro i hix hi hst
  by_cases h : 1 ≤ x ∧ x ≤ M
  · have hfo := foOfMem_eq envsF x h
    by_cases hxi : i = x
    · subst hxi
      rw [decodedMTreeOfEnvs, dif_pos h]
      rw [hst]
      simp [readCount]
    · rw [reach_eq envsF kroots x h] at hix
      simp only [Finset.mem_union, Finset.mem_singleton] at hix
      rcases hix with hix | hix | hix
      · exact absurd hix hxi
      · split_ifs at hix with hc
        · have hchild := ih _ hc.2 h.1 h.2 i hix hi hst
          rw [decodedMTreeOfEnvs, dif_pos h]
          rcases hsx : memRowStateOf (envsF ⟨x - 1, by omega⟩) with _ | _ | _ | _
          · simp only [readCount, if_pos hc.2]; omega
          · rw [hsx] at hfo; simp [MemoryTable.fanoutMem] at hfo; omega
          · simp only [readCount, if_pos hc.2]; omega
          · simp only [readCount, if_pos hc.2]; omega
        · simp at hix
      · split_ifs at hix with hc
        · have hchild := ih _ hc.2 h.1 h.2 i hix hi hst
          rw [decodedMTreeOfEnvs, dif_pos h]
          rcases hsx : memRowStateOf (envsF ⟨x - 1, by omega⟩) with _ | _ | _ | _
          · simp only [readCount, if_pos hc.2]; omega
          · rw [hsx] at hfo; simp [MemoryTable.fanoutMem] at hfo; omega
          · rw [hsx] at hfo; simp [MemoryTable.fanoutMem] at hfo; omega
          · rw [hsx] at hfo; simp [MemoryTable.fanoutMem] at hfo; omega
        · simp at hix
  · rw [reach_out envsF kroots x h] at hix; simp at hix

/-- **Every `read_root` row's exponent is paired in some decoded root tree**, given the BFS
tiling, `UniqueExponents` at every root tree and balanced read/verify counts (R4's first
conclusion). -/
theorem paired_of_read_row
    (htile : kroots + Sf (foOfMem envsF) M = M) (hv : BFSValidF kroots (foOfMem envsF) M)
    (hU : ∀ r ∈ Finset.Icc 1 kroots, UniqueExponents (decodedMTreeOfEnvs envsK envsF kroots r))
    (hbal : ∀ r ∈ Finset.Icc 1 kroots, ∀ e,
      readCount e (decodedMTreeOfEnvs envsK envsF kroots r) =
        verifyCount e (decodedMTreeOfEnvs envsK envsF kroots r))
    (k : Fin M) (hst : memRowStateOf (envsF k) = .read_root) :
    ∃ r ∈ Finset.Icc 1 kroots,
      Paired (rowExp envsF k) (decodedMTreeOfEnvs envsK envsF kroots r) := by
  have hi : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ M := ⟨by omega, k.isLt⟩
  obtain ⟨r, hr1, hrk, hmem⟩ := reach_cover envsF kroots htile hv (k.val + 1) hi.1 hi.2
  have hk : (⟨k.val + 1 - 1, by omega⟩ : Fin M) = k := Fin.ext (by simp)
  have hst' : memRowStateOf (envsF ⟨k.val + 1 - 1, by omega⟩) = .read_root := by
    rw [hk]; exact hst
  have hpos := readCount_pos_of_reach envsK envsF kroots r (k.val + 1) hmem hi hst'
  rw [hk] at hpos
  have hrI : r ∈ Finset.Icc 1 kroots := Finset.mem_Icc.mpr ⟨hr1, hrk⟩
  have hle := (hU r hrI (rowExp envsF k)).1
  have hb := hbal r hrI (rowExp envsF k)
  refine ⟨r, hrI, ?_, ?_⟩ <;> omega

end Forest

end Nock.RedTeam.Batch971
