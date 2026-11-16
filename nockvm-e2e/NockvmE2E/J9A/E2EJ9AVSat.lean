/-
**joint satisfiability of the instance-side hypotheses of `exec_e2e_J9AVR`** at the literal
`XI170 toy9R` (accept-vacuity rule).  Kernel literals only (`decide +kernel`); no existing file or statement is edited.

SCOPE NOTE (stated limit): `hk : 1 ≤ k` FAILS at the absent instance `abs9R` (`k = 0`, J9A/Abs9R.lean:45; `abs9R_k0` below), so the online theorem
`exec_e2e_J9AVR` says nothing about the absent instance; its non-vacuity is witnessed at `toy9R` only (k = 6).  `hk` is not weakened.
`exec_e2e_J9AVR` has no `hk` / `hdomS` / `hsk` / `hT` / `T` binders of its own (those belong to the `hcoll_J8` / `HFixJ8V4` route); `toy9R_k`
and `toy9R_dom` are given because the FRI round structure (`pSpec k`, `smoothDomain nD`) needs them and they are the J-8 analogues.
-/
import NockvmE2E.J9A.E2EJ9AToyR
import NockvmE2E.J9A.E2EJ9AVR
import NockvmE2E.Exec.Abs9R

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.J9A.E2EJ9AVSat
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.Exec.Toy9R

theorem toy9R_l : toy9R.l = 170 := rfl

/-- `1 ≤ k` (k = 6) -/
theorem toy9R_k : (XI170 toy9R).k = 6 := rfl

theorem toy9R_hk : 1 ≤ (XI170 toy9R).k := by rw [toy9R_k]; decide

/-- the domain bound `hdomS` (as `HFixJ8V5Sat.toy1X_dom`, at `s1 = 1`) -/
theorem toy9R_dom : 2 ^ (∑ _j : Fin ((XI170 toy9R).k + 1), ((1 : ℕ+) : ℕ)) * (1 : ℕ+).val ≤ 2 ^ (XI170 toy9R).nD := by
  rw [toy9R_k]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, PNat.one_coe, Nat.mul_one, PNat.val_ofNat]
  have h : (XI170 toy9R).nD = 13 := rfl
  rw [h]; norm_num

/-- the scope limit: `hk` fails at the absent instance -/
theorem abs9R_k0 : (XI170 Abs9R.abs9R).k = 0 := rfl

/-- `hz` at `Statement = Salt = Unit` -/
theorem hz_unit : ∃ (encZ : Unit × Unit → List ℕ) (decZ : List ℕ → Unit × Unit), ∀ x, decZ (encZ x) = x :=
  ⟨fun _ => [], fun _ => ((), ()), fun _ => rfl⟩

/-- the numeric budget binders (`hQFS`, `hQH`, `hV`) are satisfiable (by 0) -/
theorem budgets_sat : ∃ Q_FS Q_H V : ℕ, Q_FS ≤ 2 ^ 64 ∧ Q_H ≤ 2 ^ 64 ∧ V ≤ 2 ^ 32 :=
  ⟨0, 0, 0, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-- the three side conditions jointly at the literal -/
theorem sat_core :
    1 ≤ (XI170 toy9R).k ∧ toy9R.l = 170 ∧
      2 ^ (∑ _j : Fin ((XI170 toy9R).k + 1), ((1 : ℕ+) : ℕ)) * (1 : ℕ+).val ≤ 2 ^ (XI170 toy9R).nD :=
  ⟨toy9R_hk, toy9R_l, toy9R_dom⟩

/-! ## the instance binders of `exec_e2e_J9AVR` (generic instances, found by `inferInstance`) -/
section Inst
open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open NockvmE2E.Merkle NockvmE2E.Exec.E2EOnlineP

open NockvmE2E.Exec.E2E (NQuery)

/-- internal-node indices of any skeleton are finite (no instance upstream) -/
theorem finite_internalIndex : ∀ s : Skeleton, Finite (SkeletonInternalIndex s)
  | .leaf => by
    haveI : IsEmpty (SkeletonInternalIndex Skeleton.leaf) := ⟨fun x => nomatch x⟩
    infer_instance
  | .internal l r => by
    haveI := finite_internalIndex l
    haveI := finite_internalIndex r
    refine Finite.of_surjective
      (fun x : Unit ⊕ (SkeletonInternalIndex l ⊕ SkeletonInternalIndex r) =>
        match x with
        | .inl _ => (SkeletonInternalIndex.ofInternal : SkeletonInternalIndex (Skeleton.internal l r))
        | .inr (.inl i) => SkeletonInternalIndex.ofLeft i
        | .inr (.inr i) => SkeletonInternalIndex.ofRight i) ?_
    intro y
    cases y with
    | ofInternal => exact ⟨.inl (), rfl⟩
    | ofLeft i => exact ⟨.inr (.inl i), rfl⟩
    | ofRight i => exact ⟨.inr (.inr i), rfl⟩

theorem finite_NQuery (skels : List Skeleton) : Finite (NQuery skels) := by
  unfold NQuery
  have : ∀ j : Fin skels.length, Finite (SkeletonInternalIndex (skels.get j)) := fun _ => finite_internalIndex _
  have : Finite (MAddress skels) := inferInstanceAs (Finite ((j : Fin skels.length) × SkeletonInternalIndex (skels.get j)))
  have : Finite NockvmE2E.Exec.E2E.DgJ8 := inferInstance
  infer_instance
noncomputable example : SampleableType KC := SampleableType.ofFintype KC
noncomputable example (FK : Type) [Finite FK] (FR : FK → Type) [∀ k, SampleableType (FR k)] (skelsF : List Skeleton) :
    ∀ d, SampleableType (NockvmE2E.Exec.E2EJ8V.SideRng skelsF FR d) := fun d => by
  rcases d with q | k
  · exact (inferInstanceAs (SampleableType NockvmE2E.Exec.E2E.DgJ8))
  · exact (inferInstanceAs (SampleableType (FR k)))
end Inst

end NockvmE2E.J9A.E2EJ9AVSat

#print axioms NockvmE2E.J9A.E2EJ9AVSat.sat_core
#print axioms NockvmE2E.J9A.E2EJ9AVSat.abs9R_k0
#print axioms NockvmE2E.J9A.E2EJ9AVSat.hz_unit
#print axioms NockvmE2E.J9A.E2EJ9AVSat.budgets_sat
