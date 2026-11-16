/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/AtomPadP1.lean

 **The P1 atom table denotes no big atom.**

 With the canonical pad `CanonP1.hApad` (`tr.A j = C (padA j)` on the `205` round-0 atom columns), every row the
 atom reader `LinkJ8R3A.rAT` returns has `aL = 0`, `wR = 0`, `aR = 1` (rows `< nA` read the pad, rows `≥ nA` are the
 reader's default `⟨k, 0, 0, 0, 1, …⟩`). So every row denotes the limb list `[0, 1]`, the value `2^32 < p`, and the
 big-row denotation `extB p (rAT b Pb tr)` is `none` everywhere (`extB_rAT_none`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A
import Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.AtomPadP1

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader valReader_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1 (padA)

noncomputable section

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (b : Basis (Fin 3) (ZMod p) K)

/-- **Every reader row is the pad row's limbs**: `aL = 0`, `wR = 0`, `aR = 1`. -/
theorem rAT_pad (Pb : PubJ8 p) {tr : TrJ8 (ZMod p)}
    (hA : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j)) (k : ℕ) :
    (rAT b Pb tr k).aL = 0 ∧ (rAT b Pb tr k).wR = 0 ∧ (rAT b Pb tr k).aR = 1 := by
  by_cases hk : k < Pb.nA
  · have e := valReader_lt (fun k : Fin Pb.nA =>
      AtomServedQ.aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A k) ⟨k, hk⟩
    have ht : ∀ j, j < 205 → (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A
        ⟨k, hk⟩).trace j = padA j := by
      intro j hj
      have hj' : j < 349 := by omega
      simp only [AtomServedQ.aEF, Reify.envOfTrace, hj', ↓reduceDIte]
      rw [hA ⟨j, hj'⟩ hj, Polynomial.eval_C]
    have h1 : (1 : ZMod p).val = 1 := ZMod.val_one_eq_one_mod p ▸ Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt
    show (valReader _ k).aL = 0 ∧ (valReader _ k).wR = 0 ∧ (valReader _ k).aR = 1
    rw [show k = ((⟨k, hk⟩ : Fin Pb.nA) : ℕ) from rfl, e]
    refine ⟨?_, ?_, ?_⟩
    · show ((AtomServedQ.aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A ⟨k, hk⟩).trace
        Cell.aL).val = 0
      rw [ht _ (by simp [Cell.aL])]; simp [padA, Cell.aL]
    · show ((AtomServedQ.aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A ⟨k, hk⟩).trace
        Cell.wR).val = 0
      rw [ht _ (by simp [Cell.wR])]; simp [padA, Cell.wR]
    · show ((AtomServedQ.aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A ⟨k, hk⟩).trace
        Cell.aR).val = 1
      rw [ht _ (by simp [Cell.aR])]; simp [padA, Cell.aR, h1]
  · simp [rAT, valReader, hk]

/-- **No big atom in the P1 atom table**: under the pad, `extB p (rAT b Pb tr)` is `none` at every serial. -/
theorem extB_rAT_none (Pb : PubJ8 p) {tr : TrJ8 (ZMod p)} (hp : 2 ^ 32 < p)
    (hA : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j)) :
    extB p (rAT b Pb tr) = fun _ => none := by
  funext j
  unfold extB
  rw [dif_neg]
  rintro ⟨l, hd, hq⟩
  have hl : l = [0, 1] := by
    cases hd with
    | top h => rw [(rAT_pad b Pb hA j).1, (rAT_pad b Pb hA j).2.2]
    | step h _ => rw [(rAT_pad b Pb hA j).2.1] at h; cases h
  subst hl
  simp [Nock.Atoms.val, Nat.ofDigits, Nock.Atoms.B] at hq
  omega

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.AtomPadP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AtomPadP1.rAT_pad
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AtomPadP1.extB_rAT_none
