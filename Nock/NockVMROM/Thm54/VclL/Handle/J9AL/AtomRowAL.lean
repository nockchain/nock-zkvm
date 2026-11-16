/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AtomRowAL.lean

  **The atom-table inputs of `AluSvcAL.hsemAL` at the J-9 AL reader.**
  Everything at `p = Nock.Atoms.p` (`Fp`), with the instance block of `AluSvcAL` section Sem.

  * `atomAL_len`: `nA ≤ |RR49AL.atomAL r Pb tr|` (the truncation at `r.A` loses nothing).
  * `rowRead_rAT`: `AtomWalkAL.RowRead (atomAL r Pb tr) (rAT b Pb.toPubJ8 tr.toJ8) nA`.  `rowsAJ8` and `rAT` read
    the same coin-free row environments `envOfTrace tr.A`; `reB0` casts `natOf` (`< p`) through `val`.  No chip fact.
  * `hin_rAT`: `wR = 1 → idR < nA`, from the atom chip's `ValidityServed` (`ReaderR3bJ8.idR_lt_of_served`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.SoundJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.RR49AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AtomWalkAL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomRowAL

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow atomChipHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT rAT_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader valReader_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.RR49AL (reB0)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (rowsAJ8 rowsB0 rowsB0_length)
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (natOf_eq_val)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qA)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (idR_lt_of_served)
open Nock.Atoms (Fp)

noncomputable section

section Rows
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  [Fact (ringChar Fp).Prime] [Algebra (ZMod (ringChar Fp)) K] [Algebra Fp (Quad (algebraMap Fp K δ))]
  [Algebra (ZMod (ringChar Fp)) (Quad (algebraMap Fp K δ))]

theorem atomAL_len (r : RowsJ9AL) (Pb : PubJ9AL Nock.Atoms.p) (tr : TrJ9AL Fp) (hA : Pb.nA ≤ r.A) :
    Pb.nA ≤ (RR49AL.atomAL r Pb tr).length := by
  unfold RR49AL.atomAL
  simp [TraceJ8.rowsAJ8, rowsB0_length, hA]

theorem rowRead_rAT (r : RowsJ9AL) (Pb : PubJ9AL Nock.Atoms.p) (tr : TrJ9AL Fp) (hA : Pb.nA ≤ r.A) :
    AtomWalkAL.RowRead (RR49AL.atomAL r Pb tr) (rAT (K := K) b Pb.toPubJ8 tr.toJ8) Pb.nA := by
  intro k hk
  have hl : k < (rowsAJ8 Pb.nodesA Pb.orbitA tr.toJ8).length := by
    simp [rowsAJ8, rowsB0_length, hk]
  have hrc : ringChar Fp = Nock.Atoms.p := ZMod.ringChar_zmod_n _
  have hrow : (rowsAJ8 Pb.nodesA Pb.orbitA tr.toJ8)[k] = cellB0Of (Framework.Reify.envOfTrace tr.toJ8.A
      Pb.orbitA.ω (Pb.nodesA ⟨k, hk⟩) (fun _ => 0) (fun _ => 0)) := by
    simp [rowsAJ8, rowsB0, List.getElem_ofFn]
  have hrk : rAT (K := K) b Pb.toPubJ8 tr.toJ8 k = valReader (fun k : Fin Pb.nA =>
      aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.toJ8.A k) k := rfl
  have hv := valReader_lt (fun k : Fin Pb.nA => aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0)
      tr.toJ8.A k) ⟨k, hk⟩
  rw [hrk]
  rw [hv]
  have he : (aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.toJ8.A ⟨k, hk⟩).trace =
      (Framework.Reify.envOfTrace tr.toJ8.A Pb.orbitA.ω (Pb.nodesA ⟨k, hk⟩) (fun _ => 0) (fun _ => 0)).trace := by
    funext j
    simp only [aEF, Reify.envOfTrace, TraceJ8.widthA_eq]
  have key : ∀ x : Fp, (((x.val : ZMod (ringChar Fp)).val : ℕ) : Fp).val = x.val := by
    intro x
    have h1 : ((x.val : ZMod (ringChar Fp)).val) = x.val := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega)
    rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt x)]
  have hone : ∀ x : Fp, decide (x = 1) = decide (x.val = 1) := by
    intro x
    by_cases h : x = 1
    · subst h; simp [ZMod.val_one]
    · have : x.val ≠ 1 := fun h1 => h (by
        have := ZMod.val_injective _ (h1.trans (ZMod.val_one _).symm); exact this)
      simp [h, this]
  refine ⟨reB0 Nock.Atoms.p ((rowsAJ8 Pb.nodesA Pb.orbitA tr.toJ8)[k]), ?_, ?_, ?_, ?_, ?_⟩
  · unfold RR49AL.atomAL
    rw [List.getElem?_take_of_lt (by omega)]
    simp [List.getElem?_eq_getElem hl]
  all_goals simp only [hrow, he]
  · simp only [reB0, cellB0Of, hone]
  · simp only [reB0, cellB0Of, natOf_eq_val]
  · simp only [reB0, cellB0Of, natOf_eq_val, key]
  · simp only [reB0, cellB0Of, natOf_eq_val, key]

theorem hin_rAT (Pb : PubJ9AL Nock.Atoms.p) (tr : TrJ9AL Fp) (χ : Coins frameJ8 K) (pubsA : ℕ → K)
    (hsatA : (atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubsA).rap.Satisfies
      (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) pubsA))
    (hbindA : (atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubsA).BindsPreprocessing
      (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) pubsA))
    (hinjA : Function.Injective Pb.nodesA)
    (hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA),
      Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω)
    (hnpA : Pb.nA < Nock.Atoms.p)
    (hservedA : ValidityServed (cellTableOf δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubsA
      (AtomChipHQ.restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubsA
        (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) pubsA)))) :
    ∀ j < Pb.nA, (rAT (K := K) b Pb.toPubJ8 tr.toJ8 j).wR = 1 → (rAT (K := K) b Pb.toPubJ8 tr.toJ8 j).idR < Pb.nA := by
  intro j hj hw
  have hEr := rAT_eq δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) pubsA
  rw [← hEr] at hw ⊢
  have hv := valReader_lt (fun k : Fin Pb.nA => aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubsA
    (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) pubsA) k) ⟨j, hj⟩
  have hv' : valReader (fun k : Fin Pb.nA => aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubsA
    (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) pubsA) k) j = _ := hv
  rw [hv'] at hw ⊢
  have h1 : (aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubsA (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) pubsA)
      ⟨j, hj⟩).trace Cell.wR = 1 :=
    ZMod.val_injective _ (hw.trans (ZMod.val_one Nock.Atoms.p).symm)
  exact idR_lt_of_served hsatA hbindA hinjA hadjA hnpA hservedA ⟨j, hj⟩ h1

end Rows

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomRowAL
