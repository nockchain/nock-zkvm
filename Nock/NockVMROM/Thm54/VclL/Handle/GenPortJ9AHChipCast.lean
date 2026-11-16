/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHChipCast.lean

  Pattern `ComplJ9AOfMem` §1. Does not import `AcceptsJ9A`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast

open Nock Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle

noncomputable section

section Generic
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

variable {n m : ℕ} (e : n = m) (hn : 0 < n) (hm : 0 < m) (ν : Fin n → ZMod p) (μ : Fin m → ZMod p)
  (hνμ : ∀ i : Fin n, ν i = μ (Fin.cast e i)) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
  (chals pubs : ℕ → K)

/-- `powN` reads only `i.val`. -/
theorem powN_cast (i : Fin n) :
    ComplJ8Of.powN o m (Fin.cast e i) = ComplJ8Of.powN o n i := rfl

include e hνμ

theorem cellOK_reidx(T : Fin 242 → (ZMod p)[X])
    (H : (CellTwinKW.cellChipHQKW δ b hm μ o chals pubs).rap.Satisfies T ∧
      (CellTwinKW.cellChipHQKW δ b hm μ o chals pubs).BindsPreprocessing T) :
    (CellTwinKW.cellChipHQKW δ b hn ν o chals pubs).rap.Satisfies T ∧
      (CellTwinKW.cellChipHQKW δ b hn ν o chals pubs).BindsPreprocessing T := by
  subst e
  obtain rfl : ν = μ := funext hνμ
  exact H

theorem walkOK_reidx (kr : ℕ) (T : Fin 166 → (ZMod p)[X])
    (H : (WalkJ8.walkChipJ8 δ kr b hm μ o chals pubs).rap.Satisfies
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width δ kr b hm μ o chals pubs) j)) ∧
      (WalkJ8.walkChipJ8 δ kr b hm μ o chals pubs).BindsPreprocessing
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width δ kr b hm μ o chals pubs) j))) :
    (WalkJ8.walkChipJ8 δ kr b hn ν o chals pubs).rap.Satisfies
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width δ kr b hn ν o chals pubs) j)) ∧
      (WalkJ8.walkChipJ8 δ kr b hn ν o chals pubs).BindsPreprocessing
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width δ kr b hn ν o chals pubs) j)) := by
  subst e
  obtain rfl : ν = μ := funext hνμ
  exact H

theorem atomOK_reidx (T : Fin 349 → (ZMod p)[X])
    (H : (AtomChipHQ.atomChipHQ δ b hm μ o chals pubs).rap.Satisfies
        (fun j => T (Fin.cast (AtomChipHQ.atomChipHQ_width δ b hm μ o chals pubs) j)) ∧
      (AtomChipHQ.atomChipHQ δ b hm μ o chals pubs).BindsPreprocessing
        (fun j => T (Fin.cast (AtomChipHQ.atomChipHQ_width δ b hm μ o chals pubs) j))) :
    (AtomChipHQ.atomChipHQ δ b hn ν o chals pubs).rap.Satisfies
        (fun j => T (Fin.cast (AtomChipHQ.atomChipHQ_width δ b hn ν o chals pubs) j)) ∧
      (AtomChipHQ.atomChipHQ δ b hn ν o chals pubs).BindsPreprocessing
        (fun j => T (Fin.cast (AtomChipHQ.atomChipHQ_width δ b hn ν o chals pubs) j)) := by
  subst e
  obtain rfl : ν = μ := funext hνμ
  exact H

theorem atomLOK_reidx (T : Fin 349 → (ZMod p)[X])
    (H : (AtomChipHQL.atomChipHQL δ b hm μ o chals pubs).rap.Satisfies
        (fun j => T (Fin.cast (AtomChipHQL.atomChipHQL_width δ b hm μ o chals pubs) j)) ∧
      (AtomChipHQL.atomChipHQL δ b hm μ o chals pubs).BindsPreprocessing
        (fun j => T (Fin.cast (AtomChipHQL.atomChipHQL_width δ b hm μ o chals pubs) j))) :
    (AtomChipHQL.atomChipHQL δ b hn ν o chals pubs).rap.Satisfies
        (fun j => T (Fin.cast (AtomChipHQL.atomChipHQL_width δ b hn ν o chals pubs) j)) ∧
      (AtomChipHQL.atomChipHQL δ b hn ν o chals pubs).BindsPreprocessing
        (fun j => T (Fin.cast (AtomChipHQL.atomChipHQL_width δ b hn ν o chals pubs) j)) := by
  subst e
  obtain rfl : ν = μ := funext hνμ
  exact H

theorem awOK_reidx (kr : ℕ) (T : Fin 166 → (ZMod p)[X])
    (H : AcceptsJ8V.AWChipOK δ b kr hm μ o chals pubs
      (fun j => T (Fin.cast (CellTwinK.walkChipHQK_width δ kr b hm μ o chals pubs) j))) :
    AcceptsJ8V.AWChipOK δ b kr hn ν o chals pubs
      (fun j => T (Fin.cast (CellTwinK.walkChipHQK_width δ kr b hn ν o chals pubs) j)) := by
  subst e
  obtain rfl : ν = μ := funext hνμ
  exact H

end Generic

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast in
#print axioms powN_cast
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast in
#print axioms cellOK_reidx
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast in
#print axioms walkOK_reidx
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast in
#print axioms atomOK_reidx
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast in
#print axioms atomLOK_reidx
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast in
#print axioms awOK_reidx
