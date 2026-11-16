/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplClosedChecked.lean

  The closed completeness theorems `ComplJ9AClosed.complJ9A_closed`, `ComplJ8Closed.complJ8_closed` and
  `ComplJ9BClosed.complJ9B_closed`, with the two binders `hRt`, `hregAx` replaced by the registry-level
  `hC : CheckedRegistry.CompiledBy p Rg Rt` (via `CheckedRegistry.hRt_hregAx_of`).
  Instances for a `CheckedReg` and for the empty registry (J-9 A). -/
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AClosed
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

noncomputable section

/-! ## J-9 A -/

section J9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A Rows31A axOnA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

section Rec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen

open Classical in
theorem complJ9A_closed_of(hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (hC : CheckedRegistry.CompiledBy p Rg Rt)
    (h31A : Rows31A (DA)) :
    let B := BRun9A δ b Rt hgen hpG h31A
    (∀ χ, B.Good χ → AcceptsJ9A δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9A B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  obtain ⟨hRt, hregAx⟩ := CheckedRegistry.hRt_hregAx_of hC hgen
  exact ComplJ9AClosed.complJ9A_closed δ b Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA hRt hregAx h31A

end Rec

section Inst
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

open Classical in
theorem complJ9A_closed_checked(C : CheckedRegistry.CheckedReg p)
    (hgen : genX C.toVR.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
    (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p C.toVR C.Rt hgen).roots)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p C.toVR C.Rt hgen).preads)
    (h31A : Rows31A (j9aDataOf p C.toVR C.Rt hgen)) :
    let B := BRun9A δ b C.Rt hgen hpG h31A
    (∀ χ, B.Good χ → AcceptsJ9A δ b B.Pb C.toVR.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9A B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A δ b B.Pb C.toVR.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) :=
  complJ9A_closed_of δ b C.Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA C.compiledBy h31A

open Classical in
theorem complJ9A_closed_empty(Rt : ℕ → Nock.Jet.Autogen.Tpl)
    (hgen : genX Nock.Jet.VerifiedRegistry.empty.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
    (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Nock.Jet.VerifiedRegistry.empty Rt hgen).roots)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Nock.Jet.VerifiedRegistry.empty Rt hgen).preads)
    (h31A : Rows31A (j9aDataOf p Nock.Jet.VerifiedRegistry.empty Rt hgen)) :
    let B := BRun9A δ b Rt hgen hpG h31A
    (∀ χ, B.Good χ → AcceptsJ9A δ b B.Pb Nock.Jet.VerifiedRegistry.empty.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9A B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A δ b B.Pb Nock.Jet.VerifiedRegistry.empty.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) :=
  complJ9A_closed_of δ b Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA (CheckedRegistry.compiledBy_empty p Rt) h31A

end Inst
end J9A

/-! ## J-8 -/

section J8
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8 ComplJ8Obligations ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed

section Closed
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

open Classical in
theorem complJ8_closed_of (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hC : CheckedRegistry.CompiledBy p Rg Rt)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    let B := BRunA δ b Rt hgen hpG h31
    (∀ χ, B.Good χ → AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  obtain ⟨hRt, hregAx⟩ := CheckedRegistry.hRt_hregAx_of hC hgen
  exact ComplJ8Closed.complJ8_closed δ b Rt hgen hpG hax hop5 hclA hleaf hwalk hwalkA hRt hregAx h31

end Closed
end J8

/-! ## J-9 B -/

section J9B
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8 ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf

section Rec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen

open Classical in
theorem complJ9B_closed_of (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (hC : CheckedRegistry.CompiledBy p Rg Rt)
    (h31 : Rows31 (DD)) :
    let B := BRun9 δ b Rt hgen hpG h31
    (∀ χ, B.Good χ → AcceptsJ9V.AcceptsJ9V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9V.AcceptsJ9V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  obtain ⟨hRt, hregAx⟩ := CheckedRegistry.hRt_hregAx_of hC hgen
  exact ComplJ9BClosed.complJ9B_closed δ b Rt hgen hpG hax hop5 hleaf hwalk hwalkA hRt hregAx h31

end Rec
end J9B

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked
#print axioms complJ9A_closed_of
#print axioms complJ9A_closed_checked
#print axioms complJ9A_closed_empty
#print axioms complJ8_closed_of
#print axioms complJ9B_closed_of
end Axioms
