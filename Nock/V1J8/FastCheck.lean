/-
  Nock/V1J8/FastCheck.lean

  **`checkFast`.**  `FastLag` installs `@[csimp]` replacements `checkCompX ⇝ checkCompXF`,
  `checkM ⇝ checkMF` (kernel-checked equal), which only affect definitions compiled after them.  `checkJ8` and its
  chip checkers are defined earlier, so this module restates them (each a definitional copy) so that the
  compiled code uses the fast versions.  `checkFast_eq : checkFast I = checkJ8 I` is kernel-checked (`checkStaticJ8F_eq`, the rest definitional).
-/
import Nock.V1J8.FastEval
import Nock.V1J8.FastStatic
import Nock.V1J8.CheckJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.V1J8.Check

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.StrictExtension
open Nock.V1J8.Exe Nock.V1J8.CompX Nock.V1J8.MemX
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellTemplateHQKW)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkTemplateJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomTemplateHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomTemplateHQ)
open Nock.Jet.ChipJ8 (jetTemplateJ8T)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkTemplateHQK)

namespace Fast

def checkCellKW {n : ℕ} (T : TabM n) : Bool := checkM (cellTemplateHQKW deltaF) T
def checkWalkJ8 (kr : ℕ) {n : ℕ} (T : TabM n) : Bool := checkM (walkTemplateJ8 deltaF kr) T
def checkAtomHQL {n : ℕ} (T : TabM n) : Bool := checkM (atomTemplateHQL deltaF) T
def checkAtomHQ {n : ℕ} (T : TabM n) : Bool := checkM (atomTemplateHQ deltaF) T
def checkJchip {n : ℕ} (T : TabM n) : Bool := checkM (jetTemplateJ8T deltaF) T
def checkJOK {n : ℕ} (T : TabM n) : Bool :=
  (checkJchip T && nodupB T && decide (0 < n) && Nock.V1J8.MemX.adjB T) ||
  (decide (n = 0) && zero3 (T.pubs 0) && zero3 (T.pubs 1) && zero3 (T.pubs 2) && zero3 (T.pubs 3))
def checkAW (kr : ℕ) {n : ℕ} (T : TabM n) : Bool := checkM (walkTemplateHQK deltaF kr) T
def checkAWOK (kr : ℕ) {n : ℕ} (T : TabM n) : Bool :=
  (checkAW kr T && nodupB T && Nock.V1J8.MemX.adjB T && decide (1 ≤ kr) && decide (kr ≤ n) && decide (kr + n < p)) ||
  (decide (kr = 0) && zero3 (T.pubs 0) && zero3 (T.pubs 1) &&
    zero3 (T.pubs Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubXQ) &&
    zero3 (T.pubs (Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubXQ + 1)) &&
    zero3 (T.pubs Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubPQ) &&
    zero3 (T.pubs (Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubPQ + 1)))

def chipsB (I : InJ8) : Bool :=
  checkCompX (tabX I) && checkCellKW (tabC I) && checkWalkJ8 I.kroots (tabW I) && checkJOK (tabJ I) &&
  checkAtomHQ (tabA I) && checkAWOK I.krootsV (tabV I) && checkAtomHQL (tabA I)

end Fast

/-- **The fast executable J-8 checker**: `checkJ8` with the chip checkers compiled after the fast `csimp`s. -/
def checkFast (I : InJ8) : Bool :=
  if hv : validB I = true then
    checkStaticJ8F (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g &&
    checkPubJ8E (mkPb I ((validB_iff I).mp hv)) I.c I.χ I.M && Fast.chipsB I
  else false

/-- The fast chip builder `Fast.chipsB` agrees with `chipsB` (definitionally). -/
theorem checkFast_chipsB (I : InJ8) : Fast.chipsB I = chipsB I := rfl

/-- **`checkFast = checkJ8`** (definitional). -/
theorem checkFast_eq (I : InJ8) : checkFast I = checkJ8 I := by
  unfold checkFast checkJ8
  split_ifs with hv
  · rw [checkStaticJ8F_eq, checkFast_chipsB]
  · rfl

section Iff
variable [iA : Algebra Nock.Atoms.Fp KQ] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- **`checkFast I = true` iff the input is valid and accepted**: for a registry `Rg` with `RegOK I Rg`, the fast check succeeds exactly when there is a `ValidJ8 I` under which `AcceptsJ8V` holds for the input's claim, coins, message, trace and row bounds. -/
theorem checkFast_iff (I : InJ8) (Rg : Nock.Jet.Registry) (hreg : RegOK I Rg) :
    checkFast I = true ↔ ∃ hv : ValidJ8 I,
      AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb I hv) Rg I.c (toχ I.χ) I.M.toMsg (mkTr I) I.r I.g := by
  rw [checkFast_eq]; exact checkJ8_iff I Rg hreg

end Iff

end Nock.V1J8.Check

#print axioms Nock.V1J8.Check.checkFast_eq
#print axioms Nock.V1J8.Check.checkFast_iff
#print axioms Nock.TraceGenExe.mulU_toNat
#print axioms Nock.TraceGenExe.Gold.mulF_eq
#print axioms Nock.V1J8.FastLag.checkM_eq_F
#print axioms Nock.V1J8.FastLag.checkCompX_eq_F
#print axioms Nock.V1J8.FastEval.checkM_eq_G
#print axioms Nock.V1J8.FastEval.checkCompX_eq_G
#print axioms Nock.V1J8.checkStaticJ8F_eq
#print axioms Nock.V1J8.nodupB_eq_F
