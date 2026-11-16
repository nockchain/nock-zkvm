/-
  NockvmE2E/Z38/IfaceJ.lean

  Interface of the template-jet theorem side: `layOfX` (the datum's layout as a function on the jet rows), `PreJLink` (the datum's J fixed columns are the loaded
  ones, twin of `PreLLink`), `DX9LJ` (the static datum over `catJ`, twin of `DX9L`), `Wit9LJ` (`Wit9L` with "no jet table" replaced by `PreJLink`, same position).
  Not zero-knowledge.
-/
import NockvmE2E.J9AL.WitJ9AL
import NockvmE2E.J9AL.LagrJ9AL
import NockvmE2E.J9AL.RVUJ9AL
import NockvmE2E.Z38.RunGate9LJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.Z38.IfaceJ

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec.MaskOkK (polyOfArr)
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.PbOfX9L NockvmE2E.J9AL.PregJ9AL NockvmE2E.J9AL.DatX9LOk
open NockvmE2E.J9AL.LagrJ9AL (PreLLink numOf9L)
open NockvmE2E.J9AL.RVUJ9AL (PrimsCan InpLink9L)
open NockvmE2E.J9A.RunGate9L (PrimsLink kOfL kVOfL pregOkF)
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open NockvmE2E.Z38.JetPre (layJ regsOfPub idxOfPub rkOfPub)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (cornerC9L)
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP (addPrims)
open Nock.Jet.ChipJ8 (PRow)

noncomputable section

/-- the datum's layout as a function on the jet rows -/
def layOfX (XI : ExecInst) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8") :
    Fin (hNof XI "jetChipJ8") → PRow := fun i => (layJ XI.pubIn)[(i : ℕ)]'(by have := i.2; omega)

/-- the jet twin of `PreLLink`: the datum's J fixed columns are the loaded ones -/
def PreJLink (XI : ExecInst) (d : Datum9AL) : Prop :=
  ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id = "jetChipJ8" → ∀ c, c < 18 →
    Lagrange.interpolate Finset.univ d.Pb.nodesJ (fun i => Nock.Jet.ChipJ8.jetPre d.Pb.lay c i) =
      polyOfArr (XI.pre[XI.tabs[t].col0 + c]!)

/-- the static datum over `XI` with template jets over `catJ` (registry `(addPrims catJ.toVR (primsOf XI)).R`) -/
def DX9LJ (XI : ExecInst) (h : shapeOkF famJ9AL XI = true)
    (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8") (kroots krootsV : ℕ) (c : P8PublicClaim) : Datum9AL :=
  ⟨PbOfX9L XI h kroots krootsV NockvmE2E.Z38.CatJ.catJ.toCR.Rt (regsOfPub XI.pubIn) XI.pubIn.calls (idxOfPub XI.pubIn) (rkOfPub XI.pubIn)
      (layOfX XI hlen),
    (addPrims NockvmE2E.Z38.CatJ.catJ.toCR.toVR (primsOf XI)).R, c, cornerC9L, 2 ^ 31, XI.hN, zv XI.hGen⟩

/-- **`Wit9LJ XI c Q`**: `Wit9L` with the "no jet table" conjunct replaced by `PreJLink XI d` (same position) -/
def Wit9LJ (XI : ExecInst) (c : P8PublicClaim) (Q : Datum9AL → Prop) : Prop :=
  ∃ (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L XI d),
    StmtP9AL d ∧ InpLink9L d XI.pubIn ∧ PrimsCan XI.pubIn ∧ (∀ id ∈ d.Pb.regs, id < P) ∧
    (∀ t : Fin XI.tabs.size, (chipNumeralF famJ9AL XI.tabs[t].chip).getD 0 = numOf9L d (sigma9L XI t)) ∧
    (d.Pb.nJ = 0 → XI.pubLay.present[3]! = false) ∧ (d.Pb.krootsV = 0 → XI.pubLay.present[5]! = false) ∧
    (d.Pb.axOn = false → XI.pubLay.present[6]! = false) ∧ (d.Pb.spOn = false → XI.pubLay.present[7]! = false) ∧
    (d.Pb.aluOn = false → XI.pubLay.present[8]! = false) ∧
    PreLLink XI d ∧
    PreJLink XI d ∧
    (∃ (R : NockvmE2E.J8.TabRestr (NockvmE2E.J9AL.GenJ9AL.J9AL d hdk)) (hT : R.T' = XI.tabs.size),
      (∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) ∧ (NockvmE2E.J9AL.GenJ9AL.J9AL d hdk).AccOn R.q) ∧
    d.c = c ∧ Q d

end

end NockvmE2E.Z38.IfaceJ
