/-
  NockvmE2E/Z38/CatJ.lean

  The fixed, kernel-checked template-jet catalogue `catJ : CheckedRegP p` (fixed catalogue):
  template `TN` (Batch4892's, `x : F` at axis 2, `d : N` at axis 3, body `build [x*x, d]`) registered at id 7, plus the big-atom
  primitive `add` at id 8.  `wt / axPos / axLt` are proved once, by the same tactics as `Nock.RedTeam.Batch4892.CN`
  (no `decide` over an instance).  Own copy: nothing here imports the RedTeam demo.
  Only catalogue jets are covered; a new jet needs a new catalogue and a new kernel proof.  Not zero-knowledge.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALData

set_option autoImplicit false

namespace NockvmE2E.Z38.CatJ

open Nock.Jet Nock.Jet.Autogen
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry (CheckedReg)
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP (CheckedRegP)

/-- `x : F` at axis 2, `d : N` at axis 3; body `build [x*x, d]` (as Batch4892 `TN`). -/
def TN : Tpl where
  k := 2
  ax := ![2, 3]
  inTy := ![.F, .N]
  outTy := .L 2 .N
  body := Ex.build [.mul (.var 0) (.var 0), .var 1]

theorem TN_wt (p : ℕ) : TN.WellTyped p := by
  unfold Tpl.WellTyped TN Ex.build
  simp only [List.foldr]
  exact HasTy.pair (HasTy.weakN (HasTy.mul (by simpa using HasTy.var (p := p) (inTy := ![.F, .N]) 0)
    (by simpa using HasTy.var (p := p) (inTy := ![.F, .N]) 0)))
    (HasTy.pair (by simpa using HasTy.var (p := p) (inTy := ![.F, .N]) 1) (HasTy.nil _))

abbrev pG : ℕ := Nock.Field.p

/-- the template registry: id 7 at `TN` -/
def CN : CheckedReg pG where
  hp := by decide
  Rt := fun _ => TN
  regs := [7]
  wt := fun _ _ => TN_wt _
  axPos := fun _ _ => by decide
  axLt := fun _ _ i => by fin_cases i <;> decide

/-- the catalogue: `CN` (id 7) plus the big-atom primitive `add` at id 8 -/
def catJ : CheckedRegP pG where
  toCR := CN
  prims := [(8, .add)]
  ndP := by decide

theorem catJ_compiledByP :
    Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP.CompiledByP pG catJ.toVR catJ.toCR.Rt catJ.prims :=
  catJ.compiledByP

end NockvmE2E.Z38.CatJ

section Axioms
open NockvmE2E.Z38.CatJ
#print axioms TN_wt
#print axioms CN
#print axioms catJ
#print axioms catJ_compiledByP
end Axioms
