/-
  NockvmE2E/Emit/ComputeX9.lean

  The J-9 A twin compute chip `computeChipVCLHX9` (width 137, `wRAP = ![83, 54]`) as an emitter spec.

  Twin of `Emit/Compute.lean` + `computeSpec0` (`Emit/Chips.lean`):
  * base gates = the twin's round-0 gates `arithGatesX9 ++ eqGatesX9` at `ℚ → 𝔽_p`, columns renamed by `permX9`
    (twin columns `123..136` become RAP columns `69..82`);
  * `mixed` = the 18 `𝕂`-valued accumulator gates over `slotsX9` (`accKGatesHX9`, replacing the 54 coordinate-level
    `accGatesHX9`) ++ the four `𝕂′` slot pairs ++ the walk gates over 20 states (`walkGatesFX9`), with the BASE parts
    (`Lift g`, `Scale g _`) renamed by `permX9` and the `𝕂`-roles by `feX9` (`69..122 ↦ (r − 69)/3`);
  * rounds `![83, 18·3]` (`widthHX9 = 137`).
  The challenge / public leaf conventions are the J-8 compute's (`fX`, `fpX`): `AcceptsJ9A` feeds `chalVJ8`.
-/
import NockvmE2E.Emit.Chips
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP

set_option autoImplicit false

namespace Nock.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp

/-- The 18 `𝕂`-valued accumulator gates of the twin (same order as `accGatesHX9`'s six blocks). -/
def accKOf9 (b : Bal) (im : Bool) (accBase pubBase : ℕ) : List (MixedExpr Gl) :=
  accKGates (slotsX9.map fun S => ⟨S.actB b, if im then S.invIm else S.inv⟩) accBase pubBase

def accKGatesHX9 : List (MixedExpr Gl) :=
  accKOf9 .x false accXX pubRhoX ++ accKOf9 .x true accXXi pubRhoXIm ++
  accKOf9 .p false accPX pubRhoP ++ accKOf9 .p true accPXi pubRhoPIm ++
  accKOf9 .s false accSX pubRhoSX ++ accKOf9 .s true accSXi pubRhoSXi

/-- twin column (base) ↦ RAP/document column -/
def feB9 (r : ℕ) : ℕ := permX9 r

/-- `𝕂`-role of a twin trace leaf: base columns by `permX9`, round-1 `𝕂` block `69..122` ↦ `(r − 69)/3`. -/
def feX9 (r : ℕ) : ℕ := if 123 ≤ r then r - 54 else if 69 ≤ r then (r - 69) / 3 else r

/-- rename the base coefficient parts of a mixed expression by `permX9` -/
def renBaseM : MixedExpr Gl → MixedExpr Gl
  | .Var k i => .Var k i
  | .Lift g => .Lift (renC permX9 g)
  | .Scale g u => .Scale (renC permX9 g) (renBaseM u)
  | .Const c => .Const c
  | .Add x y => .Add (renBaseM x) (renBaseM y)
  | .Sub x y => .Sub (renBaseM x) (renBaseM y)
  | .Neg x => .Neg (renBaseM x)
  | .Mul x y => .Mul (renBaseM x) (renBaseM y)
  | .Pow x n => .Pow (renBaseM x) n

def slotPairsFlat9 : List (MixedExpr Gl) := (slotPairsX9 Gl Nock.Emit.δ).flatMap (fun q => [q.1, q.2])

/-- `computeChipVCLHX9`'s gates as source gates (twin columns, before leaf renaming). -/
def computeSpec9_0 : TSpec where
  rounds := 2
  baseCols := [83, 0]
  extCols := [0, 18]
  base := ((arithGatesX9 ++ (eqGatesX9 (F := ℚ)).map ChipH.EqG.gate).map (ChipH.mapC (fun q : ℚ => (q : Gl)))).map (renC permX9)
  ext := []
  mixed := (accKGatesHX9 ++ slotPairsFlat9 ++ walkGatesFX9).map renBaseM
  ext1 := []
  ext3 := []
  eqc := []

def computeSpec9 : TSpec := computeSpec9_0.rename fX feX9 fpX

def emit_compute9 := emitDag computeSpec9

theorem computeSpec9_cols : computeSpec9.baseCols.sum + 3 * computeSpec9.extCols.sum = 137 := by decide
theorem computeSpec9_nbase : computeSpec9.base.length = (arithGatesX9 ++ (eqGatesX9 (F := ℚ)).map ChipH.EqG.gate).length := by
  simp [computeSpec9, computeSpec9_0, TSpec.rename]

/-- kernel round trip `decodeDag ∘ emitDag` of the J-9 A compute chip -/
theorem emit_compute9_eq : decodeDag emit_compute9 = some computeSpec9.gates := by decide +kernel

end Nock.Emit

#print axioms Nock.Emit.computeSpec9_cols
#print axioms Nock.Emit.emit_compute9_eq
