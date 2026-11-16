/-
  NockvmE2E/Emit/Chips.lean

  The J-8 chips emitted, with kernel-checked `decode (emit chip) = chip gate lists` (up to `norm`).
-/
import NockvmE2E.Emit.Dag
import NockvmE2E.Emit.Compute
import Nock.Jet.ChipJ8T
import Nock.TraceGenExe.K6
import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
import Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

set_option autoImplicit false

namespace Nock.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ChipH

/-- The `𝕂′` non-residue the executable checker uses (`TraceGenExe/K6.lean:21`). -/
def δ : Gl := Nock.TraceGenExe.deltaF

def jetTemplate : ChipTemplate Gl := Nock.Jet.ChipJ8.jetTemplateJ8T δ
def atomTemplate : ChipTemplate Gl := AtomChipHQL.atomTemplateHQL δ
def cellKWTemplate : ChipTemplate Gl := CellTwinKW.cellTemplateHQKW δ

/-- The concrete `kroots` for the two walk chips: `1` (the J-8 atom-walk dispatch demo, `GenJ8.lean:134`). -/
def kroots : ℕ := 1

def walkAtomTemplate : ChipTemplate Gl := CellTwinK.walkTemplateHQK δ kroots
def walkJ8Template : ChipTemplate Gl := WalkJ8.walkTemplateJ8 δ kroots

/-! ### Slot maps (chip-family challenge conventions → the document's 19 frame coins + derived slots)

Document slots `0..18` ARE the `frameJ8` coins (the checker's `CoinsE`); `>= 19` are derived `γ′` powers, `19 + (j − 11)`.
* memory family (cell KW, atom walk, compute walk): `chalsMJ8E` (`V1J8/CheckJ8.lean:71-77`): `j < 11` coin `j`; `11 ≤ j ≤ 32`
  `Re/Im γ′^((j−11)/2)` with `γ′ = (χ4, χ6)` (`gV`, `CheckJ8.lean:68`); `33, 34` (`CellH.hGam/hRho`, `ProvideH.lean:268-269`) coins
  `11, 12`; `35, 36` coins `15, 16`.  (`TeleHQ.lean:80` reads leaves `33/35` = `γH′`, the HANDLE coins `(χ11, χ15)`, not `γ′`.)
* atom: `chalsAJ8ZE` (`CheckJ8.lean:92-96`): `37, 38 ↦` coins `2, 3` (`z`); `2, 3 ↦` coins `17, 18` (`y`); else memory.
* jet: `chalsJJ8E` (`CheckJ8.lean:99-104`): `j < 8`, `j % 4 ↦` coins `11, 12, 15, 16`.
* compute (`col0Id` flat convention): leaf `3q ↦` coin of `coinHQE q` (`V1J8/PubExe.lean:134-138`): `11,12,13,14,15,16`;
  trace-column leaves `r ≥ 69` are physical coordinate 0 of `𝕂`-column `(r − 69)/3`; public `𝕂`-leaves are flat `r ↦ r/3`. -/

def fM (j : ℕ) : ℕ :=
  if j < 11 then j else if j ≤ 32 then j + 8 else if j = 33 then 11 else if j = 34 then 12
  else if j = 35 then 15 else if j = 36 then 16 else j
def fA (j : ℕ) : ℕ := if j = 37 then 2 else if j = 38 then 3 else if j = 2 then 17 else if j = 3 then 18 else fM j
def fJ (j : ℕ) : ℕ := [11, 12, 15, 16].getD (j % 4) 0
def fX (j : ℕ) : ℕ := [11, 12, 13, 14, 15, 16].getD (j / 3) 0
def feX (r : ℕ) : ℕ := if 69 ≤ r then (r - 69) / 3 else r
def fpX (r : ℕ) : ℕ := r / 3

/-- `computeChipVCLHX`'s gates as source gates: the round-0 base gates (`arithGatesX`, `eqGatesX`), the 18 `𝕂`-valued
accumulator gates (`Compute.lean`, replacing the 54 coordinate-level base gates), the four `𝕂′` slot pairs, the walk gates;
rounds `![69, 18·3]` (`widthHX = 123`). -/
def computeSpec0 : TSpec where
  rounds := 2
  baseCols := [69, 0]
  extCols := [0, 18]
  base := (ChipHX.arithGatesX (F := ℚ) ++ ChipHX.eqGatesX.map ChipH.EqG.gate).map (ChipH.mapC (fun q : ℚ => (q : Gl)))
  ext := []
  mixed := accKGatesHX ++ (ChipHX.slotPairsX Gl δ).flatMap (fun q => [q.1, q.2]) ++ ChipHX.walkGatesFX
  ext1 := []
  ext3 := []
  eqc := []

/-- `baseGatesFX` = round-0 base gates ++ (the cast accumulator gates, now emitted as `𝕂` gates). -/
theorem computeBase_split :
    ChipHX.baseGatesFX (F := Gl) = (ChipHX.arithGatesX (F := ℚ)).map (ChipH.mapC (fun q : ℚ => (q : Gl))) ++
      ChipHX.accGatesHX (F := Gl) ++ ((ChipHX.eqGatesX (F := ℚ)).map ChipH.EqG.gate).map (ChipH.mapC (fun q : ℚ => (q : Gl))) := by
  rw [ChipHX.baseGatesFX, ChipHX.baseGatesHX, accGatesHX_cast]
  simp [List.map_append]

def jetSpec := (TSpec.ofTemplate jetTemplate).rename fJ id id
def atomSpec := (TSpec.ofTemplate atomTemplate).rename fA id id
def cellKWSpec := (TSpec.ofTemplate cellKWTemplate).rename fM id id
def walkAtomSpec := (TSpec.ofTemplate walkAtomTemplate).rename fM id id
def walkJ8Spec := (TSpec.ofTemplate walkJ8Template).rename fM id id
def computeSpec := computeSpec0.rename fX feX fpX

def emit_jet := emitDag jetSpec
def emit_atom := emitDag atomSpec
def emit_cellKW := emitDag cellKWSpec
def emit_walkAtom := emitDag walkAtomSpec
def emit_walkJ8 := emitDag walkJ8Spec
def emit_compute := emitDag computeSpec

end Nock.Emit
#print axioms Nock.Emit.computeBase_split
