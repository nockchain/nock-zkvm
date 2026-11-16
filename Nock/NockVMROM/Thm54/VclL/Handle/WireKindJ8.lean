/-
  Nock/NockVMROM/Thm54/VclL/Handle/WireKindJ8.lean

  **The cell twin's export PROVIDE reads the
  pre-wire key `keyH`, not the wire key `keyHK`.**  New module, additive, receipt only.

  SPEC §2.1 / §3.4: the cell export balance `x` carries the WIRE kind `k = w + kb ∈ {0, 1, 2}` (2 = big atom),
  compute consumes `cellRecX = (p.v, l.k, l.v, r.k, r.v)` with `Hd.k` the wire kind (`ChipHX`: `k = kc + 2·kb`),
  and `RowSemChipX.RecOK` reads a consumed `x` record at kind `2` through the atom denotation.  A-3s proved
  `exportHK_genuine` about `keyHK` (`keyH` with kind entries `w + kb`) — but `cellChipHQK`'s mixed gates are
  `Cell.mixedGates δF ++ CellHQ.gates δF` (`CellTwinK.lean:169`), whose provide inverse is
  `invHQ · denKeyQ keyH = 1` (`MemHQ.lean`, `CellHQ.gatesQ`): the key the chip PUTS INTO the balance has kind
  entries `w ∈ {0, 1}`.  So:
  * `cellHQK_mixed` / `cellHQ_provide_keyH` (rfl): the provide denominator is `denKeyQ keyH`;
  * `keyH_kind_bool`: on a base row (boolean `wL`), the provided kind entry is `0` or `1`, never `2`;
  * `keyH_ne_keyHK_big`: on a big-atom child (`wL = 1`, `kbL = 1`) the provided entry is `1` while the wire
    key (and compute's consumed record) has `2` (`2 ≠ 1` in `F` of characteristic `≠ 1`).
  Repair (U): a twin whose `CellHQ.gates` provide `denKeyQ keyHK` (same 242 columns, degree
  unchanged, no new event or coin; the IO summand #5 is over the same key count).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WireKindJ8

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle

section Finding
variable {F : Type} [Field F]

theorem cellHQK_mixed (δF : F) :
    (CellTwinK.cellTemplateHQK δF).mixedTransition = Cell.mixedGates δF ++ CellHQ.gates δF := rfl

/-- **The provide inverse of the export balance reads `keyH`** (kind entries `w`), not `keyHK`. -/
theorem cellHQ_provide_keyH (δF : F) :
    (CellHQ.gatesQ δF).head? =
      some (QE.sub (QE.mul δF (QE.var CellHQ.invHQ) (HQ.denKeyQ δF CellH.keyH)) QE.one) := rfl

/-- The provided left kind entry is the weight `wL`. -/
theorem keyH_kindL (eF : Env F) :
    ((CellH.keyH : List (CoeffExpr F)).map fun g => g.eval eF)[1]? = some (eF.trace Cell.wL) := by
  simp [CellH.keyH, CoeffExpr.eval, cv]

/-- The wire left kind entry is `wL + kbL`. -/
theorem keyHK_kindL (eF : Env F) :
    ((TwoProviderQ.keyHK : List (CoeffExpr F)).map fun g => g.eval eF)[1]? =
      some (eF.trace Cell.wL + eF.trace CellTwinK.kbL) := by
  simp [TwoProviderQ.keyHK, CoeffExpr.eval, cv]

/-- **The provided kind entry is never `2`** on a row with boolean `wL` (`2 ≠ 0`, `2 ≠ 1` in `F`). -/
theorem keyH_kind_bool (h20 : (2 : F) ≠ 0) (h21 : (2 : F) ≠ 1) (eF : Env F)
    (hw : eF.trace Cell.wL = 0 ∨ eF.trace Cell.wL = 1) :
    ((CellH.keyH : List (CoeffExpr F)).map fun g => g.eval eF)[1]? ≠ some 2 := by
  rw [keyH_kindL]
  intro h
  have h' : eF.trace Cell.wL = 2 := Option.some.inj h
  rcases hw with hw | hw
  · exact h20 (h'.symm.trans hw)
  · exact h21 (h'.symm.trans hw)

/-- **On a big-atom child the provided key and the wire key differ** (entry `1`: `1` vs `2`). -/
theorem keyH_ne_keyHK_big (h2 : (2 : F) ≠ 1) (eF : Env F) (hw : eF.trace Cell.wL = 1)
    (hkb : eF.trace CellTwinK.kbL = 1) :
    (CellH.keyH : List (CoeffExpr F)).map (fun g => g.eval eF) ≠
      (TwoProviderQ.keyHK : List (CoeffExpr F)).map (fun g => g.eval eF) := by
  intro h
  have e := congrArg (fun l : List F => l[1]?) h
  rw [keyH_kindL, keyHK_kindL, hw, hkb] at e
  have e1 : (1 : F) = 1 + 1 := Option.some.inj e
  exact h2 (by rw [← one_add_one_eq_two]; exact e1.symm)

end Finding

end Nock.NockVMROM.Thm54.VclL.Handle.WireKindJ8
