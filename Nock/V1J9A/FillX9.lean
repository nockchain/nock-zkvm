/-
  Nock/V1J9A/FillX9.lean

  `ComplJ9ACompRow.colX9` is
  noncomputable (`colX` decides with `Classical`; `ringChar F` is not computable). `colX9E` is the same formula with
  `FillX.colXE` for `colX` and the literal prime `P` for `ringChar F`; `colX9E_eq` (kernel theorem) at any field with
  `DecidableEq` and `CharP F P`. `nodeLab9E` / `nodeLab9E_eq` likewise for `ComplJ9AReadsAt.nodeLab9`. -/
import Nock.V1J8.FillX
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AReadsAt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Nock.V1J9A.FillX9

open Nock Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (labelColsX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (bitN colS0B colS10B colS10S colX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReadsAt (labV nodeLab9)
open Nock.J9A.NounAx (top segRd)

section Fill
variable {F : Type} [Field F] [DecidableEq F] (P : ℕ) (H : Noun → ℕ × ℕ)
  (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

def colS0BE (r : RowNX) (n : ℕ) (fst lst : F) : ℕ → F := fun c =>
  if c < 17 then 0 else if c < 123 then Nock.V1J8.FillX.colXE H pd r fst lst c
  else if c = 123 then 1 else if c = 126 then (idOf n : F) else 0

def colS10BE (r : RowNX) (n : ℕ) (fst lst : F) : ℕ → F := fun c =>
  if c < 17 then 0 else if c < 123 then Nock.V1J8.FillX.colXE H pd r fst lst c
  else if c = 124 then 1 else if c = 126 then (idOf n : F)
  else if c = 127 then (if P ≤ n then 2 else 3)
  else if c = 128 then (if P ≤ n then hv H r.ftth else ((64 * idOf n + 1 : ℕ) : F))
  else 0

def colS10SE (n m : ℕ) (r : RowNX) (fst lst : F) : ℕ → F := fun c =>
  let b : ℕ → F := fun i => ((bitN m i : ℕ) : F)
  let hd : F := if m = top n then 1 else 0
  let z1 : F := if segRd n m = 1 then 1 else 0
  let pw1 : F := (1 + b 0) * ((1 + 3 * b 1) * (1 + 15 * b 2))
  let pw2 : F := (1 + 255 * b 3) * ((1 + 65535 * b 4) * (1 + 4294967295 * b 5))
  let pw : F := 2 * (pw1 * pw2)
  if c < 17 then 0
  else if c = 19 then z1 else if c = 20 then pw1 else if c = 21 then b 0 else if c = 22 then pw2
  else if c = 23 then pw else if c = 24 then 1 - z1
  else if c = 27 then (if m = top n ∧ P ≤ n then 2 else 3)
  else if c = 28 then (if m = top n ∧ P ≤ n then (idOf n : F) else ((64 * idOf n + m : ℕ) : F))
  else if c = 50 then 1
  else if c < 61 then Nock.V1J8.FillX.colXE H pd r fst lst c
  else if c = 61 then b 1
  else if c = 62 then (1 - b 0) * ((1 - b 1) * (1 - b 2))
  else if c = 63 then (1 - b 3) * ((1 - b 4) * (1 - b 5))
  else if c = 65 then b 2 else if c = 67 then b 3
  else if c < 125 then 0
  else if c = 125 then 1 else if c = 126 then (idOf n : F)
  else if c = 127 then (if m = 0 then 0 else 3)
  else if c = 128 then (if m = 0 then 1 else ((64 * idOf n + (m - 1) : ℕ) : F))
  else if c = 129 then b 4 else if c = 130 then b 5 else if c = 131 then hd
  else if c = 132 then b 0 * (b 1 * b 2) else if c = 133 then b 3 * (b 4 * b 5)
  else if c = 134 then ((n / 2 ^ (32 * m) % 2 ^ 32 : ℕ) : F)
  else if c = 135 then hd * (pw - 1) + (1 - hd) * (2 * pw - 2)
  else if c = 136 then ((segRd n m : ℕ) : F)
  else 0

/-- **The executable honest round-0 columns of a J-9 A row** (chip numbering `0..136`). -/
def colX9E (l : LX9) (fst lst : F) : ℕ → F :=
  match l.chip with
  | .old => Nock.V1J8.FillX.colXE H pd l.rn fst lst
  | .s0B => colS0BE H pd idOf l.rn l.n fst lst
  | .s10B => colS10BE P H pd idOf l.rn l.n fst lst
  | .s10S => colS10SE P H pd idOf l.n l.m l.rn fst lst

/-- The executable honest label of a node. -/
def nodeLab9E (u : Nock.Walk.NTree LX9) : List F :=
  labV (colX9E P H pd idOf u.label 0 0) labelColsX

end Fill

section Eq
variable {F : Type} [Field F] [DecidableEq F] (P : ℕ) [CharP F P] (H : Noun → ℕ × ℕ)
  (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

theorem colS0BE_eq (r : RowNX) (n : ℕ) (fst lst : F) :
    colS0BE H pd idOf r n fst lst = colS0B H pd idOf r n fst lst := by
  funext c
  unfold colS0BE colS0B
  rw [Nock.V1J8.FillX.colXE_eq]

theorem colS10BE_eq (r : RowNX) (n : ℕ) (fst lst : F) :
    colS10BE P H pd idOf r n fst lst = colS10B H pd idOf r n fst lst := by
  funext c
  unfold colS10BE colS10B
  rw [Nock.V1J8.FillX.colXE_eq, ringChar.eq F P]

theorem colS10SE_eq (n m : ℕ) (r : RowNX) (fst lst : F) :
    colS10SE P H pd idOf n m r fst lst = colS10S H pd idOf n m r fst lst := by
  funext c
  unfold colS10SE colS10S
  rw [Nock.V1J8.FillX.colXE_eq, ringChar.eq F P]

/-- **`colX9E_eq`: the executable twin-compute fill is the honest builder `colX9`.** -/
theorem colX9E_eq (l : LX9) (fst lst : F) :
    colX9E P H pd idOf l fst lst = colX9 H pd idOf l fst lst := by
  unfold colX9E colX9
  cases l.chip
  · exact Nock.V1J8.FillX.colXE_eq H pd l.rn fst lst
  · exact colS0BE_eq H pd idOf l.rn l.n fst lst
  · exact colS10BE_eq P H pd idOf l.rn l.n fst lst
  · exact colS10SE_eq P H pd idOf l.n l.m l.rn fst lst

theorem nodeLab9E_eq (u : Nock.Walk.NTree LX9) :
    nodeLab9E P H pd idOf u = nodeLab9 (F := F) H pd idOf u := by
  unfold nodeLab9E nodeLab9
  rw [colX9E_eq]

end Eq

#print axioms colX9E_eq
#print axioms nodeLab9E_eq

end Nock.V1J9A.FillX9
