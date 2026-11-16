import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily
import Nock.NockVMROM.Thm54.RecordCarrier

/-!
# The shared VCL-L record view : validity / export (with the side slot) / path

.

* **The three accumulators** (`Fin 3`, `mVCL`): `0` validity `(fp, lo + hi·√δ, idx)` (`5` entries),
  `1` export `(fp p, fp l, fp r, idx, side)` (`11` entries, Q5 (c)), `2` path
  `(fp root, fp child, acc, rootIdx)` (`8` entries).
* **`KeyVCL`**: one constructor per accumulator; the export key is `(idx, side)` — the `Bool` now carries
  the side, so the two records of one cell are different keys (`sideKey_sides`); the path key is
  `(rootIdx, axis)` (a root-serial path key is unservable, `Compute/Keys.lean`
  `root_serial_key_unservable`, so the key carries the axis).
* **`recordViewVCL : RecordView F K Kio Kio KeyVCL C S hC mVCL`**, generic in the tables.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL
namespace RV

open Nock Nock.ComputeTable
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.RecordCarrier

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## 1. Widths and keys -/

/-- The record widths: validity `5`, export `11` (with the side), path `8`. -/
def mVCL : Fin 3 → ℕ
  | 0 => 5
  | 1 => 11
  | 2 => 8

theorem mVCL_vals : mVCL 0 = 5 ∧ mVCL 1 = 11 ∧ mVCL 2 = 8 := ⟨rfl, rfl, rfl⟩

/-- **The VCL-L key**: validity by cell serial; export by `(cell serial, side)`; path by
`(root serial, axis)`. -/
inductive KeyVCL
  | valid (idx : ℕ)
  | export (idx : ℕ) (side : Bool)
  | path (rootIdx : ℕ) (axis : ℕ)
  deriving DecidableEq

/-! ## 2. The readers -/

section readers
variable {Kio : Type} [Field Kio] [DecidableEq Kio]

/-- The fingerprint in entries `b, b+1, b+2`. -/
def fpAt {m : ℕ} (r : Fin m → Kio) (b : ℕ) (h : b + 2 < m) : FP Kio :=
  ⟨r ⟨b, by omega⟩, r ⟨b + 1, by omega⟩, r ⟨b + 2, by omega⟩⟩

/-- The side of an export record (entry `10`): `true` iff it is `1`. -/
def sideOf (r : Fin 11 → Kio) : Bool := decide (r 10 = 1)

/-- Export: `(p, l, r, idx, side)`. -/
noncomputable def exportKey (r : Fin 11 → Kio) : KeyVCL := .export (natLift (r 9)) (sideOf r)
def exportRoot (r : Fin 11 → Kio) : FP Kio := fpAt r 0 (by omega)
def exportChild (r : Fin 11 → Kio) : FP Kio :=
  if sideOf r then fpAt r 6 (by omega) else fpAt r 3 (by omega)
def exportAxis (r : Fin 11 → Kio) : ℕ := if sideOf r then 3 else 2

/-- Path: `(root, child, acc, rootIdx)`. -/
noncomputable def pathKey (r : Fin 8 → Kio) : KeyVCL := .path (natLift (r 7)) (natLift (r 6))
def pathRoot (r : Fin 8 → Kio) : FP Kio := fpAt r 0 (by omega)
def pathChild (r : Fin 8 → Kio) : FP Kio := fpAt r 3 (by omega)
noncomputable def pathAxis (r : Fin 8 → Kio) : ℕ := natLift (r 6)

/-- Validity: `(fp, lo + hi·√δ, idx)`. -/
noncomputable def validKey (r : Fin 5 → Kio) : KeyVCL := .valid (natLift (r 4))
def validRoot (r : Fin 5 → Kio) : FP Kio := fpAt r 0 (by omega)

/-- The readers per accumulator. -/
noncomputable def keyVCL : ∀ a : Fin 3, (Fin (mVCL a) → Kio) → KeyVCL
  | 0 => validKey
  | 1 => exportKey
  | 2 => pathKey

def rootVCL : ∀ a : Fin 3, (Fin (mVCL a) → Kio) → FP Kio
  | 0 => validRoot
  | 1 => exportRoot
  | 2 => pathRoot

def childVCL : ∀ a : Fin 3, (Fin (mVCL a) → Kio) → FP Kio
  | 0 => validRoot
  | 1 => exportChild
  | 2 => pathChild

noncomputable def axisVCL : ∀ a : Fin 3, (Fin (mVCL a) → Kio) → ℕ
  | 0 => fun _ => 1
  | 1 => exportAxis
  | 2 => pathAxis

end readers

/-! ## 3. The record view -/

/-- **`recordViewVCL`**: the shared VCL-L record view (`Kfp := Kio`), generic in the compute table
`C`, the memory shape `S` and the height `hC`; the axis reads only the record. -/
noncomputable def recordViewVCL (F K Kio : Type) [Field F] [Field K] [Algebra F K] [Field Kio]
    [DecidableEq Kio] (C : TableSpec) (S : MemShape) (hC : ℕ) :
    RecordView F K Kio Kio KeyVCL C S hC mVCL where
  key := keyVCL
  root := rootVCL
  child := childVCL
  axis := fun a _ _ _ r => axisVCL a r

section receipts
variable {F K Kio : Type} [Field F] [Field K] [Algebra F K] [Field Kio] [DecidableEq Kio]
  {C : TableSpec} {S : MemShape} {hC : ℕ}

theorem recordViewVCL_export (r : Fin 11 → Kio) (V : VerifierData F K hC S) (b : B0Cols F C)
    (bm : ∀ t, B0Cols F (S.table t)) :
    (recordViewVCL F K Kio C S hC).key 1 r = .export (natLift (r 9)) (sideOf r) ∧
      (recordViewVCL F K Kio C S hC).root 1 r = fpAt r 0 (by omega) ∧
      (recordViewVCL F K Kio C S hC).child 1 r =
        (if r 10 = 1 then fpAt r 6 (by omega) else fpAt r 3 (by omega)) ∧
      (recordViewVCL F K Kio C S hC).axis 1 V b bm r = (if r 10 = 1 then 3 else 2) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show exportChild r = _
    by_cases h : r 10 = 1 <;> simp [exportChild, sideOf, h]
  · show exportAxis r = _
    by_cases h : r 10 = 1 <;> simp [exportAxis, sideOf, h]

/-- The validity record's axis is `1` (slot 1 = the root), so `Noun.slot` serves it. -/
theorem recordViewVCL_valid_axis (r : Fin 5 → Kio) (V : VerifierData F K hC S) (b : B0Cols F C)
    (bm : ∀ t, B0Cols F (S.table t)) (n : Noun) :
    (recordViewVCL F K Kio C S hC).axis 0 V b bm r = 1 ∧
      Noun.slot ((recordViewVCL F K Kio C S hC).axis 0 V b bm r) n = some n ∧
      (recordViewVCL F K Kio C S hC).root 0 r = (recordViewVCL F K Kio C S hC).child 0 r :=
  ⟨rfl, by show Noun.slot 1 n = some n; simp [Noun.slot], rfl⟩

/-! ## 4. -/

def rec0 (f fh ft : FP Kio) (fIdx : Kio) : Fin 11 → Kio :=
  ![f.1, f.2, f.3, fh.1, fh.2, fh.3, ft.1, ft.2, ft.3, fIdx, 1]

def rec1 (ft fth ftt : FP Kio) (vIdx : Kio) : Fin 11 → Kio :=
  ![ft.1, ft.2, ft.3, fth.1, fth.2, fth.3, ftt.1, ftt.2, ftt.3, vIdx, 0]

/-- **Record 0 fits** at `recordViewVCL`: root `f`, child `f_t`, axis `3 = joinRecordAxis st ax S 0`,
given the paper's `mr1 = ⟨f, f_t, 3⟩`. -/
theorem d1_record0_fits (V : VerifierData F K hC S) (b : B0Cols F C) (bm : ∀ t, B0Cols F (S.table t))
    (st : State) (ax : ℕ → ℕ) (S' : ℕ) (f fh ft : FP Kio) (fIdx : Kio)
    (mr1 : MemRec Kio) (h : mr1.root = f ∧ mr1.child = ft) :
    (recordViewVCL F K Kio C S hC).root 1 (rec0 f fh ft fIdx) = mr1.root ∧
      (recordViewVCL F K Kio C S hC).child 1 (rec0 f fh ft fIdx) = mr1.child ∧
      (recordViewVCL F K Kio C S hC).axis 1 V b bm (rec0 f fh ft fIdx) = joinRecordAxis st ax S' 0 := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨-, hr, hc, ha⟩ := recordViewVCL_export (C := C) (rec0 f fh ft fIdx) V b bm
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, h1]; rfl
  · rw [hc, h2]; simp [rec0, fpAt]
  · rw [ha]; simp [rec0, joinRecordAxis]

/-- **Record 1 fits** at every non-path state: root `f_t`, child `f_th`, axis `2`. -/
theorem d1_record1_fits (V : VerifierData F K hC S) (b : B0Cols F C)
    (bm : ∀ t, B0Cols F (S.table t)) (st : State) (hst : st ≠ .s0) (ax : ℕ → ℕ) (S' : ℕ)
    (ft fth ftt : FP Kio) (vIdx : Kio) (mr2 : MemRec Kio) (h : mr2.root = ft ∧ mr2.child = fth) :
    (recordViewVCL F K Kio C S hC).root 1 (rec1 ft fth ftt vIdx) = mr2.root ∧
      (recordViewVCL F K Kio C S hC).child 1 (rec1 ft fth ftt vIdx) = mr2.child ∧
      (recordViewVCL F K Kio C S hC).axis 1 V b bm (rec1 ft fth ftt vIdx) = joinRecordAxis st ax S' 1 := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨-, hr, hc, ha⟩ := recordViewVCL_export (C := C) (rec1 ft fth ftt vIdx) V b bm
  have h10 : rec1 ft fth ftt vIdx 10 ≠ 1 := by simp [rec1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, h1]; rfl
  · rw [hc, h2, if_neg h10]; simp [rec1, fpAt]
  · have : joinRecordAxis st ax S' 1 = 2 := by
      cases st <;> first | rfl | exact absurd rfl hst
    rw [ha, this, if_neg h10]

/-- **The two sides are different keys** (the `Bool` of the export key carries information). -/
theorem sideKey_sides (f fh ft fth ftt : FP Kio) (i : Kio) :
    (recordViewVCL F K Kio C S hC).key 1 (rec0 f fh ft i) = .export (natLift i) true ∧
      (recordViewVCL F K Kio C S hC).key 1 (rec1 ft fth ftt i) = .export (natLift i) false := by
  refine ⟨?_, ?_⟩ <;> simp [recordViewVCL, keyVCL, exportKey, sideOf, rec0, rec1]

theorem no_sideless_child (child : (Fin 10 → Kio) → FP Kio) (rec : Fin 10 → Kio) (l r : FP Kio)
    (hlr : l ≠ r) (h0 : child rec = r) (h1 : child rec = l) : False :=
  hlr (h1.symm.trans h0)

end receipts

end RV
end VclL
end Nock.NockVMROM.Thm54
