/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkLblVSX.lean

  **Card C-2 part 2: the compute walk's label language at J-8** —
  the twin of the 40th's `WalkLblVS` over `StateX` / `LocalVSX.RowVSX` / `kidsX`
  (= `ChipHX.childrenX`).

  The compute walk of `ChipHX.walkGatesX` runs over the row label `(s, f, e)` (six base coordinates
  `ChipHX.labelColsX`, no state tag) and the child labels `ChipHX.childrenX`.  Changes from the 40th:
  the handle kind is the WIRE kind `k ∈ {0, 1, 2}` (`encH` lifts it as a number, not a bit), the
  fanouts of the six J-8 states (`s10` 3, `s10L` 1, `s10T` 0, `s11s` 1, `s11d` 2, `s11j` 1), and
  `SmallR` bounds kinds and values (`s10L`'s child is `(s, (0, a/2), e)`; `ChipHX.labAtom` writes the
  atom formula's kind coordinate as `0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX

open Nock Nock.Walk
open Nock.Edit (StateX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX

/-- **The fanout of a state** (the number of `kidsX`). -/
def fanS : StateX → ℕ
  | .s2 => 3
  | .s3 => 1
  | .s4 => 1
  | .s5 => 2
  | .s6 => 2
  | .s7 => 2
  | .s8 => 2
  | .s9 => 2
  | .cons => 2
  | .s10 => 3
  | .s10L => 1
  | .s11s => 1
  | .s11d => 2
  | .s11j => 1
  | _ => 0

theorem fanS_le (s : StateX) : fanS s ≤ 3 := by cases s <;> simp [fanS]

theorem kidsX_length (r : RowVSX) : (kidsX r).length = fanS r.st := by
  unfold kidsX
  cases r.st <;> simp [fanS]

/-- A placeholder triple (never read inside `fanS`). -/
def trip0 : TripX := ((0, 0), (0, 0), (0, 0))

/-- A child row: its `(s, f, e)` is the triple, the rest junk (only `(s, f, e)` is encoded). -/
def childRow (t : TripX) : RowVSX where
  st := .s0
  s := t.1
  f := t.2.1
  e := t.2.2
  sf1 := (0, 0)
  sf2 := (0, 0)
  fh := (0, 0)
  ft := (0, 0)
  fth := (0, 0)
  ftt := (0, 0)
  ftth := (0, 0)
  fttt := (0, 0)
  m := (0, 0)

@[simp] theorem childRow_trip (t : TripX) : (childRow t).trip = t := by
  simp [childRow, RowVSX.trip]

section Enc
variable {K : Type} [Field K]

/-- A handle's two coordinates in `𝕂`: `(kind, value)`. -/
def encH (h : HX) : K × K := ((h.1 : K), (h.2 : K))

/-- **The six coordinates of a triple** (`ChipH.labelCols`' order `s.k s.v f.k f.v e.k e.v`). -/
def encT (t : TripX) : Fin 6 → K :=
  ![(encH t.1).1, (encH t.1).2, (encH t.2.1).1, (encH t.2.1).2, (encH t.2.2).1, (encH t.2.2).2]

/-- **The encoding of a walk label**: its own `(s, f, e)`. -/
def enc (a : StateX × RowVSX) : Fin 6 → K := encT a.2.trip

/-- **The commit relation of the compute walk**: the state is the row's, exactly the first `fanS`
children are present, and child `j` encodes the row's `j`-th `kidsX` triple. -/
def FV (a : StateX × RowVSX) (xout : Fin 3 → Option (StateX × RowVSX)) : Prop :=
  a.1 = a.2.st ∧ ∀ j : Fin 3, ((j : ℕ) < fanS a.1 ↔ xout j ≠ none) ∧
    ∀ c, xout j = some c → enc (K := K) c = encT ((kidsX a.2).getD j trip0)

end Enc

/-- Every handle value of a row is below `p` (decoded values are `natOf` of `𝔽` columns). -/
def SmallR (p : ℕ) (r : RowVSX) : Prop :=
  ∀ h ∈ [r.s, r.f, r.e, r.sf1, r.sf2, r.fh, r.ft, r.fth, r.ftt, r.ftth, r.fttt, r.m], h.1 < p ∧ h.2 < p

section Rows
variable (rows : ℕ → RowVSX)

/-- The walk's label column: `(state, row)`. -/
def lblOf (i : ℕ) : StateX × RowVSX := ((rows i).st, rows i)

/-- The walk's fanout column. -/
def foOf (i : ℕ) : ℕ := fanS (rows i).st

/-- The committed child labels: child `l` (`1`-indexed) of row `i` is its `(l−1)`-th `kidsX` triple. -/
def clabOf (i l : ℕ) : StateX × RowVSX := (.s0, childRow ((kidsX (rows i)).getD (l - 1) trip0))

theorem foOf_le (i : ℕ) : foOf rows i ≤ 3 := fanS_le _

/-- **The commit relation holds of every row by construction.** -/
theorem fv_commit {K : Type} [Field K] (i : ℕ) :
    FV (K := K) (lblOf rows i)
      (fun j : Fin 3 => if (j : ℕ) < foOf rows i then some (clabOf rows i (j + 1)) else none) := by
  refine ⟨rfl, fun j => ⟨?_, ?_⟩⟩
  · by_cases h : (j : ℕ) < fanS (rows i).st <;> simp [lblOf, foOf, h]
  · intro c hc
    simp only [foOf] at hc
    by_cases hj : (j : ℕ) < fanS (rows i).st
    · simp only [hj, if_true, Option.some.injEq] at hc
      subst hc
      simp [enc, clabOf, lblOf]
    · simp [hj] at hc

end Rows

end Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
