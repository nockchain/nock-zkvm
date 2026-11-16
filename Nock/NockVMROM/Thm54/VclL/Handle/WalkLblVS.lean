/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkLblVS.lean

The compute walk of `ChipH.walkGates` runs over the row label `(s, f, e)` (six base coordinates
  `ChipH.labelCols`, no state tag) and the child labels `ChipH.children` (= `LocalVS.kids`).  For
  `Walk_IOP_forest_final_card_of_label` the walk label is `(st, row) : State × RowVS`:

  * `fanS` — the fanout of a state (`(kids r).length = fanS r.st`, `kids_length`);
  * `encH` / `encT` / `enc` — a handle's two coordinates `(kind ∈ {0,1}, value)` lifted to `𝕂`, the
    six coordinates of a triple, the encoding of a walk label (its own `(s, f, e)`); the chip's
    `curL` / `childSum` are `rlc γ` of exactly these when the handle values are the `natOf` of the
    committed columns;
  * `childRow` / `clabOf` — the committed child labels of a row (only `(s, f, e)` is read);
  * `lblOf` / `foOf` — the walk's label column and fanout column of a row table `rows : ℕ → RowVS`;
  * `FV` — the commit relation: the state is the row's, exactly the first `fanS` children are present,
    and child `j` encodes the row's `j`-th `kids` triple.  It reads the children only through `enc`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LocalVS

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS

open Nock Nock.Walk
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.VclL.Handle (VHandle)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS

/-- **The fanout of a state** (the number of `kids`). -/
def fanS : State → ℕ
  | .s2 => 3
  | .s3 => 1
  | .s4 => 1
  | .s5 => 2
  | .s6 => 2
  | .s7 => 2
  | .s8 => 2
  | .s9 => 2
  | .cons => 2
  | _ => 0

theorem fanS_le (s : State) : fanS s ≤ 3 := by cases s <;> simp [fanS]

theorem kids_length (r : RowVS) : (kids r).length = fanS r.st := by
  unfold kids
  cases r.st <;> simp [fanS]

/-- A placeholder triple (never read inside `fanS`). -/
def trip0 : Trip := ((false, 0), (false, 0), (false, 0))

/-- A child row: its `(s, f, e)` is the triple, the rest junk (only `(s, f, e)` is encoded). -/
def childRow (t : Trip) : RowVS where
  st := .s0
  s := t.1
  f := t.2.1
  e := t.2.2
  sf1 := (false, 0)
  sf2 := (false, 0)
  fh := (false, 0)
  ft := (false, 0)
  fth := (false, 0)
  ftt := (false, 0)
  ftth := (false, 0)
  fttt := (false, 0)
  m := (false, 0)

@[simp] theorem childRow_trip (t : Trip) : (childRow t).trip = t := by
  simp [childRow, RowVS.trip]

section Enc
variable {K : Type} [Field K]

/-- A handle's two coordinates in `𝕂`: `(kind, value)`. -/
def encH (h : VHandle) : K × K := (if h.1 then 1 else 0, (h.2 : K))

/-- **The six coordinates of a triple** (`ChipH.labelCols`' order `s.k s.v f.k f.v e.k e.v`). -/
def encT (t : Trip) : Fin 6 → K :=
  ![(encH t.1).1, (encH t.1).2, (encH t.2.1).1, (encH t.2.1).2, (encH t.2.2).1, (encH t.2.2).2]

/-- **The encoding of a walk label**: its own `(s, f, e)`. -/
def enc (a : State × RowVS) : Fin 6 → K := encT a.2.trip

/-- **The commit relation of the compute walk**: the state is the row's, exactly the first `fanS`
children are present, and child `j` encodes the row's `j`-th `kids` triple. -/
def FV (a : State × RowVS) (xout : Fin 3 → Option (State × RowVS)) : Prop :=
  a.1 = a.2.st ∧ ∀ j : Fin 3, ((j : ℕ) < fanS a.1 ↔ xout j ≠ none) ∧
    ∀ c, xout j = some c → enc (K := K) c = encT ((kids a.2).getD j trip0)

end Enc

/-- Every handle value of a row is below `p` (decoded values are `natOf` of `𝔽` columns). -/
def SmallR (p : ℕ) (r : RowVS) : Prop :=
  r.s.2 < p ∧ r.f.2 < p ∧ r.e.2 < p ∧ r.sf1.2 < p ∧ r.sf2.2 < p ∧ r.fh.2 < p ∧ r.ft.2 < p ∧
    r.fth.2 < p ∧ r.ftt.2 < p ∧ r.ftth.2 < p ∧ r.fttt.2 < p ∧ r.m.2 < p

section Rows
variable (rows : ℕ → RowVS)

/-- The walk's label column: `(state, row)`. -/
def lblOf (i : ℕ) : State × RowVS := ((rows i).st, rows i)

/-- The walk's fanout column. -/
def foOf (i : ℕ) : ℕ := fanS (rows i).st

/-- The committed child labels: child `l` (`1`-indexed) of row `i` is its `(l−1)`-th `kids` triple. -/
def clabOf (i l : ℕ) : State × RowVS := (.s0, childRow ((kids (rows i)).getD (l - 1) trip0))

theorem foOf_le (i : ℕ) : foOf rows i ≤ 3 := fanS_le _

/-- **The commit relation holds of every row by construction.** -/
theorem fv_commit {K : Type} [Field K] (i : ℕ) :
    FV (K := K) (lblOf rows i)
      (fun j : Fin 3 => if (j : ℕ) < foOf rows i then some (clabOf rows i (j + 1)) else none) := by
  refine ⟨rfl, fun j => ⟨?_, ?_⟩⟩
  · by_cases h : (j : ℕ) < foOf rows i
    · have h' : (j : ℕ) < fanS (rows i).st := h
      simp [lblOf, foOf, h']
    · have h' : ¬ (j : ℕ) < fanS (rows i).st := h
      simp [lblOf, foOf, h']
  · intro c hc
    by_cases hj : (j : ℕ) < foOf rows i
    · beta_reduce at hc
      rw [if_pos hj] at hc
      cases hc
      simp [enc, clabOf, lblOf]
    · beta_reduce at hc
      rw [if_neg hj] at hc
      cases hc

end Rows

end Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS
