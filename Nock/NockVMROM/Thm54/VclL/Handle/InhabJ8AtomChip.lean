/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8AtomChip.lean

  **The atom table of exactly ONE row, the inert pad row, accepted
  and bound by `atomChipHQL` (hence by `atomChipHQ`).**

  * `padC`: the cell part's honest `238`-column function (`CellTraceHQ.colHQ` of `InhabJ8AtomCell.padCol`, handle
    multiplicity `mh = 0`, honest `𝕂′` inverse / accumulator fills); `newR0 : ℕ → Fin 0 → F` (no list rows).
  * **`padTraceA`** = `HonestA8.atomTraceHQ … padC newPad` (`= padExt newR0 padNew` at `n = 1`, `padExt_eq`): the one-row `349`-column atom trace.
  * **`pad_atomChipHQL_sat`**, **`pad_atomChipHQL_bind`**: `atomChipHQL` accepts and binds `ofHQ padTraceA`, at
    publics that vanish on `0.. 11` (every terminal: validity `0/1`, export `2/3`, handle `4/5`, `mb` `6/7`, `mi`
    `8/9`, consume `10/11`), under the seven non-vanishing denominators of the pad row (three cell IO keys, the cell
    handle key, the atom `mb`, old-export and inc keys).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell
import Nock.NockVMROM.Thm54.VclL.Handle.AtomGenJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomChip

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomGenJ8
open Module
open scoped Polynomial

noncomputable section

section Defs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- No list rows. -/
def newR0 : ℕ → Fin 0 → F := fun _ i => i.elim0

/-- The atom columns `130.. 204` of every row: the inert pad row's (`padNew`). -/
def newPad {n : ℕ} : ℕ → Fin n → F := fun j _ => padNew j

theorem padExt_eq : padExt (newR0 (F := F)) (padNew (F := F)) = (newPad : ℕ → Fin (0 + 1) → F) := by
  funext j i
  exact padExt_last _ _ j i (by omega)


/-- The cell part's honest `238`-column function of the pad row (`mh = 0`). -/
def padC (γ ρ z : Quad (algebraMap F K δF)) : ℕ → Fin n → F :=
  CellTraceHQ.colHQ δF b (padCol δF b γ ρ z) (fun _ => 0)
    (CellTraceHQ.ivF δF b hn nodes orbit chals pubs (padCol δF b γ ρ z) (fun _ => 0))
    (CellTraceHQ.avF δF b hn nodes orbit chals pubs (padCol δF b γ ρ z) (fun _ => 0))

/-- **The one-row atom trace** (`atomChipHQ` view). -/
def padTraceA (γ ρ z : Quad (algebraMap F K δF)) :=
  HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs (padC δF b hn nodes orbit chals pubs γ ρ z)
    (newPad (F := F))

/-- **The one-row atom trace** read at `atomChipHQL` (same `349` columns). -/
def padTraceL (γ ρ z : Quad (algebraMap F K δF)) :=
  ofHQ δF b hn nodes orbit chals pubs (padTraceA δF b hn nodes orbit chals pubs γ ρ z)

end Defs

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h : ℕ} (hn : 0 < 1)
  (nodes : Fin 1 → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem padC_cell (γ ρ z : Quad (algebraMap F K δF)) :
    padC δF b hn nodes orbit chals pubs γ ρ z Cell.wL (lastI (n0 := 0)) = 0 ∧
    padC δF b hn nodes orbit chals pubs γ ρ z Cell.wR (lastI (n0 := 0)) = 0 ∧
    padC δF b hn nodes orbit chals pubs γ ρ z Cell.aL (lastI (n0 := 0)) = 0 ∧
    padC δF b hn nodes orbit chals pubs γ ρ z Cell.aR (lastI (n0 := 0)) = 1 := by
  simp [padC, CellTraceHQ.colHQ, extColF, padCol, cellCol, CellVals.base, padVals, cellFill, cellFillInv,
    padRow, Cell.wL, Cell.wR, Cell.aL, Cell.aR]

/-- **`pad_atomChipHQL_sat`**: `atomChipHQL` accepts the one-row pad trace. -/
theorem pad_atomChipHQL_sat (γ ρ z : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (padRow δF z)) ≠ 0)
    (hx0 : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) 0) ≠ 0)
    (hx1 : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) 1) ≠ 0)
    (hpole : ∀ i, CellTraceHQ.dRow δF b hn nodes orbit chals pubs (padCol δF b γ ρ z) (fun _ => 0) i ≠ 0)
    (hz1 : ∀ i, HonestA8.dMB δF b hn nodes orbit chals pubs (padC δF b hn nodes orbit chals pubs γ ρ z)
      (newPad (F := F)) i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δF b hn nodes orbit chals pubs (padC δF b hn nodes orbit chals pubs γ ρ z)
      (newPad (F := F)) i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δF b hn nodes orbit chals pubs (padC δF b hn nodes orbit chals pubs γ ρ z)
      (newPad (F := F)) i ≠ 0)
    (hpub : ∀ j < 12, pubs j = 0) :
    (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies
      (padTraceL δF b hn nodes orbit chals pubs γ ρ z) := by
  have hcell := (pad_cellChipHQ_sat δF b hn nodes orbit chals pubs γ ρ z hok hzc hz hv hx0 hx1 hpole
    (hpub 0 (by omega)) (hpub 1 (by omega)) (hpub 2 (by omega)) (hpub 3 (by omega))
    (hpub 4 (by decide)) (hpub 5 (by decide))).1
  have hq : ∀ k, k + 1 < 12 → Quad.mk (algebraMap F K δF) (pubs k) (pubs (k + 1)) = 0 := by
    intro k hk
    rw [hpub k (by omega), hpub (k + 1) hk, Quad.mk_zero']
  have e := padExt_eq (F := F)
  rw [← e] at hz1 hz2 hz3
  unfold padTraceL padTraceA
  rw [← e]
  refine atomChipHQL_accepts_honest_pad δF b hn nodes orbit chals pubs
    (padC δF b hn nodes orbit chals pubs γ ρ z) (newR0 (F := F)) (inj1 nodes) (adj1 nodes orbit) hcell
    (padC_cell δF b hn nodes orbit chals pubs γ ρ z) (fun i hi => absurd hi (by omega)) hz1 hz2 hz3 ?_ ?_ ?_
  · rw [hq pubMB (by decide)]; simp
  · rw [hq pubC (by decide)]; simp
  · rw [hq pubMI (by decide)]; simp

/-- **`pad_atomChipHQL_bind`**: the one-row pad trace carries the fixed preprocessing (no hypothesis). -/
theorem pad_atomChipHQL_bind (γ ρ z : Quad (algebraMap F K δF)) :
    (atomChipHQL δF b hn nodes orbit chals pubs).BindsPreprocessing
      (padTraceL δF b hn nodes orbit chals pubs γ ρ z) := by
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by norm_num)
  · exact honestQ_one hn nodes _ (by norm_num)

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomChip
