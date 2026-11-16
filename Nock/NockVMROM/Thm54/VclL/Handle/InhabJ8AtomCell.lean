/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8AtomCell.lean

  **The cell part of the atom table's ONE inert pad row.**

  The pad row of `AtomGenJ8` is the cell `[0 1]`: `wL = wR = 0`, `(aL, aR) = (0, 1)`, `idx = 0`, `lo = 1`
  (`= loL + loR + 1`), `hi = 0`, rank bit `0` set, every multiplicity `mv = mx = mx1 = mh = 0`, the fingerprints
  `l = atomFP z 0`, `r = atomFP z 1`, `p = cons z l r`.

  * `padRow` / `padVals`: the row and its honest fill (`cellFill`) on `Fin 1`.
  * `pad_baseFacts`, `pad_mixedFacts`: the `123` base gates' and the `22` `𝕂′` equations' facts at the row,
    under three non-vanishing denominators (`vKeyOf`, `xKeyOf · 0`, `xKeyOf · 1`) and `z ≠ 0`, with the two
    cell terminals (`pubs 0/1`, `pubs 2/3`) equal to `0`.
  * **`pad_cellChipHQ_sat`**: `cellChipHQ` accepts (with preprocessing) the honest one-row `𝕂′` cell twin trace
    `cellTraceHQ … (cellCol padVals) 0` (multiplicity `mh = 0`), under the extra handle denominator
    `CellTraceHQ.dRow ≠ 0` and `pubs 4 = pubs 5 = 0`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTwinQ
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemAccept
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemFill

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

noncomputable section

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "Q" => Quad (algebraMap F K δF)

/-- **The pad cell `[0 1]`** as a cell row (inverses / accumulators `0`: `cellFill` overwrites them). -/
def padRow (z : Q) : CellVals F Q where
  idx := 0
  idL := 0
  idR := 0
  wL := 0
  wR := 0
  aL := 0
  aR := 1
  lo := 1
  hi := 0
  loL := 0
  hiL := 0
  loR := 0
  hiR := 0
  carry := 0
  mv := 0
  mx := 0
  mx1 := 0
  bit := fun k => if k = 0 then 1 else 0
  p := ComputeTable.FP.cons z (ComputeTable.FP.atomFP z (liftQ δF 0)) (ComputeTable.FP.atomFP z (liftQ δF 1))
  l := ComputeTable.FP.atomFP z (liftQ δF 0)
  r := ComputeTable.FP.atomFP z (liftQ δF 1)
  vInv := 0
  lInv := 0
  rInv := 0
  x0Inv := 0
  x1Inv := 0
  vAcc := 0
  xAcc := 0

/-- The honest filled pad row on the one-row table. -/
def padVals {n : ℕ} (γ ρ z : Q) : Fin n → CellVals F Q := fun j => cellFill δF γ ρ (fun _ => padRow δF z) j

theorem pad_baseFacts0 (z : Q) (i : Fin 1) : CellBaseFacts (fun _ : Fin 1 => padRow δF z) i := by
  refine ⟨fun _ => rfl, fun hi => absurd hi (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [padRow]
  · intro k hk; split_ifs <;> simp_all

theorem pad_baseFacts (γ ρ z : Q) (i : Fin 1) : CellBaseFacts (padVals δF γ ρ z) i :=
  cellBaseFacts_fill δF γ ρ (fun _ => padRow δF z) i (pad_baseFacts0 δF z i)

theorem pad_vTerm (γ ρ z : Q) : vTermOf δF (cellFillInv δF γ ρ (padRow δF z)) = 0 := by
  simp [vTermOf, cellFillInv, padRow, liftQ]

theorem pad_xTerm (γ ρ z : Q) : xTermOf δF (cellFillInv δF γ ρ (padRow δF z)) = 0 := by
  simp [xTermOf, cellFillInv, padRow, liftQ]

theorem pad_mixedFacts (pubs : ℕ → K) (γ ρ z : Q) (hz : z ≠ 0)
    (hv : FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (padRow δF z)) ≠ 0)
    (hx0 : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) 0) ≠ 0)
    (hx1 : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) 1) ≠ 0)
    (hp0 : pubs 0 = 0) (hp1 : pubs 1 = 0) (hp2 : pubs 2 = 0) (hp3 : pubs 3 = 0) (i : Fin 1) :
    CellMixedFacts δF pubs γ ρ z (padVals δF γ ρ z) i := by
  refine cellFill_facts γ ρ (fun _ => padRow δF z) z pubs i hz (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ => hv) (fun _ _ h => absurd rfl h) (fun _ _ h => absurd rfl h)
    (fun _ _ => hx0) (fun _ _ => hx1) ?_ ?_
  · rw [Finset.sum_range_one, pad_vTerm, hp0, hp1, Quad.mk_zero']
  · rw [Finset.sum_range_one, pad_xTerm, hp2, hp3, Quad.mk_zero']

end Row

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h : ℕ} (hn : 0 < 1)
  (nodes : Fin 1 → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem inj1 : Function.Injective nodes := fun a c _ => Subsingleton.elim a c

theorem adj1 : ∀ (i : Fin 1) (hi : (i : ℕ) + 1 < 1), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω :=
  fun i hi => absurd hi (by omega)

/-- The cell part's column function (`cellCol` of the filled pad row). -/
def padCol {n : ℕ} (γ ρ z : Quad (algebraMap F K δF)) : ℕ → Fin n → F := cellCol δF b (padVals δF γ ρ z)

/-- **The one-row `ok`-gated cell chip accepts the pad row.** -/
theorem pad_cellOk (γ ρ z : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (padRow δF z)) ≠ 0)
    (hx0 : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) 0) ≠ 0)
    (hx1 : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) 1) ≠ 0)
    (hp0 : pubs 0 = 0) (hp1 : pubs 1 = 0) (hp2 : pubs 2 = 0) (hp3 : pubs 3 = 0) :
    RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (padCol δF b γ ρ z) 225
        (Fin.cast (cellChipOk_w δF b hn nodes orbit chals pubs true) j)) :=
  cellOk_sat δF b hn nodes orbit chals pubs (padVals δF γ ρ z) (inj1 nodes) (adj1 nodes orbit) γ ρ z hok hzc
    (pad_baseFacts δF γ ρ z) (pad_mixedFacts δF pubs γ ρ z hz hv hx0 hx1 hp0 hp1 hp2 hp3)

/-- **`pad_cellChipHQ_sat`**: the `𝕂′` cell twin `cellChipHQ` accepts (with preprocessing) the honest one-row
trace of the pad cell `[0 1]` at handle multiplicity `mh = 0`. -/
theorem pad_cellChipHQ_sat (γ ρ z : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (padRow δF z)) ≠ 0)
    (hx0 : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) 0) ≠ 0)
    (hx1 : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) 1) ≠ 0)
    (hpole : ∀ i, CellTraceHQ.dRow δF b hn nodes orbit chals pubs (padCol δF b γ ρ z) (fun _ => 0) i ≠ 0)
    (hp0 : pubs 0 = 0) (hp1 : pubs 1 = 0) (hp2 : pubs 2 = 0) (hp3 : pubs 3 = 0)
    (hp4 : pubs CellHQ.pubHQ = 0) (hp5 : pubs (CellHQ.pubHQ + 1) = 0) :
    RAP.SatisfiesWithPreprocessing (cellChipHQ δF b hn nodes orbit chals pubs)
      (fun j => CellTraceHQ.cellTraceHQ δF b hn nodes orbit chals pubs (padCol δF b γ ρ z) (fun _ => 0)
        (Fin.cast (cellChipHQ_width δF b hn nodes orbit chals pubs) j)) := by
  refine cellTwinQ_accepted δF b hn nodes orbit chals pubs _ _ (inj1 nodes) (adj1 nodes orbit)
    (pad_cellOk δF b hn nodes orbit chals pubs γ ρ z hok hzc hz hv hx0 hx1 hp0 hp1 hp2 hp3) hpole ?_
  rw [hp4, hp5, Quad.mk_zero', Finset.sum_range_one]
  simp [CellTraceH.mN, liftQ]

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell
