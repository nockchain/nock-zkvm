/-
  Nock/NockVMROM/Thm54/VclL/Handle/DenRecH.lean

  Additive.

  * `den_cellRec`: for the compute chip's `den (cellRec p l r)` at the honest values, the denominator is
    `recDen ρ γ (p.v, (l.k, l.v), (r.k, r.v))` (the cell twin's export-key denominator, `HonestMh.recDen`);
  * `recDenP`, `den_walkRec`: the walk-record denominator `ρ + idx + γ axis + γ² k + γ³ v`;
  * `den_cellRec_entry`: at the columns of an honest row `colVal cells r _ _`, the export entry's
    denominator is `recDen ρ γ (entryRec cells x)` when the entry's parent is a cell (always, for a
    semantically valid row: `exportEntries_cell`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkGatesH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestMh

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH

noncomputable section

section Den
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The compute chip's denominator of a record, as `ρ + rlc_γ`. -/
theorem den_eval (eK : Env K) (eF : Env F) (r : List ℕ) :
    evalMQ (den (F := ℚ) r) eK eF =
      eK.chal chalRhoL + rlcL (eK.chal chalGammaL) 0 (r.map fun i => algebraMap F K (eF.trace i)) := by
  unfold den
  simp only [evalMQ]
  rw [evalMQ_rlcKey .traceCur chalGammaL eK eF (fun i => eF.trace i) (fun i => rfl)]

/-- **A cell record's denominator is the export key's `recDen`.** -/
theorem den_cellRec (eK : Env K) (eF : Env F) (p l r : Hd) :
    evalMQ (den (F := ℚ) (cellRec p l r)) eK eF =
      recDen (eK.chal chalRhoL) (eK.chal chalGammaL)
        (eF.trace p.v, (eF.trace l.k, eF.trace l.v), (eF.trace r.k, eF.trace r.v)) := by
  rw [den_eval]
  simp [cellRec, rlcL, recDen]
  ring

/-- The walk-record denominator `ρ + idx + γ axis + γ² k + γ³ v` of `(idx, axis, (k, v))`. -/
def recDenP (ρ γ : K) (k : F × F × (F × F)) : K :=
  ρ + algebraMap F K k.1 + γ * algebraMap F K k.2.1 + γ ^ 2 * algebraMap F K k.2.2.1 +
    γ ^ 3 * algebraMap F K k.2.2.2

theorem den_walkRec (eK : Env K) (eF : Env F) (root : Hd) (axis : ℕ) (ch : Hd) :
    evalMQ (den (F := ℚ) (walkRec root axis ch)) eK eF =
      recDenP (eK.chal chalRhoL) (eK.chal chalGammaL)
        (eF.trace root.v, eF.trace axis, (eF.trace ch.k, eF.trace ch.v)) := by
  rw [den_eval]
  simp [walkRec, rlcL, recDenP]
  ring

end Den

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- At the columns of an honest row, an export entry whose parent is a cell has the denominator of its
consumed record, when the entry's three nouns are the row's handle nouns in the chip's slot order. -/
theorem recDen_entry (cells : List Noun) (ρ γ : K) (x : Noun × Noun × Noun) (hc : x.1.isCell = true) :
    recDen ρ γ (entryRec (F := F) cells x) =
      recDen ρ γ ((hdl (F := F) cells x.1).2, hdl (F := F) cells x.2.1, hdl (F := F) cells x.2.2) := by
  obtain ⟨p, l, r⟩ := x
  obtain ⟨a, b, rfl⟩ : ∃ a b, p = Noun.cell a b := by
    cases p with
    | atom _ => simp [Noun.isCell] at hc
    | cell a b => exact ⟨a, b, rfl⟩
  simp [entryRec, hdl]

end Row

end

end Nock.NockVMROM.Thm54.VclL.Handle
