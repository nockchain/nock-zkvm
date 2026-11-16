/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestMh.lean

  Additive.

  * `mhH`: the honest multiplicity column of `cellChipH` (column 129): at the row of closure noun `n`,
    the number of consumed export records equal to the key of `n` (the honest consume count).
  * `exportEntries_H`: the OP3 hosting changes no export entry (`rowOfSkelH` vs `rowOfSkel`).
  * `export_total_link`: with the LogUp weight `1 / (ρ + RLC_γ(record))` the compute side's consumed total
    equals the cell twin's `mh`-weighted provided total, over the extended-demand table.

  NOT done here (UNCONFIRMED, remaining): `cellChipH` acceptance at the honest table (a cell-chip trace
  generator with the `mh`, `32/33` columns) and the per-row identification of the accumulator `termVal`
  with the sum of `1/den` over `exportEntries` (a slot-by-slot case analysis on the active states).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRowsH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.SemanticStrategy ComputeTable

noncomputable section

section Mh
variable {K F : Type} [Field K] [Field F]

theorem exportEntries_H (sk : ComputeRowSkeleton) :
    exportEntries (rowOfSkelH sk) = exportEntries (rowOfSkel sk) := by
  by_cases h3 : (rowOfSkel sk).op = 3
  · simp [rowOfSkelH, h3, exportEntries]
  · rw [rowOfSkelH_of_ne _ h3]

/-- **The consumed export records of all rows** (the VS honest compute side). -/
def consumedH (rows : List (GenComputeRow K)) : List (F × (F × F) × (F × F)) :=
  rows.flatMap fun g => (exportEntries (rowOfSkelH g.skel)).map (entryRec (demandH rows).cells)

/-- **The honest `mh` column** of `cellChipH` at the row of closure noun `n`. -/
def mhH [DecidableEq F] (rows : List (GenComputeRow K)) (n : Noun) : ℕ :=
  (consumedH (F := F) rows).count (expKey (demandH rows).cells n)

/-- The RLC of an export record at the coins `(ρ, γ)` (`ChipH.cellRec` order, powers `0..4`), in an
extension `L` of the base field. -/
def recDen {L : Type} [Field L] [Algebra F L] (ρ γ : L) (k : F × (F × F) × (F × F)) : L :=
  ρ + algebraMap F L k.1 + γ * algebraMap F L k.2.1.1 + γ ^ 2 * algebraMap F L k.2.1.2 +
    γ ^ 3 * algebraMap F L k.2.2.1 + γ ^ 4 * algebraMap F L k.2.2.2

/-- **The export total link.**  For any weight, in particular `1 / recDen`: the compute side's consumed
total equals the cell twin's `mh`-weighted provided total (`mhH` as the multiplicity). -/
theorem export_total_link {M : Type} [AddCommMonoid M] [DecidableEq F]
    (rows : List (GenComputeRow K))
    (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem)
    (hlen : (demandH rows).cells.length < ringChar F) (f : F × (F × F) × (F × F) → M) :
    ((consumedH (F := F) rows).map f).sum =
      ((demandH rows).cells.map fun n =>
        (mhH (F := F) rows n) • f (expKey (demandH rows).cells n)).sum := by
  have := export_balance (F := F) rows hsem hlen f
  simp only [consumedH, mhH, exportEntries_H]
  exact this

theorem export_total_link_inv {L : Type} [Field L] [Algebra F L] [DecidableEq F]
    (rows : List (GenComputeRow K)) (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem)
    (hlen : (demandH rows).cells.length < ringChar F) (ρ γ : L) :
    ((consumedH (F := F) rows).map fun k => (recDen ρ γ k)⁻¹).sum =
      ((demandH rows).cells.map fun n =>
        (mhH (F := F) rows n : L) * (recDen ρ γ (expKey (F := F) (demandH rows).cells n))⁻¹).sum := by
  rw [export_total_link rows hsem hlen (fun k => (recDen ρ γ k)⁻¹)]
  simp [nsmul_eq_mul]

end Mh

end

end Nock.NockVMROM.Thm54.VclL.Handle
