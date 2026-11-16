/-
  Nock/RedTeam/Batch1799Thm54VclLSideSlotExport.lean

  Production: `Thm54/VclL/Chips/ChipRAP.lean` (`Cell.mx1` B0 col 128, `Cell.xProvInv1`
  role 30, `Cell.xKeyS`, two provider inverse gates, `xTerm = mx·inv₀ + mx1·inv₁`; path consumes
  `(p, l, r, cellIdx, side)`), `Thm54/VclL/Chips/ExportTelescope.lean`.

  * Cell chip `(w, s, d) = (225, 255, 4)` (was `(218, 249, 4)`: `+1` B0, `+1` `𝕂′` inverse = `+7`
    columns, `+2` `𝕂`-gates); path chip unchanged `(112, 122, 4)`.
  * `cellExportFacts` (`IOFacts` at `m = 11`), `path_edges_exported` (every path row's edge is
    `EdgeExported`, no `ExportBalanced` premise), `xKey_decode` (the side slot is decoded).
  * NC: the two records of one cell differ only in the side slot (`side_records_distinct`), and
    without it (the first `10` entries) they coincide (`sideless_records_collide`) — the record
    could not name the child.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ExportTelescope
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1799

open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

section
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (eK : Env K) (eF : Env F)

theorem xKey_length : (Cell.xKey (F := F)).length = 10 := rfl

/-- The side slot separates the two records of one cell. -/
theorem side_records_distinct :
    keyVec δF 11 (Cell.xKeyS 0) eK eF ≠ keyVec δF 11 (Cell.xKeyS 1) eK eF := by
  intro h
  have := congrFun h ⟨10, by decide⟩
  have h10 : ∀ x : QE F, (Cell.xKey ++ [x]).getD 10 QE.zero = x := fun x => rfl
  simp only [keyVec, Cell.xKeyS, h10, ev_base, CoeffExpr.eval, liftQ, map_zero, map_one] at this
  exact zero_ne_one this

/-- **NC**: without the side slot the two records coincide. -/
theorem sideless_records_collide :
    keyVec δF 10 (Cell.xKeyS 0) eK eF = keyVec δF 10 (Cell.xKeyS 1) eK eF := by
  funext c
  fin_cases c <;> rfl
end

theorem cell_fingerprint_1799 {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] (δF : F)
    (b : Module.Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : Nock.NockVMROM.Thm54.StrictExtension.StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 ∧
      (cellChip δF b hn nodes orbit chals pubs).rap.s = 255 ∧
      (cellChip δF b hn nodes orbit chals pubs).rap.d = 4 :=
  ⟨(cellChip_fingerprint δF b hn nodes orbit chals pubs).1, (cellChip_fingerprint δF b hn nodes orbit chals pubs).2.1,
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).2.2.1⟩

#print axioms cell_fingerprint_1799
#print axioms cellChip_deg
#print axioms cell_export_telescope
#print axioms path_export_telescope
#print axioms cell_export_sum
#print axioms path_internal_sum
#print axioms cellExportFacts
#print axioms xKey_decode
#print axioms path_edges_exported
#print axioms side_records_distinct
#print axioms sideless_records_collide

end Nock.RedTeam.Batch1799
