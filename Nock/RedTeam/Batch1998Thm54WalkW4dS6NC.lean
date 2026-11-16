/-
  Nock/RedTeam/Batch1998Thm54WalkW4dS6NC.lean

  `ZMod 67` stands for the `𝕂′` values
  `compress(record)` (all non-zero).

  * **S6-1, export consume dropped → forged walk accepted.**  The export accumulator balances the cell
    table's provides (`mx · inv`) against the walk rows' consumes and the compute side's lookups
    (`ExportTelescopeW.walk_export_telescope`, `cellExportFactsW`).  One cell with key value `2`, no compute
    lookup, one walk row consuming key value `3` (NOT a cell key, so `KeysExported` fails):
    WITH the consume term the balance `mx·2⁻¹ − 3⁻¹ = 0` has no solution in `mx` that is a count of
    walk rows ≤ 1 (`mx = 0` gives `−3⁻¹ ≠ 0`, `mx = 1` gives `2⁻¹ − 3⁻¹ ≠ 0`) — rejected; the honest walk
    (key `2`, `mx = 1`) balances.  WITHOUT it, the forger sets `mx = 0` and the balance `0 = 0` holds with
    the walk row's key `3` absent from the cell table — accepted.
  * **S6-2, multiplicity phantoms.**  The walk's path-provide multiplicities `mL`, `mR` are prover-chosen.
    A phantom (`mR = 1` on a record value `7` no compute read requests) is REJECTED by the path
    terminal pin `Σ m·inv = ρ₂ = Σ_{deep reads} inv` (`1·5⁻¹ + 1·7⁻¹ ≠ 5⁻¹`), the honest walk (`mL = 1` on
    the requested record `5`, `mR = 0`) balances, and with the pin dropped (`ρ₂` free) the phantom is
    accepted.  A phantom that cancels needs a negative multiplicity on a DISTINCT record, which the
    balance also rejects (`5⁻¹ + 7⁻¹ − 9⁻¹ ≠ 5⁻¹`).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Nock.RedTeam.Batch1998

instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-- The export balance of one cell row (`mx` consumers of key `c`) and one walk row consuming key `w`,
with (`consume = true`) or without the walk's consume term; no compute lookup. -/
def exportBalance (consume : Bool) (mx c w : ZMod 67) : ZMod 67 :=
  mx * c⁻¹ - (if consume then w⁻¹ else 0)

/-- **S6-1: the export consume is load-bearing.** -/
theorem nc_export_consume_dropped :
    -- honest walk (consumes the cell's key `2`, `mx = 1`): balanced
    exportBalance true 1 2 2 = 0 ∧
    -- forged walk (consumes key `3`, no cell has it): rejected at every `mx ∈ {0, 1}`
    exportBalance true 0 2 3 ≠ 0 ∧ exportBalance true 1 2 3 ≠ 0 ∧
    -- consume dropped: the forger's `mx = 0` balances, though the walk key is no cell key
    exportBalance false 0 2 3 = 0 ∧ (3 : ZMod 67) ∉ ({2} : Finset (ZMod 67)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩

/-- The path-provide total of a walk row with multiplicities `mL`, `mR` on records `rL`, `rR`. -/
def provideRow (mL mR rL rR : ZMod 67) : ZMod 67 := mL * rL⁻¹ + mR * rR⁻¹

/-- **S6-2: multiplicity phantoms are rejected by the path terminal, and only by it.** -/
theorem nc_multiplicity_phantom :
    -- the compute side requests the one deep read whose record value is `5`
    -- honest: `mL = 1` on `5`, `mR = 0`: balanced against `ρ₂ = 5⁻¹`
    provideRow 1 0 5 7 = (5 : ZMod 67)⁻¹ ∧
    -- phantom: `mR = 1` on the unrequested record `7`: rejected by the pin
    provideRow 1 1 5 7 ≠ (5 : ZMod 67)⁻¹ ∧
    -- cancelling phantom on distinct records (`+1` on `7`, `−1` on `9`): rejected
    provideRow 1 1 5 7 + provideRow 0 (-1) 5 9 ≠ (5 : ZMod 67)⁻¹ ∧
    -- pin dropped (`ρ₂` free): the phantom's total is some `ρ₂`, accepted
    ∃ ρ₂ : ZMod 67, provideRow 1 1 5 7 = ρ₂ := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨_, rfl⟩⟩

end Nock.RedTeam.Batch1998

#print axioms Nock.RedTeam.Batch1998.nc_export_consume_dropped
#print axioms Nock.RedTeam.Batch1998.nc_multiplicity_phantom
