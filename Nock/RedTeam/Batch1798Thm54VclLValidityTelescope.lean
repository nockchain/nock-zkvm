/-
  Nock/RedTeam/Batch1798Thm54VclLValidityTelescope.lean

  **The validity accumulator ⇒ weighted IO facts ⇒
  `ValidityServed`.**  Production: `Thm54/VclL/Chips/Telescope.lean`.

  * `den_ev_compress`: the chip denominator `ρ′ + RLC′(es)` is `FiniteIO.compress ⟨γ′, ρ′⟩` of the
    key vector when the challenge vector satisfies `ChalsOK` (ρ′ at leaves 5/7, γ′^i at 11+2i/12+2i);
    `chalsVCL` is a challenge vector at frame coins that satisfies it (`chalsVCL_ok`); the γ′-power
    leaves are disjoint from the coin leaves (`gpow_slots_disjoint`).
  * `cell_validity_telescope`, `cell_validity_sum`, `cellValidityFacts`: the frame's `IOFacts` at
    `m = 5` (providers `(vKeyP, mv)`, internal = weighted child keys).
  * `cell_validityServed`, `cellTable_accepts_of_lookup`: `ValidityServed` / `TableAccepts` with no
    `ValidityServed` premise (from `finiteIO_lookup_sound_weighted` over `reqs ++ internal`).
  * NC `telescope_needs_init`: step + terminal without the init gate do not give the sum.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.Telescope
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1798

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

/-- **NC**: without the init gate the telescope fails (`n = 1`, `acc 0 = 1`, `term 0 = 0`, `ρ = 1`). -/
theorem telescope_needs_init :
    ∃ (acc term : ℕ → ℤ) (ρ : ℤ), (∀ i, i + 1 < 1 → acc (i + 1) = acc i + term (i + 1)) ∧
      acc (1 - 1) = ρ ∧ ¬ (∑ i ∈ Finset.range 1, term i = ρ) :=
  ⟨fun _ => 1, fun _ => 0, 1, fun i hi => absurd hi (by omega), rfl, by simp⟩

#print axioms telescope
#print axioms den_ev_compress
#print axioms chalsVCL_ok
#print axioms gpow_slots_disjoint
#print axioms cell_validity_telescope
#print axioms cell_validity_sum
#print axioms cellValidityFacts
#print axioms cell_validityServed
#print axioms cellTable_accepts_of_lookup
#print axioms telescope_needs_init

end Nock.RedTeam.Batch1798
