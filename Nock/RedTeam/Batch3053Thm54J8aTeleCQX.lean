/-
  Nock/RedTeam/Batch3053Thm54J8aTeleCQX.lean

  The compute half of the J-8 handle-class balances on `computeChipVCLHX`:
  * `slotGateQX_val_spec`, the row facts `act_bool` / `act_pairwise` / `pairF_bool` / `pairF_act`
    (one-hot row, base gates; the pair flags `pr`, `pr2` exclusive with their slots' entries);
  * `termQX_row`: a row's `𝕂′` term into balance `b` = `Σ (D r)⁻¹` over `consQX b`;
  * `accX_rows`: the accumulator telescope at the masks `17 / 18`;
  * `compute_balanceX`: on an accepted trace, `Σ_rows Σ_{consQX b} (D r)⁻¹ = (Re ρ_b, Im ρ_b)` for
    `b ∈ {x, p, s}` (publics `15/21`, `18/24`, `27/30`), pair denominators nonzero;
  * `consQX_activeX`: the summed records are `activeX` filtered by balance.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX

namespace Nock.RedTeam.Batch3053

open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX

#print axioms slotsX_cast
#print axioms slotGateQX_val_spec
#print axioms act_bool
#print axioms act_pairwise
#print axioms pairF_bool
#print axioms pairF_act
#print axioms termQX_row
#print axioms accX_rows
#print axioms termQX_eq
#print axioms compute_balanceX
#print axioms consQX_activeX

end Nock.RedTeam.Batch3053
