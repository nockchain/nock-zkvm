/-
  Nock/RedTeam/Batch1714Thm54VclLAxColumn.lean

  **The round-0
  axis column `ax`.**

  Production: `Thm54/VclL/Compute/AxGate.lean`.  Column `221` (round 0, `colRoundVCL_ax`); gate
  `s0·(f_t.leaf − ax) + s9·(f_th.leaf − ax) = 0` as three coordinate gates of degree 2
  (`axGates`, `axGates_degree`); `f_t.leaf` / `f_th.leaf` are the deployed decoder's `𝕂`-roles 41 / 44
  (`decodeDec_ft_leaf` / `decodeDec_fth_leaf`, `rfl`).
  * (i) coin-free honest `ax`: `honestAx` (a function of the skeleton row's `state` and `formula`),
    `honest_axGates` (the gate holds at the honest row at EVERY seed `z`; `enc_atom_leaf`);
  * (ii) `axGate_ax0` / `axGate_ax9`: on a row where the gates vanish, `natLift ax = n` whenever the
    decoded `f_t.leaf` (resp. `f_th.leaf`) is `(n : K)`, `n < ringChar F` — `Batch1171.RowFacts.ax0/ax9`'s
    clause at `ax (S + 2/3) := natLift ax`; `natLift_lt` gives its `< q` half;
  * (iii) `nc_ax_gate_dropped`: `vclGates_not_ax` (column 221 is read by no gate of `computeChipVCL`,
    through the bounded support facts `keptGates309_colsIn309`), so overwriting `ax` keeps every
    `vclGates` gate at zero and the decoded leaf fixed while the served axis becomes `n + 1 ≠ n`;
    the real gate rejects that row.
  Repaired chip `computeChipVCLA` (`vclRAPA_fingerprint`: `(e, w, s, d, k) = (3, 222, 312, 4, 2)`,
  `wRAP = ![208, 14]`), `computeChipVCLA_sat_iff`; B0 path key `path_key_clause` at
  `KeyVCLA = (ℕ × Bool) ⊕ (ℕ × ℕ)` (`colRoundVCLA_zero_iff`: B0 = `0..12`, `202..207`, `220`, `221`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.AxGate
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1714

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms colRoundVCL_ax
#print axioms axGates_degree
#print axioms decodeDec_ft_leaf
#print axioms decodeDec_fth_leaf
#print axioms honest_axGates
#print axioms honestAx_s0
#print axioms honestAx_s9
#print axioms axGate_ax0
#print axioms axGate_ax9
#print axioms natLift_lt
#print axioms vclGates_not_ax
#print axioms vclGates_set_ax
#print axioms nc_ax_gate_dropped
#print axioms vclRAPA_fingerprint
#print axioms computeChipVCLA_sat_iff
#print axioms colRoundVCLA_zero_iff
#print axioms path_key_clause

end Nock.RedTeam.Batch1714
