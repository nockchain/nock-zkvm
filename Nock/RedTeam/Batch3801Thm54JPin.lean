/-
  Nock/RedTeam/Batch3801Thm54JPin.lean

  * the pin: `pinKey` / `pinCons` (J tagged balance), the claim keys in the cell validity external
    list (`regClaims_provided`); `pin_forces` (`(kN, vN) = (1, idx id)`, needs `regs` nodup);
    `hReg_of_pin` (through `hReg_of_served` at `vN = idx id`);
  * the provider direction of the weighted LogUp: `consumed_of_fibre`, `sum_effP`, and the negative
    control `fibre_cancel` (a weight-`≠ 0` provider need not be consumed: the obligation is on
    EFFECTIVE providers, not `m ≠ 0`);
  * `jetProvOKE`, `hSubE_of_service`, the one-event `bal_of_serviceE` / `pin_servedE`, and the
    assembly `jetProvOK_pin`;
  * the budgets `weightJ8Pin` (`+#regs` on summands #2 and #6), the figure `figJ8Pin_155`, tight
    `figJ8Pin_not_156`.
-/
import Nock.Jet.SubJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8

namespace Nock.RedTeam.Batch3801

open Nock.Jet.PinJ8 Nock.Jet.FibreJ8 Nock.Jet.SubJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8

instance fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The pin key is the `provK` form of a `.reg` row at handle `(1, idx)`, tag `2` first. -/
theorem pinKey_eq (id idx : ℕ) :
    (pinKey id idx : List (ZMod 7)) = [((2 : ℕ) : ZMod 7), (id : ZMod 7), 1, (idx : ZMod 7)] := rfl

#print axioms inchip_served
#print axioms pin_served
#print axioms reg_filterMap
#print axioms reg_unique
#print axioms pin_forces
#print axioms hReg_of_pin
#print axioms claimVec_inj
#print axioms claims_served2
#print axioms regClaims_provided
#print axioms fibreW_effP
#print axioms fibreW_map
#print axioms sum_effP
#print axioms consumed_of_fibre
#print axioms served_effective
#print axioms fibre_cancel
#print axioms liftS_effE
#print axioms balance_effE
#print axioms jetProvOKE
#print axioms hSubE_of_service
#print axioms inchip_servedE
#print axioms bal_of_serviceE
#print axioms pin_servedE
#print axioms jetProvOK_pin
#print axioms weightJ8Pin_zero
#print axioms weightJ8P_le_pin
#print axioms eps_validity_pin
#print axioms eps_service_pin
#print axioms boundJ8Pin_eq
#print axioms figJ8Pin_155
#print axioms figJ8Pin_not_156

end Nock.RedTeam.Batch3801
