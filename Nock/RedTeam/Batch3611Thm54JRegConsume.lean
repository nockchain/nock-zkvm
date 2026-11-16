/-
  Nock/RedTeam/Batch3611Thm54JRegConsume.lean

  * `hReg_of_served` (`claimK_genuine_cell`), `jetProvOK_R`, the weighted `jetProvOKW`, `jProvW_sum`;
  * the toy: `toy_gatesR`, `toy_reg_cell`, `toyCall_weighted`.
-/
import Nock.Jet.ChipJ8RToy

namespace Nock.RedTeam.Batch3611

open Nock.Jet.ChipJ8 Nock.Jet.RegJ8R

/-- The registry row is selected by the new base gate and by the new consume slot. -/
theorem reg_row_read :
    (regKindGate : Nock.NockVMROM.Thm54.CoordinateCompiler.CoeffExpr ℚ) =
      .mul (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv (Kd.sel .reg))
        (.sub (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv Col.kN) (.const 1)) ∧
    Kd.sel .reg = 0 := ⟨rfl, rfl⟩

#print axioms jetTemplateJ8R_width
#print axioms gatesJR_degree
#print axioms baseGatesJR_deg
#print axioms gatesJR_keyOK
#print axioms baseGatesJR_serialFree
#print axioms keyOKJR_flags
#print axioms jetRapJ8R_restrict_sat
#print axioms kN_of_regKind
#print axioms hReg_of_served
#print axioms jetProvOK_R
#print axioms sum_filter_weighted
#print axioms jetProvOKW
#print axioms jProvW_sum
#print axioms toy_gatesR
#print axioms toy_reg_cell
#print axioms toyCall_weighted

end Nock.RedTeam.Batch3611
