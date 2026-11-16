/-
  Nock/RedTeam/Batch2045Thm54VSMemProviders.lean

  1. **Widths** (`rfl` / `decide`): cell twin `cellChipH` `232` (`225 + mh + 2 𝕂`-roles), walk twin
     `walkChipH` `151` (`132 + 4` handle columns `+ 5 𝕂`-roles).
  2. **Restriction**: a twin-accepted trace restricted to the original's columns is accepted by the
     original chip (`cellChipH_restrict_sat`, `walkChipH_restrict_sat`, generic
     `expandChip_restrict`), so the existing chip theorems apply unchanged.  Positive controls: the
     read-set instrument flags a read of the first twin column / role (`colsBelow`, `mixBelow`).
  3. **Genuineness**: `exportH_genuine` (cell), `walkH_records_genuine` (walk, outside the SAME
     `walkEvent`), `claimH_genuine` / `claim_handles_denote` (validity-key claim record).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkH
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimH

set_option autoImplicit false

namespace Nock.RedTeam.Batch2045

open Nock Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle

/-! ## Positive controls of the read-set instrument (it does see the twin's new columns) -/

theorem pc_colsBelow_flags_mh : colsBelow 129 (.var .traceCur 129 : CoeffExpr ℚ) = false := by decide
theorem pc_colsBelow_flags_next : colsBelow 21 (.var .traceNext 21 : CoeffExpr ℚ) = false := by decide
theorem pc_colsBelow_flags_coin : colsBelow 129 (.var .challenge 0 : CoeffExpr ℚ) = false := by decide
theorem pc_mixBelow_flags_invH :
    mixBelow 32 129 (.Var .traceCur 32 : MixedExpr ℚ) = false := by decide
theorem pc_mixBelow_flags_lift :
    mixBelow 37 21 (.Lift (.var .traceCur 21) : MixedExpr ℚ) = false := by decide
/-- …and passes the original's last column / role. -/
theorem pc_below_passes :
    colsBelow 129 (.var .traceCur 128 : CoeffExpr ℚ) = true ∧
      mixBelow 32 129 (.Var .traceNext 31 : MixedExpr ℚ) = true := by decide

/-! ## The new gate counts -/

theorem cellH_gates_length : (CellH.gates (F := ℚ)).length = 4 := rfl
theorem walkH_gates_length : (WalkHC.gates (F := ℚ)).length = 9 := rfl

#print axioms cellChipH_width
#print axioms walkChipH_width
#print axioms cellChipH_s
#print axioms expandChip_restrict
#print axioms cellChipH_restrict_sat
#print axioms walkChipH_restrict_sat
#print axioms keyH_eval
#print axioms exportH_genuine
#print axioms enc_inj_decoded_or_atom
#print axioms walkH_of_reconGoal
#print axioms walkH_records_genuine
#print axioms claim_census_inj
#print axioms claimH_genuine
#print axioms claim_handles_denote
#print axioms pc_below_passes

end Nock.RedTeam.Batch2045
