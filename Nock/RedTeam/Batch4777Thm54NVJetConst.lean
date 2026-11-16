/-
  `nvJet_final_const`: the jet witness plus `probJ8V_final_clean`'s conclusion at the constant trace map
  `Q := fun _ => mkTr Ijet`, with `hQ : StJ8 Q` discharged by `stagedCols_const`.
-/
import Nock.RedTeam.Batch4776Thm54NVJetClean

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch4777

open Nock.NockVMROM.Thm54.SVFrame Nock.V1J8.Exe Nock.V1J8.Check Nock Nock.TraceGenExe Nock.RedTeam.Batch4771 Nock.RedTeam.Batch4774 Nock.RedTeam.Batch4775 Nock.RedTeam.Batch4776 Nock.V1J8
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)

/-- The constant trace map is staged. -/
theorem stJ8_const (T : TrJ8 (ZMod Nock.Field.p)) : StJ8 (fun _ : Coins frameJ8 KC => T) :=
  ⟨stagedCols_const _ _ _, stagedCols_const _ _ _, stagedCols_const _ _ _, stagedCols_const _ _ _,
    stagedCols_const _ _ _, stagedCols_const _ _ _⟩

open Classical in
/-- The field `KC` has characteristic `Nock.Field.p`. -/
theorem charP_KC : CharP KC Nock.Field.p :=
  charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective Nock.Field.p

open Classical in
/-- The quadratic extension `Quad δ` of `KC` has characteristic `Nock.Field.p`. -/
theorem charP_Quad : @CharP (Quad (algebraMap (ZMod Nock.Field.p) KC deltaF)) _ Nock.Field.p := by
  haveI := charP_KC
  exact charP_of_injective_algebraMap (algebraMap KC (Quad (algebraMap (ZMod Nock.Field.p) KC deltaF))).injective
    Nock.Field.p

open Classical in
/-- **Non-vacuity at a constant-jet claim**: the input `Ijet` is valid and `AcceptsJ8V` holds for it at the registry `RgJ`, on a nonempty set of coins (see the conjuncts below). -/
theorem nvJet_final_const :
    ∃ hv : ValidJ8 Ijet,
      Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb Ijet hv) RgJ Ijet.c
        (toχ Ijet.χ) Ijet.M.toMsg (mkTr Ijet) EncInjJ8.cornerC Ijet.g ∧
      ((Finset.univ.filter fun χ : Coins frameJ8 KC =>
        (∃ M : MsgJ8' Nock.Field.p KC deltaF, Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3
          (mkPb Ijet hv) RgJ Ijet.c χ M (mkTr Ijet) EncInjJ8.cornerC Ijet.g) ∧ ¬ Nock.Jet.HoldsN Ijet.c).card : ℚ) /
        Fintype.card (Coins frameJ8 KC) < 1 / (2 : ℚ) ^ 155 :=
  haveI := charP_KC
  haveI := charP_Quad
  nvJet_hyps_final_clean (fun _ => mkTr Ijet) (stJ8_const _)

end Nock.RedTeam.Batch4777

#print axioms Nock.RedTeam.Batch4777.stJ8_const
#print axioms Nock.RedTeam.Batch4777.charP_KC
#print axioms Nock.RedTeam.Batch4777.charP_Quad
#print axioms Nock.RedTeam.Batch4777.nvJet_final_const
