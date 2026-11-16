/-
  **The atom-walk witness (`Ine`, op 5 on `p` vs `p+1`, `krootsV = 2`) inside `probJ8V_final`'s regime**: from
  `ine_check` via `checkJ8_iff`, restated at `r := EncInjJ8.cornerC` by `acceptsJ8V_mono_rows` with `0 < Pb.krootsV`, the
  empty registry, the claim true, every numeric binder of `probJ8V_final_clean`; then the conclusion of
  `probJ8V_final_clean` at the constant trace map, with `hQ` and the `CharP` instances discharged.
-/
import Nock.RedTeam.Batch4778Thm54NVEq5
import Nock.RedTeam.Batch4777Thm54NVJetConst

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch4779

open Nock.NockVMROM.Thm54.SVFrame Nock.V1J8.Exe Nock.V1J8.Check Nock Nock.TraceGenExe Nock.RedTeam.Batch4771 Nock.RedTeam.Batch4774 Nock.RedTeam.Batch4775 Nock.RedTeam.Batch4776 Nock.RedTeam.Batch4777 Nock.RedTeam.Batch4778 Nock.V1J8
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe corner31)
open Nock.Atoms (lenL)
open Nock.V1J8.Gen (regOf)

/-- The (empty) registry of `Ine`. -/
abbrev RgE : Nock.Jet.Registry := regOf Ine.Rt []

theorem ine_regOK : RegOK Ine RgE := by
  intro i hi
  simp [Ine] at hi

theorem rgE_faithful : RgE.Faithful := by
  intro n j h
  simp [RgE, regOf] at h

theorem ine_holdsN : Nock.Jet.HoldsN Ine.c := ⟨1000, by decide +kernel⟩

theorem ine_krootsV : 0 < Ine.krootsV := by decide

/-- The input `Ine` lies in the intended regime: it is valid, `AcceptsJ8V` holds for it, and the field, registry and claim side conditions hold. -/
theorem eq5_in_regime : ∃ hv : ValidJ8 Ine,
    Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb Ine hv) RgE Ine.c
      (toχ Ine.χ) Ine.M.toMsg (mkTr Ine) EncInjJ8.cornerC Ine.g ∧
    0 < (mkPb Ine hv).krootsV ∧ Nock.Jet.HoldsN Ine.c ∧ RgE.Faithful ∧
    Fintype.card KC = Nock.NockVMROM.Thm54.VclL.Events.cK ∧ Nock.Field.p = Nock.Atoms.p ∧
    RowsLe EncInjJ8.cornerC EncInjJ8.cornerC ∧
    (∀ x < ringChar (ZMod Nock.Field.p), lenL x ≤ EncInjJ8.cornerC.maxlen) ∧
    2 * fuelChip ≤ EncInjJ8.cornerC.leaves ∧
    (mkPb Ine hv).nA + 2 ≤ EncInjJ8.cornerC.maxlen ∧ Ine.g ≤ 2 ^ 31 ∧
    (mkPb Ine hv).n ≤ EncInjJ8.cornerC.N ∧ (mkPb Ine hv).nC ≤ EncInjJ8.cornerC.D ∧
    (mkPb Ine hv).nW ≤ EncInjJ8.cornerC.W ∧ (mkPb Ine hv).nA ≤ EncInjJ8.cornerC.A ∧
    (mkPb Ine hv).nV ≤ EncInjJ8.cornerC.AW ∧ (mkPb Ine hv).nC ≤ 2 ^ 31 ∧
    (censusG (mkPb Ine hv) Ine.c).length ≤ 2 ^ 31 := by
  haveI : Fact (ringChar (ZMod Nock.Field.p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
  haveI hcp : CharP KC (ringChar (ZMod Nock.Field.p)) := by
    rw [ZMod.ringChar_zmod_n]; exact charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective _
  letI : Algebra (ZMod (ringChar (ZMod Nock.Field.p))) KC := ZMod.algebra KC _
  obtain ⟨hv, hA⟩ := (checkJ8_iff Ine RgE ine_regOK).mp ine_check
  have hrc : ringChar (ZMod Nock.Field.p) = Nock.Field.p := ZMod.ringChar_zmod_n _
  have hpG : Nock.Field.p = Nock.Atoms.p := rfl
  refine ⟨hv, ?_, ?_, ine_holdsN, rgE_faithful, by rw [Nock.TraceGenExe.KC_card, Nock.NockVMROM.Thm54.VclL.Events.cK_eq], hpG, ?_, ?_,
    le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine acceptsJ8V_mono_rows deltaF powerBasis3 hA ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (first | decide +kernel | (unfold EncInjJ8.cornerC corner31; decide +kernel))
  · show 0 < Ine.krootsV
    exact ine_krootsV
  · simp [RowsLe]
  · intro x hx
    rw [hrc] at hx
    unfold lenL
    rw [if_pos hx]
    show 1 ≤ 2 ^ 31
    norm_num
  all_goals ((try simp only [mkPb, censusG]); first | decide +kernel | (unfold EncInjJ8.cornerC corner31; decide +kernel))

open Classical in
/-- **`probJ8V_final_clean`'s conclusion for the atom-walk witness at the constant trace map** (`hQ`, `CharP`s discharged). -/
theorem eq5_final_const :
    ∃ hv : ValidJ8 Ine,
      Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb Ine hv) RgE Ine.c
        (toχ Ine.χ) Ine.M.toMsg (mkTr Ine) EncInjJ8.cornerC Ine.g ∧ 0 < (mkPb Ine hv).krootsV ∧
      ((Finset.univ.filter fun χ : Coins frameJ8 KC =>
        (∃ M : MsgJ8' Nock.Field.p KC deltaF, Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3
          (mkPb Ine hv) RgE Ine.c χ M (mkTr Ine) EncInjJ8.cornerC Ine.g) ∧ ¬ Nock.Jet.HoldsN Ine.c).card : ℚ) /
        Fintype.card (Coins frameJ8 KC) < 1 / (2 : ℚ) ^ 155 := by
  haveI := charP_KC
  haveI := charP_Quad
  obtain ⟨hv, hA, hK, hJ, hF, hcK, hpG, hr, hqM, hk, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩ := eq5_in_regime
  exact ⟨hv, hA, hK, Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8.probJ8V_final_clean deltaF powerBasis3 (mkPb Ine hv) hF
    Ine.c (fun _ => mkTr Ine) (stJ8_const _) hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg⟩

end Nock.RedTeam.Batch4779

#print axioms Nock.RedTeam.Batch4779.rgE_faithful
#print axioms Nock.RedTeam.Batch4779.ine_holdsN
#print axioms Nock.RedTeam.Batch4779.eq5_in_regime
#print axioms Nock.RedTeam.Batch4779.eq5_final_const
