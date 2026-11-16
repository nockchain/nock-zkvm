/-
  Nock/RedTeam/Batch4774Thm54NVJetFinal.lean
  **A kernel-checked non-vacuity witness of the J-8 verifier predicate that uses a jet.**  `checkJ8_iff` (with `RegOK`, proved here as `ijet_regOK`) turns it
  into `AcceptsJ8V`; `HoldsN` of the claim is a kernel `evalN` computation.
-/
import Nock.RedTeam.Batch4772Thm54NVJetParts
import Nock.RedTeam.Batch4773Thm54NVJetC
import Nock.V1J8.GenJet

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.RedTeam.Batch4771 Nock.V1J8.Gen

namespace Nock.RedTeam.Batch4774

open Nock.RedTeam.Batch4772 Nock.RedTeam.Batch4773

theorem ijet_check : checkJ8 Ijet = true := by
  unfold checkJ8
  rw [dif_pos ijet_valid]
  simp only [Bool.and_eq_true]
  refine ⟨⟨ijet_static, ijet_pub⟩, ?_⟩
  unfold chipsB
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨ijet_X, ijet_C⟩, ijet_W⟩, ijet_J⟩, ijet_A⟩, ijet_AW⟩, ijet_AL⟩

/-- The registry of the input. -/
abbrev RgJ : Nock.Jet.Registry := regOf (fun _ => Nock.RedTeam.Batch4771.tinyT) [7]

theorem ijet_regOK : RegOK Ijet RgJ := by
  intro i hi
  have h7 : i = 7 := by simpa [Ijet, Qregs] using hi
  subst h7
  refine ⟨by simp [RgJ, regOf, Ijet, Qregs], ?_⟩
  exact Nock.Jet.Autogen.HasTy.add (Nock.Jet.Autogen.HasTy.var ⟨0, by decide⟩) (Nock.Jet.Autogen.HasTy.var ⟨1, by decide⟩)

theorem tinyT_wt : (Nock.RedTeam.Batch4771.tinyT).WellTyped Nock.Field.p :=
  Nock.Jet.Autogen.HasTy.add (Nock.Jet.Autogen.HasTy.var ⟨0, by decide⟩) (Nock.Jet.Autogen.HasTy.var ⟨1, by decide⟩)

/-- **The registry is faithful** (every entry is a compiled well-typed template: J-2 `compile_jetSpec_faithful`),
the premise `hRg` of `probJ8V_final`. -/
theorem rgJ_faithful : RgJ.Faithful := by
  intro n j h
  unfold RgJ regOf at h
  split_ifs at h
  cases h
  exact Nock.Jet.Autogen.compile_jetSpec_faithful (by decide +kernel) _ tinyT_wt

theorem ijet_holdsN : Nock.Jet.HoldsN Ijet.c := ⟨1000, by decide +kernel⟩

theorem ijet_nJ : 0 < (Ijet.J).n := by decide +kernel

/-- **The jetted non-vacuity witness**: the honest input is valid, accepted by `AcceptsJ8V` at Goldilocks (the
verifier data, coins, message, traces, rows and budget all built from the input), the J chip is present
(`0 < Pb.nJ`, the registry is `[7]`), and the claim is true (`HoldsN`). -/
theorem nvJet_goldilocks : ∃ hv : ValidJ8 Ijet,
    Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb Ijet hv) RgJ Ijet.c (toχ Ijet.χ) Ijet.M.toMsg (mkTr Ijet)
      Ijet.r Ijet.g ∧ 0 < (mkPb Ijet hv).nJ ∧ (mkPb Ijet hv).regs = [7] ∧ Nock.Jet.HoldsN Ijet.c ∧ RgJ.Faithful := by
  haveI : Fact (ringChar (ZMod Nock.Field.p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
  haveI hcp : CharP KC (ringChar (ZMod Nock.Field.p)) := by
    rw [ZMod.ringChar_zmod_n]; exact charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective _
  letI : Algebra (ZMod (ringChar (ZMod Nock.Field.p))) KC := ZMod.algebra KC _
  obtain ⟨hv, h⟩ := (checkJ8_iff Ijet RgJ ijet_regOK).mp ijet_check
  exact ⟨hv, h, ijet_nJ, rfl, ijet_holdsN, rgJ_faithful⟩

end Nock.RedTeam.Batch4774

#print axioms Nock.RedTeam.Batch4774.ijet_check
#print axioms Nock.RedTeam.Batch4774.nvJet_goldilocks
