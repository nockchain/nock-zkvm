/-
  Nock/RedTeam/Batch1997Thm54WalkW4dToys.lean

  **The walk family's completeness at two concrete programs, NO
  hypotheses** (twins of `Batch1956.vcl_completeness_toy` and `Batch1963.vcl_completeness_toy_axis1`).

  Neither demand has a path-kind read, so the walk table is the one dummy row
  (`krW + |walkRows| ≤ 2`, via `walkLen_le_pathLen` and `pathLen = 1`).
-/
import Nock.RedTeam.Batch1996Thm54WalkW4dCompletenessChosen
import Nock.RedTeam.Batch1956Thm54VclCompletenessToy
import Nock.RedTeam.Batch1963Thm54VclCompletenessToyAxis1

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1997

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.RedTeam.Batch1259 (subj0 form0 T0)
open Nock.RedTeam.Batch1938 Nock.RedTeam.Batch1955
open Nock.RedTeam.Batch1956 (instFactSevenNS δ7 hK3_toy h1_32 hrun_toy hbound_toy runTree_toy hsize_toy
  hrowsC_toy hsizeT_toy hsizeP_toy hleaf_toy hmemC_toy haxis_toy)

noncomputable section

local notation "Fp" => Nock.Field.Fp
local notation "Kc" => Nock.Field.K

instance instFactRCFp : Fact (ringChar Fp).Prime := Batch1996.fact_ringChar_zmod Nock.Field.p

noncomputable instance instAlgRCFp : Algebra (ZMod (ringChar Fp)) Kc := Batch1996.algRC Nock.Field.p Kc

/-! ## 1. `*[0 [1 0]]` -/

theorem hmemW_toy :
    krW (demT (runTree (K := Kc) δ7 hrun_toy hbound_toy)).cells (demT (runTree (K := Kc) δ7 hrun_toy hbound_toy)).preads +
      (walkRows (demT (runTree (K := Kc) δ7 hrun_toy hbound_toy)).cells
        (demT (runTree (K := Kc) δ7 hrun_toy hbound_toy)).preads).length < ringChar Fp := by
  have h1 := krW_le_rows (demT (runTree (K := Kc) δ7 hrun_toy hbound_toy)).cells
    (demT (runTree (K := Kc) δ7 hrun_toy hbound_toy)).preads
  have h2 : (walkRows (demT (runTree (K := Kc) δ7 hrun_toy hbound_toy)).cells
      (demT (runTree (K := Kc) δ7 hrun_toy hbound_toy)).preads).length ≤
      pathLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_toy hbound_toy) :=
    Batch1979.walkLen_le_pathLen δ7 (romTree_spec _)
  rw [runTree_toy] at h1 h2 ⊢
  rw [Batch1955.pathLen_T0] at h2
  have := goldilocks_hq
  omega

/-- The honest compute–walk datum of the quote run. -/
def HJtoy : HonestVCLJW (K := Kc) δ7 1 1 1 :=
  honestVCLJW_of_run δ7 1 1 1 hrun_toy hbound_toy 0 0 hK3_toy goldilocks_hp le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32)
    hsize_toy hrowsC_toy hsizeT_toy hsizeP_toy

theorem hmemRowsW_toy : ∀ k, HJtoy.V.memRows k + 1 < ringChar Fp :=
  memRowsW_of_run δ7 1 1 1 hrun_toy hbound_toy 0 hK3_toy le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) hmemC_toy hmemW_toy

theorem hkpW_toy : krT δ7 HJtoy.t + HJtoy.V.memRows (tWW 1 1) < ringChar Fp :=
  kpW_of_run δ7 1 1 1 hrun_toy hbound_toy 0 hK3_toy le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) hmemW_toy

open Classical in
/-- **Walk-family completeness at `*[0 [1 0]]`, NO hypotheses.** -/
theorem vcl_completenessW_toy :
    HJtoy.V.claim = ⟨subj0, form0, .atom 0⟩ ∧ HJtoy.t = T0 ∧
    ((Finset.univ.filter fun χ : Coins frameVCL Kc =>
        ∃ s ∈ (CFvW4 (K := Kc) δ7 1 1 1).honestBad HJtoy.toHonestVCLT ++
            (MFvW4 (K := Kc) δ7 1 1 1 (krT δ7 HJtoy.t)).honestBad
              (jointMemW HJtoy (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_toy
                hmemRowsW_toy haxis_toy hkpW_toy),
          s.mem ((CFvW4 (K := Kc) δ7 1 1 1).honestQ HJtoy.toHonestVCLT χ,
            (MFvW4 (K := Kc) δ7 1 1 1 (krT δ7 HJtoy.t)).honestQ
              (jointMemW HJtoy (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_toy
                hmemRowsW_toy haxis_toy hkpW_toy) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL Kc) ≤
      epsilonOf ((CFvW4 (K := Kc) δ7 1 1 1).honestBad HJtoy.toHonestVCLT ++
        (MFvW4 (K := Kc) δ7 1 1 1 (krT δ7 HJtoy.t)).honestBad
          (jointMemW HJtoy (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_toy
            hmemRowsW_toy haxis_toy hkpW_toy)) := by
  have h1 := Batch1995.vcl_completenessW_of_run (K := Kc) δ7 1 1 1 hrun_toy hbound_toy 0 0
    (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hK3_toy goldilocks_hp le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32)
    hsize_toy hrowsC_toy hsizeT_toy hsizeP_toy hleaf_toy hmemC_toy hmemW_toy haxis_toy
  exact ⟨h1.1, h1.2.1.trans runTree_toy, h1.2.2⟩

/-! ## 2. `*[0 [0 1]]` (the axis-1 read) -/

open Nock.RedTeam.Batch1963 (subjA formA TA hrun_A hbound_A runTree_A hsize_A hrowsC_A hsizeT_A hsizeP_A
  hleaf_A hmemC_A haxis_A pathLen_A)

theorem hmemW_A :
    krW (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).cells (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).preads +
      (walkRows (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).cells
        (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).preads).length < ringChar Fp := by
  have h1 := krW_le_rows (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).cells
    (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).preads
  have h2 : (walkRows (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).cells
      (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).preads).length ≤
      pathLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_A hbound_A) :=
    Batch1979.walkLen_le_pathLen δ7 (romTree_spec _)
  rw [runTree_A] at h1 h2 ⊢
  rw [pathLen_A] at h2
  have := goldilocks_hq
  omega

/-- The honest compute–walk datum of the axis-1 run. -/
def HJA : HonestVCLJW (K := Kc) δ7 1 1 1 :=
  honestVCLJW_of_run δ7 1 1 1 hrun_A hbound_A 0 0 hK3_toy goldilocks_hp le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32)
    hsize_A hrowsC_A hsizeT_A hsizeP_A

theorem hmemRowsW_A : ∀ k, HJA.V.memRows k + 1 < ringChar Fp :=
  memRowsW_of_run δ7 1 1 1 hrun_A hbound_A 0 hK3_toy le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) hmemC_A hmemW_A

theorem hkpW_A : krT δ7 HJA.t + HJA.V.memRows (tWW 1 1) < ringChar Fp :=
  kpW_of_run δ7 1 1 1 hrun_A hbound_A 0 hK3_toy le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) hmemW_A

open Classical in
/-- **Walk-family completeness at `*[0 [0 1]]`, NO hypotheses.** -/
theorem vcl_completenessW_toy_axis1 :
    HJA.V.claim = ⟨subjA, formA, .atom 0⟩ ∧ HJA.t = TA ∧
    ((Finset.univ.filter fun χ : Coins frameVCL Kc =>
        ∃ s ∈ (CFvW4 (K := Kc) δ7 1 1 1).honestBad HJA.toHonestVCLT ++
            (MFvW4 (K := Kc) δ7 1 1 1 (krT δ7 HJA.t)).honestBad
              (jointMemW HJA (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_A
                hmemRowsW_A haxis_A hkpW_A),
          s.mem ((CFvW4 (K := Kc) δ7 1 1 1).honestQ HJA.toHonestVCLT χ,
            (MFvW4 (K := Kc) δ7 1 1 1 (krT δ7 HJA.t)).honestQ
              (jointMemW HJA (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_A
                hmemRowsW_A haxis_A hkpW_A) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL Kc) ≤
      epsilonOf ((CFvW4 (K := Kc) δ7 1 1 1).honestBad HJA.toHonestVCLT ++
        (MFvW4 (K := Kc) δ7 1 1 1 (krT δ7 HJA.t)).honestBad
          (jointMemW HJA (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_A
            hmemRowsW_A haxis_A hkpW_A)) := by
  have h1 := Batch1995.vcl_completenessW_of_run (K := Kc) δ7 1 1 1 hrun_A hbound_A 0 0
    (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hK3_toy goldilocks_hp le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32)
    hsize_A hrowsC_A hsizeT_A hsizeP_A hleaf_A hmemC_A hmemW_A haxis_A
  exact ⟨h1.1, h1.2.1.trans runTree_A, h1.2.2⟩

end

end Nock.RedTeam.Batch1997

#print axioms Nock.RedTeam.Batch1997.vcl_completenessW_toy
#print axioms Nock.RedTeam.Batch1997.vcl_completenessW_toy_axis1
#print axioms Nock.RedTeam.Batch1997.hmemW_toy
#print axioms Nock.RedTeam.Batch1997.hmemW_A
