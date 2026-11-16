/-
  Nock/RedTeam/Batch2010Thm54Capstone39Toy.lean

  Zero explicit binders. Then
  `optimizedFullStrictNockVMROM_of_package` (`«Thm:NockVMROM»`) at the chosen package. Axioms: see the `#print axioms` lines below. -/

import Nock.RedTeam.Batch1997Thm54WalkW4dToys
import Nock.RedTeam.Batch1956Thm54VclCompletenessToy
import Nock.NockVMROM.Thm54.Walk39.GenNockCompilesVCL

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch2010

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
open Nock.Walk39.Nock.NockVMROM.Thm54.TraceGen.VCL38
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.VclL.Compute
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.RedTeam.Batch1956 Nock.RedTeam.Batch1955 Nock.RedTeam.Batch1938
open Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen

noncomputable section

local notation "Fp" => Nock.Field.Fp
local notation "Kc" => Nock.Field.K

local instance charRingKc : CharP Kc (ringChar Kc) := ringChar.charP Kc

abbrev s0 : Noun := Batch1259.subj0
abbrev f0 : Noun := Batch1259.form0

theorem hbound_zmod : RunBoundedBy Nock.Field.p 1 s0 f0 := by
  have := hbound_toy; rwa [ZMod.ringChar_zmod_n] at this

/-- The 38th `nockCompiles_zmod` at the toy run (the six `∀` premises still open). -/
def b2010_open :=
  nockCompiles_zmod (p := Nock.Field.p) (K := Kc) hrun_toy hbound_zmod
    (by simpa [ZMod.ringChar_zmod_n] using hs_toy) (by simpa [ZMod.ringChar_zmod_n] using hf_toy)
    hK3_toy (by simpa [ZMod.ringChar_zmod_n] using goldilocks_hq)

theorem runTree_any (δF : Fp) [Fact (¬ IsSquare (algebraMap Fp Kc δF))]
    (hb : RunBoundedBy (ringChar Fp) 1 s0 f0) :
    VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hb = Batch1259.T0 := Batch1259.romTree0 _

/-- **The 38th capstone statement at the toy run, zero explicit binders**: the compiler's package at
`*[0 [1 0]] = 0` over Goldilocks satisfies `OptimizedFullStrictThm54Statement` and carries the claim. -/
theorem leaf_any (δF : Fp) [Fact (¬ IsSquare (algebraMap Fp Kc δF))] :
    programLeafBound (airReorder (Batch1259.T0 (K := T0Tower.Quad (algebraMap Fp Kc δF)))) ≤ 2 ^ 110 := by
  rw [Batch1259.leaf0]; norm_num

theorem axis_any (δF : Fp) [Fact (¬ IsSquare (algebraMap Fp Kc δF))] :
    VclL.Compute.programAxisBound (airReorder (Batch1259.T0 (K := T0Tower.Quad (algebraMap Fp Kc δF)))) < 2 ^ 63 := by
  rw [axis_T0]; norm_num

theorem hq_zmod : 2 ^ 63 < Nock.Field.p := by
  simpa [ZMod.ringChar_zmod_n] using goldilocks_hq

theorem hmemW_any (δF : Fp) [Fact (¬ IsSquare (algebraMap Fp Kc δF))] :
    krW (demT (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod)).cells
        (demT (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod)).preads +
      (walkRows (demT (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod)).cells
        (demT (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod)).preads).length < Nock.Field.p := by
  have h1 := krW_le_rows (demT (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod)).cells
    (demT (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod)).preads
  have h2 : (walkRows (demT (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod)).cells
      (demT (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod)).preads).length ≤
      pathLen (K := Kc) δF (VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hbound_zmod) :=
    Batch1979.walkLen_le_pathLen δF (romTree_spec _)
  erw [runTree_any] at h1 h2 ⊢
  rw [Batch1955.pathLen_T0] at h2
  have := hq_zmod
  omega

def b2010_nockCompiles_zmod_toy :=
  haveI : Fact (¬ IsSquare (algebraMap (ZMod Nock.Field.p) Kc (δc (hqz hq_zmod)))) :=
    ⟨δc_nonsquare (hqz hq_zmod) hK3_toy⟩
  b2010_open
    (by rw [hCg, hTg, hPg, runTree_any, nRows_T0, cellLen_T0 (K := Kc), pathLen_T0 (K := Kc)]
        simpa [heightOf] using goldilocks_orbit_dvd (h := 1) (by norm_num))
    (by rw [runTree_any, nRows_T0]; have := hq_zmod; omega)
    (by rw [runTree_any, cellLen_T0 (K := Kc)]; have := hq_zmod; omega)
    (by exact hmemW_any _)
    (by rw [runTree_any]; exact leaf_any _)
    (by rw [runTree_any]; exact axis_any _)

/-- **`«Thm:NockVMROM»` (the live capstone) at the compiler's package for the quote run, zero explicit
binders**: the package chosen by the live `nockCompiles_zmod` satisfies the live
`OptimizedFullStrictThm54Statement` by the capstone theorem itself. -/
theorem b2010_capstone_toy :
    Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (Classical.choose b2010_nockCompiles_zmod_toy) :=
  Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package _

end

end Nock.RedTeam.Batch2010

#print axioms Nock.RedTeam.Batch2010.b2010_nockCompiles_zmod_toy
#print axioms Nock.RedTeam.Batch2010.b2010_capstone_toy
