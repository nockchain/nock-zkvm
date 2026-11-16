import Nock.RedTeam.Batch1956Thm54VclCompletenessToy
import Nock.NockVMROM.Thm54.VCL38.GenNockCompilesVCL

/-! A concrete toy instance of the VCL38 `nockCompiles` capstone over the Goldilocks field `ZMod Nock.Field.p`. It supplies the run, tree-shape, leaf and axis bounds for the toy program and states the resulting capstone term without explicit binders. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1770

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
open Nock.VCL38.Nock.NockVMROM.Thm54.TraceGen.VCL38
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

def b1770_open :=
  nockCompiles_zmod (p := Nock.Field.p) (K := Kc) hrun_toy hbound_zmod
    (by simpa [ZMod.ringChar_zmod_n] using hs_toy) (by simpa [ZMod.ringChar_zmod_n] using hf_toy)
    hK3_toy (by simpa [ZMod.ringChar_zmod_n] using goldilocks_hq)

theorem runTree_any (δF : Fp) [Fact (¬ IsSquare (algebraMap Fp Kc δF))]
    (hb : RunBoundedBy (ringChar Fp) 1 s0 f0) :
    VclL.Compute.TowerD.runTree (K := Kc) δF hrun_toy hb = Batch1259.T0 := Batch1259.romTree0 _

theorem leaf_any (δF : Fp) [Fact (¬ IsSquare (algebraMap Fp Kc δF))] :
    programLeafBound (airReorder (Batch1259.T0 (K := T0Tower.Quad (algebraMap Fp Kc δF)))) ≤ 2 ^ 110 := by
  rw [Batch1259.leaf0]; norm_num

theorem axis_any (δF : Fp) [Fact (¬ IsSquare (algebraMap Fp Kc δF))] :
    VclL.Compute.programAxisBound (airReorder (Batch1259.T0 (K := T0Tower.Quad (algebraMap Fp Kc δF)))) < 2 ^ 63 := by
  rw [axis_T0]; norm_num

theorem hq_zmod : 2 ^ 63 < Nock.Field.p := by
  simpa [ZMod.ringChar_zmod_n] using goldilocks_hq

def b1770_nockCompiles_zmod_toy :=
  haveI : Fact (¬ IsSquare (algebraMap (ZMod Nock.Field.p) Kc (δc (hqz hq_zmod)))) :=
    ⟨δc_nonsquare (hqz hq_zmod) hK3_toy⟩
  b1770_open
    (by rw [hCg, hTg, hPg, runTree_any, nRows_T0, cellLen_T0 (K := Kc), pathLen_T0 (K := Kc)]
        simpa [heightOf] using goldilocks_orbit_dvd (h := 1) (by norm_num))
    (by rw [runTree_any, nRows_T0]; have := hq_zmod; omega)
    (by rw [runTree_any, cellLen_T0 (K := Kc)]; have := hq_zmod; omega)
    (by rw [runTree_any, pathLen_T0 (K := Kc)]; have := hq_zmod; omega)
    (by rw [runTree_any]; exact leaf_any _)
    (by rw [runTree_any]; exact axis_any _)

end

end Nock.RedTeam.Batch1770
