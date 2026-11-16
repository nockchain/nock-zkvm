import Nock.V1J8.FillAtom
import Nock.V1J8.GenAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs

/-!

`walkGen`'s dummy is irrelevant on a non-empty read list; the exec atom walk at `padN` is the honest walk
at `regroup`; `regV D` is the record with regrouped atom reads, and all size/membership data transfer. -/

set_option autoImplicit false
open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd

theorem foldl_roots_ne_nil (rs : List (Noun × ℕ)) : ∀ acc : List Noun, acc ≠ [] →
    rs.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) acc ≠ [] := by
  induction rs with
  | nil => intro acc h; exact h
  | cons x rs ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    split_ifs
    · exact h
    · simp

theorem groupReads_ne_nil {rs : List (Noun × ℕ)} (h : rs ≠ []) : Nock.V1J8.Gen.groupReads rs ≠ [] := by
  obtain ⟨x, rs, rfl⟩ := List.exists_cons_of_ne_nil h
  unfold Nock.V1J8.Gen.groupReads
  simp only [ne_eq, List.map_eq_nil_iff]
  rw [List.foldl_cons]
  apply foldl_roots_ne_nil
  simp

theorem walkGen_dummy (d d' : Noun) {rs : List (Noun × ℕ)} (h : rs ≠ []) :
    Nock.V1J8.Gen.walkGen d rs = Nock.V1J8.Gen.walkGen d' rs := by
  have hg : (Nock.V1J8.Gen.groupReads rs).isEmpty = false := by
    simpa [List.isEmpty_iff] using groupReads_ne_nil h
  simp only [Nock.V1J8.Gen.walkGen, hg]
  rfl

theorem walkGen_padN_eq_map (cells : List Noun) (rs : List (Noun × ℕ)) (h : rs ≠ [])
    (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) (hwalk : ComplJ8Walk.WalkDepthOK rs) :
    (Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN rs).1 = (walkRows cells (regroup rs)).map wrowOf ∧
      (Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN rs).2 = krW cells (regroup rs) := by
  rw [walkGen_dummy Nock.V1J8.Gen.padN (cells.headD (.atom 0)) h]
  exact walkGen_eq_map cells rs hall hwalk

theorem walkGen_snd_ne_zero (d : Noun) {rs : List (Noun × ℕ)} (h : rs ≠ []) :
    (Nock.V1J8.Gen.walkGen d rs).2 ≠ 0 := by
  have hg : (Nock.V1J8.Gen.groupReads rs).isEmpty = false := by
    simpa [List.isEmpty_iff] using groupReads_ne_nil h
  have hne := groupReads_ne_nil h
  simp only [Nock.V1J8.Gen.walkGen, hg]
  simpa using hne

theorem regroup_eq_nil_iff {rs : List (Noun × ℕ)} : regroup rs = [] ↔ rs = [] := by
  constructor
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have := (mem_regroup rs x).mpr hx
    rw [h] at this
    simp at this
  · rintro rfl
    simp [regroup, rootsR]

section Reg
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The record with regrouped atom reads. -/
abbrev regV (D : J8Data p Rg fuel s f r) : J8Data p Rg fuel s f r := { D with preads := regroup D.preads }

theorem regV_acs (D : J8Data p Rg fuel s f r) : (regV D).acs = D.acs := rfl
theorem regV_rows (D : J8Data p Rg fuel s f r) : (regV D).rows = D.rows := rfl
theorem regV_H (D : J8Data p Rg fuel s f r) : (regV D).H = D.H := rfl
theorem regV_cells (D : J8Data p Rg fuel s f r) : (regV D).cells = D.cells := rfl
theorem regV_vs (D : J8Data p Rg fuel s f r) : (regV D).vs = D.vs := rfl
theorem regV_krV (D : J8Data p Rg fuel s f r) : (regV D).krV = D.krV := rfl
theorem regV_mxA (D : J8Data p Rg fuel s f r) : (regV D).mxA = D.mxA := rfl
theorem regV_mhA (D : J8Data p Rg fuel s f r) : (regV D).mhA = D.mhA := rfl

theorem walkRows_regV_perm (D : J8Data p Rg fuel s f r) (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true) :
    (walkRows (regV D).acs (regV D).preads).Perm (walkRows D.acs D.preads) :=
  walkRows_regroup_perm D.acs D.preads hall

theorem nVOf_regV (D : J8Data p Rg fuel s f r) (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true) :
    nVOf (regV D) = nVOf D := by
  unfold nVOf
  by_cases h : D.preads = []
  · have h' : (regV D).preads = [] := regroup_eq_nil_iff.mpr h
    rw [if_pos h', if_pos h]
  · have h' : (regV D).preads ≠ [] := fun e => h (regroup_eq_nil_iff.mp e)
    rw [if_neg h', if_neg h]
    exact (walkRows_regV_perm D hall).length_eq

theorem krVOf_regV (D : J8Data p Rg fuel s f r) (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true) :
    krVOf (regV D) = krVOf D := by
  unfold krVOf
  by_cases h : D.preads = []
  · have h' : (regV D).preads = [] := regroup_eq_nil_iff.mpr h
    rw [if_pos h', if_pos h]
  · have h' : (regV D).preads ≠ [] := fun e => h (regroup_eq_nil_iff.mp e)
    rw [if_neg h', if_neg h]
    exact krW_regroup D.acs D.preads hall

theorem sizesJ8_regV (D : J8Data p Rg fuel s f r) (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true) :
    sizesJ8 (regV D) = sizesJ8 D := by
  unfold sizesJ8
  rw [nVOf_regV D hall]

theorem walkDepthOK_regV (D : J8Data p Rg fuel s f r) (h : ComplJ8Walk.WalkDepthOK D.preads) :
    ComplJ8Walk.WalkDepthOK (regV D).preads :=
  walkDepthOK_regroup D.preads h

theorem hall_regV (D : J8Data p Rg fuel s f r) (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true) :
    ∀ x ∈ (regV D).preads, VclL.isPathAx x.2 = true :=
  fun x hx => hall x ((mem_regroup _ _).mp hx)

theorem hwA_regV (D : J8Data p Rg fuel s f r) (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true)
    (hwA : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs) :
    ∀ u ∈ walkRows (regV D).acs (regV D).preads, u.label.node ∈ (regV D).acs :=
  fun u hu => hwA u ((walkRows_regV_perm D hall).mem_iff.mp hu)

end Reg

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.foldl_roots_ne_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.groupReads_ne_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.walkGen_dummy
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.walkGen_padN_eq_map
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.walkGen_snd_ne_zero
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regroup_eq_nil_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regV_acs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regV_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regV_H
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regV_cells
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regV_vs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regV_krV
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regV_mxA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.regV_mhA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.walkRows_regV_perm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.nVOf_regV
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.krVOf_regV
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.sizesJ8_regV
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.walkDepthOK_regV
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.hall_regV
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd.hwA_regV
