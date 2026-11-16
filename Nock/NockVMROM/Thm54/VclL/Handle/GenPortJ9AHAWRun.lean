/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAWRun.lean

With `DA := j9aDataOf P Rg Rt hgen` and `DR := regV DA`:
  * data equalities `readsJ_eq`, `vsKrVJ_eq`, `ptJ_eq`, `HAJ_eq`, `rIAJ_eq`, `acsLJ_eq`, `krV_zero_iff`;
  * present: `vs_krV_present` (`DA.vs`, `DA.krV` are the rows / roots of the regrouped record `DR`), `vRPJ_eq_awE`;
  * absent: `V_absent`, `pubsV_absent`;
  * **`genJ9AX_aw_n`** (`I.V.n = nVOf DA`), `genJ9AX_aw_n'` (`= nVOf DR`), **`genJ9AX_aw_krootsV`**,
    **`genJ9AX_aw_pubs`**, `genJ9AX_aw_pubs_orb`, `genJ9AX_aw_pubs_avOf9`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPubs
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalFA
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ADataRec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd (krW_regroup)
open Nock.V1J9A Nock.V1J9A.GenJ9AX

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRun

/-! ## 1. Data equalities (no atom-walk hypotheses) -/

section Data
variable {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t) = [])
include hnc

theorem cs_eq (χe : CoinsE) :
    csJ s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).cells :=
  (ComplJ9BClosed.genJ9A_data Rt hgen rfl hnc).2.1

theorem acsLJ_eq (χe : CoinsE) :
    acsLJ s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).acs :=
  (ComplJ9BClosed.genJ9A_data Rt hgen rfl hnc).2.2

theorem ptJ_eq (χe : CoinsE) :
    ptJ s f χe (RnOf t r) = ComplJ8Data.ptrP P (j9aDataOf P Rg Rt hgen).acs (j9aDataOf P Rg Rt hgen).rows := by
  show Nock.V1J8.Gen.ptrE (acsLJ s f χe (RnOf t r)) (Nock.V1J8.Gen.stopEdges _) = _
  rw [GenPortJ9.ptrE_eq', acsLJ_eq Rt hgen hnc χe]
  rfl

theorem HAJ_eq (χe : CoinsE) :
    HAJ s f χe (RnOf t r) = Nock.V1J8.Gen.hdl (j9aDataOf P Rg Rt hgen).acs := by
  unfold HAJ
  rw [acsLJ_eq Rt hgen hnc χe]

theorem rIAJ_eq (χe : CoinsE) :
    rIAJ s f χe (RnOf t r) = ComplJ8Data.rIAP P (j9aDataOf P Rg Rt hgen).acs := by
  unfold rIAJ
  rw [acsLJ_eq Rt hgen hnc χe]
  rfl

/-- **The exec atom-walk reads are `DA.preads`.** -/
theorem readsJ_eq (χe : CoinsE) :
    readsJ s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).preads := by
  obtain ⟨-, hcs, hacs⟩ := ComplJ9BClosed.genJ9A_data Rt hgen rfl hnc
  obtain ⟨-, -, hpd⟩ := GenPortJ9.genJ9A_pointer_data Rt hgen rfl hnc
  have hH : HJ s f χe (RnOf t r) = (ComplJ8Data.j8DataOf P Rg Rt hgen).H := by
    unfold HJ
    rw [cs_eq Rt hgen hnc χe, acsLJ_eq Rt hgen hnc χe, GenPortJ9A.hdlB_eq_hdlP]
    rfl
  have hpd' : pdJ s f χe (RnOf t r) = (ComplJ8Data.j8DataOf P Rg Rt hgen).pd := by
    unfold pdJ ptJ
    exact hpd
  rw [ComplJ9ADataRec.j9aDataOf_preads]
  unfold readsJ
  rw [hH, hpd']
  rfl

/-- **`vsKrVJ`** is `DA`'s `(vs, krV)`. -/
theorem vsKrVJ_eq (χe : CoinsE) :
    vsKrVJ s f χe (RnOf t r) = ((j9aDataOf P Rg Rt hgen).vs, (j9aDataOf P Rg Rt hgen).krV) := by
  have h := GenPortJ9A.genJ9AX_data (p := P) Rt hgen rfl hnc χe
  dsimp only at h
  have h3 : (vsKrVJ s f χe (RnOf t r)).1 = (j9aDataOf P Rg Rt hgen).vs := h.2.2.1
  have h4 : (vsKrVJ s f χe (RnOf t r)).2 = (j9aDataOf P Rg Rt hgen).krV := h.2.2.2.1
  exact Prod.ext h3 h4

/-- `vsKrVJ` on a non-empty read list is `walkGen padN`. -/
theorem vsKrVJ_ne (χe : CoinsE) (hne : (j9aDataOf P Rg Rt hgen).preads ≠ []) :
    Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN (j9aDataOf P Rg Rt hgen).preads =
      ((j9aDataOf P Rg Rt hgen).vs, (j9aDataOf P Rg Rt hgen).krV) := by
  have e := vsKrVJ_eq Rt hgen hnc χe
  unfold vsKrVJ at e
  rw [readsJ_eq Rt hgen hnc χe] at e
  have hie : (j9aDataOf P Rg Rt hgen).preads.isEmpty = false := by
    cases hh : (j9aDataOf P Rg Rt hgen).preads.isEmpty
    · rfl
    · exact absurd (List.isEmpty_iff.mp hh) hne
  simp only [hie, Bool.false_eq_true, if_false] at e
  exact e

theorem krV_zero_iff (χe : CoinsE) :
    (vsKrVJ s f χe (RnOf t r)).2 = 0 ↔ (j9aDataOf P Rg Rt hgen).preads = [] := by
  by_cases h : (j9aDataOf P Rg Rt hgen).preads = []
  · unfold vsKrVJ
    rw [readsJ_eq Rt hgen hnc χe, h]
    simp
  · refine ⟨fun hz => ?_, fun hh => absurd hh h⟩
    have e := vsKrVJ_ne Rt hgen hnc χe h
    rw [vsKrVJ_eq Rt hgen hnc χe] at hz
    have := GenPortJ9AHAWOrd.walkGen_snd_ne_zero Nock.V1J8.Gen.padN h
    rw [e] at this
    exact absurd hz this

end Data

/-! ## 2. The atom walk at the run -/

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t) = [])
  (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
  (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
include hnc hax9 hwalkA

local notation "DA" => j9aDataOf P Rg Rt hgen
local notation "DR" => regV (j9aDataOf P Rg Rt hgen)

theorem hall_DA : ∀ x ∈ (DA).preads, VclL.isPathAx x.2 = true :=
  ComplJ9ABalFA.hallA_A Rt hgen (rfl : P = Nock.Atoms.p)

theorem hwA_DA : ∀ u ∈ walkRows (DA).acs (DA).preads, u.label.node ∈ (DA).acs :=
  ComplJ9ABalFA.hwA_A Rt hgen (rfl : P = Nock.Atoms.p)

theorem hwalk_DA : ComplJ8Walk.WalkDepthOK (DA).preads :=
  ComplJ9ADataRec.walkDepthOK_preadsA Rt hgen hax9 hwalkA

theorem hwA_DR : ∀ u ∈ walkRows (DR).acs (DR).preads, u.label.node ∈ (DR).acs :=
  hwA_regV (DA) (hall_DA Rt hgen hnc hax9 hwalkA) (hwA_DA Rt hgen hnc hax9 hwalkA)

theorem hcl_DR : ∀ y ∈ (DR).acs, y.isCell = true :=
  fun y hy => ComplJ8OfBal.acs_cell Rt hgen (rfl : P = Nock.Atoms.p) y hy

theorem hsm_DR : ∀ y ∈ (DR).acs, GenPortJ9AHAtomRow.Small y := by
  intro y hy
  have hbigs : ∀ a ∈ (DA).bigs, P ≤ a := fun a ha =>
    ((ComplJ8Atom.mem_bigsP P (ComplJ8Data.j8DataOf P Rg Rt hgen).roots
      (ComplJ8Data.j8DataOf P Rg Rt hgen).rows a).mp ha).2
  exact GenPortJ9AHAtomRow.small_of_acs (DA).bigs (DA).dupP hbigs y hy

/-- **Present**: `DA.vs`, `DA.krV` are the rows / roots of the regrouped record. -/
theorem vs_krV_present (χe : CoinsE) (hne : (DA).preads ≠ []) :
    (DA).vs = ((walkRows (DR).acs (DR).preads).map GenPortJ9AHWalkBfs.wrowOf) ∧
      (DA).krV = krW (DR).acs (DR).preads := by
  have e := vsKrVJ_ne Rt hgen hnc χe hne
  obtain ⟨a, b⟩ := GenPortJ9AHAWOrd.walkGen_padN_eq_map (DA).acs (DA).preads hne
    (hall_DA Rt hgen hnc hax9 hwalkA) (hwalk_DA Rt hgen hnc hax9 hwalkA)
  rw [e] at a b
  exact ⟨a, b⟩

/-- **The exec atom-walk table (present) is `awE` at the regrouped record.** -/
theorem vRPJ_eq_awE (χe : CoinsE) (hne : (DA).preads ≠ []) :
    vRPJ s f χe (RnOf t r) = awE χe (DR) := by
  have hz : (vsKrVJ s f χe (RnOf t r)).2 ≠ 0 :=
    fun hh => hne ((krV_zero_iff Rt hgen hnc χe).mp hh)
  obtain ⟨h1, h2⟩ := vs_krV_present Rt hgen hnc hax9 hwalkA χe hne
  rw [vRPJ_of_krV_ne s f χe _ hz, ptJ_eq Rt hgen hnc χe, HAJ_eq Rt hgen hnc χe, rIAJ_eq Rt hgen hnc χe,
    acsLJ_eq Rt hgen hnc χe, vsKrVJ_eq Rt hgen hnc χe]
  show walkGenRowsBE _ _ _ _ _ _ _ _ _ (DA).vs (DA).krV = _
  rw [h1, h2]

/-- **Absent**: the table is the one-row zero chip. -/
theorem V_absent (χe : CoinsE) (h : (DA).preads = []) :
    (recJ9AX s f χe t r).V = chipOf #[Array.replicate 166 0] := by
  rw [recX_V, vRPJ_of_krV_zero s f χe _ ((krV_zero_iff Rt hgen hnc χe).mpr h)]

theorem pubsV_absent (χe : CoinsE) (h : (DA).preads = []) :
    (recJ9AX s f χe t r).M.pubsV = fun _ => 0 := by
  rw [recX_M_pubsV, vRPJ_of_krV_zero s f χe _ ((krV_zero_iff Rt hgen hnc χe).mpr h)]

/-- **`genJ9AX_aw_n'`**: the exec atom-walk chip has `nVOf DR` rows. -/
theorem genJ9AX_aw_n' (χe : CoinsE) : (recJ9AX s f χe t r).V.n = nVOf (DR) := by
  by_cases h : (DA).preads = []
  · rw [V_absent Rt hgen hnc hax9 hwalkA χe h]
    have h' : (DR).preads = [] := regroup_eq_nil_iff.mpr h
    unfold nVOf
    rw [if_pos h']
    rfl
  · have h' : (DR).preads ≠ [] := fun e => h (regroup_eq_nil_iff.mp e)
    rw [recX_V, vRPJ_eq_awE Rt hgen hnc hax9 hwalkA χe h]
    exact GenPortJ9AHAW.walkGenRowsBE_size χe (DR) h'

/-- **`genJ9AX_aw_n`**: the exec atom-walk chip has `nVOf DA` rows. -/
theorem genJ9AX_aw_n (χe : CoinsE) : (recJ9AX s f χe t r).V.n = nVOf (DA) :=
  (genJ9AX_aw_n' Rt hgen hnc hax9 hwalkA χe).trans
    (nVOf_regV (DA) (hall_DA Rt hgen hnc hax9 hwalkA))

/-- **`genJ9AX_aw_krootsV`**: the exec atom-walk root count is `krVOf DA`. -/
theorem genJ9AX_aw_krootsV (χe : CoinsE) : (recJ9AX s f χe t r).krootsV = krVOf (DA) := by
  rw [recX_krootsV]
  by_cases h : (DA).preads = []
  · rw [(krV_zero_iff Rt hgen hnc χe).mpr h]
    unfold krVOf
    rw [if_pos h]
  · have hh := vs_krV_present Rt hgen hnc hax9 hwalkA χe h
    rw [vsKrVJ_eq Rt hgen hnc χe]
    show (DA).krV = _
    rw [hh.2]
    unfold krVOf
    rw [if_neg h]
    exact krW_regroup (DA).acs (DA).preads (hall_DA Rt hgen hnc hax9 hwalkA)

/-- **`genJ9AX_aw_pubs`**: the exec atom-walk publics are the honest `pubsVOf9` at `DA`, at every orbit with
injective nodes. -/
theorem genJ9AX_aw_pubs (χe : CoinsE) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf (DA)))) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsV j) = pubsVOf9 deltaF powerBasis3 (DA) o (toχ χe) j := by
  by_cases h0 : (DA).preads = []
  · rw [pubsV_absent Rt hgen hnc hax9 hwalkA χe h0]
    show K3.toK 0 = _
    unfold pubsVOf9
    rw [if_pos h0, K3.toK_zero]
  · have h' : (DR).preads ≠ [] := fun e => h0 (regroup_eq_nil_iff.mp e)
    have hall := hall_DA Rt hgen hnc hax9 hwalkA
    have hinj' : Function.Injective (powN o (nVOf (DR))) := by
      rw [nVOf_regV (DA) hall]
      exact hinj
    rw [recX_M_pubsV, vRPJ_eq_awE Rt hgen hnc hax9 hwalkA χe h0]
    rw [GenPortJ9AHAWPubs.walkGenRowsBE_pubs χe (DR) (hwA_DR Rt hgen hnc hax9 hwalkA) (hsm_DR Rt hgen hnc hax9 hwalkA)
      (hcl_DR Rt hgen hnc hax9 hwalkA) h' o hinj' j]
    exact GenPortJ9AHAWPub.pubsVOf9_perm deltaF powerBasis3 (D := DA) (D' := DR) rfl rfl
      (regroup_eq_nil_iff) (walkRows_regV_perm (DA) hall) o o hinj hinj' (toχ χe) ▸ rfl

/-- **Corollary at the honest orbit `orbJ8 DA hF`.** -/
theorem genJ9AX_aw_pubs_orb (χe : CoinsE) (hF : DvdOK (DA)) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsV j) = pubsVOf9 deltaF powerBasis3 (DA) (orbJ8 (DA) hF) (toχ χe) j := by
  have hmem : nVOf (DA) ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hinj : Function.Injective (powN (orbJ8 (DA) hF) (nVOf (DA))) :=
    (powN_ok _ (le_two_pow_ht _ hmem)).1
  exact genJ9AX_aw_pubs Rt hgen hnc hax9 hwalkA χe (orbJ8 (DA) hF) hinj j

/-- **Same, in the shape of `BRun9A`'s `avOf9.pubsV`** (any `AVPart`; `rfl`). -/
theorem genJ9AX_aw_pubs_avOf9 (χe : CoinsE) (hF : DvdOK (DA)) (AV : AVPart P KC) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsV j) = (avOf9 deltaF powerBasis3 (DA) hF AV).pubsV (toχ χe) j :=
  genJ9AX_aw_pubs_orb Rt hgen hnc hax9 hwalkA χe hF j

end Run

#print axioms cs_eq
#print axioms acsLJ_eq
#print axioms ptJ_eq
#print axioms HAJ_eq
#print axioms rIAJ_eq
#print axioms readsJ_eq
#print axioms vsKrVJ_eq
#print axioms vsKrVJ_ne
#print axioms krV_zero_iff
#print axioms hall_DA
#print axioms hwA_DA
#print axioms hwalk_DA
#print axioms hwA_DR
#print axioms hcl_DR
#print axioms hsm_DR
#print axioms vs_krV_present
#print axioms vRPJ_eq_awE
#print axioms V_absent
#print axioms pubsV_absent
#print axioms genJ9AX_aw_n'
#print axioms genJ9AX_aw_n
#print axioms genJ9AX_aw_krootsV
#print axioms genJ9AX_aw_pubs
#print axioms genJ9AX_aw_pubs_orb
#print axioms genJ9AX_aw_pubs_avOf9

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRun
