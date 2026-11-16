/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHMsgJ.lean

  **Honest link: data equalities, sizes and messages of the J-9 AL exec record `recJ9ALXJ` at the
  record's data `j9alDataOf` (= `DL`).** Twins of `GenPortJ9AHMsgJ` /
  `GenPortJ9AHJRun`:

  * §1 the data equalities at `DL` (`mv_eqL mb_eqL jrows_eqL regs_eqL ids_eqL lay_eqL mh_eqL`), by `rfl` or the
    J-9 A proofs under `bumpAll`;
  * §2 `regOK_genJ9ALXJ` (from `CompiledByP`; the registered ids are J-only);
  * §3 the C / J / A sizes and messages at `DL` (`size_C_L size_J_L size_A_L`, `msg_pubsC_L msg_pubsJ_L
    msg_pubsA_L`); the X / W / V / AX / SP fields are `recJ9AXJ`'s by `rfl` (`GenPortJ9ALHJRun.toInJ9A_*`), so
    `GenPortJ9AHMsgJ`'s lemmas apply at `(recJ9ALXJ …).toInJ9A`;
  * §4 `validJ9AL_recJ9ALXJ`, `orbAdmL_recJ9ALXJ`.

  NOT in this module (the ALU bridge): the size and publics of the ALU chip `AL` (`size_L`, `msg_pubsL`);
  `validJ9AL_recJ9ALXJ` takes the ALU table's size facts as hypotheses.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALClosed
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMsgJ

section Run

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf cellsA_pos acsA_pos)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (N9 Rows31A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (DvdOK orbJ8 pubsCOf pubsAOf pubsJOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf rows9J W9J fxJ axOnJ spOnJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (bumpAll mhJP)
open Nock.V1J9AL.GenJ9ALXJ (genJ9ALXJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
  (hN_runJ orbOK_J orb_of_size fits_of_size sizes31J toQ_lastScanMapJ toQ_termEJ toQ_sXEJ jGen_snd)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData
  (j9alDataOf jCallsP aCallsP pcallsR primsC idxPOf primPinL aluXL aluBL mh0A rtP rtP_of_not_mem)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX Nock.V1J9A.GenCompX9
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.CheckJ9ALIff
open Nock.Jet.Prim (PrimOp)

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen)) (χe : CoinsE)

local notation "DA" => j9aDataOf P Rg Rt hgen
local notation "DL" => j9alDataOf P Rg Rt prims hgen
local notation "IL" => recJ9ALXJ Rt prims s f χe t r
local notation "h31L" => ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A
local notation "BL" => ComplJ9ALRun.B8L deltaF powerBasis3 Rt hgen prims hpG h31L

/-! ## 1. Data equalities at `DL` -/

theorem cs_eqL : csK Rt s f χe (RnOf t r) = (DL).cells := cs_eqJ Rt hgen χe
theorem acs_eqL : acsK Rt s f χe (RnOf t r) = (DL).acs := acs_eqJ Rt hgen χe
theorem H_eqL : HK Rt s f χe (RnOf t r) = (DL).H := HJ_eqJ Rt hgen χe
theorem mx_eqL : mxK Rt s f χe (RnOf t r) = (DL).mx := rfl
theorem calls_eqL : callsJLK Rt prims s f χe (RnOf t r) = (DL).calls := rfl
theorem regs_eqL : regsJLK Rt prims s f χe (RnOf t r) = (DL).regs := rfl
theorem ids_eqL : idsJLK Rt prims s f χe (RnOf t r) = (DL).ids := rfl
theorem idx_eqL : idxK Rt s f χe (RnOf t r) = (DL).idx := rfl
theorem pc_eqL : pcLK Rt prims s f χe (RnOf t r) = pcallsR (prims.map Prod.fst) (DA).rows := rfl
theorem mv_eqL : mvLK Rt prims s f χe (RnOf t r) = (DL).mv := rfl
theorem jrows_eqL : jrowsLK Rt prims s f χe (RnOf t r) = (DL).jrows := rfl

theorem lay_eqL : List.ofFn (IL).lay = (DL).lay := by
  show List.ofFn (layLK Rt prims s f χe (RnOf t r)).get = _
  rw [List.ofFn_get]
  rfl

/-- The J-9 A export count before the J reads is `mh0A`. -/
theorem mh0_eqL : mhCountsX9E (csK Rt s f χe (RnOf t r)) (compK Rt s f χe (RnOf t r)).bases
    (wsKrK Rt s f χe (RnOf t r)).1 = mh0A P Rg Rt hgen := by
  have hbs : GenCompX9.basesX9 (HK Rt s f χe (RnOf t r)) (pdK Rt s f χe (RnOf t r))
      (idOfK Rt s f χe (RnOf t r)) (W9J s f χe (RnOf t r)) =
      ComplJ9ADataRec.basesA9 P (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
        (ComplJ9ARun.idOfA (p := P) Rt hgen) (bfsForest [ComplJ9AGen.genX9T t]) := by
    rw [GenPortJ9A.basesX9_eq, HJ_eqJ Rt hgen χe, GenPortJ9AHJRun.pd_eqJ Rt hgen χe,
      GenPortJ9AHJRun.idOf_eqJ Rt hgen χe]
    try rfl
  show ComplJ9ADataRec.mhCountsX9 P (csK Rt s f χe (RnOf t r))
    (GenCompX9.basesX9 (HK Rt s f χe (RnOf t r)) (pdK Rt s f χe (RnOf t r))
      (idOfK Rt s f χe (RnOf t r)) (W9J s f χe (RnOf t r))) (wsKrK Rt s f χe (RnOf t r)).1 = _
  rw [hbs]
  rfl

theorem mh_eqL : mhLK Rt prims s f χe (RnOf t r) = (DL).mh := by
  show bumpAll (mhJP P (mhCountsX9E (csK Rt s f χe (RnOf t r)) (compK Rt s f χe (RnOf t r)).bases
    (wsKrK Rt s f χe (RnOf t r)).1) (jrowsLK Rt prims s f χe (RnOf t r)))
      (aluXL (csK Rt s f χe (RnOf t r)) (pcLK Rt prims s f χe (RnOf t r))) = _
  rw [mh0_eqL Rt hgen χe]
  rfl

/-- The base atom-validity count is `DA.mb`. -/
theorem mb0_eqL : Nock.V1J9.Gen9.mbCounts9 (acsK Rt s f χe (RnOf t r)) (csK Rt s f χe (RnOf t r))
    (cK Rt s f χe (RnOf t r)) = (DA).mb := by
  show Nock.V1J9.Gen9.mbCounts9 (DA).acs (DA).cells ⟨s, f, r⟩ = (DA).mb
  rw [← ComplJ9BOf.mbCountsP9_gen]
  exact (ComplJ9BOf.j9_mb_eq Rg Rt hgen).symm

theorem mb_eqL : mbLK Rt prims s f χe (RnOf t r) = (DL).mb := by
  show bumpAll (Nock.V1J9.Gen9.mbCounts9 (acsK Rt s f χe (RnOf t r)) (csK Rt s f χe (RnOf t r))
    (cK Rt s f χe (RnOf t r))) (aluBL P (acsK Rt s f χe (RnOf t r)) (pcLK Rt prims s f χe (RnOf t r))) = _
  rw [mb0_eqL Rt hgen χe]
  rfl

theorem cRPLK_eqL :
    cRPLK Rt prims s f χe (RnOf t r) =
      cellGenB (coOf χe) (yE χe) (hdlB (DL).cells (DL).acs) (bigIdOf (DL).acs) (DL).cells
        (DL).mv (DL).mx (Array.replicate (DL).cells.length 0) (DL).mh := by
  unfold cRPLK mx1K HK
  rw [cs_eqL Rt prims hgen χe, acs_eqL Rt prims hgen χe, mv_eqL Rt prims hgen χe, mx_eqL Rt prims hgen χe,
    mh_eqL Rt prims hgen χe]

theorem aRPLK_eqL :
    aRPLK Rt prims s f χe (RnOf t r) =
      atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA := by
  have hinfo : infoOfE (acsK Rt s f χe (RnOf t r)) (ptK Rt s f χe (RnOf t r)) (RnOf t r).rows =
      (DA).info := GenPortJ9.infoOfE_eq _ _
  have hv : (vsKrVK Rt s f χe (RnOf t r)).1 = (DA).vs :=
    congrArg Prod.fst (GenPortJ9AHMsgJ.vsKrVK_eqJ Rt hgen χe)
  have hmx : wCounts (rIAK Rt s f χe (RnOf t r)) (acsK Rt s f χe (RnOf t r)) (vsKrVK Rt s f χe (RnOf t r)).1 =
      (DA).mxA := by
    rw [hv]; rfl
  unfold aRPLK
  rw [hinfo, mb_eqL Rt prims hgen χe, hmx, GenPortJ9AHMsgJ.ptK_eqJ Rt hgen χe, acs_eqJ Rt hgen χe]
  try rfl

/-! ## 2. The registry premise -/

/-- **`RegOK` for the mixed record.**  The registered ids are the J calls' (non-primitive) ids; `hC` covers them.
`Rt0` is the base template table; the generator runs at `rtP Rt0 prims`, which is `Rt0` off the primitive ids. -/
theorem regOK_genJ9ALXJ {Rg : Nock.Jet.VerifiedRegistry} {Rt0 : ℕ → Nock.Jet.Autogen.Tpl}
    {prims : List (ℕ × PrimOp)} {fuel : ℕ} {s f : Noun} {χe : CoinsE} {I : InJ9AL}
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims)
    (hI : genJ9ALXJ Rg.R (rtP Rt0 prims) prims fuel s f χe = some I) : RegOK I.toInJ8 Rg.R := by
  obtain ⟨t, r, hg, rfl⟩ := genJ9ALXJ_some hI
  intro i hi
  have hi' : i ∈ regsJLK (rtP Rt0 prims) prims s f χe (RnOf t r) := hi
  have hid : i ∈ (callsJLK (rtP Rt0 prims) prims s f χe (RnOf t r)).map Prod.fst := List.mem_dedup.mp hi'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hid
  have hc' : c ∈ jCallsP (prims.map Prod.fst) (callsOf (ComplJ8Data.rowsOfT t)) := hc
  obtain ⟨hcm, hnp⟩ := ComplJ9ALData.jCallsP_sub _ _ c hc'
  have hcalled : c.1 ∈ CalledIds t :=
    GenPortJ9AHJRun.callsIds_calledIds hg (List.mem_map_of_mem (f := Prod.fst) hcm)
  obtain ⟨hj, -, hw⟩ := (CheckedRegistryP.hRt_hregAx_ofP hC hg).1 c.1 hcalled hnp
  have e : (rtP Rt0 prims) c.1 = Rt0 c.1 := rtP_of_not_mem Rt0 prims hnp
  show Rg.R c.1 = some ⟨((rtP Rt0 prims) c.1).toTemplate P, Nock.Jet.Autogen.compile P ((rtP Rt0 prims) c.1)⟩ ∧
    ((rtP Rt0 prims) c.1).WellTyped P
  rw [e]
  exact ⟨hj, hw⟩

/-! ## 3. Sizes and messages of the C / J / A chips at `DL` -/

theorem n_C_L : (IL).C.n = (DL).cells.length := by
  have e : (IL).C.n = (DL).cells.length := by
    show (chipOf (cRPLK Rt prims s f χe (RnOf t r)).1).n = _
    rw [cRPLK_eqL Rt prims hgen χe]
    exact GenPortJ9AHCell.cellGenB_size _ _ _ _ _ _ _ _ _
  exact e

theorem n_A_L : (IL).A.n = (DL).acs.length := by
  have e : (IL).A.n = (DL).acs.length := by
    show (chipOf (aRPLK Rt prims s f χe (RnOf t r)).1).n = _
    rw [aRPLK_eqL Rt prims hgen χe]
    exact GenPortJ9AHAtomCols2.atomGenE_size (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info
      (DL).mb (DL).mxA (DL).mhA
  exact e

theorem jrows_len_layLK : (DL).jrows.length = (layLK Rt prims s f χe (RnOf t r)).length := by
  have h := ComplJ9ALData.jrows_preL (p := P) Rt prims hgen
  have h2 := congrArg List.length h
  rw [List.length_map] at h2
  exact h2

theorem n_J_L : (IL).J.n = (DL).jrows.length :=
  (jrows_len_layLK Rt prims hgen χe).symm

include hpG h31A in
theorem size_C_L : (IL).C.n = (BL).Pb.nC := n_C_L Rt prims hgen χe
include hpG h31A in
theorem size_A_L : (IL).A.n = (BL).Pb.nA := n_A_L Rt prims hgen χe
include hpG h31A in
theorem size_J_L : (IL).J.n = (BL).Pb.nJ := n_J_L Rt prims hgen χe

theorem hcs_DL (χe : CoinsE) : ∀ c ∈ (DL).cells, c.isCell = true := by
  rw [← cs_eqL Rt prims hgen χe]
  exact fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1

theorem hcl_DL (χe : CoinsE) : ComplJ8Data.ClP (DL).cells [] := by
  rw [← cs_eqL Rt prims hgen χe]
  exact ComplJ8Data.cells_closed _

include hpG h31A in
theorem msg_pubsC_L : (IL).toInJ9A.toMsg.pubsC = ((BL).M (toχ χe)).pubsC := by
  funext j
  have hF := ComplJ9ALRun.hFL Rt hgen prims hpG h31L
  show K3.toK ((cRPLK Rt prims s f χe (RnOf t r)).2 j) =
    pubsCOf deltaF powerBasis3 (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) (orbJ8 (DL) hF) (toχ χe) j
  have hmem : (DL).cells.length ∈ ComplJ8Of.sizesJ8 (DL) := by
    simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (orbJ8 (DL) hF) (DL).cells.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  rw [cRPLK_eqL Rt prims hgen χe]
  exact GenPortJ9AHCell.cellGenB_pubs χe (DL).cells (DL).acs
    (hcs_DL Rt prims hgen χe) (hcl_DL Rt prims hgen χe) (DL).mv (DL).mx
    (DL).mh (DL) rfl rfl rfl rfl rfl (ComplJ9ALData.cellsL_pos Rt prims hgen)
    (orbJ8 (DL) hF) hinj j

include hpG h31A in
theorem msg_pubsA_L : (IL).toInJ9A.toMsg.pubsA = ((BL).M (toχ χe)).pubsA := by
  funext j
  have hF := ComplJ9ALRun.hFL Rt hgen prims hpG h31L
  have hmem : (DL).acs.length ∈ ComplJ8Of.sizesJ8 (DL) := by simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (orbJ8 (DL) hF) (DL).acs.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  show K3.toK ((aRPLK Rt prims s f χe (RnOf t r)).2 j) =
    pubsAOf deltaF powerBasis3 (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) (orbJ8 (DL) hF) (toχ χe) j
  rw [aRPLK_eqL Rt prims hgen χe]
  have hacs : (DL).acs = ComplJ8Data.acsP P (DL).bigs (DL).dupP := rfl
  have hinfo : (DL).info = ComplJ8Data.infoOfP P (DL).acs (DL).rows := rfl
  have hg : ComplJ8Atom.GenHyp (DL).bigs (DL).dupP (DL).rows (DL).mb :=
    ComplJ9ALTables.genHyp_mbL Rg Rt prims hgen (hN_runJ Rt hgen h31A)
  exact GenPortJ9AHAtom.atomGenE_pubs (DL) hacs hinfo hg χe (ComplJ9ALData.acsL_pos Rt prims hgen)
    (orbJ8 (DL) hF) hinj j

/-- The J chip's four publics are `pubsJOf` at ANY J-8 data (`GenPortJ9AHMsgJ.jGen_pubs`, abstracted from `DA`). -/
theorem jGen_pubsG (D : ComplJ8Data.J8Data P Rg fuel s f r) (i : ℕ) :
    K3.toK ((jGen χe D.jrows).2 i) = pubsJOf deltaF D (toχ χe) i := by
  have hT := toQ_lastScanMapJ D.jrows (termE χe)
    (Nock.Jet.ChipJ8T.HonestRAP.termJ deltaF (VerJ8.chalsJJ8 (toχ χe))) (toQ_termEJ χe)
  have hX := toQ_lastScanMapJ D.jrows (sXE χe)
    (Nock.Jet.ChipJ8T.HonestRAP.sX deltaF (VerJ8.chalsJJ8 (toχ χe))) (toQ_sXEJ χe)
  have hR0 : pubsJOf deltaF D (toχ χe) 0 = Quad.re _ (∑ k : Fin D.jrows.length,
      Nock.Jet.ChipJ8T.HonestRAP.termJ deltaF (VerJ8.chalsJJ8 (toχ χe)) (D.jrows.get k)) := rfl
  have hR1 : pubsJOf deltaF D (toχ χe) 1 = Quad.im _ (∑ k : Fin D.jrows.length,
      Nock.Jet.ChipJ8T.HonestRAP.termJ deltaF (VerJ8.chalsJJ8 (toχ χe)) (D.jrows.get k)) := rfl
  have hR2 : pubsJOf deltaF D (toχ χe) 2 = Quad.re _ (∑ k : Fin D.jrows.length,
      Nock.Jet.ChipJ8T.HonestRAP.sX deltaF (VerJ8.chalsJJ8 (toχ χe)) (D.jrows.get k)) := rfl
  have hR3 : pubsJOf deltaF D (toχ χe) 3 = Quad.im _ (∑ k : Fin D.jrows.length,
      Nock.Jet.ChipJ8T.HonestRAP.sX deltaF (VerJ8.chalsJJ8 (toχ χe)) (D.jrows.get k)) := rfl
  have L0 : (jGen χe D.jrows).2 0 = (lastK6 (scanK6 (D.jrows.map (termE χe)))).re := rfl
  have L1 : (jGen χe D.jrows).2 1 = (lastK6 (scanK6 (D.jrows.map (termE χe)))).im := rfl
  have L2 : (jGen χe D.jrows).2 2 = (lastK6 (scanK6 (D.jrows.map (sXE χe)))).re := rfl
  have L3 : (jGen χe D.jrows).2 3 = (lastK6 (scanK6 (D.jrows.map (sXE χe)))).im := rfl
  by_cases h0 : i = 0
  · subst h0
    rw [L0, hR0, ← hT, re_toQ]
  by_cases h1 : i = 1
  · subst h1
    rw [L1, hR1, ← hT, im_toQ]
  by_cases h2 : i = 2
  · subst h2
    rw [L2, hR2, ← hX, re_toQ]
  by_cases h3 : i = 3
  · subst h3
    rw [L3, hR3, ← hX, im_toQ]
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 4 := ⟨i - 4, by omega⟩
  have hR4 : pubsJOf deltaF D (toχ χe) (i' + 4) = 0 := by
    simp [pubsJOf]
  have hL4 : (jGen χe D.jrows).2 (i' + 4) = 0 := by
    simp [jGen_snd]
  rw [hL4, hR4]
  exact K3.toK_zero

theorem msg_pubsJ_L : (IL).toInJ9A.toMsg.pubsJ = ((BL).M (toχ χe)).pubsJ := by
  funext i
  exact jGen_pubsG χe (DL) i

/-! ## 4. Validity and orbit admissibility -/

include hpG h31A in
theorem sizes31L (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (IL).X.n ≤ 2 ^ 31 ∧ (IL).C.n ≤ 2 ^ 31 ∧ (IL).W.n ≤ 2 ^ 31 ∧ (IL).J.n ≤ 2 ^ 31 ∧ (IL).A.n ≤ 2 ^ 31 ∧
      (IL).V.n ≤ 2 ^ 31 ∧ (IL).AX.n ≤ 2 ^ 31 ∧ (IL).SP.n ≤ 2 ^ 31 := by
  obtain ⟨sX, -, sW, -, -, sV, sAX, sSP⟩ := sizes31J Rt hgen hpG h31A χe hwalk9 hax9 hwalkA
  have h31 := h31L
  have hC : (DL).cells.length ≤ 2 ^ 31 := h31 _ (by simp [ComplJ9ARun.sizesA, ComplJ8Of.sizesJ8])
  have hJ : (DL).jrows.length ≤ 2 ^ 31 := h31 _ (by simp [ComplJ9ARun.sizesA, ComplJ8Of.sizesJ8])
  have hA : (DL).acs.length ≤ 2 ^ 31 := h31 _ (by simp [ComplJ9ARun.sizesA, ComplJ8Of.sizesJ8])
  refine ⟨?_, (n_C_L Rt prims hgen χe).le.trans hC, ?_, (n_J_L Rt prims hgen χe).le.trans hJ,
    (n_A_L Rt prims hgen χe).le.trans hA, ?_, ?_, ?_⟩
  · rw [toInJ9A_X Rt prims s f χe t r]; exact sX
  · rw [toInJ9A_W Rt prims s f χe t r]; exact sW
  · rw [toInJ9A_V Rt prims s f χe t r]; exact sV
  · rw [toInJ9A_AX Rt prims s f χe t r]; exact sAX
  · rw [toInJ9A_SP Rt prims s f χe t r]; exact sSP

include hpG h31A in
/-- **`ValidJ9AL` of the mixed record**: the J-9 A chips as for `recJ9AXJ`, the C / J / A chips at `DL`, and the ALU
chip's admissible shape (the table is non-empty and has at most `2^31` rows: the ALU bridge's size facts). -/
theorem validJ9AL_recJ9ALXJ (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (hnL : 0 < (lRPLK Rt prims s f χe (RnOf t r)).1.size)
    (hsL : (lRPLK Rt prims s f χe (RnOf t r)).1.size ≤ 2 ^ 31) :
    ValidJ9AL (IL) := by
  obtain ⟨sX, sC, sW, sJ, sA, sV, sAX, sSP⟩ := sizes31L Rt prims hgen hpG h31A χe hwalk9 hax9 hwalkA
  refine
    { toValidJ9A := ValidJ9A.mk' (IL).toInJ9A ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩
      nL := ?_
      oAL := ?_ }
  · rw [toInJ9A_X Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).nX
  · rw [size_C_L Rt prims hgen hpG h31A χe]; exact (BL).Pb.hnC
  · rw [toInJ9A_W Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).nW
  · rw [size_A_L Rt prims hgen hpG h31A χe]; exact (BL).Pb.hnA
  · rw [toInJ9A_V Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).nV
  · rw [toInJ9A_X Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).oX
  · exact orb_of_size _ rfl sC
  · rw [toInJ9A_W Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).oW
  · exact orbOK_J (layLK Rt prims s f χe (RnOf t r)).length sJ _
  · exact orb_of_size _ rfl sA
  · rw [toInJ9A_V Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).oV
  · rw [toInJ9A_AX Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).nAX
  · rw [toInJ9A_AX Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).oAX
  · rw [toInJ9A_SP Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).nSP
  · rw [toInJ9A_SP Rt prims s f χe t r]; exact (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA).oSP
  · exact hnL
  · exact orb_of_size (lRPLK Rt prims s f χe (RnOf t r)).1 rfl hsL

include hpG h31A in
theorem orbAdmL_recJ9ALXJ (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (hnL : 0 < (lRPLK Rt prims s f χe (RnOf t r)).1.size)
    (hsL : (lRPLK Rt prims s f χe (RnOf t r)).1.size ≤ 2 ^ 31) :
    OrbAdmL (IL) (orbOfL (IL)) := by
  obtain ⟨sX, sC, sW, sJ, sA, sV, sAX, sSP⟩ := sizes31L Rt prims hgen hpG h31A χe hwalk9 hax9 hwalkA
  exact orbAdmL_self (validJ9AL_recJ9ALXJ Rt prims hgen hpG h31A χe hwalk9 hax9 hwalkA hnL hsL)
    (fits_of_size _ rfl sX) (fits_of_size _ rfl sC) (fits_of_size _ rfl sW)
    (GenPortJ9AHOrb.hOf_spec (layLK Rt prims s f χe (RnOf t r)).length sJ).2.1
    (fits_of_size _ rfl sA) (fits_of_size _ rfl sV) (fits_of_size _ rfl sAX) (fits_of_size _ rfl sSP)
    (fits_of_size (lRPLK Rt prims s f χe (RnOf t r)).1 rfl hsL)

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMsgJ

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMsgJ
#print axioms mv_eqL
#print axioms mh_eqL
#print axioms mb_eqL
#print axioms jrows_eqL
#print axioms lay_eqL
#print axioms regOK_genJ9ALXJ
#print axioms size_C_L
#print axioms size_A_L
#print axioms size_J_L
#print axioms msg_pubsC_L
#print axioms msg_pubsA_L
#print axioms msg_pubsJ_L
#print axioms validJ9AL_recJ9ALXJ
#print axioms orbAdmL_recJ9ALXJ
end Axioms
