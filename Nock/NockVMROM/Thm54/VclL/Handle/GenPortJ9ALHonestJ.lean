/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHonestJ.lean

  **Honest link for J-9 AL: honest acceptance of `genJ9ALXJ`.** Twin of
  `GenPortJ9AHonestJ` (`honest_rec_atJ` / `genJ9AXJ_honest_at` / `checkJ9AX_genJ9AXJ`) with `recJ9ALXJ` for
  `recJ9AXJ`, `complJ9AL_closed_of` (`CompiledByP`, template table `rtP Rt0 prims`) for `complJ9A_closed_of`, and the
  ALU chip.

  * §1 the run-level ALU wrapper (generic template table `Rt`): data equalities, `hpreg`, `hblk`, `hsz`, `hgood`
    (the record's pole family at `nLRun = aluLen + 1` rows, extended to any row count past the table), the full
    orbit, the ALU publics against the record's, and `hALk_recL` (both branches: a primitive is called, or not);
  * §2 validity of the record (`validJ9AL_recJ9ALXJ'`: L1's lemma with the ALU table's shape as `OrbOK` + positivity,
    because the generator's ALU chip has `3·2^h` rows, which may exceed `2^31`), orbit admissibility, the budget;
  * §3 `honest_rec_atJL`: the core at the global `Algebra Fp 𝕂′` instance;
  * §4 the deliverables `genJ9ALXJ_honest_at`, `genJ9ALXJ_honest`, `checkJ9ALX_genJ9ALXJ`.

  Branch (ii) (no primitive call, `aluOn = false`, `zeroChip`) is NOT routed through `genJ9AXJ_honest_at`: that
  theorem needs `CompiledBy P Rg (rtP Rt0 prims)`, which fails whenever `prims ≠ []` (a registered primitive id maps
  to `primSpec`, not to a compiled template).  Instead every non-ALU field comes, in both branches, from
  `BRun9AL`'s acceptance by the L2 ports and the transport; only `hALk` and the ALU terminals are split, and branch
  (ii)'s `hALk` is the absent branch of `ALChipOK` (the route of `AcceptsJ9AL.of_A`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHLink
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHCellE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAtomE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaticJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHGoodCoinJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ
import Nock.V1J9AL.CheckJ9ALIff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb orbOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHLink (IL_AL IL_pubsL IL_aluOn IL_prims)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf rtP)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.CheckJ9ALIff
open Nock.V1J9AL.GenAluE
open Nock.Jet.Prim (PrimOp primSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8)

noncomputable section

/-! ## 0. Generic facts -/

/-- A chip whose table has `3·2^k` rows (`1 ≤ k ≤ 32`) is on an admissible orbit. -/
theorem orbOK_chipOf_pow [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC] (tbl : Array (Array (ZMod P))) (k : ℕ) (hs : tbl.size = 3 * 2 ^ k) (h1 : 1 ≤ k)
    (h32 : k ≤ 32) : OrbOK (chipOf tbl) := by
  have hh : (chipOf tbl).h = k := by
    show hOf tbl.size = k
    rw [hs]; exact GenPortJ9ALHAluE.hOf_three_pow k h1 (by omega)
  rw [← orbB_iff]
  unfold orbB
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true (hh ▸ h1), ?_⟩
  show ordOK (ωOf (chipOf tbl).h) (chipOf tbl).h = true
  rw [hh]
  exact GenPortJ9AHOrb.ordOK_ωOf k h1 h32

/-- Columns of a chip literal with `colsOf` columns. -/
theorem cols_of_eqJ (J' : ChipIn) {h n : ℕ} {ω : Gold} {tbl : Array (Array (ZMod P))}
    (hJ : J' = ⟨h, n, ω, colsOf tbl n⟩) (j : ℕ) (i : Fin J'.n) : J'.cols j i = (tbl.getD i #[]).getD j 0 := by
  subst hJ; rfl

/-! Message projections of `toMsgL`, over a VARIABLE record. -/
theorem toMsgL_m (I : InJ9AL) : I.toMsgL.m = I.toInJ9A.toMsg.m := rfl
theorem toMsgL_rho (I : InJ9AL) : I.toMsgL.ρ = I.toInJ9A.toMsg.ρ := rfl
theorem toMsgL_rhoS (I : InJ9AL) : I.toMsgL.ρS = I.toInJ9A.toMsg.ρS := rfl
theorem toMsgL_pubsC (I : InJ9AL) : I.toMsgL.pubsC = I.toInJ9A.toMsg.pubsC := rfl
theorem toMsgL_pubsJ (I : InJ9AL) : I.toMsgL.pubsJ = I.toInJ9A.toMsg.pubsJ := rfl
theorem toMsgL_pubsA (I : InJ9AL) : I.toMsgL.pubsA = I.toInJ9A.toMsg.pubsA := rfl
theorem toMsgL_pubsW (I : InJ9AL) : I.toMsgL.pubsW = I.toInJ9A.toMsg.pubsW := rfl
theorem toMsgL_pubsV (I : InJ9AL) : I.toMsgL.pubsV = I.toInJ9A.toMsg.pubsV := rfl
theorem toMsgL_pubsX (I : InJ9AL) : I.toMsgL.pubsX = I.toInJ9A.toMsg.pubsX := rfl
theorem toMsgL_pubsS (I : InJ9AL) : I.toMsgL.pubsS = I.toInJ9A.toMsg.pubsS := rfl

/-- No primitive call: no called id is a primitive id, so the called primitives are none. -/
theorem primsC_nil_of (prims : List (ℕ × PrimOp)) (rows : Array RowNX)
    (h : ComplJ9ALData.pcallsR (prims.map Prod.fst) rows = []) :
    ComplJ9ALData.primsC prims ((callsOf rows).map Prod.fst) = [] := by
  have h1 := ComplJ9ALData.pcallsR_fst (prims.map Prod.fst) rows
  rw [h, List.map_nil] at h1
  unfold ComplJ9ALData.primsC
  rw [List.filter_eq_nil_iff]
  intro q hq hmem
  simp only [decide_eq_true_eq] at hmem
  obtain ⟨c, hc, hcq⟩ := List.mem_map.mp hmem
  have hcm : c ∈ ComplJ9ALData.aCallsP (prims.map Prod.fst) (callsOf rows) := by
    unfold ComplJ9ALData.aCallsP
    refine List.mem_filter.mpr ⟨hc, ?_⟩
    simp only [decide_eq_true_eq]
    rw [hcq]
    exact List.mem_map_of_mem hq
  rw [← h1] at hcm
  simp at hcm

/-! ## 1. The run-level ALU wrapper -/

section Alu
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (χe : CoinsE)

local notation "RN" => RnOf t r
local notation "CS" => csK Rt s f χe (RnOf t r)
local notation "HM" => HK Rt s f χe (RnOf t r)
local notation "PS" => psCLK Rt prims s f χe (RnOf t r)
local notation "IDS" => idsK Rt s f χe (RnOf t r)
local notation "PC" => pcLK Rt prims s f χe (RnOf t r)
local notation "VC" => ComplJ9ALData.idxPOf (csK Rt s f χe (RnOf t r)) prims
local notation "MR" => ComplJ9ALRun.mRun (t := t) prims
local notation "PSR" => ComplJ9ALRun.psRun (p := P) Rt hgen prims
local notation "VCR" => ComplJ9ALRun.vcRun (p := P) Rt hgen prims
local notation "CLR" => AluSatRun.clsRun (p := P) Rt prims hgen
local notation "TBR" => ComplJ9ALRun.tbR deltaF Rt hgen prims
local notation "ALEN" => ComplJ9ALRun.aluLen (K := KC) deltaF Rt hgen prims
local notation "NLR" => ComplJ9ALRun.nLRun (K := KC) deltaF Rt hgen prims
local notation "TE" => aluGenE χe (csK Rt s f χe (RnOf t r)) (HK Rt s f χe (RnOf t r))
  (psCLK Rt prims s f χe (RnOf t r)) (idsK Rt s f χe (RnOf t r)) (pcLK Rt prims s f χe (RnOf t r))
local notation "IL" => recJ9ALXJ Rt prims s f χe t r

theorem ps_eqR : PS = PSR := rfl

theorem vc_eqR : VC = VCR := by
  rw [GenPortJ9ALHMsgJ.cs_eqL Rt prims hgen χe]; rfl

theorem cls_eqR : callsLOf CS HM PS PC = CLR := by
  have e : callsLOf CS HM PS PC = callsLOf CS HM prims PC :=
    GenPortJ9ALHAlu.callsLOf_eq CS HM prims (ComplJ8Data.rowsOfT t)
  rw [e, GenPortJ9ALHMsgJ.cs_eqL Rt prims hgen χe, GenPortJ9ALHMsgJ.H_eqL Rt prims hgen χe]
  rfl

theorem preg_eqR : (pregsOf CS PS IDS : List (BRow (ZMod P))) = AluSatPreg.pregsP PS VC MR :=
  GenPortJ9ALHAlu.pregsOf_eq CS prims (ComplJ8Data.rowsOfT t)

theorem tb_eqR (y : Quad (algebraMap (ZMod P) KC deltaF)) :
    tblP (K := KC) deltaF P y (AluSatPreg.pregsP PS VC MR) (callsLOf CS HM PS PC) = TBR y := by
  rw [cls_eqR Rt prims hgen χe, vc_eqR Rt prims hgen χe]
  rfl

theorem tbE_eqR :
    GenPortJ9ALHAlu.tbE (yE χe) (pregsOf CS PS IDS) (callsLOf CS HM PS PC) =
      TBR (AluPoles.yOf deltaF (toχ χe)) := by
  show tblP (K := KC) deltaF P (K6.toQ (yE χe)) _ _ = _
  rw [GenPortJ9ALHAluE.toQ_yE_yOf, preg_eqR Rt prims χe]
  exact tb_eqR Rt prims hgen χe _

theorem rowsB_len :
    (aluRowsB P (pregsOf CS PS IDS : List (BRow (ZMod P))) (callsLOf CS HM PS PC)).length = ALEN := by
  rw [← GenPortJ9ALHAlu.tbE_length (yE χe), tbE_eqR Rt prims hgen χe]
  exact ComplJ9ALRun.tbR_length deltaF Rt hgen prims _

theorem hszE (h31L : ALEN < 2 ^ 31) :
    (aluRowsB P (pregsOf CS PS IDS : List (BRow (ZMod P))) (callsLOf CS HM PS PC)).length ≤ 2 ^ 31 := by
  rw [rowsB_len Rt prims hgen χe]; omega

theorem hblkE (hpG : P = Nock.Atoms.p) (h31 : ComplJ9ARun.Rows31A (j9alDataOf P Rg Rt prims hgen))
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) :
    ∀ cl ∈ callsLOf CS HM PS PC, BlockBaseSat (F := ZMod P) P cl ∧ BlockIdentSat (K := KC) deltaF P cl := by
  rw [cls_eqR Rt prims hgen χe]
  intro cl hcl
  have hok := AluCallOK.callOK_run_G Rt prims hgen hpG h31 hnd hprim hnoDec hlimb cl hcl
  exact ⟨AluSatBlock.blockBaseSat_G hpG cl hok, AluSatBlock.blockIdentSat_G deltaF hpG cl hok⟩

/-- **`hgood` at any row count**: the record's ALU pole family at `nLRun = aluLen + 1` rows covers every row count
(the rows from the table's last on are the padding row). -/
theorem hgoodE {χ : SVFrame.Coins FrameJ8.frameJ8 KC}
    (hg : ∀ e ∈ AluPoles.famAL deltaF TBR NLR, χ ∉ e.ev) (n : ℕ) :
    ∀ e ∈ AluPoles.famAL deltaF
      (fun y => tblP (K := KC) deltaF P y (AluSatPreg.pregsP PS VC MR) (callsLOf CS HM PS PC)) n, χ ∉ e.ev := by
  have hT : (fun y => tblP (K := KC) deltaF P y (AluSatPreg.pregsP PS VC MR) (callsLOf CS HM PS PC)) = TBR :=
    funext fun y => tb_eqR Rt prims hgen χe y
  rw [hT]
  refine GenPortJ9ALHAluE.famAL_good_of_le TBR (m := NLR) (Nat.succ_pos _) ?_ χ hg n
  intro y i hi
  have hl : (tblP (K := KC) deltaF P y (AluSatPreg.pregsP (F := ZMod P) PSR VCR MR) CLR).length = ALEN :=
    ComplJ9ALRun.tbR_length deltaF Rt hgen prims y
  have hn : NLR = ALEN + 1 := rfl
  have h1 := GenPortJ9ALHAluE.rowAt_tblP_last (AluSatPreg.pregsP (F := ZMod P) PSR VCR MR) CLR y i
    (by rw [hl]; omega)
  have h2 := GenPortJ9ALHAluE.rowAt_tblP_last (AluSatPreg.pregsP (F := ZMod P) PSR VCR MR) CLR y (NLR - 1)
    (by rw [hl]; omega)
  exact h1.trans h2.symm

theorem aluOn_true (hpc : PC ≠ []) : aluOnLK Rt prims s f χe RN = true := by
  unfold aluOnLK
  cases h : pcLK Rt prims s f χe (RnOf t r) with
  | nil => exact absurd h hpc
  | cons _ _ => rfl

theorem aluOn_false (hpc : PC = []) : aluOnLK Rt prims s f χe RN = false := by
  unfold aluOnLK; rw [hpc]; rfl

theorem lRP_on (hpc : PC ≠ []) : lRPLK Rt prims s f χe RN = TE := by
  unfold lRPLK; rw [if_pos (aluOn_true Rt prims χe hpc)]

theorem lRP_off (hpc : PC = []) : lRPLK Rt prims s f χe RN = zeroChip := by
  unfold lRPLK; rw [if_neg (by rw [aluOn_false Rt prims χe hpc]; decide)]

theorem psR_nil (hpc : PC = []) : PSR = [] :=
  primsC_nil_of prims (ComplJ8Data.rowsOfT t) hpc

theorem clR_nil (hpc : PC = []) : CLR = [] := by
  show callsLOf _ _ prims (ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t)) = []
  rw [show ComplJ9ALData.pcallsR (prims.map Prod.fst) (ComplJ8Data.rowsOfT t) = [] from hpc]
  rfl

theorem tbR_pad (hpc : PC = []) (y : Quad (algebraMap (ZMod P) KC deltaF)) :
    TBR y = [(padRow, QRow.zero)] := by
  show tblP (K := KC) deltaF P y (AluSatPreg.pregsP (F := ZMod P) PSR VCR MR) CLR = _
  rw [psR_nil Rt prims hgen χe hpc, clR_nil Rt prims hgen χe hpc]
  rfl

/-- **The record's primitive table is the honest one** (branch (ii): both are empty). -/
theorem prims_eqR : (IL).prims = PSR := by
  rw [IL_prims]
  by_cases hpc : PC = []
  · rw [if_neg (by rw [aluOn_false Rt prims χe hpc]; decide), psR_nil Rt prims hgen χe hpc]
  · rw [if_pos (aluOn_true Rt prims χe hpc)]; rfl

/-- **The ALU chip of the record**: non-empty, on an admissible orbit, at most `3·2^32` rows; full when on. -/
theorem al_shape (h31L : ALEN < 2 ^ 31) :
    0 < (IL).AL.n ∧ OrbOK (IL).AL ∧ (IL).AL.n ≤ 3 * 2 ^ 32 ∧
      ((IL).aluOn = true → (IL).AL.n = 3 * 2 ^ (IL).AL.h) := by
  by_cases hpc : PC = []
  · have e : (IL).AL = chipOf zeroChip.1 := by rw [IL_AL, lRP_off Rt prims χe hpc]
    refine ⟨by rw [e]; show 0 < 1; omega, by rw [e]; exact GenPortJ9AHMsgJ.orb_of_size _ rfl (by
      show 1 ≤ 2 ^ 31; norm_num), by rw [e]; show 1 ≤ 3 * 2 ^ 32; norm_num, fun h => ?_⟩
    rw [IL_aluOn, aluOn_false Rt prims χe hpc] at h
    exact absurd h (by decide)
  · have e : (IL).AL = chipOf TE.1 := by rw [IL_AL, lRP_on Rt prims χe hpc]
    have hsz := hszE Rt prims hgen χe h31L
    have hspec := GenPortJ9AHOrb.hOf_spec _ hsz
    have hsize := GenPortJ9ALHAluE.aluGenE_size χe CS HM PS IDS PC
    have hfull := GenPortJ9ALHAluE.chipOf_aluGenE_full χe CS HM PS IDS PC hsz
    have hn : (chipOf TE.1).n = GenPortJ9ALHAluE.NE (pregsOf CS PS IDS) (callsLOf CS HM PS PC) := hsize
    have hpow : (2 : ℕ) ^ hOf (aluRowsB P (pregsOf CS PS IDS : List (BRow (ZMod P))) (callsLOf CS HM PS PC)).length
        ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hspec.2.2
    refine ⟨?_, ?_, ?_, fun _ => by rw [e]; exact hfull⟩
    · rw [e, hn]; exact GenPortJ9ALHAluE.NE_pos _ _
    · rw [e]; exact orbOK_chipOf_pow _ _ hsize hspec.1 hspec.2.2
    · rw [e, hn]; exact Nat.mul_le_mul_left 3 hpow

/-- **The ALU terminals of the record are the honest record's** at the three `Quad.mk` positions. -/
theorem pubsL_eqR (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (h31L : ALEN < 2 ^ 31) :
    let M' := (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 Rt hgen prims hpG h31A).M (toχ χe)
    Quad.mk (algebraMap (ZMod P) KC deltaF) ((IL).toMsgL.pubsL AluSZChipJ9.pubALv)
        ((IL).toMsgL.pubsL (AluSZChipJ9.pubALv + 1)) =
      Quad.mk _ (M'.pubsL AluSZChipJ9.pubALv) (M'.pubsL (AluSZChipJ9.pubALv + 1)) ∧
    Quad.mk (algebraMap (ZMod P) KC deltaF) ((IL).toMsgL.pubsL AluSZChipJ9.pubALs)
        ((IL).toMsgL.pubsL (AluSZChipJ9.pubALs + 1)) =
      Quad.mk _ (M'.pubsL AluSZChipJ9.pubALs) (M'.pubsL (AluSZChipJ9.pubALs + 1)) ∧
    Quad.mk (algebraMap (ZMod P) KC deltaF) ((IL).toMsgL.pubsL AluSZChipJ9.pubALx)
        ((IL).toMsgL.pubsL (AluSZChipJ9.pubALx + 1)) =
      Quad.mk _ (M'.pubsL AluSZChipJ9.pubALx) (M'.pubsL (AluSZChipJ9.pubALx + 1)) := by
  intro M'
  have eM : M'.pubsL = ComplJ9ALRun.pubsLOf deltaF Rt hgen prims (toχ χe) :=
    congrArg (fun M => M.pubsL) (ComplJ9ALClosed.mixM_eq deltaF powerBasis3 Rt hgen prims (toχ χe) hpG h31A)
  have hV : Quad.mk (algebraMap (ZMod P) KC deltaF) (M'.pubsL AluSZChipJ9.pubALv)
      (M'.pubsL (AluSZChipJ9.pubALv + 1)) = ComplJ9ALRun.SV deltaF Rt hgen prims NLR (toχ χe) := by
    rw [eM]; simp only [ComplJ9ALRun.pubsLOf, AluSZChipJ9.pubALv]
    exact ComplJ8Of.pub2_mk2 deltaF _ 0 rfl
  have hS : Quad.mk (algebraMap (ZMod P) KC deltaF) (M'.pubsL AluSZChipJ9.pubALs)
      (M'.pubsL (AluSZChipJ9.pubALs + 1)) = ComplJ9ALRun.SS deltaF Rt hgen prims NLR (toχ χe) := by
    rw [eM]; simp only [ComplJ9ALRun.pubsLOf, AluSZChipJ9.pubALs]
    norm_num
    exact ComplJ8Of.pub2_mk2 deltaF _ 2 rfl
  have hX : Quad.mk (algebraMap (ZMod P) KC deltaF) (M'.pubsL AluSZChipJ9.pubALx)
      (M'.pubsL (AluSZChipJ9.pubALx + 1)) = ComplJ9ALRun.SX deltaF Rt hgen prims NLR (toχ χe) := by
    rw [eM]; simp only [ComplJ9ALRun.pubsLOf, AluSZChipJ9.pubALx]
    norm_num
    exact ComplJ8Of.pub2_mk2 deltaF _ 4 rfl
  rw [hV, hS, hX]
  have ePL : (IL).toMsgL.pubsL = fun i => K3.toK ((lRPLK Rt prims s f χe RN).2 i) := rfl
  by_cases hpc : PC = []
  · -- branch (ii): both sides vanish
    have hz : (IL).toMsgL.pubsL = fun _ => 0 := by
      rw [ePL, lRP_off Rt prims χe hpc]; funext i; exact K3.toK_zero
    have htb := tbR_pad Rt prims hgen χe hpc (AluPoles.yOf deltaF (toχ χe))
    simp only [ComplJ9ALRun.SV, ComplJ9ALRun.SS, ComplJ9ALRun.SX, htb, GenPortJ9ALHLink.sumV_pad,
      GenPortJ9ALHLink.sumS_pad, GenPortJ9ALHLink.sumX_pad, hz, Quad.mk_zero']
    exact ⟨trivial, trivial, trivial⟩
  · -- branch (i): the executable sums are the honest sums over more padding rows
    have hsz := hszE Rt prims hgen χe h31L
    have hspec := GenPortJ9AHOrb.hOf_spec _ hsz
    have hlen := rowsB_len Rt prims hgen χe
    have htb := tbE_eqR Rt prims hgen χe
    have hlE : (TBR (AluPoles.yOf deltaF (toχ χe))).length ≤
        GenPortJ9ALHAluE.NE (pregsOf CS PS IDS) (callsLOf CS HM PS PC) := by
      rw [ComplJ9ALRun.tbR_length]; show ALEN ≤ 3 * _; rw [← hlen]; exact hspec.2.1
    have hlR : (TBR (AluPoles.yOf deltaF (toχ χe))).length ≤ NLR := by
      rw [ComplJ9ALRun.tbR_length]; show ALEN ≤ ALEN + 1; omega
    have e0 : (IL).toMsgL.pubsL = fun j => K3.toK (TE.2 j) := by rw [ePL, lRP_on Rt prims χe hpc]
    have sV := GenPortJ9ALHAluE.sumV_eq χe (pregsOf CS PS IDS) (callsLOf CS HM PS PC) (n := _) rfl
    have sS := GenPortJ9ALHAluE.sumS_eq χe (pregsOf CS PS IDS) (callsLOf CS HM PS PC) (n := _) rfl
    have sX := GenPortJ9ALHAluE.sumX_eq χe (pregsOf CS PS IDS) (callsLOf CS HM PS PC) (n := _) rfl
    rw [htb] at sV sS sX
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, GenPortJ9ALHAluE.aluGenE_snd]
      exact sV.trans (GenPortJ9ALHLink.sumV_stable deltaF _ _ hlE hlR)
    · rw [e0, GenPortJ9ALHAluE.aluGenE_snd]
      exact sS.trans (GenPortJ9ALHLink.sumS_stable deltaF _ _ hlE hlR)
    · rw [e0, GenPortJ9ALHAluE.aluGenE_snd]
      exact sX.trans (GenPortJ9ALHLink.sumX_stable deltaF _ _ hlE hlR)

/-- **`hALk` at the record, at any admissible orbit** (present branch when a primitive is called, absent otherwise). -/
theorem hALk_recL (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (h31L : ALEN < 2 ^ 31) (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 Rt hgen prims hpG h31A).Good (toχ χe))
    (o : OrbJ9AL) (ho : OrbAdmL (IL) o) (hv' : ValidJ9AL (withOrbL (IL) o)) :
    AcceptsJ9AL.ALChipOK deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv').aluOn
      (mkPbAL (withOrbL (IL) o) hv').prims (mkPbAL (withOrbL (IL) o) hv').hnL
      (mkPbAL (withOrbL (IL) o) hv').nodesL (mkPbAL (withOrbL (IL) o) hv').orbitL
      (mkPbAL (withOrbL (IL) o) hv').preL (chalsALJ8 deltaF (toχ (withOrbL (IL) o).χ))
      (withOrbL (IL) o).toMsgL.pubsL
      (RealIOJ9AL.qAL deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv') (withOrbL (IL) o).toTrL
        (chalsALJ8 deltaF (toχ (withOrbL (IL) o).χ)) (withOrbL (IL) o).toMsgL.pubsL) := by
  by_cases hpc : PC = []
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · show (IL).aluOn = false
      rw [IL_aluOn]; exact aluOn_false Rt prims χe hpc
    · show (IL).prims = []
      rw [IL_prims, if_neg (by rw [aluOn_false Rt prims χe hpc]; decide)]
    · have hz : (withOrbL (IL) o).toMsgL.pubsL = fun _ => 0 := by
        show (fun i => K3.toK ((lRPLK Rt prims s f χe RN).2 i)) = _
        rw [lRP_off Rt prims χe hpc]; funext i; exact K3.toK_zero
      rw [hz]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have h31 := ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A
    have hon := aluOn_true Rt prims χe hpc
    have hT := lRP_on Rt prims χe hpc
    have hfam := ComplJ9ALRun.goodAL_famAL deltaF powerBasis3 Rt hgen prims hpG h31A h31 hχ
    have hfull0 := (al_shape Rt prims hgen χe h31L).2.2.2 (by rw [IL_aluOn]; exact hon)
    have hL : (withOrbL (IL) o).AL = reorb (chipOf TE.1) o.AL := by
      rw [withOrbL_AL, IL_AL, hT]
    have hfull : (withOrbL (IL) o).AL.n = 3 * 2 ^ (withOrbL (IL) o).AL.h := by
      rw [withOrbL_AL]; show (IL).AL.n = 3 * 2 ^ o.AL.h; rw [ho.ALh]; exact hfull0
    exact GenPortJ9ALHAluE.alE_at (withOrbL (IL) o) hv' χe CS HM PS IDS PC VC MR
      (preg_eqR Rt prims χe)
      (fun q hq => hnoDec q (List.mem_filter.mp hq).1)
      (hblkE Rt prims hgen χe hpG h31 hnd hprim hnoDec hlimb)
      (hszE Rt prims hgen χe h31L) o.AL hL
      (by show (lRPLK Rt prims s f χe RN).2 = _; rw [hT])
      (by show aluOnLK Rt prims s f χe RN = true; exact hon)
      (by show (if aluOnLK Rt prims s f χe RN then PS else []) = PS; rw [if_pos hon])
      rfl hfull (hgoodE Rt prims hgen χe hfam _)

end Alu

/-! ## 2. Validity, admissibility and the budget of the record -/

section Rec
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen)) (χe : CoinsE)

local notation "IL" => recJ9ALXJ Rt prims s f χe t r
local notation "RN" => RnOf t r
local notation "BLL" => ComplJ9ALRun.B8L deltaF powerBasis3 Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)

include hpG h31A in
/-- **`ValidJ9AL` of the record** (L1's `validJ9AL_recJ9ALXJ` with the ALU chip's shape as `0 < n` and `OrbOK`). -/
theorem validJ9AL_recJ9ALXJ' (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (hnL : 0 < (IL).AL.n) (hoAL : OrbOK (IL).AL) : ValidJ9AL (IL) := by
  obtain ⟨sX, sC, sW, sJ, sA, sV, sAX, sSP⟩ :=
    GenPortJ9ALHMsgJ.sizes31L Rt prims hgen hpG h31A χe hwalk9 hax9 hwalkA
  have V := GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA
  refine
    { toValidJ9A := ValidJ9A.mk' (IL).toInJ9A ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩
      nL := hnL
      oAL := hoAL }
  · rw [toInJ9A_X Rt prims s f χe t r]; exact V.nX
  · rw [GenPortJ9ALHMsgJ.size_C_L Rt prims hgen hpG h31A χe]; exact (BLL).Pb.hnC
  · rw [toInJ9A_W Rt prims s f χe t r]; exact V.nW
  · rw [GenPortJ9ALHMsgJ.size_A_L Rt prims hgen hpG h31A χe]; exact (BLL).Pb.hnA
  · rw [toInJ9A_V Rt prims s f χe t r]; exact V.nV
  · rw [toInJ9A_X Rt prims s f χe t r]; exact V.oX
  · exact GenPortJ9AHMsgJ.orb_of_size _ rfl sC
  · rw [toInJ9A_W Rt prims s f χe t r]; exact V.oW
  · exact GenPortJ9AHMsgJ.orbOK_J (layLK Rt prims s f χe RN).length sJ _
  · exact GenPortJ9AHMsgJ.orb_of_size _ rfl sA
  · rw [toInJ9A_V Rt prims s f χe t r]; exact V.oV
  · rw [toInJ9A_AX Rt prims s f χe t r]; exact V.nAX
  · rw [toInJ9A_AX Rt prims s f χe t r]; exact V.oAX
  · rw [toInJ9A_SP Rt prims s f χe t r]; exact V.nSP
  · rw [toInJ9A_SP Rt prims s f χe t r]; exact V.oSP

include hpG h31A in
/-- **The record's own orbits are admissible** (the ALU chip's `n ≤ 3·2^h` given). -/
theorem orbAdmL_recJ9ALXJ' (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (hnL : 0 < (IL).AL.n) (hoAL : OrbOK (IL).AL) (hfit : (IL).AL.n ≤ 3 * 2 ^ (IL).AL.h) :
    OrbAdmL (IL) (orbOfL (IL)) := by
  obtain ⟨sX, sC, sW, sJ, sA, sV, sAX, sSP⟩ :=
    GenPortJ9ALHMsgJ.sizes31L Rt prims hgen hpG h31A χe hwalk9 hax9 hwalkA
  exact orbAdmL_self (validJ9AL_recJ9ALXJ' Rt prims hgen hpG h31A χe hwalk9 hax9 hwalkA hnL hoAL)
    (GenPortJ9AHMsgJ.fits_of_size _ rfl sX) (GenPortJ9AHMsgJ.fits_of_size _ rfl sC)
    (GenPortJ9AHMsgJ.fits_of_size _ rfl sW)
    (GenPortJ9AHOrb.hOf_spec (layLK Rt prims s f χe RN).length sJ).2.1
    (GenPortJ9AHMsgJ.fits_of_size _ rfl sA) (GenPortJ9AHMsgJ.fits_of_size _ rfl sV)
    (GenPortJ9AHMsgJ.fits_of_size _ rfl sAX) (GenPortJ9AHMsgJ.fits_of_size _ rfl sSP) hfit

/-- **The static budget hypotheses of the record** at `m = mLK`. -/
theorem staticHypJL_rec : GenPortJ9ALHStaticJ.StaticHypJL (IL) (mLK Rt prims s f χe RN) := by
  refine ⟨⟨GenPortJ9ALHLink.IL_r Rt prims s f χe t r, ?_, GenPortJ9ALHLink.IL_rAX Rt prims s f χe t r,
    GenPortJ9ALHLink.IL_rSP Rt prims s f χe t r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · rw [GenPortJ9ALHLink.IL_g, GenPortJ9ALHLink.IL_regs]
  · rw [GenPortJ9ALHLink.IL_J]; show (layLK Rt prims s f χe RN).length ≤ _; unfold mLK; omega
  · rw [toInJ9A_X]; show (compK Rt s f χe RN).rows.size ≤ _; unfold mLK; omega
  · rw [GenPortJ9ALHLink.IL_C]; show (cRPLK Rt prims s f χe RN).1.size ≤ _; unfold mLK; omega
  · rw [toInJ9A_W]; show (wRPK Rt s f χe RN).1.size ≤ _; unfold mLK; omega
  · rw [GenPortJ9ALHLink.IL_A]; show (aRPLK Rt prims s f χe RN).1.size ≤ _; unfold mLK; omega
  · rw [toInJ9A_V]; show (vRPK Rt s f χe RN).1.size ≤ _; unfold mLK; omega
  · rw [toInJ9A_AX]; show (xRPK Rt s f χe RN).1.size ≤ _; unfold mLK; omega
  · rw [toInJ9A_SP]; show (sRPK Rt s f χe RN).1.size ≤ _; unfold mLK; omega
  · show (lRPLK Rt prims s f χe RN).1.size ≤ _; unfold mLK; omega

end Rec

theorem staticHypJL_withOrbL [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC] {I : InJ9AL} {m : ℕ} (o : OrbJ9AL) (H : GenPortJ9ALHStaticJ.StaticHypJL I m) :
    GenPortJ9ALHStaticJ.StaticHypJL (withOrbL I o) m :=
  ⟨GenPortJ9AHLinkJ.staticHypJ_withOrb o.toA H.toStaticHypJ, H.hAL, H.sAL⟩

/-! ## 3. The core, at the global `Algebra Fp 𝕂′` instance -/

section Core
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt0 : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (χe : CoinsE)

local notation "IL" => recJ9ALXJ (rtP Rt0 prims) prims s f χe t r

theorem pbEqsL (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (o : OrbJ9AL) (hv' : ValidJ9AL (withOrbL (IL) o)) :
    ((mkPbAL (withOrbL (IL) o) hv').n =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.n) ∧
    ((mkPbAL (withOrbL (IL) o) hv').nC =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nC) ∧
    ((mkPbAL (withOrbL (IL) o) hv').nW =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nW) ∧
    ((mkPbAL (withOrbL (IL) o) hv').kroots =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.kroots) ∧
    ((mkPbAL (withOrbL (IL) o) hv').nA =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nA) ∧
    ((mkPbAL (withOrbL (IL) o) hv').nV =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nV) ∧
    ((mkPbAL (withOrbL (IL) o) hv').nX =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nX) ∧
    ((mkPbAL (withOrbL (IL) o) hv').nS =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nS) := by
  have h31 := ComplJ9ALRun.rows31L_of_A (rtP Rt0 prims) hgen prims h31A
  have ePb : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb =
      ComplJ9ALRun.PbL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A h31 := rfl
  have hn : (mkPbAL (withOrbL (IL) o) hv').n =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.n := by
    rw [ePb, ComplJ9ALRun.PbL_n]
    show (IL).toInJ9A.X.n = _
    rw [toInJ9A_X]; exact GenPortJ9AHMsgJ.size_X (rtP Rt0 prims) hgen hpG h31A χe
  have hnC : (mkPbAL (withOrbL (IL) o) hv').nC =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nC := by
    rw [ePb, ComplJ9ALRun.PbL_nC]
    exact GenPortJ9ALHMsgJ.size_C_L (rtP Rt0 prims) prims hgen hpG h31A χe
  have hnW : (mkPbAL (withOrbL (IL) o) hv').nW =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nW := by
    rw [ePb, ComplJ9ALRun.PbL_nW]
    show (IL).toInJ9A.W.n = _
    rw [toInJ9A_W]; exact GenPortJ9AHMsgJ.size_W (rtP Rt0 prims) hgen hpG h31A χe hwalk9
  have hkr : (mkPbAL (withOrbL (IL) o) hv').kroots =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.kroots := by
    rw [ePb]
    show (IL).toInJ9A.kroots = _
    rw [toInJ9A_kroots]; exact GenPortJ9AHMsgJ.size_kroots (rtP Rt0 prims) hgen hpG h31A χe hwalk9
  have hnA : (mkPbAL (withOrbL (IL) o) hv').nA =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nA := by
    rw [ePb, ComplJ9ALRun.PbL_nA]
    exact GenPortJ9ALHMsgJ.size_A_L (rtP Rt0 prims) prims hgen hpG h31A χe
  have hnV : (mkPbAL (withOrbL (IL) o) hv').nV =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nV := by
    rw [ePb, ComplJ9ALRun.PbL_nV]
    show (IL).toInJ9A.V.n = _
    rw [toInJ9A_V]; exact GenPortJ9AHMsgJ.size_V (rtP Rt0 prims) hgen hpG h31A χe hax9 hwalkA
  have hnX : (mkPbAL (withOrbL (IL) o) hv').nX =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nX := by
    rw [ePb, ComplJ9ALRun.PbL_nX]
    show (IL).toInJ9A.AX.n = _
    rw [toInJ9A_AX]; exact GenPortJ9AHMsgJ.size_AX (rtP Rt0 prims) hgen hpG h31A χe
  have hnS : (mkPbAL (withOrbL (IL) o) hv').nS =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.nS := by
    rw [ePb, ComplJ9ALRun.PbL_nS]
    show (IL).toInJ9A.SP.n = _
    rw [toInJ9A_SP]; exact GenPortJ9AHMsgJ.size_SP (rtP Rt0 prims) hgen hpG h31A χe
  exact ⟨hn, hnC, hnW, hkr, hnA, hnV, hnX, hnS⟩

theorem regEqsL (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (o : OrbJ9AL) (hv' : ValidJ9AL (withOrbL (IL) o)) :
    ((mkPbAL (withOrbL (IL) o) hv').regs =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.regs) ∧
    ((mkPbAL (withOrbL (IL) o) hv').ids =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.ids) ∧
    ((mkPbAL (withOrbL (IL) o) hv').idx =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.idx) ∧
    ((mkPbAL (withOrbL (IL) o) hv').rk =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.rk) ∧
    ((mkPbAL (withOrbL (IL) o) hv').Rt =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.Rt) ∧
    ((mkPbAL (withOrbL (IL) o) hv').prims =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.prims) ∧
    ((mkPbAL (withOrbL (IL) o) hv').idxP =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.idxP) ∧
    ((mkPbAL (withOrbL (IL) o) hv').rkP =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.rkP) := by
  have h31 := ComplJ9ALRun.rows31L_of_A (rtP Rt0 prims) hgen prims h31A
  have ePb : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb =
      ComplJ9ALRun.PbL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A h31 := rfl
  have hreg : (mkPbAL (withOrbL (IL) o) hv').regs =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.regs := by
    rw [ePb, ComplJ9ALRun.PbL_regs]
    show (IL).toInJ9A.regs = _
    rw [GenPortJ9ALHLink.IL_regs]; rfl
  have hids : (mkPbAL (withOrbL (IL) o) hv').ids =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.ids := by
    rw [ePb, ComplJ9ALRun.PbL_ids]
    show (IL).toInJ9A.ids = _
    rw [GenPortJ9ALHLink.IL_ids]; rfl
  have hidxE : (mkPbAL (withOrbL (IL) o) hv').idx =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.idx := by
    rw [ePb, ComplJ9ALRun.PbL_idx]
    show (IL).toInJ9A.idx = _
    rw [toInJ9A_idx]; rfl
  have hrkE : (mkPbAL (withOrbL (IL) o) hv').rk =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.rk := by
    rw [ePb, ComplJ9ALRun.PbL_rk]
    show (IL).toInJ9A.rk = _
    rw [toInJ9A_rk]; rfl
  have hRtE : (mkPbAL (withOrbL (IL) o) hv').Rt =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.Rt := by
    rw [ePb, ComplJ9ALRun.PbL_Rt]
    show (IL).toInJ9A.Rt = _
    rw [toInJ9A_Rt]; rfl
  have hpr : (mkPbAL (withOrbL (IL) o) hv').prims =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.prims := by
    rw [ePb, ComplJ9ALRun.PbL_prims]
    exact prims_eqR (rtP Rt0 prims) prims hgen χe
  have hix : (mkPbAL (withOrbL (IL) o) hv').idxP =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.idxP := by
    rw [ePb, ComplJ9ALRun.PbL_idxP]
    exact vc_eqR (rtP Rt0 prims) prims hgen χe
  have hrkP : (mkPbAL (withOrbL (IL) o) hv').rkP =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.rkP := by
    rw [ePb, ComplJ9ALRun.PbL_rkP]; rfl
  exact ⟨hreg, hids, hidxE, hrkE, hRtE, hpr, hix, hrkP⟩

theorem msgEqsL1 (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (o : OrbJ9AL) (hv' : ValidJ9AL (withOrbL (IL) o)) :
    ((withOrbL (IL) o).toMsgL.m =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).m) ∧
    ((withOrbL (IL) o).toMsgL.ρ =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).ρ) ∧
    ((withOrbL (IL) o).toMsgL.ρS =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).ρS) ∧
    ((withOrbL (IL) o).toMsgL.pubsC =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsC) ∧
    ((withOrbL (IL) o).toMsgL.pubsJ =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsJ) := by
  have h31 := ComplJ9ALRun.rows31L_of_A (rtP Rt0 prims) hgen prims h31A
  have hm : (withOrbL (IL) o).toMsgL.m =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).m :=
    ((congrArg (fun M => M.m) (withOrbL_toMsgL (IL) o)).trans (toMsgL_m (IL))).trans <|
    (GenPortJ9ALHLink.IL_toMsg_m (rtP Rt0 prims) prims s f χe t r).trans
      ((GenPortJ9AHMsgJ.msg_m (rtP Rt0 prims) hgen hpG h31A χe).trans
        (ComplJ9ALClosed.m_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm)
  have hρ : (withOrbL (IL) o).toMsgL.ρ =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).ρ :=
    ((congrArg (fun M => M.ρ) (withOrbL_toMsgL (IL) o)).trans (toMsgL_rho (IL))).trans <|
    (GenPortJ9ALHLink.IL_toMsg_rho (rtP Rt0 prims) prims s f χe t r).trans
      ((GenPortJ9AHMsgJ.msg_ρ (rtP Rt0 prims) hgen hpG h31A χe).trans
        ((congrArg (fun x => x.ρ) (ComplJ9ALClosed.mixM_eq deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe)
          hpG h31A)).trans (ComplJ9ALClosed.mixM_rho deltaF _ _ _)).symm)
  have hρS : (withOrbL (IL) o).toMsgL.ρS =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).ρS :=
    ((congrArg (fun M => M.ρS) (withOrbL_toMsgL (IL) o)).trans (toMsgL_rhoS (IL))).trans <|
    (GenPortJ9ALHLink.IL_toMsg_rhoS (rtP Rt0 prims) prims s f χe t r).trans
      ((GenPortJ9AHMsgJ.msg_ρS (rtP Rt0 prims) hgen hpG h31A χe).trans
        (ComplJ9ALClosed.rhoS_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm)
  have hMC : (withOrbL (IL) o).toMsgL.pubsC =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsC :=
    ((congrArg (fun M => M.pubsC) (withOrbL_toMsgL (IL) o)).trans (toMsgL_pubsC (IL))).trans <|
    (GenPortJ9ALHMsgJ.msg_pubsC_L (rtP Rt0 prims) prims hgen hpG h31A χe).trans
      (ComplJ9ALClosed.pubsC_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm
  have hMJ : (withOrbL (IL) o).toMsgL.pubsJ =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsJ :=
    ((congrArg (fun M => M.pubsJ) (withOrbL_toMsgL (IL) o)).trans (toMsgL_pubsJ (IL))).trans <|
    (GenPortJ9ALHMsgJ.msg_pubsJ_L (rtP Rt0 prims) prims hgen hpG h31A χe).trans
      (ComplJ9ALClosed.pubsJ_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm
  exact ⟨hm, hρ, hρS, hMC, hMJ⟩

theorem msgEqsL2 (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (o : OrbJ9AL) (hv' : ValidJ9AL (withOrbL (IL) o)) :
    ((withOrbL (IL) o).toMsgL.pubsA =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsA) ∧
    ((withOrbL (IL) o).toMsgL.pubsW =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsW) ∧
    ((withOrbL (IL) o).toMsgL.pubsV =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsV) ∧
    ((withOrbL (IL) o).toMsgL.pubsX =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsX) ∧
    ((withOrbL (IL) o).toMsgL.pubsS =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsS) := by
  have h31 := ComplJ9ALRun.rows31L_of_A (rtP Rt0 prims) hgen prims h31A
  have hMA : (withOrbL (IL) o).toMsgL.pubsA =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsA :=
    ((congrArg (fun M => M.pubsA) (withOrbL_toMsgL (IL) o)).trans (toMsgL_pubsA (IL))).trans <|
    (GenPortJ9ALHMsgJ.msg_pubsA_L (rtP Rt0 prims) prims hgen hpG h31A χe).trans
      (ComplJ9ALClosed.pubsA_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm
  have hMW : (withOrbL (IL) o).toMsgL.pubsW =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsW :=
    ((congrArg (fun M => M.pubsW) (withOrbL_toMsgL (IL) o)).trans (toMsgL_pubsW (IL))).trans <|
    (GenPortJ9ALHLink.IL_toMsg_pubsW (rtP Rt0 prims) prims s f χe t r).trans
      ((GenPortJ9AHMsgJ.msg_pubsW (rtP Rt0 prims) hgen hpG h31A χe hwalk9).trans
        (ComplJ9ALClosed.pubsW_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm)
  have hMV : (withOrbL (IL) o).toMsgL.pubsV =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsV :=
    ((congrArg (fun M => M.pubsV) (withOrbL_toMsgL (IL) o)).trans (toMsgL_pubsV (IL))).trans <|
    (GenPortJ9ALHLink.IL_toMsg_pubsV (rtP Rt0 prims) prims s f χe t r).trans
      ((GenPortJ9AHMsgJ.msg_pubsV (rtP Rt0 prims) hgen hpG h31A χe hax9 hwalkA).trans
        (ComplJ9ALClosed.pubsV_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm)
  have hMX : (withOrbL (IL) o).toMsgL.pubsX =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsX :=
    ((congrArg (fun M => M.pubsX) (withOrbL_toMsgL (IL) o)).trans (toMsgL_pubsX (IL))).trans <|
    (GenPortJ9ALHLink.IL_toMsg_pubsX (rtP Rt0 prims) prims s f χe t r).trans
      ((GenPortJ9AHMsgJ.msg_pubsX (rtP Rt0 prims) hgen hpG h31A χe).trans
        (ComplJ9ALClosed.pubsXX_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm)
  have hMS : (withOrbL (IL) o).toMsgL.pubsS =
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe)).pubsS :=
    ((congrArg (fun M => M.pubsS) (withOrbL_toMsgL (IL) o)).trans (toMsgL_pubsS (IL))).trans <|
    (GenPortJ9ALHLink.IL_toMsg_pubsS (rtP Rt0 prims) prims s f χe t r).trans
      ((GenPortJ9AHMsgJ.msg_pubsS (rtP Rt0 prims) hgen hpG h31A χe).trans
        (ComplJ9ALClosed.pubsS_eqL deltaF powerBasis3 (rtP Rt0 prims) hgen prims (toχ χe) hpG h31A).symm)
  exact ⟨hMA, hMW, hMV, hMX, hMS⟩

theorem lenL (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (o : OrbJ9AL) (hv' : ValidJ9AL (withOrbL (IL) o))
    (hnd : (prims.map Prod.fst).Nodup)
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31) :
    ((mkPbAL (withOrbL (IL) o) hv').nL + (mkPbAL (withOrbL (IL) o) hv').n < P) ∧ (3 + (mkPbAL (withOrbL (IL) o) hv').regs.length + (mkPbAL (withOrbL (IL) o) hv').prims.length +
      (mkPbAL (withOrbL (IL) o) hv').nL + 2 * (mkPbAL (withOrbL (IL) o) hv').nC < P) := by
  have h31 := ComplJ9ALRun.rows31L_of_A (rtP Rt0 prims) hgen prims h31A
  obtain ⟨hnL, hoAL, hAL34, -⟩ := al_shape (rtP Rt0 prims) prims hgen χe h31L
  have ePb : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb =
      ComplJ9ALRun.PbL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A h31 := rfl
  have hn : (mkPbAL (withOrbL (IL) o) hv').n =
      (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.n := by
    rw [ePb, ComplJ9ALRun.PbL_n]
    show (IL).toInJ9A.X.n = _
    rw [toInJ9A_X]; exact GenPortJ9AHMsgJ.size_X (rtP Rt0 prims) hgen hpG h31A χe
  have hlen := GenPortJ9ALHLink.lengthsX (rtP Rt0 prims) hgen prims hpG h31 hnd (IL).AL.n (by omega)
  have hn9 : (mkPbAL (withOrbL (IL) o) hv').n = ComplJ9ARun.N9 t := by
    rw [hn, ePb, ComplJ9ALRun.PbL_n]; rfl
  have hlenL1 : (mkPbAL (withOrbL (IL) o) hv').nL + (mkPbAL (withOrbL (IL) o) hv').n < P := by
    rw [hn9]; exact hlen.1
  have hlenCP : 3 + (mkPbAL (withOrbL (IL) o) hv').regs.length + (mkPbAL (withOrbL (IL) o) hv').prims.length +
      (mkPbAL (withOrbL (IL) o) hv').nL + 2 * (mkPbAL (withOrbL (IL) o) hv').nC < P := by
    have e1 : (mkPbAL (withOrbL (IL) o) hv').regs = (j9alDataOf P Rg (rtP Rt0 prims) prims hgen).regs := by
      show (IL).toInJ9A.regs = _; rw [GenPortJ9ALHLink.IL_regs]; rfl
    have e2 : (mkPbAL (withOrbL (IL) o) hv').prims = ComplJ9ALRun.psRun (p := P) (rtP Rt0 prims) hgen prims :=
      prims_eqR (rtP Rt0 prims) prims hgen χe
    have e3 : (mkPbAL (withOrbL (IL) o) hv').nC = (j9alDataOf P Rg (rtP Rt0 prims) prims hgen).cells.length :=
      GenPortJ9ALHMsgJ.n_C_L (rtP Rt0 prims) prims hgen χe
    have e4 : (mkPbAL (withOrbL (IL) o) hv').nL = (IL).AL.n := rfl
    rw [e1, e2, e3, e4]; exact hlen.2
  exact ⟨hlenL1, hlenCP⟩

theorem nonChip_recL (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (o : OrbJ9AL) (hv' : ValidJ9AL (withOrbL (IL) o))
    (hnd : (prims.map Prod.fst).Nodup)
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31)
    (NC0 : GenPortJ9ALHNonChip.NonChipJ9AL deltaF powerBasis3 (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb Rg.R (ComplJ8.cJ s f r) (toχ χe)
      ((ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).M (toχ χe))) :
    GenPortJ9ALHNonChip.NonChipJ9AL deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv') Rg.R
      (withOrbL (IL) o).c (toχ (withOrbL (IL) o).χ) (withOrbL (IL) o).toMsgL := by
  obtain ⟨hn, hnC, hnW, hkr, hnA, hnV, hnX, hnS⟩ := pbEqsL Rt0 prims hgen χe hpG hax9 hwalk9 hwalkA h31A o hv'
  obtain ⟨hreg, hids, hidxE, hrkE, hRtE, hpr, hix, hrkP⟩ := regEqsL Rt0 prims hgen χe hpG hax9 hwalk9 hwalkA h31A o hv'
  obtain ⟨hm, hρ, hρS, hMC, hMJ⟩ := msgEqsL1 Rt0 prims hgen χe hpG hax9 hwalk9 hwalkA h31A o hv'
  obtain ⟨hMA, hMW, hMV, hMX, hMS⟩ := msgEqsL2 Rt0 prims hgen χe hpG hax9 hwalk9 hwalkA h31A o hv'
  obtain ⟨hlenL1, hlenCP⟩ := lenL Rt0 prims hgen χe hpG hax9 hwalk9 hwalkA h31A o hv' hnd h31L
  have hlayE : List.ofFn (mkPbAL (withOrbL (IL) o) hv').lay =
      List.ofFn (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Pb.lay := by
    rw [NC0.hlay, ← hRtE, ← hreg, ← hids]
    exact GenPortJ9ALHMsgJ.lay_eqL (rtP Rt0 prims) prims hgen χe
  obtain ⟨hLv, hLs, hLx⟩ := pubsL_eqR (rtP Rt0 prims) prims hgen χe hpG h31A h31L
  have NC : GenPortJ9ALHNonChip.NonChipJ9AL deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv') Rg.R
      (withOrbL (IL) o).c (toχ (withOrbL (IL) o).χ) (withOrbL (IL) o).toMsgL := by
    show GenPortJ9ALHNonChip.NonChipJ9AL deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv') Rg.R
      (ComplJ8.cJ s f r) (toχ χe) (withOrbL (IL) o).toMsgL
    exact GenPortJ9ALHLink.nonChip_transportJL deltaF powerBasis3 NC0 hn hnC hnW hkr hnA hnV hnX hnS
      hreg hids hidxE hrkE hRtE hlayE hpr hix hrkP hlenL1 hlenCP hm hρ hρS hMC hMW hMJ hMA hMV hMX hMS hLv hLs hLx
  exact NC

/-- **`honest_rec_atJL`: honest acceptance of the J-9 AL record at any admissible orbit.**
For a generated run `hgen` at the Goldilocks prime (with ALU and primitives `prims`), under the J-9 A axis,
op-5, leaf and walk-depth conditions, the registry condition `CompiledByP` with distinct primitive ids, every table
of at most `2^31` rows (ALU length `< 2^31`), primitive operands within 62 limbs and no decrement primitive: at every
good coin `χe`, and for every admissible per-chip orbit `o`, the record `recJ9ALXJ` with orbit `o` is valid
(`ValidJ9AL`) and `AcceptsJ9AL` accepts it. -/
theorem honest_rec_atJL (hpG : P = Nock.Atoms.p) (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Good (toχ χe))
    (o : OrbJ9AL) (ho : OrbAdmL (IL) o) :
    ∃ hv : ValidJ9AL (withOrbL (IL) o),
      AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv) Rg.R (withOrbL (IL) o).c
        (toχ (withOrbL (IL) o).χ) (withOrbL (IL) o).toMsgL (withOrbL (IL) o).toTrL (withOrbL (IL) o).toRowsL
        (withOrbL (IL) o).g := by
  -- the honest record and its acceptance
  have hcl := ComplJ9ALClosed.complJ9AL_closed_of deltaF powerBasis3 Rt0 hgen prims hpG hax9 hop5 hleaf hwalk9
    hwalkA hC hnd h31A h31L hlimb hnoDec
  have AH := hcl.1 (toχ χe) hχ
  have NC0 := GenPortJ9ALHNonChip.nonChip_of_acceptsL deltaF powerBasis3 AH
  obtain ⟨hRt, hregAx, hprim⟩ := CheckedRegistryP.hRt_hregAx_ofP hC hgen
  have hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨((rtP Rt0 prims) id).toTemplate P, Nock.Jet.Autogen.compile P ((rtP Rt0 prims) id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB ((rtP Rt0 prims) id) = true ∧ ((rtP Rt0 prims) id).WellTyped P := by
    intro id hid hn
    rw [ComplJ9ALData.rtP_of_not_mem Rt0 prims hn]
    exact hRt id hid hn
  have h31 := ComplJ9ALRun.rows31L_of_A (rtP Rt0 prims) hgen prims h31A
  have hχA := ComplJ9ALClosed.gBA_of deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A (toχ χe) hχ
  have hχ8 := ComplJ9ALClosed.gL_of deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A (toχ χe) hχ
  have L := GenPortJ9AHLinkJ.execLink_recJ9AXJ (rtP Rt0 prims) hgen hpG h31A hax9 hwalk9 hwalkA χe
  -- the ALU chip's shape and validity
  obtain ⟨hnL, hoAL, hAL34, -⟩ := al_shape (rtP Rt0 prims) prims hgen χe h31L
  have hv := validJ9AL_recJ9ALXJ' (rtP Rt0 prims) prims hgen hpG h31A χe hwalk9 hax9 hwalkA hnL hoAL
  have hv' : ValidJ9AL (withOrbL (IL) o) := validJ9AL_withOrbL hv ho
  refine ⟨hv', ?_⟩
  have hvA : ValidJ9A (withOrb (IL).toInJ9A o.toA) := hv'.toValidJ9A
  have NC := nonChip_recL Rt0 prims hgen χe hpG hax9 hwalk9 hwalkA h31A o hv' hnd h31L NC0
  -- nodes
  obtain ⟨⟨⟨hinjX, hadjX⟩, ⟨hinjC, hadjC⟩, ⟨hinjW, hadjW⟩, ⟨hinjA, hadjA⟩⟩, -⟩ := nodes_withOrbL ho hv'
  -- budgets
  have H := staticHypJL_withOrbL o (staticHypJL_rec (rtP Rt0 prims) prims (s := s) (f := f) (t := t) (r := r) χe)
  have hb := GenPortJ9ALHStaticJ.budJ9AL_staticJ (withOrbL (IL) o) hv' _ H
  have hbV := GenPortJ9ALHStaticJ.hbudV_staticJL (withOrbL (IL) o) hv' _ H
  have eB : (withOrbL (IL) o).g + (withOrbL (IL) o).toRowsL.N =
      (withOrbL (IL) o).g + max 10 (2 * mLK (rtP Rt0 prims) prims s f χe (RnOf t r)) := by
    show (withOrbL (IL) o).g + (withOrbL (IL) o).r.N = _
    rw [H.hr]; rfl
  -- chips
  have IA_χ : (IL).toInJ9A.χ = χe := (toInJ9A_χ (rtP Rt0 prims) prims s f χe t r).trans L.hχI
  have cell := GenPortJ9ALHCellE.cellE_atL (rtP Rt0 prims) prims hgen hpG h31A hleaf χe (IL).toInJ9A
    ((GenPortJ9ALHLink.IL_C (rtP Rt0 prims) prims s f χe t r).trans
      (congrArg (fun x => chipOf x.1) (GenPortJ9ALHMsgJ.cRPLK_eqL (rtP Rt0 prims) prims hgen χe)))
    ((GenPortJ9ALHLink.IL_pubsC (rtP Rt0 prims) prims s f χe t r).trans
      (congrArg Prod.snd (GenPortJ9ALHMsgJ.cRPLK_eqL (rtP Rt0 prims) prims hgen χe)))
    o.toA ho.toA hvA hχ8
  have atom := GenPortJ9ALHAtomE.atomE_atL (rtP Rt0 prims) prims hgen hpG h31A χe (IL).toInJ9A
    ((GenPortJ9ALHLink.IL_A (rtP Rt0 prims) prims s f χe t r).trans
      (congrArg (fun x => chipOf x.1) (GenPortJ9ALHMsgJ.aRPLK_eqL (rtP Rt0 prims) prims hgen χe)))
    ((GenPortJ9ALHLink.IL_pubsA (rtP Rt0 prims) prims s f χe t r).trans
      (congrArg Prod.snd (GenPortJ9ALHMsgJ.aRPLK_eqL (rtP Rt0 prims) prims hgen χe)))
    o.toA ho.toA hvA hχ8
  have walk := GenPortJ9AHWalkE.walkE_at (rtP Rt0 prims) hgen hwalk9 hpG h31A χe (IL).toInJ9A
    ((toInJ9A_W (rtP Rt0 prims) prims s f χe t r).trans L.hW)
    ((toInJ9A_pubsW (rtP Rt0 prims) prims s f χe t r).trans L.hpW)
    ((toInJ9A_kroots (rtP Rt0 prims) prims s f χe t r).trans L.hkr) o.toA ho.toA hvA hχA
  have jchip := GenPortJ9ALHOrbJ.j_atL (rtP Rt0 prims) prims hgen hpG h31A hRtJ (IL).toInJ9A
    ((GenPortJ9ALHMsgJ.lay_eqL (rtP Rt0 prims) prims hgen χe).trans
      (ComplJ9ALData.jrows_preL (p := P) (rtP Rt0 prims) prims hgen).symm)
    (fun j i _ => by
      rw [cols_of_eqJ _ (GenPortJ9ALHLink.IL_J (rtP Rt0 prims) prims s f χe t r) j i, IA_χ]; rfl)
    ((GenPortJ9ALHLink.IL_pubsJ (rtP Rt0 prims) prims s f χe t r).trans (by rw [IA_χ]; rfl)) o.toA ho.toA hvA hχ8
  exact
    { hsatX := GenPortJ9AHXASE.hsatXE_at (rtP Rt0 prims) hgen hpG h31A hax9 hop5 χe (IL).toInJ9A
        ((toInJ9A_c (rtP Rt0 prims) prims s f χe t r).trans L.hc) IA_χ
        ((toInJ9A_X (rtP Rt0 prims) prims s f χe t r).trans L.hX)
        ((GenPortJ9ALHLink.IL_toMsg_m (rtP Rt0 prims) prims s f χe t r).trans L.hm)
        ((GenPortJ9ALHLink.IL_toMsg_rho (rtP Rt0 prims) prims s f χe t r).trans L.hρ)
        ((GenPortJ9ALHLink.IL_toMsg_rhoS (rtP Rt0 prims) prims s f χe t r).trans L.hρS)
        o.toA ho.toA hvA hχA
      hinjX := hinjX
      hadjX := hadjX
      hsatC := cell.1
      hbindC := cell.2
      hinjC := hinjC
      hadjC := hadjC
      hnpC := NC.hnpC
      hsatW := walk.1
      hbindW := walk.2
      hinjW := hinjW
      hadjW := hadjW
      hkW := NC.hkW
      hknW := NC.hknW
      hkpW := NC.hkpW
      hJk := jchip
      hsatA := atom.1.1
      hbindA := atom.1.2
      hinjA := hinjA
      hadjA := hadjA
      hnpA := NC.hnpA
      hVk := GenPortJ9AHAWE.awE_at (rtP Rt0 prims) hgen hax9 hwalkA hpG h31A χe (IL).toInJ9A IA_χ
        (fun h => ⟨(toInJ9A_V (rtP Rt0 prims) prims s f χe t r).trans (L.hVon h).1,
          (toInJ9A_pubsV (rtP Rt0 prims) prims s f χe t r).trans (L.hVon h).2⟩)
        (fun h => ⟨(toInJ9A_V (rtP Rt0 prims) prims s f χe t r).trans (L.hVoff h).1,
          (toInJ9A_pubsV (rtP Rt0 prims) prims s f χe t r).trans (L.hVoff h).2⟩)
        ((toInJ9A_krootsV (rtP Rt0 prims) prims s f χe t r).trans L.hkrV) o.toA ho.toA hvA hχA
      hGx := NC.hGx
      hGp := NC.hGp
      hGS := NC.hGS
      hlay := NC.hlay
      hsmall := NC.hsmall
      huniq := NC.huniq
      hTpl := NC.hTpl
      hnd := NC.hnd
      hidx := NC.hidx
      hrk := NC.hrk
      hlt := NC.hlt
      hsumC' := NC.hsumC'
      hbalA' := NC.hbalA'
      hvalA0 := NC.hvalA0
      hfxC := NC.hfxC
      hfxA := NC.hfxA
      hclI := NC.hclI
      hclR := NC.hclR
      hcen' := NC.hcen'
      hlenC := NC.hlenC
      hlenA := NC.hlenA
      hcellF := NC.hcellF
      hnAS := NC.hnAS
      hbud := by rw [eB]; exact hb
      hbudV := ⟨hbV.1, hbV.2.1, hbV.2.2.1, hbV.2.2.2.1, hbV.2.2.2.2.1, hbV.2.2.2.2.2.1⟩
      hsatL := atom.2.1
      hbindL := atom.2.2
      hAXk := GenPortJ9AHXASE.hAXkE_at (rtP Rt0 prims) hgen hpG h31A χe (IL).toInJ9A IA_χ
        ((toInJ9A_AX (rtP Rt0 prims) prims s f χe t r).trans L.hAX)
        ((toInJ9A_pubsX (rtP Rt0 prims) prims s f χe t r).trans L.hpX)
        ((toInJ9A_axOn (rtP Rt0 prims) prims s f χe t r).trans L.haxOn)
        ((congrArg ChipIn.n (toInJ9A_AX (rtP Rt0 prims) prims s f χe t r)).trans L.hszAX)
        o.toA ho.toA hvA hχA
      hSPk := GenPortJ9AHXASE.hSPkE_at (rtP Rt0 prims) hgen hpG h31A hax9 χe (IL).toInJ9A IA_χ
        (fun h => ⟨(toInJ9A_SP (rtP Rt0 prims) prims s f χe t r).trans (L.hSPon h).1,
          (toInJ9A_pubsS (rtP Rt0 prims) prims s f χe t r).trans (L.hSPon h).2⟩)
        (fun h => (toInJ9A_pubsS (rtP Rt0 prims) prims s f χe t r).trans (L.hSPoff h))
        ((toInJ9A_spOn (rtP Rt0 prims) prims s f χe t r).trans L.hspOn)
        ((congrArg ChipIn.n (toInJ9A_SP (rtP Rt0 prims) prims s f χe t r)).trans L.hszSP)
        (GenPortJ9ALHMsgJ.n_A_L (rtP Rt0 prims) prims hgen χe)
        o.toA ho.toA hvA hχA
      hlenX := NC.hlenX
      hALk := hALk_recL (rtP Rt0 prims) prims hgen χe hpG h31A h31L hnd hprim hnoDec hlimb hχ o ho hv'
      hPrim := NC.hPrim
      hdisjP := NC.hdisjP
      hlenL := ⟨NC.hlenL.1, hbV.2.2.2.2.2.2, NC.hlenL.2⟩
      hndP := NC.hndP
      hrkP := NC.hrkP
      hltP := NC.hltP
      hlenCP := NC.hlenCP }

end Core

/-! ## 4. The deliverables -/

section Final
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  [iA : Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod P) KC deltaF))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`genJ9ALXJ_honest_at`: every output of the J-9 AL input generator is valid and accepted, at every admissible
orbit.**  Under the hypotheses of `complJ9AL_closed_of` (Goldilocks prime, J-9 A axis, op-5, leaf and walk-depth
conditions, `CompiledByP` with distinct primitive ids, every table of at most `2^31` rows (ALU length `< 2^31`), primitive operands within 62
limbs, no decrement primitive), if `genJ9ALXJ` produces the input `I` at a good coin `χe`, then for every
admissible per-chip orbit `o`, the input `I` with orbit `o` is valid (`ValidJ9AL`) and `AcceptsJ9AL` accepts it. -/
theorem genJ9ALXJ_honest_at (hpG : P = Nock.Atoms.p) {Rt0 : ℕ → Nock.Jet.Autogen.Tpl} {prims : List (ℕ × PrimOp)}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    {χe : CoinsE} {I : InJ9AL}
    (hI : Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ Rg.R (rtP Rt0 prims) prims fuel s f χe = some I)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Good (toχ χe))
    (o : OrbJ9AL) (ho : OrbAdmL I o) :
    ∃ hv : ValidJ9AL (withOrbL I o),
      AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL I o) hv) Rg.R (withOrbL I o).c
        (toχ (withOrbL I o).χ) (withOrbL I o).toMsgL (withOrbL I o).toTrL (withOrbL I o).toRowsL
        (withOrbL I o).g := by
  obtain ⟨t', r', hgen', hIeq⟩ := genJ9ALXJ_some hI
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj (hgen'.symm.trans hgen))
  rw [h1, h2] at hIeq
  subst hIeq
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact honest_rec_atJL Rt0 prims hgen χe hpG hax9 hop5 hleaf hwalk9 hwalkA hC hnd h31A h31L hlimb hnoDec hχ o ho

/-- **`genJ9ALXJ_honest`: every output of the J-9 AL input generator is valid and accepted at its own orbit.**
Under the same hypotheses as `genJ9ALXJ_honest_at` (Goldilocks prime, J-9 A axis, op-5, leaf and walk-depth
conditions, `CompiledByP` with distinct primitive ids, every table of at most `2^31` rows (ALU length `< 2^31`), primitive operands within 62
limbs, no decrement primitive, a good coin `χe`), if `genJ9ALXJ` produces `I` then `I` is valid (`ValidJ9AL`) and
`AcceptsJ9AL` accepts it with the orbit the generator itself chose. -/
theorem genJ9ALXJ_honest (hpG : P = Nock.Atoms.p) {Rt0 : ℕ → Nock.Jet.Autogen.Tpl} {prims : List (ℕ × PrimOp)}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    {χe : CoinsE} {I : InJ9AL}
    (hI : Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ Rg.R (rtP Rt0 prims) prims fuel s f χe = some I)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Good (toχ χe)) :
    ∃ hv : ValidJ9AL I,
      AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL I hv) Rg.R I.c (toχ I.χ) I.toMsgL I.toTrL I.toRowsL I.g := by
  obtain ⟨t', r', hgen', hIeq⟩ := genJ9ALXJ_some hI
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj (hgen'.symm.trans hgen))
  rw [h1, h2] at hIeq
  subst hIeq
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  obtain ⟨hnL, hoAL, -, hfullOn⟩ := al_shape (rtP Rt0 prims) prims hgen χe h31L
  have hfit : (recJ9ALXJ (rtP Rt0 prims) prims s f χe t r).AL.n ≤
      3 * 2 ^ (recJ9ALXJ (rtP Rt0 prims) prims s f χe t r).AL.h := by
    by_cases hon : (recJ9ALXJ (rtP Rt0 prims) prims s f χe t r).aluOn = true
    · exact (hfullOn hon).le
    · have hpc : pcLK (rtP Rt0 prims) prims s f χe (RnOf t r) = [] := by
        by_contra hpc
        exact hon (by rw [GenPortJ9ALHLink.IL_aluOn]; exact aluOn_true (rtP Rt0 prims) prims χe hpc)
      have e : (recJ9ALXJ (rtP Rt0 prims) prims s f χe t r).AL = chipOf zeroChip.1 := by
        rw [GenPortJ9ALHLink.IL_AL, lRP_off (rtP Rt0 prims) prims χe hpc]
      rw [e]; exact GenPortJ9AHMsgJ.fits_of_size _ rfl (by show 1 ≤ 2 ^ 31; norm_num)
  have h := honest_rec_atJL Rt0 prims hgen χe hpG hax9 hop5 hleaf hwalk9 hwalkA hC hnd h31A h31L hlimb hnoDec hχ _
    (orbAdmL_recJ9ALXJ' (rtP Rt0 prims) prims hgen hpG h31A χe hwalk9 hax9 hwalkA hnL hoAL hfit)
  rw [withOrbL_self] at h
  exact h

/-- **`checkJ9ALX_genJ9ALXJ`: the executable J-9 AL checker accepts every generated input.**
Under the same hypotheses as `genJ9ALXJ_honest` (Goldilocks prime, J-9 A axis, op-5, leaf and walk-depth
conditions, `CompiledByP` with distinct primitive ids, every table of at most `2^31` rows (ALU length `< 2^31`), primitive operands within 62
limbs, no decrement primitive, a good coin `χe`), if `genJ9ALXJ` produces `I` then `checkJ9ALX I = true`. -/
theorem checkJ9ALX_genJ9ALXJ (hpG : P = Nock.Atoms.p) {Rt0 : ℕ → Nock.Jet.Autogen.Tpl}
    {prims : List (ℕ × PrimOp)}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    {χe : CoinsE} {I : InJ9AL}
    (hI : Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ Rg.R (rtP Rt0 prims) prims fuel s f χe = some I)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Good (toχ χe)) :
    checkJ9ALX I = true := by
  have hprimI : ∀ q ∈ I.prims, Rg.R q.1 = some (primSpec q.2) := by
    obtain ⟨t', r', -, rfl⟩ := genJ9ALXJ_some hI
    intro q hq
    rw [GenPortJ9ALHLink.IL_prims] at hq
    split_ifs at hq
    · exact hC.2 q (List.mem_filter.mp hq).1
    · simp at hq
  exact (checkJ9ALX_iff I Rg.R (GenPortJ9ALHMsgJ.regOK_genJ9ALXJ hC hI) hprimI).mpr
    (genJ9ALXJ_honest hgen hpG hax9 hop5 hleaf hwalk9 hwalkA hC hnd h31A h31L hlimb hnoDec hI hχ)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ

section Axioms
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.honest_rec_atJL
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.genJ9ALXJ_honest_at
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.genJ9ALXJ_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.checkJ9ALX_genJ9ALXJ
end Axioms
