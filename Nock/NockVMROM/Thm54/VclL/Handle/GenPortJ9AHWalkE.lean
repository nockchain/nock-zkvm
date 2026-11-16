/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHWalkE.lean

  **The walk chip port at an abstract record `I`** (jet-calling runs).
  No `hnc`: the exec walk table enters only through the link hypotheses `hW hpW hkr` (RHS copied from
  `GenPortJ9AHWalkRun.wRPJ_eq` / `recJ9AX_kroots'`). Twins of `GenPortJ9AHWalkRun` §2 and `GenPortJ9AHOrbWalk` Run. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkE

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell (interp_cast)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkGlue
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPubs
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalk
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf cellsA_pos readsA)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qW)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk (walk_abs n_reorb cols_reorb)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRun (regD nodes_cast cols_via)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
  (hall_DAJ hwalk_DAJ hp_DRJ hwcell_DRJ hwroot_DRJ hcs_DAJ powN_inj_DRJ pubs_DR_DAJ)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff

noncomputable section

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
include hwalk9

local notation "DA" => j9aDataOf P Rg Rt hgen
local notation "DR" => regD (j9aDataOf P Rg Rt hgen)

/-! ## 1. Shape facts -/

theorem walkE_n' (χe : CoinsE) (I : InJ9A) (hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).1) :
    I.W.n = (walkRows (DR).cells (DR).reads).length := by
  rw [hW]
  show (walkGenRowsB _ _ _ _ _ _ _ _ _ _).1.size = _
  rw [walkGenRowsB_size, List.length_map]

theorem walkE_n (χe : CoinsE) (I : InJ9A) (hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).1) :
    I.W.n = (walkRows (DA).cells (DA).reads).length :=
  (walkE_n' Rt hgen hwalk9 χe I hW).trans (hp_DRJ Rt hgen).length_eq

theorem walkE_kroots (I : InJ9A) (hkr : I.kroots = krW (DR).cells (DR).reads) :
    I.kroots = krW (DA).cells (DA).reads :=
  hkr.trans (krW_regroup _ _ (hall_DAJ Rt hgen))

theorem walkE_cols (χe : CoinsE) (I : InJ9A) (hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).1)
    {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length))
    (i : Fin I.W.n) (c : ℕ) (hc : c < 166) :
    I.W.cols c i =
      fullCol (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (HonestK8.certUp
          (ComplJ8Enc.wColHQBE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
            (ComplJ8Of.powN o _) o (VerJ8.chalsMJ8 deltaF (toχ χe))
            (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o (toχ χe)) (ComplJ8Of.encR deltaF (toχ χe))
            (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) (DR).cells (DR).reads
            (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR)))
          (ComplJ8Walk.lenB (DR).cells (DR).reads)) c
        (Fin.cast (walkE_n' Rt hgen hwalk9 χe I hW) i) := by
  have hcg := walkGenRowsB_cols χe (DR) (hcs_DAJ Rt hgen χe)
    (hwcell_DRJ Rt hgen) (hwroot_DRJ Rt hgen)
    (fun x hx => hall_DAJ Rt hgen x ((mem_regroup _ x).mp hx))
    (walkDepthOK_regroup _ (hwalk_DAJ Rt hgen hwalk9)) o hinj
    (Fin.cast (walkE_n' Rt hgen hwalk9 χe I hW) i) c hc
  rw [Fin.val_cast] at hcg
  exact cols_via _ _ hW i c _ hcg

theorem walkE_pubs (χe : CoinsE) (I : InJ9A) (hpW : I.M.pubsW = (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).2)
    (hF : ComplJ8Of.DvdOK (DA)) (j : ℕ) :
    K3.toK (I.M.pubsW j) =
      ComplJ8Of.pubsWOf deltaF powerBasis3 (DA) (ComplJ8Of.orbJ8 (DA) hF) (toχ χe) j := by
  have e1 := walkGenRowsB_pubs χe (DR) (hcs_DAJ Rt hgen χe) (hwcell_DRJ Rt hgen) (hwroot_DRJ Rt hgen)
    (ComplJ8Of.orbJ8 (DA) hF) (powN_inj_DRJ Rt hgen hF) j
  rw [hpW]
  exact e1.trans (pubs_DR_DAJ Rt hgen χe hF j)

/-- `nodesOf I.W` at `DR`'s row count is `powN` at the chip's own orbit, and injectivity transfers. -/
theorem powN_inj_chipE (χe : CoinsE) (I : InJ9A) (hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).1) (ho : OrbOK I.W)
    (hinj : Function.Injective (nodesOf I.W)) :
    Function.Injective (ComplJ8Of.powN (mkOrbit I.W ho) (walkRows (DR).cells (DR).reads).length) := by
  have hI : Function.Injective
      (nodesOf I.W ∘ Fin.cast (walkE_n' Rt hgen hwalk9 χe I hW).symm) :=
    hinj.comp (Fin.cast_injective _)
  rw [nodes_cast _ ho (walkE_n' Rt hgen hwalk9 χe I hW)] at hI
  exact hI

theorem walkE_interp (χe : CoinsE) (I : InJ9A) (hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).1) (ho : OrbOK I.W)
    (hinj : Function.Injective (nodesOf I.W)) (j : ℕ) (hj : j < 166) :
    interpOf I.W j =
      ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit I.W ho) (walkRows (DR).cells (DR).reads).length)
        (mkOrbit I.W ho) (VerJ8.chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit I.W ho))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) ⟨j, hj⟩ := by
  have hn := walkE_n' Rt hgen hwalk9 χe I hW
  have hinj' := powN_inj_chipE Rt hgen hwalk9 χe I hW ho hinj
  unfold interpOf
  rw [interp_cast hn, nodes_cast _ ho hn]
  unfold ComplJ8Enc.walkTrWE honestQ
  refine congrArg (Lagrange.interpolate Finset.univ
    (ComplJ8Of.powN (mkOrbit I.W ho) (walkRows (DR).cells (DR).reads).length)) ?_
  funext i'
  exact walkE_cols Rt hgen hwalk9 χe I hW (mkOrbit I.W ho) hinj'
    (Fin.cast hn.symm i') j hj


/-! ## 2. The walk chip obligation (DA-only) -/

/-- **The walk chip obligation at `regD DA`**, any admissible orbit `o` (instantiate at `mkOrbit I.W ho` with
`powN_inj_chip`), families taken at `DA` (`BRun9A`'s good event). -/
theorem walkE_ok (hp63 : 2 ^ 63 < P) (h31A : ComplJ9ARun.Rows31A (DA))
    {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length))
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC)
    (hV : ∀ e ∈ ComplJ8Of.famWalkV deltaF (DA) (K := KC), χ ∉ e.ev)
    (hH : ∀ e ∈ ComplJ8Of.famWalkH deltaF (DA) (K := KC), χ ∉ e.ev) :
    (WalkJ8.walkChipJ8 deltaF (krW (DR).cells (DR).reads) powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF χ)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o χ)).rap.Satisfies
      (fun j => ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o) (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF)
        (ComplJ8Of.encR deltaF) (DR).cells (DR).reads (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR))
        (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR)) χ
        (Fin.cast (WalkJ8.walkChipJ8_width deltaF (krW (DR).cells (DR).reads) powerBasis3
          (ComplJ8Of.walk_pos (DR).cells (DR).reads)
          (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF χ)
          (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o χ)) j)) ∧
    (WalkJ8.walkChipJ8 deltaF (krW (DR).cells (DR).reads) powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF χ)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o χ)).BindsPreprocessing
      (fun j => ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o) (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF)
        (ComplJ8Of.encR deltaF) (DR).cells (DR).reads (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR))
        (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR)) χ
        (Fin.cast (WalkJ8.walkChipJ8_width deltaF (krW (DR).cells (DR).reads) powerBasis3
          (ComplJ8Of.walk_pos (DR).cells (DR).reads)
          (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF χ)
          (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o χ)) j)) := by
  have h31 := ComplJ9ARun.rows31_of_A h31A
  have hmC : (DA).cells.length ∈ ComplJ8Of.sizesJ8 (DA) := by simp [ComplJ8Of.sizesJ8]
  have hmW : (walkRows (DA).cells (DA).reads).length ∈ ComplJ8Of.sizesJ8 (DA) := by
    simp [ComplJ8Of.sizesJ8]
  have h1 := h31 _ hmC
  have h2 := h31 _ hmW
  have h3 := krW_le_rows (DA).cells (DA).reads
  have h64 : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
  have hlenW := (hp_DRJ Rt hgen).length_eq
  have hkrW := krW_regroup (DA).cells (DA).reads (hall_DAJ Rt hgen)
  have hlenW' : (walkRows (DA).cells (regroup (DA).reads)).length =
      (walkRows (DA).cells (DA).reads).length := hlenW
  have hcl : (DR).cells.length < P := by
    show (DA).cells.length < P
    omega
  have hkp : krW (DR).cells (DR).reads + (walkRows (DR).cells (DR).reads).length < P := by
    show krW (DA).cells (regroup (DA).reads) + (walkRows (DA).cells (regroup (DA).reads)).length < P
    omega
  have hadj : ∀ (i : Fin (walkRows (DR).cells (DR).reads).length)
      (hi : (i : ℕ) + 1 < (walkRows (DR).cells (DR).reads).length),
      ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length ⟨(i : ℕ) + 1, hi⟩ =
        ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length i * o.ω :=
    fun i hi => pow_succ _ _
  exact GenPortJ9AHWalkPub.walkOK_at deltaF powerBasis3 (DR) hp63 hcl hkp (walkDepthOK_regroup _ (hwalk_DAJ Rt hgen hwalk9))
    (fun x => ComplJ8Of.hdl_kind (DA).cells (DA).acs x) o hinj hadj χ
    (GenPortJ9AHWalkFam.famWalkV_good_of_perm deltaF (DA) (DR) rfl (hp_DRJ Rt hgen) χ hV)
    (GenPortJ9AHWalkFam.famWalkH_good_of_perm deltaF (DA) (DR) rfl rfl (hp_DRJ Rt hgen) χ hH)


/-! ## 3. Orbit-level -/

/-- `walkGenRowsB_pubs` at `regD DA` and an arbitrary injective orbit `O`. -/
theorem walkE_pubs_at (χe : CoinsE) (I : InJ9A) (hpW : I.M.pubsW = (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).2) {h : ℕ} (O : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN O (walkRows (DR).cells (DR).reads).length)) (j : ℕ) :
    K3.toK (I.M.pubsW j) =
      ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) O (toχ χe) j := by
  have a : ∀ c ∈ (DR).cells, c.isCell = true := hcs_DAJ Rt hgen χe
  have b := hwcell_DRJ Rt hgen
  have c := hwroot_DRJ Rt hgen
  have e1 := GenPortJ9AHWalkPubs.walkGenRowsB_pubs χe (DR) a b c O hinj j
  rw [hpW]
  exact e1

/-- `genJ9AX_walk_interp` at a chip `q = reorb I.W O'` (same columns, other orbit). -/
theorem walkE_interp_at (χe : CoinsE) (I : InJ9A) (hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).1) (q : ChipIn) (O' : Orb) (hq : q = reorb I.W O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 166) :
    interpOf q j =
      ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit q ho) (walkRows (DR).cells (DR).reads).length)
        (mkOrbit q ho) (VerJ8.chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit q ho))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) ⟨j, hj⟩ := by
  have hn : q.n = (walkRows (DR).cells (DR).reads).length := by
    exact (n_reorb _ q O' hq).trans (walkE_n' Rt hgen hwalk9 χe I hW)
  have hinj' : Function.Injective
      (ComplJ8Of.powN (mkOrbit q ho) (walkRows (DR).cells (DR).reads).length) := by
    have hI : Function.Injective (nodesOf q ∘ Fin.cast hn.symm) := hinj.comp (Fin.cast_injective _)
    rw [nodes_cast q ho hn] at hI
    exact hI
  have hcols : ∀ (i : Fin q.n) (c : ℕ) (hc : c < 166), q.cols c i =
      fullCol (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (HonestK8.certUp
          (ComplJ8Enc.wColHQBE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
            (ComplJ8Of.powN (mkOrbit q ho) _) (mkOrbit q ho) (VerJ8.chalsMJ8 deltaF (toχ χe))
            (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe))
            (ComplJ8Of.encR deltaF (toχ χe))
            (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) (DR).cells (DR).reads
            (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR)))
          (ComplJ8Walk.lenB (DR).cells (DR).reads)) c (Fin.cast hn i) := by
    intro i c hc
    have h := walkE_cols Rt hgen hwalk9 χe I hW (mkOrbit q ho) hinj'
      (Fin.cast (n_reorb _ q O' hq) i) c hc
    rw [cols_reorb _ q O' hq i c]
    exact h
  unfold interpOf
  rw [interp_cast hn, nodes_cast q ho hn]
  unfold ComplJ8Enc.walkTrWE honestQ
  refine congrArg (Lagrange.interpolate Finset.univ
    (ComplJ8Of.powN (mkOrbit q ho) (walkRows (DR).cells (DR).reads).length)) ?_
  funext i'
  exact hcols (Fin.cast hn.symm i') j hj

theorem walkE_famV (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    ∀ e ∈ ComplJ8Of.famWalkV deltaF (j9aDataOf P Rg Rt hgen) (K := KC), toχ χe ∉ e.ev :=
  fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))) e he

theorem walkE_famH (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    ∀ e ∈ ComplJ8Of.famWalkH deltaF (j9aDataOf P Rg Rt hgen) (K := KC), toχ χe ∉ e.ev :=
  fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) e he

/-- The `Hall` input of `walk_abs` at `I := recJ9AX …` (binder-free: no `Algebra Fp (Quad …)`). -/
theorem walkE_hall (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (I : InJ9A) (hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).1) (hpW : I.M.pubsW = (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).2)
    (o : OrbJ9A)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe))
    (hoW : OrbOK (reorb I.W o.W))
    (hinj0 : Function.Injective (nodesOf (reorb I.W o.W)))
    (hinjN : Function.Injective (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW)
      (walkRows (DR).cells (DR).reads).length)) :
    (withOrb I o).toMsg.pubsW =
      ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
        (mkOrbit (reorb I.W o.W) hoW) (toχ χe) ∧
    (∀ j : Fin 166, interpOf (reorb I.W o.W) j =
      ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (reorb I.W o.W) hoW))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) j) ∧
    ((WalkJ8.walkChipJ8 deltaF (krW (DR).cells (DR).reads) powerBasis3
        (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF (toχ χe))
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
          (mkOrbit (reorb I.W o.W) hoW) (toχ χe))).rap.Satisfies
      (fun j => (fun j : Fin 166 => ComplJ8Enc.walkTrWE deltaF powerBasis3
        (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (reorb I.W o.W) hoW))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) j)
        (Fin.cast (WalkJ8.walkChipJ8_width deltaF (krW (DR).cells (DR).reads) powerBasis3
          (ComplJ8Of.walk_pos (DR).cells (DR).reads)
          (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW)
            (walkRows (DR).cells (DR).reads).length)
          (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF (toχ χe))
          (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
            (mkOrbit (reorb I.W o.W) hoW) (toχ χe))) j))) ∧
    (WalkJ8.walkChipJ8 deltaF (krW (DR).cells (DR).reads) powerBasis3
        (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF (toχ χe))
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
          (mkOrbit (reorb I.W o.W) hoW) (toχ χe))).BindsPreprocessing
      (fun j => (fun j : Fin 166 => ComplJ8Enc.walkTrWE deltaF powerBasis3
        (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (reorb I.W o.W) hoW))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) j)
        (Fin.cast (WalkJ8.walkChipJ8_width deltaF (krW (DR).cells (DR).reads) powerBasis3
          (ComplJ8Of.walk_pos (DR).cells (DR).reads)
          (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW)
            (walkRows (DR).cells (DR).reads).length)
          (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF (toχ χe))
          (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
            (mkOrbit (reorb I.W o.W) hoW) (toχ χe))) j)) := by
  have hV := walkE_famV Rt hgen hwalk9 hpG h31A χe hχ
  have hH := walkE_famH Rt hgen hwalk9 hpG h31A χe hχ
  refine ⟨funext fun j => walkE_pubs_at Rt hgen hwalk9 χe I hpW _ hinjN j, ?_,
    walkE_ok Rt hgen hwalk9
      (ComplJ9AChains.hp63_of_G hpG) h31A
      (mkOrbit (reorb I.W o.W) hoW) hinjN (toχ χe) hV hH⟩
  intro j
  exact walkE_interp_at Rt hgen hwalk9 χe I hW _ o.W rfl hoW hinj0 j j.2

/-- **`hsatW ∧ hbindW` of `AcceptsJ9A` at `withOrb I o`.** -/
theorem walkE_at (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (I : InJ9A) (hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).1) (hpW : I.M.pubsW = (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
      HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (DR).cells (DR).reads)).2)
    (hkr : I.kroots = krW (DR).cells (DR).reads) (o : OrbJ9A) (ho : OrbAdm I o)
    (hv' : ValidJ9A (withOrb I o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    (WalkJ8.walkChipJ8 deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW
        (chalsMJ8 deltaF (toχ χe)) (withOrb I o).toMsg.pubsW).rap.Satisfies
      (qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb I o).toMsg.pubsW) ∧
    (WalkJ8.walkChipJ8 deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW
        (chalsMJ8 deltaF (toχ χe)) (withOrb I o).toMsg.pubsW).BindsPreprocessing
      (qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb I o).toMsg.pubsW) := by
  have hn : I.W.n = (walkRows (DR).cells (DR).reads).length :=
    walkE_n' Rt hgen hwalk9 χe I hW
  have hm := ComplJ8Of.walk_pos (DR).cells (DR).reads
  have hk :I.kroots = krW (DR).cells (DR).reads :=
    hkr
  refine walk_abs I o ho hv' (toχ χe) hn hm hk
    (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
      (mkOrbit (reorb I.W o.W) hv'.oW) (toχ χe))
    (fun j => ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hv'.oW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb I.W o.W) hv'.oW) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (reorb I.W o.W) hv'.oW))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) j) ?_
  intro hoW hinj0 hinjN
  exact walkE_hall Rt hgen hwalk9 hpG h31A χe I hW hpW o hχ hoW hinj0 hinjN

end Run

end

#print axioms walkE_n'
#print axioms walkE_n
#print axioms walkE_kroots
#print axioms walkE_cols
#print axioms walkE_pubs
#print axioms powN_inj_chipE
#print axioms walkE_interp
#print axioms walkE_ok
#print axioms walkE_pubs_at
#print axioms walkE_interp_at
#print axioms walkE_famV
#print axioms walkE_famH
#print axioms walkE_hall
#print axioms walkE_at

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkE
