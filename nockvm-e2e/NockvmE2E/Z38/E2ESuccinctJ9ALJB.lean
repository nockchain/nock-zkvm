/-
 S1: **`nock_e2e_J9ALJ_succinct_B`**, a COROLLARY of `nock_e2e_J9ALJ_succinct`.
The exists/forall prefix and the conclusion are character for character those of `nock_e2e_J9ALJ_succinct`; only the premise `hv` changes: it is now the
binding verdict `NockvmE2E.Z38.RunGate9LJB.verdict9LJVB` (the verdict behind `zBind pubIn z`, i.e. the executed verifier's `z` starts with `zHdr pubIn`).
STILL NON-ADAPTIVE as a theorem: `pubIn` is fixed (inside `XI0`) before the oracle, exactly as in `nock_e2e_J9ALJ_succinct`.  What changed is the exe: it now binds `pubIn` into the FS key.
The adaptive proof is pending.  NOT zero-knowledge.
-/
import NockvmE2E.J9AL.E2EJ9ALV
import NockvmE2E.Z38.RunGate9LJVRun
import NockvmE2E.Z38.RunGate9LJB
import NockvmE2E.Z38.LagrJ9ALJ

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.E2ESuccinctJ9ALJB
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR
open NockvmE2E.Exec.ShapeF NockvmE2E.Exec.E2EGen NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J9AChips
open NockvmE2E.J8.TieJ8G (sizes nsK gbJ chalK)
open NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A
open NockvmE2E.J9A.LagrJ9A (LagrAt9 numeralOkF)
open NockvmE2E.J9A.RunGate9L (maskOkFL)
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.TieJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.HtieJ9AL NockvmE2E.J9AL.LagrJ9AL
  NockvmE2E.J9AL.E2EJ9ALQ NockvmE2E.J9AL.E2EJ9ALP
open NockvmE2E.Exec.E2EGenT NockvmE2E.Exec.E2EGen
open NockvmE2E.Exec.E2EJ8P2 (sl0X sl1X)
open NockvmE2E.Exec.E2EJ8F (slotOK_X)
open NockvmE2E.J8.InstJ8 (P)
open NockvmE2E.J8 (TabRestr)
open NockvmE2E.J9AL.E2EJ9AL (hnqPJ9L hmV9L)
open NockvmE2E.Exec.E2EOnlineP
open NockvmE2E.Exec.E2EJ8V (SideRng HfOf FSfOf vkSide)
open NockvmE2E.Exec.SideBoundF (SideNums)
open Nock.NockVMROM.Thm54 (P8PublicClaim)

set_option hygiene false in
local notation "IG" => InstG.ofJ9AL (XI170 XI0) hsh d hdk L R hT hσ hfree
set_option hygiene false in
local notation "hopsV" => (hops9L_of_chips hsh d hchips hnum0).1
set_option hygiene false in
local notation "hnumV" => (hops9L_of_chips hsh d hchips hnum0).2.1
set_option hygiene false in
local notation "hconsV" => (hops9L_of_chips hsh d hchips hnum0).2.2
set_option hygiene false in
local notation "hszV" => hsz9L hsh d hdk L R hT hσ hfree NockvmE2E.Exec.J8Chips.jMeta hnumV hopsV
set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD (hn32_of_shapeF hsh)
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))
set_option hygiene false in
local notation "npubV" => (XI170 XI0).pubOf.size
set_option hygiene false in
local notation "hcapV" => hcap_of_shapeXF IG (XI170 XI0).pubOf.size rfl hshX
set_option hygiene false in
local notation "JXn" => (IG).JJ (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "cIV" => cIG IG (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "hcIcol" => hcI_col_G IG (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "hcIpub" => hcI_pub_G IG (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "prV" => prG IG (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "hd1" => ((d_of_shapeF hsh).symm : (1 : ℕ+).val = (XI170 XI0).d)
set_option hygiene false in
local notation "hNHV" => hNH_G IG (XI170 XI0).pubOf.size tp hcapV 1 hd1
set_option hygiene false in
local notation "hpdV" => hpd_G IG (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "GX" => GflatG IG hszV
set_option hygiene false in
local notation "PJ" => (deepParamsJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "AJ" => (airJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "R0P" => R0J JXn prV ωS (31 / 64) (friBound s1 1)
set_option hygiene false in
local notation "RestP" => RestJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "RestVP" => RestVJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "mV" => (XI170 XI0).nc * (JXn).r + (PJ).nq - 1
set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (hmV9L XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp)
set_option hygiene false in
local notation "HNQ" => ((nq_of_shapeXF hshX).trans (hnqPJ9L XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp).symm : (XI170 XI0).nq = (PJ).nq)
set_option hygiene false in
local notation "HBLK" => hblk_of_shapeXF IG (XI170 XI0).pubOf.size tp hcapV rfl hshX cIV (cI_val_G IG _ tp hcapV rfl cIV hcIcol hcIpub)
set_option hygiene false in
local notation "HBLKQ" => hblkq_F hsh (PJ).nq (HNQ).ge
set_option hygiene false in
local notation "MDV" => mdX (XI170 XI0) (hn1_of_shapeF hsh) (PJ).colRoundX
  (rkP (XI170 XI0) (PJ) rfl HNQ cIV HBLK HBLKQ) toyEncB
set_option hygiene false in
local notation "LV" => LX (XI170 XI0) (hn32_of_shapeF hsh)
set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 1 (XI170 XI0).l DgJ8 encK MDV LV (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame (JXn).Φ0 2) KC (MDV).toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 1 (XI170 XI0).l DgJ8 encK LV
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "DA" => daOf (XI170 XI0) (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 MDV cIV sl0X sl1X
  (PJ).ha (PJ).hz
  (single_az (XI170 XI0) JXn prV (ω := ωS) (31 / 64) (friBound s1 1) hNHV hpdV).1
  (single_az (XI170 XI0) JXn prV (ω := ωS) (31 / 64) (friBound s1 1) hNHV hpdV).2 m0 mf
set_option hygiene false in
local notation "EMBF" => fun (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK))
    (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList
set_option hygiene false in
local notation "SMS" => NockvmE2E.Merkle.SideMerkle.bMask (S := KC) s1 1 (XI170 XI0).l LV DgJ8 encK
set_option hygiene false in
local notation "ZStmt'" => NockvmE2E.Exec.SideInst.SStmt (XI170 XI0)
set_option hygiene false in
local notation "ZSalt'" => (Statement × Salt)
set_option hygiene false in
local notation "ZOp" => OpenAll DgJ8 (merkleSkels (SMS))
set_option hygiene false in
local notation "Zskels" => NockvmE2E.Exec.SideInst.skelsSide (XI170 XI0)
set_option hygiene false in
local notation "Zdecode" => (id : OpenAll DgJ8 (merkleSkels (SMS)) → OpenAll DgJ8 (merkleSkels (SMS)))
set_option hygiene false in
local notation "Zguards" => (trueGuards _)
set_option hygiene false in
local notation "ZChal" => (fun k : Key (ZStmt' × ZSalt') PUnit (compiledRoundsK DgJ8 ZOp (SMS)) => Key.Challenge k)
set_option hygiene false in
local notation "ZfkOf" => (NockvmE2E.Exec.SideInst.fkOfX s1 (XI170 XI0).l LV (XI170 XI0) decZ (NockvmE2E.Exec.SideInst.ω0S s1 (XI170 XI0).l LV))
set_option hygiene false in
local notation "ZfrOf" => (NockvmE2E.Exec.SideInst.frOfX s1 (XI170 XI0).l LV (XI170 XI0) (NockvmE2E.Exec.SideInst.ω0S s1 (XI170 XI0).l LV))
set_option hygiene false in
local notation "FSM" => FST XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
  (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK))
set_option hygiene false in
local notation "ZsideOf" => (fun g o => NockvmE2E.Exec.SideInst.sideOfX s1 (XI170 XI0).l LV (XI170 XI0) (FSM g) encZ o)

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability NockvmE2E.Merkle.SideMerkle in
set_option maxHeartbeats 4000000 in
/-- **`nock_e2e_J9ALJ_succinct_B`** (S1 corollary: STILL NON-ADAPTIVE as a theorem; the exe now binds `pubIn` into the FS key via `zBind`).  Statement of **`nock_e2e_J9ALJ_succinct`** (route B headline with template jets over `catJ`, clause (S)): the runtime online verdict at the loaded instance `XI0` is `.ok c`
⟹ there is a datum `d` with `d.c = c` such that every adversary within the budgets has
`Pr[verifyOnline' accepts ∧ ¬HoldsN c] ≤ 2⁻⁸² + (bfriErr + mcROM + coll)`.
Named hypotheses: `hnum : SideNums ..` (the side numerics, including `1 ≤ k`), `hTb` (`T` bounds the side-VK size).
Scope: preprocessing verifier (honest VK); chip files trusted; `k ≥ 1`; ALU big-atom jets (`aluChipJ9`) covered; template jets covered for the fixed catalogue `catJ`
(`hjet` from `PreJLink`, i.e. `jetPreOkF`); compiler TCB (the exe's `verdict9LJVB` result is trusted from the Lean compiler/runtime); not ZK; RO model; non-adaptive. -/
theorem nock_e2e_J9ALJ_succinct_B (XI0 : ExecInst) (root : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z0 : List ℕ) (π0 : FlatProof)
    (πF0 : FixProof) (c : P8PublicClaim)
    (hv : NockvmE2E.Z38.RunGate9LJB.verdict9LJVB XI0 root H Hf FS FSf z0 π0 πF0 = .ok c) :
    ∃ (hsh : shapeOkF famJ9AL (XI170 XI0) = true) (hshX : shapeXOkF famJ9AL (XI170 XI0) = true)
      (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L (XI170 XI0) d) (R : TabRestr (J9AL d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
      (hσ : ∀ t : Fin R.T', R.σ t = sigma9L (XI170 XI0) (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q)
      (hchips : chipsOkF famJ9AL (XI170 XI0) = true)
      (hnum0 : ∀ t : Fin (XI170 XI0).tabs.size, (chipNumeralF famJ9AL (XI170 XI0).tabs[t].chip).getD 0 = numOf9L d (sigma9L (XI170 XI0) t)),
    d.c = c ∧
    ∀ [instKC : SampleableType KC] (tp : Fin (IG).Jm.T)
      [iDM0 : DecidableEq ((PJ).statement (R0P) (RestP)).M0] [fM0 : Finite ((PJ).statement (R0P) (RestP)).M0]
      [iDMf : DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
      [fMf : Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
      (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
      (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
      (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
      [iCh : ∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
      (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)
      {Statement Salt W : Type} [iDS : DecidableEq Statement] [iDSa : DecidableEq Salt] [fS : Finite Statement] [fSa : Finite Salt]
      [fQ : Finite (NQuery (merkleSkels (MC)))]
      [instTab : SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
      [fQF : Finite (NQuery Zskels)]
      [instTabF : SampleableType (∀ d', succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' ZSalt' (SMS) d')]
      (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
      {θ : ℝ} {δ ε : ℝ≥0} (hnum : SideNums (XI170 XI0) (hn32_of_shapeF hsh) θ δ ε)
      (Aon : OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) +
          OracleSpec.ofFn (succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' ZSalt' (SMS)))
        (Option (Statement × Salt × FlatProof × FixProof × W)))
      (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
      (hFS : FsBound (Q := NQuery (merkleSkels (MC))) (∅ : (ofFn (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))).QueryCache)
        Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 EMBF
          (repackP (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon))))
      (hHq : IsQueryBoundP (embedAdv DgJ8 EMBF
          (repackP (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon))
        (@isHashQuery (NQuery (merkleSkels (MC))) DgJ8 _ (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))) Q_H)
      (hterm : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
        (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
        claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V)
      (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn)
      (Q_FSf Q_Hf Vf Pf T : ℕ)
      (hFSf : ∀ g : (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd),
        FsBound (Q := NQuery Zskels)
        (∅ : (ofFn (SoundnessWorld.KC DgJ8 ZOp ZStmt' ZSalt' (SMS))).QueryCache) Q_FSf (verifiedFS Zguards (sideAdv ZsideOf Aon g)))
      (hHf : ∀ g : (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd),
        IsQueryBoundP (sideAdv ZsideOf Aon g)
        (@isHashQuery (NQuery Zskels) DgJ8 _ (SoundnessWorld.KC DgJ8 ZOp ZStmt' ZSalt' (SMS))) Q_Hf)
      (htermf : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (SMS)).length) (op : ZOp)
        (logs : Fin (merkleSkels (SMS)).length → MerkleTreeExtractor.QueryLog (NQuery Zskels) DgJ8),
        claimsQueryCount (mkClaims (merkleSkels (SMS)) roots h (Zdecode op) logs) ≤ Vf)
      (hconfigf : ∀ tag, (mconfig (merkleSkels (SMS))).nodeBudget tag ≤ Pf)
      (hTb : 2 * ((NockvmE2E.Exec.VKBind.vkSp (XI170 XI0)).total - 1) ≤ T),
      Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd);
          let gF ← $ᵗ (∀ d', succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' ZSalt' (SMS) d');
          let o ← simulateQ (withTable2 g gF) Aon}[
        match o with
        | none => False
        | some (z, salt, π, πF, _) =>
          verifyOnline' (vkSide (XI170 XI0) Zskels ZChal gF)
            (HT XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g) (HfOf Zskels ZChal gF)
            (FSM g) (FSfOf Zskels ZChal ZfkOf ZfrOf gF) (encZ (z, salt)) π πF = true ∧ ¬ Nock.Jet.HoldsN c] ≤
        (2 ^ 82 : ℝ≥0∞)⁻¹ +
          (bfriErr (ω := smoothDomain (XI170 XI0).nD (hn32_of_shapeF hsh)) s1 1 (XI170 XI0).l θ δ ε Q_FSf +
            (multiCheckpointROMErrorNumerator (((XI170 XI0).k * (Q_FSf + 1)) * Pf) ((XI170 XI0).k * (Q_FSf + 1)) Vf Q_Hf : ℝ≥0∞) *
              (Nat.card DgJ8 : ℝ≥0∞)⁻¹ +
            ((Q_Hf + Vf + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card DgJ8 : ℝ≥0∞))) := by
  obtain ⟨hsh, hshX, hchips, hmask, hnumeralOk, hpreg, hl, hW, hgates⟩ := NockvmE2E.Z38.RunGate9LJVRun.verdict9LJV_run (NockvmE2E.Z38.RunGate9LJB.verdict9LJVB_sound hv).1
  obtain ⟨d, hdk, L, hS, hlink, hP, hids, hnum0, hpJ, hpV, hpX, hpS, hpL, hpreL, hpreJ, ⟨R, hT, hσ, hfree⟩, hdc, -⟩ := hW
  refine ⟨hsh, hshX, d, hdk, L, R, hT, hσ, hfree, hchips, hnum0, hdc, ?_⟩
  subst hdc
  intro instKC tp iDM0 fM0 iDMf fMf I0 I Ifin iCh m0 mf Statement Salt W iDS iDSa fS fSa fQ instTab fQF instTabF encZ decZ hz θ δ ε hnum Aon
    Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig Q_FSf Q_Hf Vf Pf T hFSf hHf htermf hconfigf hTb
  exact NockvmE2E.J9AL.E2EJ9ALV.exec_e2e_J9ALV (XI0 := XI0) (hsh := hsh) (hshX := hshX) (d := d) (hdk := hdk) (L := L) (R := R)
    (hT := hT) (hσ := hσ) (hfree := hfree) (hchips := hchips) (hnum0 := hnum0) (instKC := instKC) (tp := tp)
    (iDM0 := iDM0) (fM0 := fM0) (iDMf := iDMf) (fMf := fMf) (I0 := I0) (I := I) (Ifin := Ifin) (iCh := iCh) (m0 := m0) (mf := mf)
    (instTab := instTab) (instTabF := instTabF)
    (hl := hl) (encZ := encZ) (decZ := decZ) (hz := hz) (hS := hS) (hlink := hlink) (hP := hP) (hids := hids)
    (hpJ := hpJ) (hpV := hpV) (hpX := hpX) (hpS := hpS) (hpL := hpL) (hpreL := hpreL) (hmask := hmask) (hnumeralOk := hnumeralOk)
    (hjet := NockvmE2E.Z38.LagrJ9ALJ.hjet_of_PreJLink hsh d hdk L R hT hσ hfree _ tp _ hpreJ) (hgates := hgates) (hnum := hnum) (Aon := Aon)
    (Q_FS := Q_FS) (Q_H := Q_H) (V := V) (Pn := Pn) (hQFS := hQFS) (hQH := hQH) (hV := hV) (hFS := hFS) (hHq := hHq)
    (hterm := hterm) (hconfig := hconfig) (Q_FSf := Q_FSf) (Q_Hf := Q_Hf) (Vf := Vf) (Pf := Pf) (T := T)
    (hFSf := hFSf) (hHf := hHf) (htermf := htermf) (hconfigf := hconfigf) (hTb := hTb)

end NockvmE2E.Z38.E2ESuccinctJ9ALJB

#print axioms NockvmE2E.Z38.E2ESuccinctJ9ALJB.nock_e2e_J9ALJ_succinct_B
