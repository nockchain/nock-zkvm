/-
INST-PARSE S9: **`exec_e2e_J9A_verdict`**, the packaged form.  `exec_e2e_J9A`'s statement with its instance-side hypotheses (`hl hsh hshX hchips hmask
hnumeralOk`, the datum binders `d hdk L R hT hσ hfree hS hlink hids hnum0 hpJ hpV hpX hpS`, `hjet`) replaced by the single hypothesis
`verdict9 XI0 H FS z π = .ok c`: the verdict yields (`verdict9_run`) the five gates, `l = 170` and `Wit9 (XI170 XI0) c _`; the witness is unpacked into the datum
`d` (`d.c = c`) and `exec_e2e_J9A` is applied at it.  The datum is existentially quantified in the conclusion (AccF's ROM parameters depend on it).
Notation block copied from `E2EJ9A.lean` (its `local notation`s are not exported).
-/
import NockvmE2E.J9A.E2EJ9A
import NockvmE2E.J9A.E2EJ9ARun

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

namespace NockvmE2E.J9A.E2EJ9AVerdict
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR
open NockvmE2E.Exec.ShapeF NockvmE2E.Exec.E2EGen NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J9AChips
open NockvmE2E.J8.TieJ8G (sizes nsK gbJ chalK)
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.HtieJ9A NockvmE2E.J9A.LagrJ9A NockvmE2E.J9A.E2EJ9AQ
  NockvmE2E.J9A.E2EJ9AP NockvmE2E.Exec.E2EGenT NockvmE2E.Exec.E2EGen
open NockvmE2E.Exec.E2EJ8P2 (sl0X sl1X)
open NockvmE2E.Exec.E2EJ8F (slotOK_X)
open NockvmE2E.J8.InstJ8 (P)
open NockvmE2E.J8 (TabRestr)
open NockvmE2E.J9A.E2EJ9A (hnqPJ9 hmV9 exec_e2e_J9A)
open NockvmE2E.J9A.RunGate9 (verdict9)
open Nock.NockVMROM.Thm54 (P8PublicClaim)

set_option hygiene false in
local notation "IG" => InstG.ofJ9A (XI170 XI0) hsh d hdk L R hT hσ hfree
set_option hygiene false in
local notation "hopsV" => (hops9_of_chips hsh d hchips hnum0).1
set_option hygiene false in
local notation "hnumV" => (hops9_of_chips hsh d hchips hnum0).2.1
set_option hygiene false in
local notation "hconsV" => (hops9_of_chips hsh d hchips hnum0).2.2
set_option hygiene false in
local notation "hszV" => hsz9 hsh d hdk L R hT hσ hfree NockvmE2E.Exec.J8Chips.jDers NockvmE2E.Exec.J8Chips.jMeta hnumV hopsV
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
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (hmV9 XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp)
set_option hygiene false in
local notation "HNQ" => ((nq_of_shapeXF hshX).trans (hnqPJ9 XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp).symm : (XI170 XI0).nq = (PJ).nq)
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

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability in
set_option maxHeartbeats 4000000 in
/-- **`exec_e2e_J9A_verdict`**: if the runtime verdict at the loaded instance `XI0` is `.ok c`, then there is a datum `d` with `d.c = c` (and the
shape / chip facts of the loaded instance) such that `exec_e2e_J9A`'s bound `Pr[AccF ∧ ¬HoldsN c] ≤ 2⁻⁸²` holds, for every adversary within the bounds. -/
theorem exec_e2e_J9A_verdict (XI0 : ExecInst) (H : HFn) (FS : FSFn) (z0 : List ℕ) (π0 : FlatProof) (c : P8PublicClaim)
    (hv : verdict9 XI0 H FS z0 π0 = .ok c) :
    ∃ (hsh : shapeOkF famJ9A (XI170 XI0) = true) (hshX : shapeXOkF famJ9A (XI170 XI0) = true)
      (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 (XI170 XI0) d) (R : TabRestr (J9A d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
      (hσ : ∀ t : Fin R.T', R.σ t = sigma9 (XI170 XI0) (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q)
      (hchips : chipsOkF famJ9A (XI170 XI0) = true)
      (hnum0 : ∀ t : Fin (XI170 XI0).tabs.size, (chipNumeralF famJ9A (XI170 XI0).tabs[t].chip).getD 0 = numOf9 d (sigma9 (XI170 XI0) t)),
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
      [iSR : SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
      (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
      (Aflat : OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC))
        (Option (Statement × Salt × FlatProof × W)))
      (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
      (hFS : FsBound (Q := NQuery (merkleSkels (MC))) (∅ : (ofFn (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))).QueryCache)
        Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 EMBF Aflat)))
      (hHq : IsQueryBoundP (embedAdv DgJ8 EMBF Aflat)
        (@isHashQuery (NQuery (merkleSkels (MC))) DgJ8 _ (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))) Q_H)
      (hterm : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
        (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
        claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V)
      (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn),
      Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd);
         let o ← simulateQ (withTable g) Aflat}[
        match o with
        | none => False
        | some (z, salt, π, _) =>
          AccF XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV encZ decZ
            (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g (z, salt) π ∧ ¬ Nock.Jet.HoldsN c] ≤
        (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  obtain ⟨hsh, hshX, hchips, hmask, hnumeralOk, hl, d, hdk, L, hS, hlink, hids, hnum0, hpJ, hpV, hpX, hpS, hnj, ⟨R, hT, hσ, hfree⟩, hdc, -⟩ :=
    NockvmE2E.J9A.E2EJ9ARun.verdict9_run hv
  refine ⟨hsh, hshX, d, hdk, L, R, hT, hσ, hfree, hchips, hnum0, hdc, ?_⟩
  subst hdc
  intro instKC tp iDM0 fM0 iDMf fMf I0 I Ifin iCh m0 mf Statement Salt W iDS iDSa fS fSa fQ iSR encZ decZ hz Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig
  exact @exec_e2e_J9A XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 instKC tp iDM0 fM0 iDMf fMf I0 I Ifin iCh m0 mf Statement Salt W iDS iDSa fS fSa fQ iSR
    hl encZ decZ hz hS hlink hids hpJ hpV hpX hpS hmask hnumeralOk (fun t h => absurd h (hnj t)) Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

end NockvmE2E.J9A.E2EJ9AVerdict

#print axioms NockvmE2E.J9A.E2EJ9AVerdict.exec_e2e_J9A_verdict
