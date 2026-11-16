/-
**`exec_e2e_J9A`**, the end-to-end theorem at the J-9 A interface: `exec_e2e_generic`
(Exec/E2EGenG.lean) at `famJ9A` and `InstG.ofJ9A` (J9A/GenJ9A.lean, `J9A d hd = ofIface (clJ9A d hd) (nJ9A d hd)`), every binder
discharged from A1-A4 (`hsz hcons` from `hops9_of_chips`; `hSlotOK` = `slotOK_X`; `htie` = `htieG_of` + `tt9`; `hcur1` = `hLagr9_of`;
`hRVU` = `hRVU_J9A` via `hrd9`).  The remaining hypotheses are labelled in the BINDER LEDGER at the end of the file.
-/
import NockvmE2E.Exec.E2EGenG
import NockvmE2E.J9A.E2EJ9AQ
import NockvmE2E.J9A.E2EJ9AP
import NockvmE2E.J9A.HtieJ9A

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

/-! ## `exec_e2e_generic` -/


namespace NockvmE2E.J9A.E2EJ9A
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

variable (XI0 : ExecInst) (hsh : shapeOkF famJ9A (XI170 XI0) = true) (hshX : shapeXOkF famJ9A (XI170 XI0) = true)
  (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 (XI170 XI0) d) (R : TabRestr (J9A d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9 (XI170 XI0) (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q)
set_option hygiene false in
local notation "IG" => InstG.ofJ9A (XI170 XI0) hsh d hdk L R hT hσ hfree
variable (hchips : chipsOkF famJ9A (XI170 XI0) = true)
  (hnum0 : ∀ t : Fin (XI170 XI0).tabs.size, (chipNumeralF famJ9A (XI170 XI0).tabs[t].chip).getD 0 = numOf9 d (sigma9 (XI170 XI0) t))
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

variable [instKC : SampleableType KC]

set_option hygiene false in
local notation "npubV" => (XI170 XI0).pubOf.size
set_option hygiene false in
local notation "hcapV" => hcap_of_shapeXF IG (XI170 XI0).pubOf.size rfl hshX

variable (tp : Fin (IG).Jm.T)

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

theorem hnqPJ9 : (PJ).nq = 9 := by
  show 3 * ((J9A d hdk).d - 1) = 9
  rfl

theorem hmV9 : mV + 1 = (XI170 XI0).nc * (JXn).r + (PJ).nq := by
  have h9 := hnqPJ9 XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp
  have h2 : (JXn).r = 2 := rfl
  omega

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (hmV9 XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp)

variable [iDM0 : DecidableEq ((PJ).statement (R0P) (RestP)).M0] [fM0 : Finite ((PJ).statement (R0P) (RestP)).M0]
  [iDMf : DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [fMf : Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [iCh : ∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

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

theorem exec_e2e_J9A {Statement Salt W : Type} [iDS : DecidableEq Statement] [iDSa : DecidableEq Salt] [fS : Finite Statement] [fSa : Finite Salt]
    [fQ : Finite (NQuery (merkleSkels (MC)))]
    [iSR : SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    /- [executed] `l = 170` -/
    (hl : XI0.l = 170)
    /- [statement parameters] the statement/salt codec -/
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    /- [datum] the J-9 A datum's claim matches the instance's public input, the statement side conditions, registry ids are small -/
    (hS : StmtP9A d) (hlink : NockvmE2E.J9A.RVUJ9A.InpLink9 d (XI170 XI0).pubIn) (hids : ∀ id ∈ d.Pb.regs, id < P)
    /- [datum link] an absent optional table of the datum has `present = false` in the loader's public layout -/
    (hpJ : d.Pb.nJ = 0 → (XI170 XI0).pubLay.present[3]! = false) (hpV : d.Pb.krootsV = 0 → (XI170 XI0).pubLay.present[5]! = false)
    (hpX : d.Pb.axOn = false → (XI170 XI0).pubLay.present[6]! = false) (hpS : d.Pb.spOn = false → (XI170 XI0).pubLay.present[7]! = false)
    /- [executed] `maskOkF` and `numeralOkF` (the J-9 A `hop0Check`) -/
    (hmask : maskOkF famJ9A (XI170 XI0) = true) (hnumeralOk : numeralOkF famJ9A (XI170 XI0) = true)
    /- [TCB] the jet's registry fixed columns -/
    (hjet : ∀ t : Fin (XI170 XI0).tabs.size, (XI170 XI0).tabs[t].chip.id = "jetChipJ8" →
      ∀ c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub → (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
        LagrAt9 IG (XI170 XI0).pubOf.size tp hcapV t c)
    /- [adversary] as in `exec_e2e_final` -/
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
    (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn) :
    Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd);
       let o ← simulateQ (withTable g) Aflat}[
      match o with
      | none => False
      | some (z, salt, π, _) =>
        AccF XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV encZ decZ
          (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g (z, salt) π ∧ ¬ Nock.Jet.HoldsN d.c] ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hrate := hrate_F hsh 1 hd1
  have hrd : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      NockvmE2E.J9A.RVUJ9A.PubJ9P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
        (slotsAt (XI170 XI0) (blockEnc sl0X c0) (blockEnc sl1X c1)) (pubAt (XI170 XI0) vT) →
      (RestVP) m0 (finDecG (XI170 XI0) cIV (JXn).r (PJ).nq mf (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3) := by
    intro c0 c1 c2 c3 vT vQ hV hP
    have hslots : ∀ s ∈ slotsAt (XI170 XI0) (blockEnc sl0X c0) (blockEnc sl1X c1), canon3 s := by
      intro s hs
      unfold slotsAt at hs
      refine canon_slots _ _ ?_ s hs
      intro x hx
      rcases Array.mem_append.mp hx with hx | hx
      · exact canon_k3s _ (NockvmE2E.Exec.E2EJ8S.blockEnc_lt sl0X c0) _ x hx
      · exact canon_k3s _ (NockvmE2E.Exec.E2EJ8S.blockEnc_lt sl1X c1) _ x hx
    obtain ⟨pub, hcan, hP', hrd'⟩ := hrd9 hsh d hdk L R hT hσ hfree _ tp hcapV rfl hlink mf (PJ).nq _ vT vQ hV hP
    refine ⟨?_, hS⟩
    show PubP9A d (restr 2 (chiOfBlocks c0 c1 c2 c3)) ((prV).rd (fun c => (finDecG (XI170 XI0) cIV (JXn).r (PJ).nq mf (deepMsg vT vQ)).2.1 (c, 0)))
    rw [hrd']
    exact NockvmE2E.J9A.RVUJ9A.hRVU_J9A d hS _ hlink _ _ _ pub hslots hcan hids hpJ hpV hpX hpS _
      (fun i => hχ_F _ hsh c0 c1 c2 c3 i) hP'
  have htie := htieG_of IG hszV (XI170 XI0).pubOf.size tp hcapV prV (chalK (JXn).Φ0 sl0X sl1X)
      (tt9 hsh d hdk L R hT hσ hfree (XI170 XI0).pubOf.size tp hcapV NockvmE2E.Exec.J8Chips.jDers NockvmE2E.Exec.J8Chips.jMeta hnumV hopsV
        (chalK (JXn).Φ0 sl0X sl1X) (fun χ => slotOK_X χ) (rdSpec9 hsh hshX d hdk L R hT hσ hfree _ rfl tp hcapV))
  have hlagr := hLagr9_of hsh d hdk L R hT hσ hfree (XI170 XI0).pubOf.size tp hcapV hmask hnumeralOk hnum0 hjet
  exact @E2EGenP.G.exec_e2e_generic famJ9A (J9A d hdk) XI0 IG hshX instKC tp hszV cIV hcIcol hcIpub
    iDM0 fM0 iDMf fMf I0 I Ifin iCh sl0X sl1X m0 mf Statement Salt W iDS iDSa fS fSa fQ iSR
    hl (NockvmE2E.J9A.RVUJ9A.PubJ9P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf)
    (NockvmE2E.J9A.PubSoundJ9A.pubSound_J9 _ (hmode_of_shapeF hsh)) encZ decZ hz hconsV (by decide) (fun χ => slotOK_X χ) htie hlagr hrd
    Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

end NockvmE2E.J9A.E2EJ9A

#print axioms NockvmE2E.J9A.E2EJ9A.exec_e2e_J9A

/-
BINDER LEDGER of `exec_e2e_J9A` (LABEL | source)
  hl       : [executed] `l = 170` is checked by the exes' shape gates: `j8ShapeOk` (J8ShapeB.lean:102) and `shapeOkF` (ShapeF.lean:45),
             kernel link `hl_of_shapeF` (ShapeF.lean:132). It is also checked on VerifyMain's online `verify --vk` path, and
             `verdict9` checks it first (`verdict9_sound` gives `XI.l = 170`). Correction 11-06: an earlier label said 'only l ≥ 1 is checked';
             that was wrong.
  executed : hsh (shapeOkF famJ9A), hshX (shapeXOkF famJ9A), hchips (chipsOkF famJ9A), hmask (maskOkF famJ9A),
             hnumeralOk (numeralOkF famJ9A)  [the J-9 A `hop0Check`; `maskOkF`/`numeralOkF`/`chipsOkF` are generic over a `Fam`; the exe
             calls these same generic forms at `famJ9A` via `famGatesFail` (Exec/FamGates.lean, used by `verdict9`)]
  kernel   : the 16 literal ties (`litTies9`: 12 J-8 `J8ChipsK_*`, 4 J-9 A `J9AChipsK_*`) DISCHARGED
  datum    : hdk (DatumOK9A), hS (StmtP9A), hlink (InpLink9), hids, hnum0 (datum kroots / krootsV / nA = numeral of the loaded chip)
  datum link : L : Link9 (the J-9 A stand-in for J-8's `hd : d.Pb = PbOfX XI ...`: union domain, node powers, table sizes = the loaded
             tables' hN), hpJ hpV hpX hpS (an absent optional table is absent from the public layout)
  TCB      : hjet (the jet's registry fixed columns)
  (the former GAP `hbr` is gone: the exec chain is parametrised by the public relation, `PR:= PubJ9P`, `hPS:= pubSound_J9` at `pubMode = 2`)
  instance : R hT hσ hfree (the table restriction, abstract as at J-8), tp
  protocol / adversary : I0 I Ifin, instances, m0 mf, encZ decZ hz, Aflat, Q_FS Q_H V Pn and bounds, as in `exec_e2e_final`
  ACCEPTED FILES: `exec_e2e_J9A_verdict` (J9A/E2EJ9AVerdict.lean) [kernel] replaces every instance-side binder above
             (hsh hshX hchips hmask hnumeralOk hl, the datum and datum-link binders, hjet) by `verdict9 XI H FS z π = .ok c`, the check the
             verify-fam exe runs on the file it loaded; the parser and loader are untrusted. [read]: the compiled `main` calls `verdict9` on the
             loaded data (VerifyFamMain.lean:76). Not zero-knowledge: RS+FRI, no masking.
  DISCHARGED here : hsz hcons (hops9_of_chips + litTies9), hFids (decide), hSlotOK (slotOK_X), htie (htieG_of + tt9 + tieAt9),
    hcur1 (hLagr9_of from lagr9_*), hRVU (hRVU_J9A via hrd9 + hat9 + hχ_F), hcI_col hcI_pub (cIG), hcap, hpdeg, hdom, hdomt, hcolR, hpreN
-/
