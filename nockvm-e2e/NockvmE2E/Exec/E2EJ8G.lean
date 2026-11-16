/-
**`exec_e2e_J8F'`**, `exec_e2e_J8F` (Exec/E2EJ8F.lean, untouched) re-proved from `exec_e2e_generic` (Exec/E2EGenG.lean)
at `InstG.ofJ8`. The statement is a verbatim copy; `exec_e2e_J8F'_stmt_eq` checks it is equal to `exec_e2e_J8F`'s.
-/
import NockvmE2E.Exec.E2EGenG
import NockvmE2E.Exec.E2EJ8F

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


namespace NockvmE2E.Exec.E2EJ8G
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit NockvmE2E.J8 NockvmE2E.J8.TieJ8G
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)
open NockvmE2E.J8.TieJ8 (HopZero)
open NockvmE2E.Exec.E2EJ8P2 NockvmE2E.Exec.E2EJ8P
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Rap
open NockvmE2E.J8.InstJ8 (Φ0)
open NockvmE2E.Exec.E2EJ8F (LitTies litTies hops_of_chips numOf hat_of ns_le slotOK_X)

/-- `GflatG = Gflat` at `ofJ8`, proved once (rfl only at this depth) and reused. -/
theorem GflatG_ofJ8 (I : NockvmE2E.J8.TieJ8G.Inst) (hsz : NockvmE2E.J8.TieJ8G.HSz I) :
    E2EGen.GflatG (E2EGen.InstG.ofJ8 I) hsz = NockvmE2E.J8.TieJ8G.Gflat I hsz := by
  set_option maxRecDepth 50000 in rfl

namespace F
open NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM
open NockvmE2E.Exec.E2EJ8 NockvmE2E.Exec.E2EJ8.J8X
open NockvmE2E.J8.InstJ8 (Datum DatumOK J8 PbOfX PosX posX_of_shape hNof ω0 StmtP PubP)
open NockvmE2E.J8.TieJ8G (Inst HopsOK NumOK RdSpec Gflat hsz_of_hops gbJ hdagU_J8 hoff_J8 hdom_J8 colJ pubJ chalK)
open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8)
open NockvmE2E.Exec.MaskOk (maskOk)

variable (XI0 : ExecInst) (hsh : J8Shape.j8ShapeOk (XI170 XI0) = true) (hshX : J8Shape.j8ShapeXOk (XI170 XI0) = true)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh)
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [instKC : SampleableType KC]
variable (D : DatX (XI170 XI0) hsh) (hdk : DatumOK D.d)
variable (R : TabRestr (J8 D.d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigmaX (XI170 XI0) (Fin.cast hT t)) (hfree : (J8 D.d hdk).AccOn R.q)

set_option hygiene false in
local notation "IX" => (⟨XI170 XI0, hsh, posX_of_shape hsh, D.kroots, D.krootsV, D.Rt, D.regs, D.ids, D.idx, D.rk, D.lay, D.d, D.hd,
  hdk, D.hdN, D.hdω, R, hT, hσ, hfree⟩ : Inst)

set_option hygiene false in
local notation "npubV" => (XI170 XI0).pubOf.size
set_option hygiene false in
local notation "hcapV" => hcap_of_shapeX IX (XI170 XI0).pubOf.size rfl hshX

variable (tp : Fin (IX).Jm.T)

set_option hygiene false in
local notation "JXn" => (IX).JJ (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "prV" => prX IX (XI170 XI0).pubOf.size tp hcapV

/- the executed chip check and the datum numerals (labels in the ledger at the end) -/
variable (hchips : chipsOk (XI170 XI0) = true)
  (hnum0 : ∀ t : Fin (XI170 XI0).tabs.size,
    (chipNumeral (XI170 XI0).tabs[t].chip).getD 0 = numOf D.d (sigmaX (XI170 XI0) t))

set_option hygiene false in
local notation "hd1" => ((J8Shape.d_of_shape hsh).symm : (1 : ℕ+).val = (XI170 XI0).d)
set_option hygiene false in
local notation "hNHV" => hNH_X IX (XI170 XI0).pubOf.size tp hcapV 1 hd1
set_option hygiene false in
local notation "hpdV" => hpd_X IX (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "hopsV" => (hops_of_chips IX hchips litTies hnum0).1
set_option hygiene false in
local notation "hnumV" => (hops_of_chips IX hchips litTies hnum0).2.1
set_option hygiene false in
local notation "GX" => Gflat IX (hsz_of_hops IX jDers jMeta hnumV hopsV)
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
local notation "cIV" => cIX IX (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "mV" => (XI170 XI0).nc * (JXn).r + (PJ).nq - 1

theorem hmV_X : mV + 1 = (XI170 XI0).nc * (JXn).r + (PJ).nq := by
  have h9 : (PJ).nq = 9 := rfl
  have : (JXn).r = 2 := rfl
  omega

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (hmV_X XI0 hsh hshX D hdk R hT hσ hfree tp hchips hnum0)

variable [iDM0 : DecidableEq ((PJ).statement (R0P) (RestP)).M0] [fM0 : Finite ((PJ).statement (R0P) (RestP)).M0]
  [iDMf : DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [fMf : Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [iCh : ∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "HNQ" => ((nq_of_shapeX hshX).trans rfl : (XI170 XI0).nq = (PJ).nq)
set_option hygiene false in
local notation "HBLK" => hblk_of_shapeX IX (XI170 XI0).pubOf.size tp hcapV rfl hshX
set_option hygiene false in
local notation "HBLKQ" => hblkq_X IX (PJ).nq (HNQ).ge
set_option hygiene false in
local notation "MDV" => mdX (XI170 XI0) (J8Shape.hn1_of_shape hsh) (PJ).colRoundX
  (rkP (XI170 XI0) (PJ) rfl HNQ cIV HBLK HBLKQ) toyEncB
set_option hygiene false in
local notation "LV" => LX (XI170 XI0) (J8Shape.hn32_of_shape hsh)

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
local notation "DA" => daOf (XI170 XI0) (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 MDV cIV sl0X sl1X
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
/-- **`exec_e2e_J8F`**: `exec_e2e_J8` with every binder covered by a lemma discharged. The remaining hypotheses, with labels:
  - `hsh`, `hshX`, `hl`: EXECUTED (the verifier exe's shape gates `j8ShapeOk`, `j8ShapeXOk`, and `l = 170`);
  - `hchips`, `hnum0`: EXECUTED chip check (`chipsOk`: each loaded chip equals a literal of `J8Chips`; the 12 literal ties are the theorem `litTies`)
    + DATUM numerals (kroots / krootsV of the datum = numeral of the loaded walk chip);
  - `hmask`, `hnumeralOk`: EXECUTED (`maskOk`, `numeralOk`; the Lagrange bridge is `MaskBridge.hLagr_of`); `hjet`: TCB (the jet's 18 registry columns);
  - `hdk`, `hS`, `hlink`, `hids`: DATUM (`DatumOK`, `StmtP`, `InpLink`, registry ids);
  - `R hT hσ hfree`: the table restriction (instance: `RJ8`, `rfl`, `rfl`, `hfree_J8`, see `inst_RJ8`);
  - `tp`, `I0 I Ifin`, the instances, `encZ decZ hz`, `m0 mf`, the adversary and its bounds: protocol / adversary parameters as in `exec_e2e_final`. -/
theorem exec_e2e_J8F' {Statement Salt W : Type} [iDS : DecidableEq Statement] [iDSa : DecidableEq Salt] [fS : Finite Statement] [fSa : Finite Salt]
    [fQ : Finite (NQuery (merkleSkels (MC)))]
    [iSR : SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    /- [executed] `l = 170` -/
    (hl : XI0.l = 170)
    /- [statement parameters] the statement/salt codec -/
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    /- [datum] the datum satisfies the J-8 side conditions, its claim matches the instance's public input, registry ids are small -/
    (hS : StmtP D.d) (hlink : NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 XI0).pubIn)
    (hids : ∀ id ∈ D.d.Pb.regs, id < NockvmE2E.J8.InstJ8.P)
    /- [executed] `maskOk` and `numeralOk` (both run inside `hop0Check`) -/
    (hmask : maskOk (XI170 XI0) = true) (hnumeralOk : NockvmE2E.Exec.MaskOk.numeralOk (XI170 XI0) = true)
    /- [TCB] the jet's 18 registry fixed columns (`hpreJet`; not covered by `maskOk`) -/
    (hjet : ∀ t : Fin (XI170 XI0).tabs.size, (XI170 XI0).tabs[t].chip.id = "jetChipJ8" →
      ∀ c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub → (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
        NockvmE2E.Exec.MaskBridge.LagrAt IX (XI170 XI0).pubOf.size tp hcapV t c)
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
        AccF XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV encZ decZ
          (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g (z, salt) π ∧ ¬ Nock.Jet.HoldsN D.d.c] ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hhops := hops_of_chips IX hchips litTies hnum0
  have hsz := hsz_of_hops IX jDers jMeta hhops.2.1 hhops.1
  have hcol := hcI_col_X IX _ tp hcapV rfl
  have hpub := hcI_pub_X IX _ tp hcapV rfl
  have htie := htie_J8 IX hsz _ tp hcapV prV jDers jMeta hhops.2.1 hhops.1 (chalK (JXn).Φ0 sl0X sl1X) (fun χ => slotOK_X χ)
      (rdSpec_X IX _ tp hcapV rfl hshX)
  have hrvu := NockvmE2E.Exec.E2EJ8S.hRVU_X_of' (XI0 := XI0) (hn32 := J8Shape.hn32_of_shape hsh) (hsh := hsh) (D := D) (hdk := hdk) (R := R) (hT := hT) (hσ := hσ)
      (hfree := hfree) (npub := (XI170 XI0).pubOf.size) (tp := tp) (hcap := hcapV) (pr := prV) (dF := 1) (hNH := hNHV) (hpd := hpdV)
      (ders := jDers) (cmeta := jMeta) (hnum := hhops.2.1) (hops := hhops.1) (cI := cIV)
      (sl0 := sl0X) (sl1 := sl1X)
      (m0 := m0) (mf := mf)
      hS hlink hids (hpJ_X IX hshX) (hpV_X IX hshX hhops.2.1)
      (fun c0 c1 c2 c3 i => hχ_X (XI170 XI0) hsh c0 c1 c2 c3 i)
      (fun c0 c1 c2 c3 vT vQ hV hP => hrd_X IX _ tp hcapV rfl hshX (hat_of D.d _ hS hlink) mf _ _ vT vQ hV hP)
  have hlagr := NockvmE2E.Exec.MaskBridge.hLagr_of IX _ tp hcapV hmask hnumeralOk hnum0 hjet
  have hG := GflatG_ofJ8 IX hsz
  revert hcol hpub htie hrvu hlagr
  generalize NockvmE2E.J8.TieJ8G.Gflat IX hsz = G at *
  subst hG
  intro hcol hpub htie hrvu hlagr
  exact @E2EGenP.G.exec_e2e_generic ShapeF.famJ8 (J8 D.d hdk) XI0 (E2EGen.InstG.ofJ8 IX) hshX instKC tp hsz cIV hcol hpub
    iDM0 fM0 iDMf fMf I0 I Ifin iCh sl0X sl1X m0 mf Statement Salt W iDS iDSa fS fSa fQ iSR
    hl (NockvmE2E.Merkle.RapFriQ.PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf)
    (NockvmE2E.Merkle.RapFriQ.pubSound_J8 _ (J8Shape.hmode_of_shape hsh)) encZ decZ hz hhops.2.2 (by decide)
    (fun χ => slotOK_X χ) htie hlagr hrvu
    Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

end F

/-- statement equality with `exec_e2e_J8F` -/
example : type_of% @NockvmE2E.Exec.E2EJ8G.F.exec_e2e_J8F' = type_of% @NockvmE2E.Exec.E2EJ8F.F.exec_e2e_J8F := rfl

end NockvmE2E.Exec.E2EJ8G

#print axioms NockvmE2E.Exec.E2EJ8G.F.exec_e2e_J8F'
