/-
**`exec_e2e_J9AVR`**, the J-9 A online end-to-end theorem with the side-failure event as a BINDER.
`exec_e2e_onlineP_R` (Exec/SideOnlineR.lean) at `X0 := XI170 XI0`, `HOf := HT ..`, `FSOf := FST ..`, `hflat := exec_e2e_J9A` on the repacked
adversary (bridged by `pr_pair_congr .. Iff.rfl` as at Exec/SideOnlineRJ8.lean:209-211); `hFix : Pr[FixFailR ..] ≤ εfix` stays a binder.
Conclusion: `Pr[verifyOnline' .. ∧ ¬HoldsN d.c] ≤ 2^-82 + εfix`.  The notation block is that of J9A/E2EJ9A.lean:46-160 (the two helper theorems
`hnqPJ9`, `hmV9` are reused from there, not restated).
-/
import NockvmE2E.J9A.E2EJ9A
import NockvmE2E.Exec.SideOnlineR
import NockvmE2E.Exec.E2EOnlineP

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

namespace NockvmE2E.J9A.E2EJ9AVR
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
open NockvmE2E.J9A.E2EJ9A (hnqPJ9 hmV9)
open NockvmE2E.Exec.E2EOnlineP
open NockvmE2E.Exec.E2EJ8V (SideRng HfOf FSfOf vkSide)

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
/-- **`exec_e2e_J9AVR`**: the J-9 A online end-to-end bound with `hFix : Pr[FixFailR ..] ≤ εfix` as a binder.
Binders: those of `exec_e2e_J9A` (with `Aflat` replaced by the online adversary `Aon`), plus `skelsF FK FR fkOf frOf`, `hgates`, `εfix`, `hFix`. -/
theorem exec_e2e_J9AVR {Statement Salt W : Type} {skelsF : List Skeleton} {FK : Type} {FR : FK → Type} [DecidableEq FK]
    (fkOf : List (List ℕ) → FK) (frOf : ∀ k, FR k → ℕ → List ℕ) [SampleableType (∀ d, SideRng skelsF FR d)]
    [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    (hl : XI0.l = 170)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (hS : StmtP9A d) (hlink : NockvmE2E.J9A.RVUJ9A.InpLink9 d (XI170 XI0).pubIn) (hids : ∀ id ∈ d.Pb.regs, id < P)
    (hpJ : d.Pb.nJ = 0 → (XI170 XI0).pubLay.present[3]! = false) (hpV : d.Pb.krootsV = 0 → (XI170 XI0).pubLay.present[5]! = false)
    (hpX : d.Pb.axOn = false → (XI170 XI0).pubLay.present[6]! = false) (hpS : d.Pb.spOn = false → (XI170 XI0).pubLay.present[7]! = false)
    (hmask : maskOkF famJ9A (XI170 XI0) = true) (hnumeralOk : numeralOkF famJ9A (XI170 XI0) = true)
    (hjet : ∀ t : Fin (XI170 XI0).tabs.size, (XI170 XI0).tabs[t].chip.id = "jetChipJ8" →
      ∀ c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub → (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
        NockvmE2E.J9A.LagrJ9A.LagrAt9 IG (XI170 XI0).pubOf.size tp hcapV t c)
    (hgates : setupGates (XI170 XI0) = true)
    (Aon : OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) + OracleSpec.ofFn (SideRng skelsF FR))
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
    (εfix : ℝ≥0∞)
    (hFix : Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd); let gF ← $ᵗ (∀ d, SideRng skelsF FR d); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some (z, salt, π, πF, _) =>
        NockvmE2E.Exec.SideOnlineR.FixFailR (XI170 XI0) (vkSide (XI170 XI0) skelsF FR gF) (HfOf skelsF FR gF)
          (FST XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
            (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
          (FSfOf skelsF FR fkOf frOf gF) (encZ (z, salt)) π πF] ≤ εfix) :
    Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd); let gF ← $ᵗ (∀ d, SideRng skelsF FR d); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some (z, salt, π, πF, _) =>
        verifyOnline' (vkSide (XI170 XI0) skelsF FR gF)
          (HT XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g) (HfOf skelsF FR gF)
          (FST XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
            (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
          (FSfOf skelsF FR fkOf frOf gF) (encZ (z, salt)) π πF = true ∧ ¬ Nock.Jet.HoldsN d.c] ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ + εfix := by
  have hJ := NockvmE2E.J9A.E2EJ9A.exec_e2e_J9A (XI0 := XI0) (hsh := hsh) (hshX := hshX) (d := d) (hdk := hdk) (L := L) (R := R)
    (hT := hT) (hσ := hσ) (hfree := hfree) (hchips := hchips) (hnum0 := hnum0) (tp := tp) (I0 := I0) (I := I) (Ifin := Ifin)
    (m0 := m0) (mf := mf) (hl := hl) (encZ := encZ) (decZ := decZ) (hz := hz) (hS := hS) (hlink := hlink) (hids := hids)
    (hpJ := hpJ) (hpV := hpV) (hpX := hpX) (hpS := hpS) (hmask := hmask) (hnumeralOk := hnumeralOk) (hjet := hjet)
    (Aflat := repackP (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon)
    (Q_FS := Q_FS) (Q_H := Q_H) (V := V) (Pn := Pn) (hQFS := hQFS) (hQH := hQH) (hV := hV) (hFS := hFS) (hHq := hHq)
    (hterm := hterm) (hconfig := hconfig)
  refine le_trans (le_of_eq (NockvmE2E.Exec.E2EOnline.pr_triple_congr _ _ _ _ _ ?conv))
    (NockvmE2E.Exec.SideOnlineR.exec_e2e_onlineP_R (X0 := XI170 XI0)
      (HOf := fun g => HT XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g)
      (FSOf := fun g => FST XI0 (hn32_of_shapeF hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
        (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
      (HfOf := HfOf skelsF FR) (FSfOf := FSfOf skelsF FR fkOf frOf) (vkOf := vkSide (XI170 XI0) skelsF FR)
      (rp := fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2)))
      (zO := fun o => encZ (o.1, o.2.1)) (πO := fun o => o.2.2.1) (πFO := fun o => o.2.2.2.1)
      (BadO := fun _ => ¬ Nock.Jet.HoldsN d.c)
      (zO' := fun o => encZ (o.1, o.2.1)) (πO' := fun o => o.2.2.1) (BadO' := fun _ => ¬ Nock.Jet.HoldsN d.c)
      (hvk := fun gF => NockvmE2E.Exec.V.setup'_of_gates hgates _) (hz := fun _ => rfl) (hπ := fun _ => rfl)
      (hBad := fun _ => Iff.rfl) (A := Aon) (ε := _) (εfix := εfix) ?hfl ?hfx)
  rotate_left
  · refine le_trans (le_of_eq (NockvmE2E.Exec.E2EOnline.pr_pair_congr _ _ _ _ ?_)) hJ
    intro g o
    rcases o with _ | ⟨z, salt, π, w⟩ <;> exact Iff.rfl
  · refine le_trans (le_of_eq (NockvmE2E.Exec.E2EOnline.pr_triple_congr _ _ _ _ _ ?_)) hFix
    intro g gF o
    rcases o with _ | ⟨z, salt, π, πF, w⟩ <;> exact Iff.rfl
  · intro g gF o
    rcases o with _ | ⟨z, salt, π, πF, w⟩ <;> exact Iff.rfl

#print axioms NockvmE2E.J9A.E2EJ9AVR.exec_e2e_J9AVR

end NockvmE2E.J9A.E2EJ9AVR
