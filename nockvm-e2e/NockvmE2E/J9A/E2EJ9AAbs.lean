/-
`exec_e2e_J9A` at the chips-absent record (`exec_e2e_J9A` no longer has `hbr`; `hax hsp` are now unused, kept so the statement is stable; `hbr_absent` stays as an unused lemma) (`axOn = spOn = false`): **`exec_e2e_J9A_absent`**; pieces `pubK_absent`, `slOf_absent`, `hbr_absent`.
the end-to-end theorem at the J-9 A interface: `exec_e2e_generic`
(Exec/E2EGenG.lean) at `famJ9A` and `InstG.ofJ9A` (J9A/GenJ9A.lean, `J9A d hd = ofIface (clJ9A d hd) (nJ9A d hd)`), every binder
discharged from A1-A4 (`hsz hcons` from `hops9_of_chips`; `hSlotOK` = `slotOK_X`; `htie` = `htieG_of` + `tt9`; `hcur1` = `hLagr9_of`;
`hRVU` = `hRVU_J9A` via `hrd9`).  The remaining hypotheses are labelled in the BINDER LEDGER at the end of the file.
-/
import NockvmE2E.J9A.E2EJ9A
import NockvmE2E.J9A.WitJ9A
import NockvmE2E.J9A.RVUJ9A
import NockvmE2E.Exec.SoundClosed
set_option autoImplicit false
namespace NockvmE2E.J9A.E2EJ9AAbs
open NockvmE2E.Exec NockvmE2E.Exec.SP NockvmE2E.Exec.VL NockvmE2E.J9A.RVUJ9A

theorem rep_get (n j : ℕ) : (Array.replicate n (0 : UInt64))[j]! = 0 := by
  by_cases h : j < n
  · rw [getElem!_pos _ j (by simpa using h)]; simp
  · rw [getElem!_neg _ j (by simpa using h)]; rfl

theorem pubK_absent (n i : ℕ) : pubK (Array.replicate n 0) i = 0 := by
  unfold pubK
  rw [rep_get, rep_get, rep_get]
  exact toKV_zero

theorem slOf_absent (L : PE.PubLayout) (pub : Array UInt64) (t : ℕ) (h : L.present[t]! = false) (i : ℕ) :
    pubK (slOf L pub t) i = 0 := by
  unfold slOf; rw [h]; simpa using pubK_absent _ i

open NockvmE2E.Merkle.RapFriQ (PubJ8P)

/-- **`hbr_absent`**: with the axis and split slices absent from the public layout, the J-8 public relation is the J-9 A one -/
theorem hbr_absent (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array Nat)
    (h6 : L.present[6]! = false) (h7 : L.present[7]! = false) (slots : Array VF.K3) (pub : Array UInt64)
    (h : PubJ8P inp L slotOf slots pub) : PubJ9P inp L slotOf slots pub := by
  obtain ⟨⟨cr, pr, h1, h2, hrel⟩, hd⟩ := h
  refine ⟨⟨cr, pr, h1, h2, ?_⟩, hd⟩
  have e6 := slOf_absent L pub 6 h6
  have e7 := slOf_absent L pub 7 h7
  have hq : qmk (0 : KC) 0 = 0 := by ext <;> simp [qmk]
  unfold PubJ9Rel
  unfold SP.PubJ8Rel at hrel
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hrel
  refine ⟨r1, ?_, ?_, r4, r5, r6, r7, r8⟩
  · simp only [e6, hq, add_zero]; exact r2
  · simp only [e6, e7, hq, add_zero]; exact r3
end NockvmE2E.J9A.E2EJ9AAbs


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


namespace NockvmE2E.J9A.E2EJ9AAbs
open NockvmE2E.J9A.E2EJ9A (hnqPJ9 hmV9)
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

theorem exec_e2e_J9A_absent {Statement Salt W : Type} [iDS : DecidableEq Statement] [iDSa : DecidableEq Salt] [fS : Finite Statement] [fSa : Finite Salt]
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
    /- [executed/datum] the axis and split chips are absent from the datum (UNUSED, the J-9 A relation is carried by the exec chain at `pubMode = 2`; formerly replaced `hbr`: with the axis / split slices absent the J-8
       public relation `PubJ8P` carried by the exec chain IS the J-9 A one, `hbr_absent`) -/
    (hax : d.Pb.axOn = false) (hsp : d.Pb.spOn = false)
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
  refine NockvmE2E.J9A.E2EJ9A.exec_e2e_J9A XI0 hsh hshX d hdk L R hT hσ hfree hchips hnum0 tp I0 I Ifin m0 mf hl encZ decZ hz hS hlink hids hpJ hpV hpX hpS hmask hnumeralOk hjet
    Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

end NockvmE2E.J9A.E2EJ9AAbs

namespace NockvmE2E.J9A.E2EJ9AAbs
open NockvmE2E.J9A.InstJ9A (DatumOK9A StmtP9A)

/-- non-vacuity of the absent conditions: at the chips-absent witness record `dW` (WitJ9A) the datum conditions `hax hsp` hold together
with `DatumOK9A` and `StmtP9A` (the layout facts `hpX hpS` concern the loaded instance and are not discharged here) -/
theorem absent_conds_witness :
    DatumOK9A NockvmE2E.J9A.WitJ9A.dW ∧ StmtP9A NockvmE2E.J9A.WitJ9A.dW ∧
      NockvmE2E.J9A.WitJ9A.dW.Pb.axOn = false ∧ NockvmE2E.J9A.WitJ9A.dW.Pb.spOn = false := by
  obtain ⟨χ, M, tr, h1, h2, -, -⟩ := NockvmE2E.J9A.WitJ9A.j9a_absent_witness
  exact ⟨h1, h2, rfl, rfl⟩

end NockvmE2E.J9A.E2EJ9AAbs

#print axioms NockvmE2E.J9A.E2EJ9AAbs.hbr_absent
#print axioms NockvmE2E.J9A.E2EJ9AAbs.pubK_absent
#print axioms NockvmE2E.J9A.E2EJ9AAbs.absent_conds_witness
#print axioms NockvmE2E.J9A.E2EJ9AAbs.exec_e2e_J9A_absent
