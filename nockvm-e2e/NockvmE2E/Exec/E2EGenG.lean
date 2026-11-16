/-
part 3: **`exec_e2e_generic`** over `exec_e2e_JF` (Exec/E2EGenP.lean) and the bundle `InstG` (Exec/E2EGen.lean).
Conclusion `¬ J.Holds`.
-/
import NockvmE2E.Exec.E2EGenP

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

namespace NockvmE2E.Exec.E2EGenP.G
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR
open NockvmE2E.Exec.ShapeF NockvmE2E.Exec.E2EGen NockvmE2E.Exec.J8Chips
open NockvmE2E.J8.TieJ8G (sizes nsK gbJ chalK)

/-- `TieJ8.χf` at an arbitrary coin frame (equal to it, definitionally, at `InstJ8.Φ0`, whose `n` is `19`) -/
noncomputable def χfG {Φ : CoinFrame} (χ : Coins Φ KC) (i : ℕ) : KC := if h : i < Φ.n then χ ⟨i, h⟩ else 0

variable (F : Fam) (J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC) (XI0 : ExecInst) (IG : InstG F J (XI170 XI0))
  (hshX : shapeXOkF F (XI170 XI0) = true)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD (hn32_of_shapeF IG.hsh)
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [SampleableType KC]

set_option hygiene false in
local notation "npubV" => (XI170 XI0).pubOf.size
set_option hygiene false in
local notation "hcapV" => hcap_of_shapeXF IG (XI170 XI0).pubOf.size rfl hshX

variable (tp : Fin IG.Jm.T) (hsz : HSzG IG)

set_option hygiene false in
local notation "JXn" => IG.JJ (XI170 XI0).pubOf.size tp hcapV
variable (cI : (JXn).ι0 ≃ Fin (XI170 XI0).nc)
  (hcI_col : ∀ (t : Fin (XI170 XI0).tabs.size) c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub →
    ((cI (colJG IG (XI170 XI0).pubOf.size tp hcapV t c) : Fin (XI170 XI0).nc) : ℕ) = (XI170 XI0).tabs[t].col0 + c)
  (hcI_pub : ∀ (t : Fin (XI170 XI0).tabs.size) s, s < (XI170 XI0).tabs[t].npub →
    ((cI (pubJG IG (XI170 XI0).pubOf.size tp hcapV t s) : Fin (XI170 XI0).nc) : ℕ) =
      (XI170 XI0).pubOf[(XI170 XI0).tabs[t].pubBase + s]!)
set_option hygiene false in
local notation "prV" => prG IG (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "hd1" => ((d_of_shapeF IG.hsh).symm : (1 : ℕ+).val = (XI170 XI0).d)
set_option hygiene false in
local notation "hNHV" => hNH_G IG (XI170 XI0).pubOf.size tp hcapV 1 hd1
set_option hygiene false in
local notation "hpdV" => hpd_G IG (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "GX" => GflatG IG hsz
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

theorem hnqPJ_G : (PJ).nq = 9 := by
  show 3 * (J.d - 1) = 9
  rw [IG.hd4]

theorem hmV_G : mV + 1 = (XI170 XI0).nc * (JXn).r + (PJ).nq := by
  have h9 := hnqPJ_G F J XI0 IG hshX tp hsz
  omega

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cI (JXn).r (hmV_G F J XI0 IG hshX tp hsz)

variable [DecidableEq ((PJ).statement (R0P) (RestP)).M0] [Finite ((PJ).statement (R0P) (RestP)).M0]
  [DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (sl0 : {i : Fin (extFrame (JXn).Φ0 2).n // (extFrame (JXn).Φ0 2).sampledAfter i = 0} ≃ Fin 13)
  (sl1 : {i : Fin (extFrame (JXn).Φ0 2).n // (extFrame (JXn).Φ0 2).sampledAfter i = 1} ≃ Fin 6)
variable (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "HNQ" => ((nq_of_shapeXF hshX).trans (hnqPJ_G F J XI0 IG hshX tp hsz).symm : (XI170 XI0).nq = (PJ).nq)
set_option hygiene false in
local notation "HBLK" => hblk_of_shapeXF IG (XI170 XI0).pubOf.size tp hcapV rfl hshX cI (cI_val_G IG _ tp hcapV rfl cI hcI_col hcI_pub)
set_option hygiene false in
local notation "HBLKQ" => hblkq_F IG.hsh (PJ).nq (HNQ).ge
set_option hygiene false in
local notation "MDV" => mdX (XI170 XI0) (hn1_of_shapeF IG.hsh) (PJ).colRoundX
  (rkP (XI170 XI0) (PJ) rfl HNQ cI HBLK HBLKQ) toyEncB
set_option hygiene false in
local notation "LV" => LX (XI170 XI0) (hn32_of_shapeF IG.hsh)

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
local notation "DA" => daOf (XI170 XI0) (hn32_of_shapeF IG.hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 MDV cI sl0 sl1
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
/-- **`exec_e2e_generic`**: `Pr[AccF … ∧ ¬ J.Holds] ≤ 2^-82` at `JJ = plusJ (minusT J R) (Fin npub)` over the chip family `F`.
The per-instance hypotheses (`hsz hcons hFids hSlotOK htie hcur1 hRVU`, and the slot equivalences `sl0 sl1`) are binders. -/
theorem exec_e2e_generic {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    (hl : XI0.l = 170)
    (PR : Array VF.K3 → Array VF.G → Prop) (hPS : PubSound (XI170 XI0) PR)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (hcons : ∀ t : Fin (XI170 XI0).tabs.size, (XI170 XI0).tabs[t].chip.cons.size ≤ 100000)
    (hFids : F.ids.length * 100000 ≤ 2 ^ 20)
    (hSlotOK : ∀ χ : Coins (JXn).Φ0 KC,
      NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE jDers jMeta (chalK (JXn).Φ0 sl0 sl1 χ)) (χfG χ))
    (htie : HtieG IG hsz (XI170 XI0).pubOf.size tp hcapV prV (chalK (JXn).Φ0 sl0 sl1))
    (hcur1 : ∀ (t : Fin (XI170 XI0).tabs.size) c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub →
      (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
      (JXn).pre (colJG IG (XI170 XI0).pubOf.size tp hcapV t c) = some (((List.range (XI170 XI0).pre[(XI170 XI0).tabs[t].col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv ((XI170 XI0).pre[(XI170 XI0).tabs[t].col0 + c]!)[m]!)).sum))
    (hRVU : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      PR
        (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt (XI170 XI0) vT) →
      (RestVP) m0 (finDecG (XI170 XI0) cI (JXn).r (PJ).nq mf (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3))
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
        AccF XI0 (hn32_of_shapeF IG.hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV encZ decZ
          (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g (z, salt) π ∧ ¬ J.Holds] ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hrate := hrate_F IG.hsh 1 hd1
  exact exec_e2e_JF XI0 (hn32_of_shapeF IG.hsh) JXn prV 1 hNHV hpdV GX gbJ cI (hmV_G F J XI0 IG hshX tp hsz) I0 I Ifin encK MDV LV
    sl0 sl1 m0 mf F IG.hsh hl PR hPS encZ decZ hz
    (IG.hr.trans (r_of_shapeF IG.hsh).symm) HNQ (hkd_F IG.hsh) HBLK HBLKQ (hpub_G IG _ tp hcapV rfl cI (cI_val_G IG _ tp hcapV rfl cI hcI_col hcI_pub)) (hppt_G IG _ tp hcapV)
    (fun t k => hoff_G IG _ tp hcapV t k) rfl (hdom_G IG _ tp hcapV) (hgen_G IG _ tp hcapV)
    (hdagU_G IG _ tp hcapV hsz rfl prV ωS (31 / 64) (friBound s1 1) hNHV hpdV sl0 sl1
      (by rw [(slotOf_of_shapeF IG.hsh).2]; rfl) (by rw [(slotOf_of_shapeF IG.hsh).2]; rfl) htie cI hcI_col hcI_pub (hpre0_G IG _ tp hcapV) hcur1)
    hRVU (fun c _ h => NockvmE2E.J8.gb_indep c h) rfl rfl (d_of_shapeF IG.hsh).symm encK_ok hrate E2EJ8P.hF_X
    (hm12_G JXn cI (hmV_G F J XI0 IG hshX tp hsz))
    (E2EJ8P.htoPoly_X (hn32_of_shapeF IG.hsh) JXn prV s1 1 hNHV hpdV hrate)
    (ns_le_F IG.hsh hFids hcons) (E2EJ8P.hD_X (hn32_of_shapeF IG.hsh) JXn prV s1 1 hNHV hpdV)
    (E2EJ8P.hH_X (hn32_of_shapeF IG.hsh) JXn prV s1 1 hNHV hpdV)
    (by show 3 * (J.d - 1) + 1 ≤ 2 ^ 8; rw [IG.hd4]; norm_num) E2EJ8P.hDg_X
    Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

end NockvmE2E.Exec.E2EGenP.G

#print axioms NockvmE2E.Exec.E2EGenP.G.exec_e2e_generic

/-! ## `hops_of_fam`: hop 0 and the constraint-count cap from the executed chip check, for a family -/

namespace NockvmE2E.Exec.E2EGenH
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit NockvmE2E.Exec.ShapeF NockvmE2E.J8.TieJ8
open NockvmE2E.J8.TieJ8 (HopZero)

/-- every expected literal of the family ties to its emitted spec (kernel `tieB`) and is small -/
def LitTiesF (F : Fam) (spec : String → ℕ → TSpec) : Prop :=
  ∀ id k lit, (k, lit) ∈ F.lits id → tieB (spec id k) lit = true ∧ lit.cons.size ≤ 100000

/-- **`hops_of_fam`**: for a table whose chip passes the numeral check `chipNumeralF F`, hop 0 against the emitted DAG of its numeral
holds, and its constraint count is `≤ 100000` -/
theorem hops_of_fam (F : Fam) (spec : String → ℕ → TSpec) (LT : LitTiesF F spec) (c : Chip) (k : ℕ)
    (hk : chipNumeralF F c = some k) :
    HopZero c (emitDag (spec c.id k)) jDers jMeta c.baseCols ∧ c.cons.size ≤ 100000 := by
  obtain ⟨lit, hlit, hE⟩ := num_findF F c k hk
  obtain ⟨h1, h2⟩ := LT c.id k lit hlit
  exact ⟨NockvmE2E.J8.HopsLit.hopZero_of_tie (spec c.id k) lit c h1 hE, by
    rw [NockvmE2E.Exec.E2EJ8F.chipEqB_size c lit hE]; exact h2⟩

end NockvmE2E.Exec.E2EGenH

#print axioms NockvmE2E.Exec.E2EGenH.hops_of_fam
