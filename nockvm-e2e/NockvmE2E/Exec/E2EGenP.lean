/-
part 2: `exec_e2e_JF` (the copy of `E2EJ8.exec_e2e_J` over `shapeOkF F`) and **`exec_e2e_generic`**, the end-to-end
statement at a generic interface `J` and chip family `F` with the bundle `InstG F J (XI170 XI0)` (Exec/E2EGen.lean).
Conclusion `¬ J.Holds`.  Binder ledger at the end of the file.
-/
import NockvmE2E.Exec.E2EGen
import NockvmE2E.Exec.E2EJ8
import NockvmE2E.Exec.E2EJ8F
import NockvmE2E.Exec.E2EJ8P2
import NockvmE2E.J8.RVUJ8

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

/-! ## Part 1: `exec_e2e_J` at an abstract interface `J` (an unchanged copy) -/

namespace NockvmE2E.Exec.E2EGenP
open NockvmE2E.Exec.ShapeF
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR

variable (XI0 : ExecInst) (hn32 : (XI170 XI0).nD ≤ 32)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD hn32
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [SampleableType KC]
variable (J : RapAirJ (ZMod NockvmE2E.Exec.p) KC) [NeZero J.r] (pr : PubRead J) (d : ℕ+)
  (hNH : friBound s1 d ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)
  {nsK : ℕ} (G : Regroup (deepParamsJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd).ns nsK) (gb : Fin 3 → KC)

set_option hygiene false in
local notation "PJ" => (deepParamsJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd).regroup G gb
set_option hygiene false in
local notation "AJ" => (airJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd).regroup G gb
set_option hygiene false in
local notation "R0P" => R0J J pr ωS (31 / 64) (friBound s1 d)
set_option hygiene false in
local notation "RestP" => RestJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd
set_option hygiene false in
local notation "RestVP" => RestVJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd

variable (cI : J.ι0 ≃ Fin (XI170 XI0).nc) {m : ℕ} (hm : m + 1 = (XI170 XI0).nc * J.r + (PJ).nq)

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cI J.r hm

variable [DecidableEq ((PJ).statement (R0P) (RestP)).M0] [Finite ((PJ).statement (R0P) (RestP)).M0]
  [DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (enc : KC ↪ DgJ8)
  (md : PointMaskData (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD)) (ZMod NockvmE2E.Exec.p) DgJ8) (L : Fri.FriLeaves (ω := ωS) s1)
  {n0 n1 : ℕ} (sl0 : {i : Fin (extFrame J.Φ0 2).n // (extFrame J.Φ0 2).sampledAfter i = 0} ≃ Fin n0)
  (sl1 : {i : Fin (extFrame J.Φ0 2).n // (extFrame J.Φ0 2).sampledAfter i = 1} ≃ Fin n1)
  (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame J.Φ0 2) KC md.toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 d (XI170 XI0).l DgJ8 enc L
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "DA" => daOf (XI170 XI0) hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 md cI sl0 sl1 (PJ).ha (PJ).hz
  (single_az (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd).1
  (single_az (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd).2 m0 mf
set_option hygiene false in
local notation "EMBF" => fun (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 d (XI170 XI0).l L enc))
    (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability in
/-- **the J-8 shape**: the exec e2e figure `≤ 2^-82` at ANY interface `J` (the J-8 one is `plusJ (minusT J8 R hfree) …`), with the
decoders `daOf` and the opening facts plugged in. The binders are the remaining hypotheses (labelled in the binder list). -/
theorem exec_e2e_JF (F : Fam) {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    -- [executed] the J-8 shape of the loaded instance (the verifier exe rejects otherwise)
    (hshape : shapeOkF F (XI170 XI0) = true) (hl : XI0.l = 170)
    -- the public relation and its executed soundness
    (PR : Array VF.K3 → Array VF.G → Prop) (hPS : PubSound (XI170 XI0) PR)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    -- [construction] layout facts of `cI` against the instance
    (hr : J.r = (XI170 XI0).r) (hnq : (XI170 XI0).nq = (PJ).nq)
    (hkd : ∀ c < (XI170 XI0).nc, (XI170 XI0).colKind[c]! < 3)
    (hblk : ∀ c, (XI170 XI0).blockOf[(cI c).val]! = J.colRound0 c)
    (hblkq : ∀ q : Fin (PJ).nq, (XI170 XI0).blockOf[(XI170 XI0).nc + q.val]! = 3)
    (hpub : ∀ c, pr.pub c = true ↔ (XI170 XI0).colKind[(cI c).val]! = 2)
    (hppt : ∀ c, pr.pub c = true → pr.ppt c = toKV (XI170 XI0).ppt)
    (hoff : ∀ t k, J.off t k = zv (XI170 XI0).hGen ^ (k : ℕ))
    (hns : (PJ).ns = ((XI170 XI0).tabs.toList.map (fun t => t.chip.cons.size)).sum)
    (hHJ : J.H = (Finset.range (XI170 XI0).hN).image (fun i => zv (XI170 XI0).hShift * zv (XI170 XI0).hGen ^ i))
    (hgen : pr.gen = toKV VF.K3.gen)
    -- the DAG tie (output of `hdagU_of_tie`), the public twin
    (hdagU : ∀ (c0 : Block (extFrame J.Φ0 2) KC 0) (c1 : Block (extFrame J.Φ0 2) KC 1) (c2 : Block (extFrame J.Φ0 2) KC 2)
      (c3 : Block (extFrame J.Φ0 2) KC 3) (ζ : VF.K3) (vT : Array (Array VF.K3)),
      CanonIn (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT →
      ∀ i : Fin (PJ).ns, (termsAt (XI170 XI0) (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT)[i.1]? =
        some ((AJ).Cv (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOfG (XI170 XI0) cI J.r vT)))
    (hRVU : ∀ (c0 : Block (extFrame J.Φ0 2) KC 0) (c1 : Block (extFrame J.Φ0 2) KC 1) (c2 : Block (extFrame J.Φ0 2) KC 2)
      (c3 : Block (extFrame J.Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      PR
        (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt (XI170 XI0) vT) →
      (RestVP) m0 (finDecG (XI170 XI0) cI J.r (PJ).nq mf (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3))
    -- [kernel, `gb_indep`] independence of `gb` on the used coordinates
    (hb : ∀ c : Fin 3 → ZMod NockvmE2E.Exec.p, (∀ k, (∀ j, G.crd j ≠ k) → c k = 0) →
      ∑ k, algebraMap (ZMod NockvmE2E.Exec.p) KC (c k) * gb k = 0 → ∀ k, c k = 0)
    -- [construction] the mask data and leaves are the verifier's
    (hmd : md = mdX (XI170 XI0) (hn1_of_shapeF hshape) (PJ).colRoundX
      (rkP (XI170 XI0) (PJ) rfl hnq cI hblk hblkq) toyEncB)
    (hL : L = LX (XI170 XI0) hn32)
    (hd : d.val = XI0.d) (hEnc : EncOK enc)
    -- [numbers] the caps (from `J.cap_*`, the field, the instance numbers)
    (hrate : 64 * (2 ^ (∑ j, ((s1) j).val) * d.val) ≤ 2 ^ (XI170 XI0).nD)
    (hF : goldilocks ^ 3 ≤ Fintype.card KC) (hm12 : m + 1 ≤ 2 ^ 12)
    (htoPoly : (PJ).toPoly = udDecodeB ωS (31 / 64) (friBound s1 d))
    (hnsC : (PJ).ns ≤ 2 ^ 20) (hD : (PJ).D.card ≤ 2 ^ 32) (hH : (PJ).H.card ≤ 2 ^ 32) (hnqC : (PJ).nq + 1 ≤ 2 ^ 8)
    (hDg : goldilocks ^ 4 ≤ Nat.card DgJ8)
    -- [adversary] as in `exec_e2e_final`
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
        AccF XI0 hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin d enc md L encZ decZ
          (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 d (XI170 XI0).l L enc)) g (z, salt) π ∧ ¬ (R0P).Holds] ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hpt := pt_J (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd cI hpub hppt hoff
  have U := uniLinksN_of_da (XI170 XI0) hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin d DgJ8 enc md L PR
    rfl hr hkd cI sl0 sl1
    (single_az (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd).1
    (single_az (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd).2 m0 mf dgOf
    (dsbC, dsmC s1 d (XI170 XI0).l L enc) hpt.1 hpt.2 hns hnq hdagU hRVU
    (hH_J (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd hHJ) rfl
    (hcw_J (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd hgen)
  have O := opsU_of_layout (XI170 XI0) (PJ) rfl (AJ) hr hnq hkd cI hblk hblkq hpt.1 hpt.2 hm
  exact exec_e2e_final XI0 hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin d enc md L PR hl encZ decZ hz (DA)
    (vTOfG (XI170 XI0) cI J.r) toyEncB (rkP (XI170 XI0) (PJ) rfl hnq cI hblk hblkq) (hn1_of_shapeF hshape) hmd hL
    hPS U (colNG (XI170 XI0) cI) O (domLink_of_shapeF hshape) hd hEnc
    (rapInput_rapJ _ _) (hlink_regroup J pr ωS (31 / 64) (friBound s1 d) hNH hpd G gb hb) (by show 2 + 1 < 4; norm_num)
    (hRest_J J pr ωS (31 / 64) (friBound s1 d) hNH hpd) errJ (fun _ r => roundBound_rapJ_le _ _ _ r)
    hrate hF hm12 htoPoly hnsC hD hH hnqC errJ_le hDg Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

end NockvmE2E.Exec.E2EGenP

#print axioms NockvmE2E.Exec.E2EGenP.exec_e2e_JF
