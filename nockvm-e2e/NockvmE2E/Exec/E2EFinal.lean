/-
  NockvmE2E/Exec/E2EFinal.lean   (Coder F; proof-only)

  `exec_e2e_final`: `exec_e2e` with the `Resid` hypothesis REMOVED. The decoders are the concrete `dsbC`/`dsmC`; the five codec fields come
  from `resid_codec` (instance facts `DomLink`, `d = XI0.d`, `EncOK enc`), `hU` from `UniLinksN`, `hW0` from `OpsU`. All hypotheses are
  instance facts (pi-free, g-free).
-/
import NockvmE2E.Exec.E2EMain
import NockvmE2E.Exec.E2EResid
import NockvmE2E.Exec.E2EW0

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.multiGoal false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


namespace NockvmE2E.Exec.E2EFinal
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0

section Main
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM

variable (XI0 : ExecInst) (hn32 : (XI170 XI0).nD ≤ 32)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD hn32
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ (XI170 XI0).nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ (XI170 XI0).nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ (XI170 XI0).nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (enc : KC ↪ DgJ8)
  (md : PointMaskData P.colRoundX (Fin (2 ^ (XI170 XI0).nD)) B DgJ8) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ (XI170 XI0).nD)
variable (PR : Array VF.K3 → Array VF.G → Prop)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 d (XI170 XI0).l DgJ8 enc L

set_option hygiene false in
local notation "GG" => CoreDefinitions.univariatePowersGenerator KC m
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))

noncomputable def dsbC : RDec (batchRound KC) := { kcCodec (batchRound KC) rfl with decM := fun _ => (() : Unit) }

theorem hcsC_dsbC : ∀ c : KC, toKV (VF.K3.ofLimbs (dsbC.encC c)) = c := by
  intro c
  show toKV (VF.K3.ofLimbs (Classical.choose (limbs_surj (cast rfl c)))) = c
  exact (Classical.choose_spec (limbs_surj (cast rfl c))).2

set_option hygiene false in
local notation "EMBF" => fun (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) da (dsbC, dsmC s1 d (XI170 XI0).l L enc)) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld SoundnessCoupling
  BadBound MerkleTreeMultiExtractability in
/-- **`exec_e2e_final`**: `exec_e2e` with `Resid` replaced by instance facts only. -/
theorem exec_e2e_final {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    (hl : XI0.l = 170)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (da : MDec (RM))
    (vTOf : Array (Array VF.K3) → ι × Fin r → KC)
    (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32) (hPS : PubSound (XI170 XI0) PR)
    (U : UniLinksN (XI170 XI0) hn32 P A R0 Rest RestV e I0 I Ifin d DgJ8 enc md L PR dgOf (mdAppend (RM) (BM) da (dsbC, dsmC s1 d (XI170 XI0).l L enc)) vTOf)
    (colN : ι ⊕ Fin P.nq → ℕ) (O : OpsU (XI170 XI0) P A e vTOf colN rk encB)
    (hDom : DomLink (XI170 XI0) hn32) (hd : d.val = XI0.d) (hEnc : EncOK enc)
    (hR0 : RapInput R0 4)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, Polynomial.eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < 4)
    (hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
      SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    (hrate : 64 * (2 ^ (∑ j, ((s1) j).val) * d.val) ≤ 2 ^ (XI170 XI0).nD)
    (hF : goldilocks ^ 3 ≤ Fintype.card KC) (hm : m + 1 ≤ 2 ^ 12)
    (htoPoly : P.toPoly = udDecodeB ωS (31 / 64) (friBound s1 d))
    (hns : P.ns ≤ 2 ^ 20) (hD : P.D.card ≤ 2 ^ 32) (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8)
    (herrOld : ∀ r, errOld r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞))
    (hDg : goldilocks ^ 4 ≤ Nat.card DgJ8)
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
        AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsbC, dsmC s1 d (XI170 XI0).l L enc)) g (z, salt) π ∧ ¬ R0.Holds] ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ :=
  have RC := resid_codec XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L hDom hd hEnc encB rk hn1 hmd hL encZ decZ da dsbC
  exec_e2e XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR hl encZ decZ hz da dsbC (dsmC s1 d (XI170 XI0).l L enc) vTOf encB rk hn1 hmd hL hPS
    ⟨hU_of_N XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR encZ decZ da dsbC (dsmC s1 d (XI170 XI0).l L enc) vTOf U, RC.hX, RC.hcod0, RC.hcod, RC.hvalF, RC.hPdec,
      hW0_of_opsU XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L PR encZ decZ hz da dsbC (dsmC s1 d (XI170 XI0).l L enc) vTOf encB rk hn1 hmd hL U colN O hcsC_dsbC⟩
    hR0 hlink hnb hRest errOld herr0 hrate hF hm htoPoly hns hD hH hnq herrOld hDg Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

end Main

end NockvmE2E.Exec.E2EFinal
#print axioms NockvmE2E.Exec.E2EFinal.hcsC_dsbC
#print axioms NockvmE2E.Exec.E2EFinal.exec_e2e_final
